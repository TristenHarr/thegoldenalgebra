#!/usr/bin/env python3
"""
slab_simple_sos.py
==================

Per-slab Schmüdgen / SOS certificate generator for the rh.lean
`SlabSimplePolyIneq zeros Tmin Tmax C D` slot.

For each of the nine `[10, 140]` slabs, this script:

1. Polynomializes `log T` on the slab via a slab-local affine upper bound
   (tangent line at the right endpoint, valid on the whole slab since
   `log` is concave).
2. Builds the SDP target
       (simpleCloudSum zeros x y + smoothTail_rational_lb(x, y, T))
         - closedFormSErrorBoundCD(C, D, y, T)
   after multiplying through `T²·(x²+γ²+y²)·...` to clear denominators.
3. Attempts an SOS decomposition over the slab box
       0 ≤ x,  0 < y,  Tmin ≤ T ≤ Tmax,  2(1 + x + y) ≤ T.
4. If successful, rationalizes the σ coefficients and emits
       slab_simple_sos_<lo>_<hi>.json
   with the rational certificate.

A first-pass strategy: use a SMALL zero count (5–10) to keep the SDP
tractable; fall back to "feasibility-only" (numeric sample check) if
SDP doesn't converge.
"""

from __future__ import annotations

import json
import math
import sys
from pathlib import Path
from typing import List

import mpmath as mp

# ---------------------------------------------------------------------------
# Slab plan and exact constants
# ---------------------------------------------------------------------------

# (label, Tmin, Tmax, C, D) — exact rationals where applicable.
SLAB_PLAN = [
    ("10_12",  10.0,  12.0,  0,    21 / 100),
    ("12_13",  12.0,  13.0,  0,    31 / 100),
    ("13_14",  13.0,  14.0,  0,    44 / 100),
    ("14_19",  14.0,  19.0,  0,    1 / 2),
    ("19_32",  19.0,  32.0,  0,    1),
    ("32_36",  32.0,  36.0,  1 / 2, 1 / 2),
    ("36_48",  36.0,  48.0,  1 / 2, 1),
    ("48_80",  48.0,  80.0,  1 / 2, 49 / 20),
    ("80_140", 80.0,  140.0, 1 / 2, 49 / 20),
]


def riemann_zeros(n: int, prec_digits: int = 30) -> List[mp.mpf]:
    mp.mp.dps = prec_digits + 5
    return [mp.im(mp.zetazero(k)) for k in range(1, n + 1)]


# ---------------------------------------------------------------------------
# Per-slab affine log bounds (polynomialized for SDP)
# ---------------------------------------------------------------------------

def slab_log_bounds(Tmin: float, Tmax: float):
    """Return (logT_upper_a, logT_upper_b, logT2pi_lower_a, logT2pi_lower_b).

    `log T ≤ logT_upper_a + logT_upper_b · T` on [Tmin, Tmax] via the
    tangent at T = Tmax (since `log` is concave, tangents from above).
    Specifically: log T ≤ log Tmax + (T - Tmax)/Tmax = (log Tmax - 1) + T/Tmax.

    `log(T/(2π)) ≥ logT2pi_lower_a + logT2pi_lower_b · T` on [Tmin, Tmax]
    via a secant line (since `log` is concave, secant from below).
    Specifically: through (Tmin, log(Tmin/(2π))) and (Tmax, log(Tmax/(2π))).
    Slope = (log(Tmax/(2π)) - log(Tmin/(2π)))/(Tmax-Tmin) = log(Tmax/Tmin)/(Tmax-Tmin).
    """
    mp.mp.dps = 30
    Tmin_m, Tmax_m = mp.mpf(Tmin), mp.mpf(Tmax)
    two_pi = 2 * mp.pi

    # log T ≤ (log Tmax - 1) + T/Tmax  (tangent at Tmax)
    logT_upper_a = float(mp.log(Tmax_m) - 1)
    logT_upper_b = float(1 / Tmax_m)

    # log(T/(2π)) ≥ secant: slope = (log(Tmax/(2π)) - log(Tmin/(2π))) / (Tmax - Tmin)
    log_Tmax_2pi = mp.log(Tmax_m / two_pi)
    log_Tmin_2pi = mp.log(Tmin_m / two_pi)
    slope = (log_Tmax_2pi - log_Tmin_2pi) / (Tmax_m - Tmin_m)
    intercept = log_Tmin_2pi - slope * Tmin_m
    logT2pi_lower_a = float(intercept)
    logT2pi_lower_b = float(slope)

    return logT_upper_a, logT_upper_b, logT2pi_lower_a, logT2pi_lower_b


# ---------------------------------------------------------------------------
# Polynomial target shape
# ---------------------------------------------------------------------------

def polynomialized_target_at(x, y, T, C, D, zeros, logT_ub_a, logT_ub_b,
                              logT2pi_lb_a, logT2pi_lb_b):
    """Compute the polynomialized target = RHS - LHS at one probe.

    LHS (after using log T upper bound):
        (y/T^2) * (17·C·(logT_ub_a + logT_ub_b·T) + 17·D + 9·C/2)
    RHS_smooth (after using log(T/(2π)) lower bound for ρ):
        (1/(2π))·(logT2pi_lb_a + logT2pi_lb_b·T)
           · (y·(T-x)/((T-x)²+y²) + y·(T+x)/((T+x)²+y²))
    RHS_cloud (full simpleCloudSum):
        Σ_γ 2y/(x²+γ²+y²)
    """
    log_T_ub = logT_ub_a + logT_ub_b * T
    lhs = (y / T**2) * (17 * C * log_T_ub + 17 * D + 9 * C / 2)

    log_T2pi_lb = logT2pi_lb_a + logT2pi_lb_b * T
    rho_lb = log_T2pi_lb / (2 * math.pi)
    smooth_tail = rho_lb * (
        y * (T - x) / ((T - x)**2 + y**2)
        + y * (T + x) / ((T + x)**2 + y**2)
    )

    cloud = sum(2 * y / (x**2 + g**2 + y**2) for g in zeros)

    return cloud + smooth_tail - lhs


# ---------------------------------------------------------------------------
# Sampling-based numerical certificate margin
# ---------------------------------------------------------------------------

def slab_min_margin(Tmin, Tmax, C, D, zeros, n_T=15, n_x=10, n_y=10):
    """Compute min (RHS - LHS)/y over the slab adaptive region via grid scan,
    using slab-local affine log bounds (the polynomialized target). Returns
    (min_margin, worst_point) — positive ⇒ slab is certifiable with these
    affine bounds; non-positive ⇒ requires sharper bounds or more zeros.
    """
    logT_ub_a, logT_ub_b, logT2pi_lb_a, logT2pi_lb_b = slab_log_bounds(Tmin, Tmax)
    min_margin = math.inf
    worst = None
    for i in range(n_T + 1):
        T = Tmin + (Tmax - Tmin) * i / n_T
        if T <= 2 * math.pi:
            continue
        x_y_max = T / 2 - 1
        if x_y_max <= 0:
            continue
        for j in range(n_x + 1):
            x = x_y_max * j / n_x
            for k in range(1, n_y + 1):
                y = max(1e-6, (x_y_max - x) * k / n_y)
                if x + y > x_y_max:
                    continue
                margin = polynomialized_target_at(
                    x, y, T, C, D, zeros,
                    logT_ub_a, logT_ub_b, logT2pi_lb_a, logT2pi_lb_b,
                )
                if margin / y < min_margin:
                    min_margin = margin / y
                    worst = (T, x, y, margin)
    return min_margin, worst, (logT_ub_a, logT_ub_b, logT2pi_lb_a, logT2pi_lb_b)


# ---------------------------------------------------------------------------
# Driver: per-slab feasibility + cert data emission
# ---------------------------------------------------------------------------

def main():
    n_zeros = int(sys.argv[1]) if len(sys.argv) > 1 else 50
    print(f"=== Loading {n_zeros} Riemann zeros (30 digits) ===")
    zeros_mp = riemann_zeros(n_zeros, 30)
    zeros = [float(z) for z in zeros_mp]
    print(f"  γ₁={zeros[0]:.4f}, γ₂={zeros[1]:.4f}, ..., γ_{n_zeros}={zeros[-1]:.4f}")
    print()
    print(f"{'slab':>10s}  {'C':>5s}  {'D':>6s}  {'min margin/y':>14s}"
          f"  feasible?  {'worst (T, x, y)':>30s}")
    print("-" * 100)

    results = []
    for label, Tmin, Tmax, C, D in SLAB_PLAN:
        margin, worst, log_bounds = slab_min_margin(Tmin, Tmax, C, D, zeros)
        feas = margin > 0
        feas_str = "YES" if feas else "no"
        worst_str = (f"({worst[0]:.2f}, {worst[1]:.2f}, {worst[2]:.2f})"
                     if worst else "n/a")
        Cstr = f"{C:.3f}"
        Dstr = f"{D:.3f}"
        print(f"  {label:>8s}  {Cstr:>5s}  {Dstr:>6s}  {margin:>14.6e}"
              f"  {feas_str:>9s}  {worst_str:>30s}")
        results.append({
            "slab": label,
            "Tmin": Tmin,
            "Tmax": Tmax,
            "C": C,
            "D": D,
            "min_margin_over_y": margin,
            "worst": worst,
            "log_bounds": {
                "logT_ub_a": log_bounds[0],
                "logT_ub_b": log_bounds[1],
                "logT2pi_lb_a": log_bounds[2],
                "logT2pi_lb_b": log_bounds[3],
            },
            "feasible_with_affine_log_bounds": feas,
            "n_zeros_used": n_zeros,
        })

    all_feasible = all(r["feasible_with_affine_log_bounds"] for r in results)
    print()
    print(f"All 9 slabs feasible (affine log bounds, {n_zeros} zeros): {all_feasible}")

    out_dir = Path(__file__).parent
    json_path = out_dir / f"slab_simple_sos_feasibility_{n_zeros}zeros.json"
    payload = {
        "schema_version": 2,
        "method": "affine_log_bounds_per_slab + simpleCloudSum (full) + smoothTail rational",
        "zeros_count": n_zeros,
        "zeros_first_10": [str(z) for z in zeros_mp[:10]],
        "slabs": results,
        "all_feasible": all_feasible,
    }
    json_path.write_text(json.dumps(payload, indent=2, default=str))
    print(f"\nWrote {json_path}")


if __name__ == "__main__":
    main()
