#!/usr/bin/env python3
"""
finite_band_feasibility.py
==========================

Per-slab feasibility scan for the FiniteBandModelMarginCertificate slot
in rh.lean.  For each slab [Tmin, Tmax] in
   [2π, 10], [10, 20], [20, 40], [40, 80], [80, 140]
report whether the inequality

    error_ub(y, T) ≤ cloud_lb(x, y) + smoothTailRational_lb(x, y, T)

is feasible with `num_zeros` zeros @ `prec_digits` digits.  The model is

    model = cloud + densityTail
    cloud(z)        = sum_{k=1}^{N}  ( 1/(z - γ_k) + 1/(z + γ_k) )
    -Im(cloud z)    = sum_k  y/((x-γ_k)² + y²) + y/((x+γ_k)² + y²)
    densityTail bound (rh.lean CLV, smoothTailRationalLowerBoundAbs):
       ρ(T) · ( y(T-|x|)/((T-|x|)²+y²) + y(T+|x|)/((T+|x|)²+y²) )
       with ρ(T) = log(T/(2π))/(2π).
    error_ub(y, T) = (y/T²) · ((17/2)·log T + 439/10)
                     (rh.lean closedFormSErrorBoundCD at C=1/2, D=49/20).

The slab is feasible iff the ratio (cloud+tail)/error stays ≥ 1 on the
adaptive region { x ≥ 0, y > 0, 2(1+x+y) ≤ T, Tmin ≤ T ≤ Tmax }.

This script does NOT generate Schmüdgen certificates yet — it just
identifies which slabs need escalation per the user's strategy:
   10 zeros → 50 zeros → tighter slab split → fresh integral bound.
"""
from __future__ import annotations

import math
import sys
from typing import List

import mpmath as mp


# ---------------------------------------------------------------------------
# 1. Riemann zeros
# ---------------------------------------------------------------------------

def riemann_zeros(n: int, prec_digits: int) -> List[mp.mpf]:
    """First `n` Riemann zeros (imaginary parts γ_k > 0) at `prec_digits` digits."""
    mp.mp.dps = prec_digits + 5
    return [mp.im(mp.zetazero(k)) for k in range(1, n + 1)]


# ---------------------------------------------------------------------------
# 2. Polynomial / rational evaluators
# ---------------------------------------------------------------------------

def error_ub(y, T):
    """rh.lean closedFormSErrorBoundCD (1/2) (49/20) y T."""
    return (y / T ** 2) * ((mp.mpf("17") / 2) * mp.log(T) + mp.mpf("439") / 10)


def cloud_minus_im(x, y, zeros):
    """-Im(cloud z) = Σ y/((x-γ_k)² + y²) + y/((x+γ_k)² + y²)."""
    total = mp.mpf(0)
    for g in zeros:
        total += y / ((x - g) ** 2 + y ** 2)
        total += y / ((x + g) ** 2 + y ** 2)
    return total


def rho(T):
    return mp.log(T / (2 * mp.pi)) / (2 * mp.pi)


def smooth_tail_rational_lb(x, y, T):
    """rh.lean smoothTailRationalLowerBoundAbs."""
    ax = abs(x)
    return rho(T) * (
        y * (T - ax) / ((T - ax) ** 2 + y ** 2)
        + y * (T + ax) / ((T + ax) ** 2 + y ** 2)
    )


# ---------------------------------------------------------------------------
# 3. Slab feasibility scan
# ---------------------------------------------------------------------------

def scan_slab(Tmin, Tmax, zeros, n_T=20, n_x=15, n_y=15):
    """Compute worst-case ratio (cloud+tail)/error and slack on grid."""
    worst_ratio = mp.inf
    worst_slack = mp.inf
    worst_pt = None
    for i in range(n_T + 1):
        T = Tmin + (Tmax - Tmin) * i / n_T
        if T <= 2 * mp.pi:
            continue
        # Adaptive region: 2(1+|x|+y) ≤ T → |x|+y ≤ T/2 - 1
        x_y_max = T / 2 - 1
        if x_y_max <= 0:
            continue
        for j in range(n_x + 1):
            x = x_y_max * j / n_x
            for k in range(1, n_y + 1):
                y = max(mp.mpf("1e-6"), (x_y_max - x) * k / n_y)
                if x + y > x_y_max:
                    continue
                eb = error_ub(y, T)
                cloud = cloud_minus_im(x, y, zeros)
                tail = smooth_tail_rational_lb(x, y, T)
                margin = cloud + tail
                ratio = margin / eb if eb > 0 else mp.inf
                slack = margin - eb
                if ratio < worst_ratio:
                    worst_ratio = ratio
                    worst_slack = slack
                    worst_pt = (float(T), float(x), float(y))
    return float(worst_ratio), float(worst_slack), worst_pt


def main():
    mp.mp.dps = 35
    num_zeros = 10
    prec_digits = 30

    print(f"=== Loading first {num_zeros} Riemann zeros @ {prec_digits} digits ===")
    zeros = riemann_zeros(num_zeros, prec_digits)
    for i, g in enumerate(zeros, 1):
        print(f"  γ_{i:>2} = {mp.nstr(g, prec_digits)}")

    slabs = [
        (2 * mp.pi, 10),
        (10, 20),
        (20, 40),
        (40, 80),
        (80, 140),
    ]

    print()
    print(f"=== Per-slab feasibility on adaptive region ({num_zeros} zeros) ===")
    print(f"  {'slab':>20s}  {'min ratio':>12s}  {'min slack':>14s}  feasible?")
    print(f"  {'----':>20s}  {'---------':>12s}  {'---------':>14s}  ---------")
    summary = []
    for Tmin, Tmax in slabs:
        ratio, slack, pt = scan_slab(Tmin, Tmax, zeros)
        feas = ratio >= 1
        label = "YES" if feas else "NO (escalate)"
        slab_lbl = f"[{float(Tmin):.4f}, {float(Tmax)}]"
        print(f"  {slab_lbl:>20s}  {ratio:>12.4f}  {slack:>14.4e}  {label}")
        if pt is not None:
            print(f"      worst case: T={pt[0]:.3f}, x={pt[1]:.3f}, y={pt[2]:.3f}")
        summary.append((Tmin, Tmax, ratio, slack, feas, pt))

    # Escalation suggestions
    print()
    print("=== Escalation plan ===")
    any_fail = False
    for Tmin, Tmax, ratio, slack, feas, pt in summary:
        if not feas:
            any_fail = True
            print(f"  slab [{float(Tmin):.4f}, {Tmax}] needs more (ratio {ratio:.4f})")
    if not any_fail:
        print(f"  All {len(summary)} slabs feasible with {num_zeros} zeros.")
        print("  Next: build closed-form Schmüdgen certificate per slab.")

    return summary


if __name__ == "__main__":
    main()
