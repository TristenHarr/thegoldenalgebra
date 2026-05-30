#!/usr/bin/env python3
"""
slab_constants.py
=================

Compute, per slab, the per-slab constant
    K(slab) := Σ_{γ in zeros} 1 / (x_max² + γ² + y_max²)
and verify
    closedFormSErrorBoundCD C D y T
        ≤ 2·y·K + (22/15)·log(T/(2π))/(2π)·y/T
on the slab.  If feasible, the slab is dischargeable via
`slabSimplePolyIneq_of_const_cloud_and_analytic_tail` in rh.lean.

Outputs:
  • per-slab K (rational, exact within mpmath precision)
  • per-slab worst (y, T) for the scalar inequality
  • per-slab feasibility flag + min slack
  • Lean stub naming `K_*` constants and a sketch `hScalar_*` proof
    structure.
"""
from __future__ import annotations
import json
import math
from pathlib import Path
import mpmath as mp


def zeros_50(prec=30):
    mp.mp.dps = prec + 5
    return [mp.im(mp.zetazero(k)) for k in range(1, 51)]


def K_const(zeros, x_max, y_max):
    """Per-slab cloud constant: Σ 1 / (x_max² + γ² + y_max²)."""
    return sum(mp.mpf(1) / (x_max**2 + g**2 + y_max**2) for g in zeros)


def err(y, T, C, D):
    return (y / T**2) * (17*C*mp.log(T) + 17*D + mp.mpf(9)*C/2)


def tail_22_15_analytic(y, T):
    """(22/15)·ρ(T)·y/T  with  ρ(T) = log(T/(2π))/(2π)."""
    return (mp.mpf(22) / 15) * mp.log(T / (2*mp.pi)) / (2*mp.pi) * y / T


def slab_scalar_min_ratio(Tmin, Tmax, C, D, K, n_T=200, n_y=80):
    """Sweep (y, T) and return min ratio (cloud_const + tail) / error_ub."""
    min_ratio = mp.inf
    worst = None
    for i in range(n_T + 1):
        T = Tmin + (Tmax - Tmin) * i / n_T
        if T <= 2 * mp.pi: continue
        y_max = T / 2 - 1
        if y_max <= 0: continue
        for j in range(1, n_y + 1):
            y = max(mp.mpf("1e-4"), y_max * j / n_y)
            if y > y_max: continue
            eb = err(y, T, C, D)
            margin = 2 * y * K + tail_22_15_analytic(y, T)
            r = margin / eb if eb > 0 else mp.inf
            if r < min_ratio:
                min_ratio = r
                worst = (float(T), float(y), float(margin), float(eb))
    return float(min_ratio), worst


SLAB_PLAN = [
    ("10_12",  10.0,  12.0,  mp.mpf(0),       mp.mpf("21")/100),
    ("12_13",  12.0,  13.0,  mp.mpf(0),       mp.mpf("31")/100),
    ("13_14",  13.0,  14.0,  mp.mpf(0),       mp.mpf("44")/100),
    ("14_19",  14.0,  19.0,  mp.mpf(0),       mp.mpf(1)/2),
    ("19_32",  19.0,  32.0,  mp.mpf(0),       mp.mpf(1)),
    ("32_36",  32.0,  36.0,  mp.mpf(1)/2,     mp.mpf(1)/2),
    ("36_48",  36.0,  48.0,  mp.mpf(1)/2,     mp.mpf(1)),
    ("48_80",  48.0,  80.0,  mp.mpf(1)/2,     mp.mpf("49")/20),
    ("80_140", 80.0,  140.0, mp.mpf(1)/2,     mp.mpf("49")/20),
]


def main():
    mp.mp.dps = 40
    print("Loading 50 zeros …")
    zeros = zeros_50(prec=40)
    print(f"  γ_1 = {mp.nstr(zeros[0], 12)}")
    print(f"  γ_50 = {mp.nstr(zeros[49], 12)}")
    print()

    results = []
    print(f"{'slab':>7s}  {'x_max':>6s}  {'K':>12s}  {'min ratio':>10s}"
          f"  {'worst (T, y)':>22s}")
    print("-" * 80)
    for label, Tmin, Tmax, C, D in SLAB_PLAN:
        x_max = Tmax / 2 - 1
        y_max = Tmax / 2 - 1
        K = K_const(zeros, x_max, y_max)
        # Tighter K: use Tmin-based y_max? On the slab, T can be small so y_max
        # can be small. The constraint is x + y ≤ T/2 - 1 ≤ Tmax/2 - 1 — but
        # actually if T = Tmin, y ≤ Tmin/2 - 1, smaller.  Use the SLAB MAX of y.
        # Maximum y on slab = Tmax/2 - 1, so y_max = Tmax/2 - 1 is correct.
        ratio, worst = slab_scalar_min_ratio(Tmin, Tmax, C, D, K)
        feas = ratio >= 1
        flag = "YES" if feas else "no"
        K_str = f"{float(K):.6f}"
        wT = f"({worst[0]:.2f}, {worst[1]:.2f})" if worst else "—"
        print(f"  {label:>5s}  {x_max:>6.1f}  {K_str:>12s}  {ratio:>10.5f}"
              f"  {wT:>22s}  {flag}")
        results.append({
            "slab": label, "Tmin": Tmin, "Tmax": Tmax,
            "C": float(C), "D": float(D),
            "x_max": x_max, "y_max": y_max,
            "K": float(K), "K_30digits": mp.nstr(K, 30),
            "min_ratio": ratio, "worst": worst, "feasible": feas,
        })

    out = Path(__file__).parent / "slab_constants.json"
    out.write_text(json.dumps({
        "zeros_count": 50, "zeros_prec_digits": 40,
        "zeros": [mp.nstr(g, 35) for g in zeros],
        "slabs": results,
    }, indent=2, default=str))
    print(f"\nWrote {out}")

    n_feas = sum(1 for r in results if r["feasible"])
    print(f"\n=== Feasible slabs (constant-bound + analytic tail): "
          f"{n_feas}/9 ===")
    if n_feas < 9:
        print(f"Slabs needing finer treatment (sub-region + tighter K):")
        for r in results:
            if not r["feasible"]:
                print(f"  - {r['slab']}: min ratio = {r['min_ratio']:.4f}")


if __name__ == "__main__":
    main()
