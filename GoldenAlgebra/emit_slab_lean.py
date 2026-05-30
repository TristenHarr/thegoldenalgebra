#!/usr/bin/env python3
"""
emit_slab_lean.py
=================

Generate per-slab Lean proofs of `SlabSimplePolyIneq` via the template
`slabSimplePolyIneq_of_const_cloud_and_analytic_tail` in rh.lean.

For each slab:
  • Define 50 zero upper bounds (rational, 4 decimal places, slightly
    above each Riemann γ_i).
  • Compute K_lb = Σ 1/(x_max² + γ_i_up² + y_max²), a rational lower
    bound for the actual Σ 1/(x_max² + γ_i² + y_max²).
  • Verify K_lb numerically clears the slab's needed K.
  • Emit Lean: 50-term list sum bound + scalar discharge + template
    application.

Output: per_slab_proofs.lean (Lean code to paste into rh.lean).
"""
from __future__ import annotations
import json
import math
from pathlib import Path
from fractions import Fraction
import mpmath as mp


def riemann_zeros_50(prec=40):
    mp.mp.dps = prec + 5
    return [mp.im(mp.zetazero(k)) for k in range(1, 51)]


def upper_bound_4_digits(g):
    """Return a Fraction upper bound on g, accurate to 4 decimals."""
    # ceil(g * 10000) / 10000  — 4 decimal places, always ≥ g.
    n = math.ceil(float(g) * 10000)
    return Fraction(n, 10000)


def K_lb_per_slab(zeros_up, x_max_sq_plus_y_max_sq):
    """Σ 1/(x_max² + γ_up² + y_max²) — exact Fraction."""
    total = Fraction(0)
    for g_up in zeros_up:
        # g_up is Fraction; g_up^2 is Fraction; denom is Fraction
        denom = x_max_sq_plus_y_max_sq + g_up * g_up
        total += Fraction(1) / denom
    return total


def needed_K_at_worst(Tmin, Tmax, C, D, K_actual_float, n_T=200, n_y=80):
    """Find the maximum K_required across the slab so error ≤ 2yK + tail."""
    needed_K_max = 0.0
    for i in range(n_T + 1):
        T = Tmin + (Tmax - Tmin) * i / n_T
        if T <= 2 * mp.pi: continue
        y_max = T / 2 - 1
        if y_max <= 0: continue
        for j in range(1, n_y + 1):
            y = max(1e-4, y_max * j / n_y)
            if y > y_max: continue
            eb = (y / T**2) * (17 * float(C) * mp.log(T)
                                + 17 * float(D) + 9 * float(C) / 2)
            tail = (mp.mpf(22)/15) * mp.log(T/(2*mp.pi))/(2*mp.pi) * y / T
            needed_K = float((eb - tail) / (2 * y)) if y > 0 else 0
            needed_K_max = max(needed_K_max, needed_K)
    return needed_K_max


SLAB_PLAN = [
    ("10_12",  10.0,  12.0,  Fraction(0),      Fraction(21, 100)),
    ("12_13",  12.0,  13.0,  Fraction(0),      Fraction(31, 100)),
    ("13_14",  13.0,  14.0,  Fraction(0),      Fraction(44, 100)),
    ("14_19",  14.0,  19.0,  Fraction(0),      Fraction(1, 2)),
    ("19_32",  19.0,  32.0,  Fraction(0),      Fraction(1)),
    ("32_36",  32.0,  36.0,  Fraction(1, 2),   Fraction(1, 2)),
    ("36_48",  36.0,  48.0,  Fraction(1, 2),   Fraction(1)),
    ("48_80",  48.0,  80.0,  Fraction(1, 2),   Fraction(49, 20)),
    ("80_140", 80.0,  140.0, Fraction(1, 2),   Fraction(49, 20)),
]


def main():
    print("Loading 50 zeros @ 40 digits …")
    zeros = riemann_zeros_50()
    zeros_up = [upper_bound_4_digits(g) for g in zeros]
    print(f"  γ_1 ≈ {mp.nstr(zeros[0], 8)},  upper-rational: {zeros_up[0]} "
          f"(decimal: {float(zeros_up[0])})")
    print(f"  γ_50 ≈ {mp.nstr(zeros[49], 8)}, upper-rational: {zeros_up[49]} "
          f"(decimal: {float(zeros_up[49])})")
    print()

    print(f"{'slab':>7s} {'x_max':>6s} {'K_lb (rational)':>18s} "
          f"{'K_needed':>10s} {'feasible?':>10s}")
    print("-" * 80)
    results = []
    for label, Tmin, Tmax, C, D in SLAB_PLAN:
        x_max = Fraction(int(Tmax * 10), 10) / 2 - 1   # x_max = Tmax/2 - 1
        # E.g. Tmax = 12.0 → x_max = 5
        # Actually for cleanliness use rational arithmetic on Tmax directly:
        x_max = Fraction(int(round(Tmax * 1000)), 1000) / 2 - 1
        xy_sq = x_max * x_max + x_max * x_max  # x_max² + y_max² with y_max = x_max
        K_lb = K_lb_per_slab(zeros_up, xy_sq)
        K_needed = needed_K_at_worst(Tmin, Tmax, C, D, float(K_lb))
        feas = float(K_lb) >= K_needed
        flag = "YES" if feas else "no"
        K_lb_dec = float(K_lb)
        print(f"  {label:>5s} {float(x_max):>6.1f} {K_lb_dec:>18.6e} "
              f"{K_needed:>10.6f} {flag:>10s}")
        results.append({
            "label": label, "Tmin": Tmin, "Tmax": Tmax,
            "C": str(C), "D": str(D),
            "x_max": str(x_max),
            "K_lb_num": K_lb.numerator,
            "K_lb_den": K_lb.denominator,
            "K_lb_decimal": K_lb_dec,
            "K_needed": K_needed,
            "feasible": feas,
        })

    out = Path(__file__).parent / "slab_K_lower_bounds.json"
    out.write_text(json.dumps({
        "zeros_up_rationals": [(g.numerator, g.denominator) for g in zeros_up],
        "results": results,
    }, indent=2))
    print(f"\nWrote {out}")
    print("\nFeasible slabs with K_lb ≥ K_needed (and 4-digit zero upper bounds):")
    for r in results:
        if r["feasible"]:
            print(f"  ✓ {r['label']}  (K_lb = {r['K_lb_decimal']:.6f},"
                  f" needs {r['K_needed']:.6f})")


if __name__ == "__main__":
    main()
