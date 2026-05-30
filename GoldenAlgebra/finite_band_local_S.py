#!/usr/bin/env python3
"""
finite_band_local_S.py
======================

Same setup as finite_band_feasibility.py, but parameterise the
error envelope by per-slab (C, D):

    error_ub(y, T; C, D) = (y/T²) · (8*(C·log T + D) + 18 * (C·(log T/(2T²) + 1/(4T²)) + D/(2T²)) * T²)
                         = (y/T²) · (8*(C·log T + D) + 9*C·log T + 9*C/2 + 9*D)

Wait — that's the closedFormSErrorBoundCD. Let me actually use the rh.lean
formula directly:

    closedFormSErrorBoundCD C D y T
      = 8·y·(C·log T + D)/T² + 18·y·(C·(log T/(2T²) + 1/(4T²)) + D/(2T²))
      = (y/T²)·( 8·C·log T + 8D + 9·C·log T + 9·C/2 + 9·D )
      = (y/T²)·( 17·C·log T + 8D + 9·C/2 + 9·D )
      = (y/T²)·( 17·C·log T + 17·D + 9·C/2 )

Hmm wait let me recompute. With C=1/2, D=49/20:
   17·(1/2)·log T + 17·(49/20) + 9·(1/2)/2
   = (17/2)·log T + 833/20 + 9/4
   = (17/2)·log T + (833 + 45)/20
   = (17/2)·log T + 878/20
   = (17/2)·log T + 439/10  ✓

Good. So in general:
    closedFormSErrorBoundCD C D y T = (y/T²) · ( 17·C·log T + (17·D + 9·C/2) )

For Mode B (C=1/2, D=1):    coefficient = (17/2)·log T + 17 + 9/4 = (17/2)·log T + 77/4
For Mode C (C=1/2, D=1/2):  coefficient = (17/2)·log T + 17/2 + 9/4 = (17/2)·log T + 43/4
For Mode D (C=0, D=D_slab): coefficient = 17·D_slab
For Mode E (C=1/2 log T scaling with smaller D_slab): explore.
"""
from __future__ import annotations

import math
from typing import List

import mpmath as mp


def riemann_zeros(n: int, prec_digits: int) -> List[mp.mpf]:
    mp.mp.dps = prec_digits + 5
    return [mp.im(mp.zetazero(k)) for k in range(1, n + 1)]


def error_ub_CD(y, T, C, D):
    """closedFormSErrorBoundCD C D y T = (y/T²)·(17·C·log T + 17·D + 9·C/2)."""
    return (y / T ** 2) * (17 * C * mp.log(T) + 17 * D + mp.mpf(9) * C / 2)


def cloud_minus_im(x, y, zeros):
    total = mp.mpf(0)
    for g in zeros:
        total += y / ((x - g) ** 2 + y ** 2)
        total += y / ((x + g) ** 2 + y ** 2)
    return total


def rho(T):
    return mp.log(T / (2 * mp.pi)) / (2 * mp.pi)


def smooth_tail_rational_lb(x, y, T):
    ax = abs(x)
    return rho(T) * (
        y * (T - ax) / ((T - ax) ** 2 + y ** 2)
        + y * (T + ax) / ((T + ax) ** 2 + y ** 2)
    )


def scan_slab(Tmin, Tmax, zeros, C, D, n_T=20, n_x=15, n_y=15):
    worst_ratio = mp.inf
    worst_pt = None
    for i in range(n_T + 1):
        T = Tmin + (Tmax - Tmin) * i / n_T
        if T <= 2 * mp.pi:
            continue
        x_y_max = T / 2 - 1
        if x_y_max <= 0:
            continue
        for j in range(n_x + 1):
            x = x_y_max * j / n_x
            for k in range(1, n_y + 1):
                y = max(mp.mpf("1e-6"), (x_y_max - x) * k / n_y)
                if x + y > x_y_max:
                    continue
                eb = error_ub_CD(y, T, C, D)
                cloud = cloud_minus_im(x, y, zeros)
                tail = smooth_tail_rational_lb(x, y, T)
                margin = cloud + tail
                ratio = margin / eb if eb > 0 else mp.inf
                if ratio < worst_ratio:
                    worst_ratio = ratio
                    worst_pt = (float(T), float(x), float(y))
    return float(worst_ratio), worst_pt


def main():
    mp.mp.dps = 35
    print("=== Loading 50 zeros @ 30 digits ===")
    zeros = riemann_zeros(50, 30)

    modes = [
        ("A: C=1/2, D=49/20 (global Turing)", mp.mpf(1)/2, mp.mpf(49)/20),
        ("B: C=1/2, D=1",                     mp.mpf(1)/2, mp.mpf(1)),
        ("C: C=1/2, D=1/2",                   mp.mpf(1)/2, mp.mpf(1)/2),
        ("D: C=0,   D=1   (constant)",        mp.mpf(0),   mp.mpf(1)),
        ("E: C=0,   D=1/2",                   mp.mpf(0),   mp.mpf(1)/2),
        ("F: C=0,   D=1/4",                   mp.mpf(0),   mp.mpf(1)/4),
    ]
    slabs = [
        (2 * mp.pi, 10),
        (10, 20),
        (20, 40),
        (40, 80),
        (80, 140),
    ]
    print()
    print(f"{'Mode':>40s} | " + " | ".join(f"[{float(t1):.3f}, {t2}]"
                                            for t1, t2 in slabs))
    print("-" * 130)
    for label, C, D in modes:
        ratios = []
        for Tmin, Tmax in slabs:
            r, _ = scan_slab(Tmin, Tmax, zeros, C, D)
            ratios.append(r)
        cells = []
        for r in ratios:
            flag = "" if r >= 1 else "*"
            cells.append(f"{r:.3f}{flag}")
        print(f"{label:>40s} | " + " | ".join(f"{c:>10s}" for c in cells))
    print()
    print(" '*' = infeasible (ratio < 1)")

    # Find lowest T0 reachable per mode
    print()
    print("=== Lowest T0 reachable per mode (sweeping 1-wide slabs) ===")
    fine_slabs = [(t, t+1) for t in range(7, 80)]
    for label, C, D in modes:
        lowest_feasible = None
        for Tmin, Tmax in fine_slabs:
            r, _ = scan_slab(Tmin, Tmax, zeros, C, D, n_T=10, n_x=10, n_y=10)
            if r >= 1:
                lowest_feasible = Tmin
                break
        if lowest_feasible is not None:
            print(f"  {label:>40s}: lowest feasible 1-wide slab starts at T={lowest_feasible}")
        else:
            print(f"  {label:>40s}: no 1-wide slab in [7,80] is feasible")


if __name__ == "__main__":
    main()
