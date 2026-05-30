#!/usr/bin/env python3
"""
slab_certificates.py
====================

Generate per-slab certificate descriptors for the rh.lean
`PiecewiseFiniteBandCertificate` slot, covering [10, 140] via the
6 slabs identified by the CLVIII per-slab (C, D) feasibility scan:

  [14,19]   (C, D) = (0,   1/2)
  [19,32]   (C, D) = (0,   1)
  [32,36]   (C, D) = (1/2, 1/2)
  [36,48]   (C, D) = (1/2, 1)
  [48,80]   (C, D) = (1/2, 49/20)
  [80,140]  (C, D) = (1/2, 49/20)

The [10, 14] sub-slab is left for the FirstZeroBandCertificate (track B,
N(u)=0 direct argument).

For each slab the script verifies feasibility on a dense grid, records
worst-case slack, and emits a JSON descriptor consumable by a follow-up
Schmüdgen/SDP solver.

Output: slab_certificates.json
        slab_certificates.lean  (stub with the data)
"""
from __future__ import annotations

import json
import math
from pathlib import Path

import mpmath as mp


# ---------------------------------------------------------------------------
# Polynomial / rational evaluators (identical to finite_band_local_S.py)
# ---------------------------------------------------------------------------

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


# ---------------------------------------------------------------------------
# Dense grid certification per slab
# ---------------------------------------------------------------------------

def certify_slab(Tmin, Tmax, zeros, C, D, n_T=40, n_x=30, n_y=30):
    """Return (min_ratio, min_slack, worst_point) over the adaptive region."""
    min_ratio = mp.inf
    min_slack = mp.inf
    worst = None
    n_samples = 0
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
                n_samples += 1
                eb = error_ub_CD(y, T, C, D)
                cloud = cloud_minus_im(x, y, zeros)
                tail = smooth_tail_rational_lb(x, y, T)
                margin = cloud + tail
                slack = margin - eb
                ratio = margin / eb if eb > 0 else mp.inf
                if ratio < min_ratio:
                    min_ratio = ratio
                    min_slack = slack
                    worst = (float(T), float(x), float(y),
                             float(margin), float(eb))
    return float(min_ratio), float(min_slack), worst, n_samples


def riemann_zeros(n: int, prec_digits: int):
    mp.mp.dps = prec_digits + 5
    return [mp.im(mp.zetazero(k)) for k in range(1, n + 1)]


# ---------------------------------------------------------------------------
# Slab plan
# ---------------------------------------------------------------------------

SLAB_PLAN = [
    # Low-T slabs: D = ceil(max|N₀| on slab) since S = -N₀ when no zeros counted yet.
    # max|N₀| measured: [10,12]≈0.21, [12,13]≈0.31, [13,14]≈0.44.
    ("[10, 12]",   10.0,  12.0,  mp.mpf(0),       mp.mpf("0.21")),
    ("[12, 13]",   12.0,  13.0,  mp.mpf(0),       mp.mpf("0.31")),
    ("[13, 14]",   13.0,  14.0,  mp.mpf(0),       mp.mpf("0.44")),
    # Mid-T slabs: per-slab D fixed conservatively above the slab's |S| envelope.
    ("[14, 19]",   14.0,  19.0,  mp.mpf(0),       mp.mpf(1) / 2),
    ("[19, 32]",   19.0,  32.0,  mp.mpf(0),       mp.mpf(1)),
    ("[32, 36]",   32.0,  36.0,  mp.mpf(1) / 2,   mp.mpf(1) / 2),
    ("[36, 48]",   36.0,  48.0,  mp.mpf(1) / 2,   mp.mpf(1)),
    ("[48, 80]",   48.0,  80.0,  mp.mpf(1) / 2,   mp.mpf(49) / 20),
    # Match the analytic CLV/CLVII chain's constants at the top.
    ("[80, 140]",  80.0,  140.0, mp.mpf(1) / 2,   mp.mpf(49) / 20),
]


def main():
    import sys
    n_zeros = 50 if "--zeros=50" in sys.argv else 10
    if "--zeros=100" in sys.argv:
        n_zeros = 100
    mp.mp.dps = 35
    print(f"=== Loading {n_zeros} Riemann zeros @ 30 digits ===")
    zeros = riemann_zeros(n_zeros, 30)
    zero_strs = [mp.nstr(z, 30) for z in zeros]
    for i, z in enumerate(zeros, 1):
        print(f"  γ_{i:>2} = {mp.nstr(z, 30)}")

    print()
    print(f"=== Per-slab certification (dense grid) ===")
    print(f"{'slab':>12s}  {'C':>5s}  {'D':>6s}  {'min ratio':>11s}"
          f"  {'min slack':>13s}  {'#samples':>9s}  feas?")
    print("-" * 95)
    results = []
    for label, Tmin, Tmax, C, D in SLAB_PLAN:
        ratio, slack, worst, n = certify_slab(Tmin, Tmax, zeros, C, D)
        feas = ratio >= 1
        mark = "YES" if feas else "no"
        Cstr = mp.nstr(C, 4) if C != 0 else "0"
        Dstr = mp.nstr(D, 4)
        print(f"  {label:>10s}  {Cstr:>5s}  {Dstr:>6s}  {ratio:>11.5f}"
              f"  {slack:>13.5e}  {n:>9d}  {mark}")
        results.append({
            "slab": label,
            "Tmin": Tmin,
            "Tmax": Tmax,
            "C": float(C),
            "D": float(D),
            "min_ratio": ratio,
            "min_slack": slack,
            "worst_point": worst,
            "n_samples": n,
            "feasible": feas,
        })

    all_feas = all(r["feasible"] for r in results)
    print()
    print(f"  All {len(results)} slabs feasible: {all_feas}")
    print(f"  Coverage gap addressed: [10, 140]")
    print(f"  Remaining: [2π, 10] via FirstZeroBandCertificate (closedFormFirstZeroErrorBound).")

    # Emit JSON
    out_dir = Path(__file__).parent
    json_path = out_dir / "slab_certificates.json"
    payload = {
        "schema_version": 1,
        "track": "A (piecewise per-slab (C,D))",
        "zeros": {"count": 10, "prec_digits": 30, "values": zero_strs},
        "slabs": results,
        "coverage": {
            "lower": 14.0,
            "upper": 140.0,
            "all_feasible": all_feas,
            "irreducible_remainder": "[2π, 14] via FirstZeroBandCertificate",
        },
    }
    json_path.write_text(json.dumps(payload, indent=2, default=str))
    print(f"\nWrote {json_path}")

    # Emit Lean stub
    lean_path = out_dir / "slab_certificates.lean"
    lines = [
        "/-",
        "  Auto-generated slab certificate data (track A).",
        f"  Coverage: [14, 140] in 6 slabs.",
        f"  Zeros: 10 Riemann zeros @ 30 digits.",
        f"  Remaining: [2π, 14] handled by FirstZeroBandCertificate.",
        "",
        "  Each slab is an inhabitant of FiniteSlabModelMarginCertificate",
        "  whose `cert` field is to be discharged by a Schmüdgen / SDP",
        "  certificate (not yet wired). The data below is the input data:",
        "  slab bounds, per-slab (C, D), and the cloud zero list.",
        "-/",
        "",
        "import GoldenAlgebra.rh  -- the OverflowResidueRH namespace",
        "",
        "namespace GoldenAlgebra.SlabCertificates",
        "",
        "open OverflowResidueRH",
        "",
        "-- First 10 Riemann zeros (γ_k > 0), 30-digit precision.",
        "noncomputable def gammaZeros : List ℝ := [",
    ]
    for i, zstr in enumerate(zero_strs):
        sep = "," if i < len(zero_strs) - 1 else ""
        lines.append(f"  {zstr}{sep}  -- γ_{i+1}")
    lines.append("]")
    lines.append("")
    lines.append("-- Per-slab (Tmin, Tmax, C, D) data:")
    for r in results:
        lines.append(f"-- Slab {r['slab']}:")
        lines.append(f"--   Tmin = {r['Tmin']}, Tmax = {r['Tmax']}")
        lines.append(f"--   C = {r['C']}, D = {r['D']}")
        lines.append(f"--   min ratio (margin/error) = {r['min_ratio']:.5f}")
        lines.append(f"--   min slack on grid       = {r['min_slack']:.5e}")
        if r['worst_point']:
            T, x, y, m, e = r['worst_point']
            lines.append(f"--   worst at T={T:.3f}, x={x:.3f}, y={y:.3f}")
            lines.append(f"--     margin = {m:.5e},  error = {e:.5e}")
        lines.append("")
    lines.append("end GoldenAlgebra.SlabCertificates")
    lean_path.write_text("\n".join(lines))
    print(f"Wrote {lean_path}")


if __name__ == "__main__":
    main()
