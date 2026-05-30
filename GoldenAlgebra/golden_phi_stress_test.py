"""
Step 41: φ robustness stress test.

Three checks for the Step 40 signal that ω = φ generalizes best for the
Lorentzian resonance match between the discretized Mellin/dilation
operator and the zeta zeros:

  (A) Fine detuning sweep ω = φ + Δ for Δ ∈ [-0.08, +0.08] step 0.005.
      Question: is there a real local minimum at φ, or did φ just happen
      to win among a sparse list?

  (B) Discretization sweep: grid sizes 150, 200, 250, 300, 400.
      Question: is the ranking robust to changing the numerical grid?

  (C) Train/test split sweep: 1-30|31-60, 1-40|41-80, 1-50|51-100,
      20-60|61-100. Question: does φ generalize across different zero
      ranges, not just one?
"""

import math
import numpy as np
from numpy.random import default_rng
from scipy.linalg import eigh_tridiagonal
from scipy.optimize import minimize
from mpmath import mp, zetazero

SQRT5 = math.sqrt(5.0)
PHI = (1.0 + SQRT5) / 2.0


def zeta_ordinates(N):
    mp.dps = 30
    return np.array([float(zetazero(k + 1).imag) for k in range(N)])


def resonance(t_grid, peaks, eps):
    diff = t_grid[:, None] - peaks[None, :]
    return np.sum(eps / (diff * diff + eps * eps), axis=1)


def positive_eigvals(u_grid, h, omega, params):
    a, b, c = params
    V = (a * np.cos(2.0 * math.pi * u_grid * omega)
         + b * np.sin(2.0 * math.pi * u_grid * omega)
         + c * u_grid)
    off = np.full(len(u_grid) - 1, 1.0 / (2.0 * h))
    w = eigh_tridiagonal(V, off, eigvals_only=True)
    return w[w > 0]


def fit_omega(omega, u_grid, h, t_train, Z_train, t_test, Z_test, eps,
              n_restarts=5, max_iter=2500, seeds=(0, 17)):
    best_loss = float("inf")
    best_p = None
    for seed in seeds:
        rng = default_rng(seed)
        for trial in range(n_restarts):
            x0 = rng.standard_normal(3) * 2.0
            res = minimize(
                lambda p: float(np.mean((
                    resonance(t_train, positive_eigvals(u_grid, h, omega, p), eps)
                    - Z_train) ** 2)),
                x0, method="Nelder-Mead",
                options={"xatol": 1e-6, "fatol": 1e-8,
                         "maxiter": max_iter, "adaptive": True},
            )
            if res.fun < best_loss:
                best_loss = res.fun
                best_p = res.x
    eig = positive_eigvals(u_grid, h, omega, best_p)
    R_tr = resonance(t_train, eig, eps)
    R_te = resonance(t_test, eig, eps)
    rmse_tr = float(np.sqrt(np.mean((R_tr - Z_train) ** 2)))
    rmse_te = float(np.sqrt(np.mean((R_te - Z_test) ** 2)))
    return rmse_tr, rmse_te


def setup_split(targets, lo, mid, hi, eps):
    """Train on ordinates [lo, mid), test on [mid, hi). Returns t_grids, Z."""
    t_train = np.linspace(max(0.0, targets[lo] - 3.0),
                          targets[mid - 1] + 3.0, 500)
    t_test = np.linspace(targets[mid] - 1.0,
                         targets[hi - 1] + 3.0, 500)
    Z_train = resonance(t_train, targets[lo:mid], eps)
    Z_test = resonance(t_test, targets[mid:hi], eps)
    return t_train, Z_train, t_test, Z_test


def make_grid(N_grid, L):
    u_grid = np.linspace(0.0, L, N_grid)
    h = u_grid[1] - u_grid[0]
    return u_grid, h


def rank_of(label, rows):
    sorted_rows = sorted(rows, key=lambda r: r["te"])
    for i, r in enumerate(sorted_rows):
        if r["label"] == label:
            return i + 1, sorted_rows[0]["label"], sorted_rows[0]["omega"]
    return None, None, None


def fmt_row(r):
    return f"ω={r['omega']:8.5f}  RMSE_tr={r['tr']:7.4f}  RMSE_te={r['te']:7.4f}"


def check_A_fine_detuning():
    print("=" * 78)
    print("(A) FINE DETUNING AROUND φ:  ω = φ + Δ, Δ ∈ [-0.08, 0.08] step 0.005")
    print("=" * 78)
    eps = 0.5
    N_grid = 250
    L = math.pi
    u_grid, h = make_grid(N_grid, L)
    targets = zeta_ordinates(60)
    t_train, Z_train, t_test, Z_test = setup_split(targets, 0, 30, 60, eps)

    deltas = np.round(np.arange(-0.08, 0.0801, 0.005), 4)
    print(f"  Grid {N_grid}, split 1-30|31-60, {len(deltas)} ω values.")
    rows = []
    for d in deltas:
        omega = PHI + d
        rmse_tr, rmse_te = fit_omega(
            omega, u_grid, h, t_train, Z_train, t_test, Z_test, eps,
            n_restarts=4, seeds=(0, 17))
        rows.append({"label": f"Δ={d:+.3f}", "omega": omega,
                     "delta": d, "tr": rmse_tr, "te": rmse_te})

    # Find best
    best = min(rows, key=lambda r: r["te"])
    phi_row = next(r for r in rows if abs(r["delta"]) < 1e-6)
    print(f"  best ω    = {best['omega']:.5f} (Δ={best['delta']:+.3f}), "
          f"RMSE_te={best['te']:.4f}")
    print(f"  φ itself  = {phi_row['omega']:.5f} (Δ=+0.000), "
          f"RMSE_te={phi_row['te']:.4f}")
    print(f"  φ rank    = {sorted(rows, key=lambda r: r['te']).index(phi_row)+1} / {len(rows)}")
    # Distance from best Δ to 0
    print(f"  best Δ    = {best['delta']:+.3f} "
          f"(distance {abs(best['delta']):.3f} from φ)")
    print()
    print(f"  Detuning curve (sorted by Δ):")
    print(f"    {'Δ':>7s}  {'ω':>8s}  {'RMSE_tr':>8s}  {'RMSE_te':>8s}")
    for r in sorted(rows, key=lambda r: r["delta"]):
        mark = " <-- φ" if abs(r["delta"]) < 1e-6 else (
            " <-- best" if r is best else "")
        print(f"    {r['delta']:+7.3f}  {r['omega']:8.5f}  "
              f"{r['tr']:8.4f}  {r['te']:8.4f}{mark}")
    print()


def check_B_grid_sizes():
    print("=" * 78)
    print("(B) GRID-SIZE ROBUSTNESS: rank of φ across N_grid ∈ {150, 200, 250, 300, 400}")
    print("=" * 78)
    eps = 0.5
    L = math.pi
    targets = zeta_ordinates(60)
    t_train, Z_train, t_test, Z_test = setup_split(targets, 0, 30, 60, eps)
    grids = [150, 200, 250, 300, 400]
    key_omegas = [
        ("φ           ", PHI),
        ("φ-0.05      ", PHI - 0.05),
        ("φ+0.05      ", PHI + 0.05),
        ("√2          ", math.sqrt(2)),
        ("√3          ", math.sqrt(3)),
        ("√5          ", math.sqrt(5)),
        ("π           ", math.pi),
        ("e           ", math.e),
        ("13/8        ", 13.0 / 8.0),
    ]
    for Ng in grids:
        u_grid, h = make_grid(Ng, L)
        rows = []
        for label, omega in key_omegas:
            rmse_tr, rmse_te = fit_omega(
                omega, u_grid, h, t_train, Z_train, t_test, Z_test, eps,
                n_restarts=4, seeds=(0, 17))
            rows.append({"label": label, "omega": omega,
                         "tr": rmse_tr, "te": rmse_te})
        sorted_rows = sorted(rows, key=lambda r: r["te"])
        phi_row = next(r for r in rows if abs(r["omega"] - PHI) < 1e-9)
        phi_rank = sorted_rows.index(phi_row) + 1
        best = sorted_rows[0]
        print(f"  N={Ng:3d}: φ rank = {phi_rank}/{len(rows)}, "
              f"φ RMSE_te={phi_row['te']:.4f}, "
              f"best={best['label'].strip()} (RMSE_te={best['te']:.4f})")
    print()


def check_C_split_robustness():
    print("=" * 78)
    print("(C) TRAIN/TEST SPLIT ROBUSTNESS")
    print("=" * 78)
    eps = 0.5
    N_grid = 250
    L = math.pi
    u_grid, h = make_grid(N_grid, L)
    targets = zeta_ordinates(140)
    splits = [
        ("1-30 | 31-60",   0,  30,  60),
        ("1-40 | 41-80",   0,  40,  80),
        ("1-50 | 51-100",  0,  50, 100),
        ("20-60 | 61-100", 20, 60, 100),
        ("1-60 | 61-120",  0,  60, 120),
    ]
    key_omegas = [
        ("φ           ", PHI),
        ("φ-0.05      ", PHI - 0.05),
        ("φ+0.05      ", PHI + 0.05),
        ("√2          ", math.sqrt(2)),
        ("√3          ", math.sqrt(3)),
        ("√5          ", math.sqrt(5)),
        ("π           ", math.pi),
        ("e           ", math.e),
        ("13/8        ", 13.0 / 8.0),
    ]
    for split_label, lo, mid, hi in splits:
        t_train, Z_train, t_test, Z_test = setup_split(targets, lo, mid, hi, eps)
        rows = []
        for label, omega in key_omegas:
            rmse_tr, rmse_te = fit_omega(
                omega, u_grid, h, t_train, Z_train, t_test, Z_test, eps,
                n_restarts=4, seeds=(0, 17))
            rows.append({"label": label, "omega": omega,
                         "tr": rmse_tr, "te": rmse_te})
        sorted_rows = sorted(rows, key=lambda r: r["te"])
        phi_row = next(r for r in rows if abs(r["omega"] - PHI) < 1e-9)
        phi_rank = sorted_rows.index(phi_row) + 1
        best = sorted_rows[0]
        print(f"  Split {split_label:18s}  φ rank = {phi_rank}/{len(rows)}, "
              f"φ RMSE_te={phi_row['te']:.4f}, "
              f"best={best['label'].strip()} (RMSE_te={best['te']:.4f})")
    print()


def main():
    check_A_fine_detuning()
    check_B_grid_sizes()
    check_C_split_robustness()


if __name__ == "__main__":
    main()
