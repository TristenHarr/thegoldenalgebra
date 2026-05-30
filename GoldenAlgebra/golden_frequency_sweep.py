"""
Step 40: Frequency sweep on a discretized Mellin/dilation operator.

H = -i d/du + V_ω(u),  V_ω(u) = a cos(2π u ω) + b sin(2π u ω) + c·u

The complex-Hermitian discretization of -i d/du on a uniform grid is
unitarily equivalent (via the diagonal phase U = diag(i^j)) to a real
symmetric tridiagonal matrix with off-diagonal 1/(2h). The potential V
is diagonal and real, unchanged by the phase conjugation. So we can use
`eigh_tridiagonal` directly — same spectrum, much faster.

Hypothesis under test: is ω = φ locally distinguished for out-of-sample
resonance matching against zeta zeros?
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
              n_restarts=8, max_iter=3000, seed=0):
    rng = default_rng(seed)
    best_loss = float("inf")
    best_p = None
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
    return rmse_tr, rmse_te, best_p


def main():
    N_zeros = 60
    N_train_idx = 30
    eps = 0.5
    N_grid = 250
    L = math.pi

    print(f"Operator: H = -i d/du + a cos(2π u ω) + b sin(2π u ω) + c u")
    print(f"Grid: {N_grid} points on [0, {L:.3f}]  (max free-momentum ≈ "
          f"{math.pi*N_grid/L:.0f})")
    print()

    targets = zeta_ordinates(N_zeros)
    t_train = np.linspace(max(0.0, targets[0] - 3.0),
                          targets[N_train_idx - 1] + 3.0, 500)
    t_test = np.linspace(targets[N_train_idx] - 1.0,
                         targets[N_zeros - 1] + 3.0, 500)
    Z_train = resonance(t_train, targets[:N_train_idx], eps)
    Z_test = resonance(t_test, targets[N_train_idx:], eps)
    null_tr = float(np.sqrt(np.mean(Z_train ** 2)))
    null_te = float(np.sqrt(np.mean(Z_test ** 2)))
    print(f"Train: ordinates 1..{N_train_idx} in t-range "
          f"[{t_train[0]:.2f}, {t_train[-1]:.2f}], null RMSE={null_tr:.3f}")
    print(f"Test : ordinates {N_train_idx+1}..{N_zeros} in t-range "
          f"[{t_test[0]:.2f}, {t_test[-1]:.2f}], null RMSE={null_te:.3f}")
    print()

    u_grid = np.linspace(0.0, L, N_grid)
    h = u_grid[1] - u_grid[0]

    sweep = [
        ("φ            ", PHI),
        ("1/φ          ", 1.0 / PHI),
        ("φ - 0.05     ", PHI - 0.05),
        ("φ + 0.05     ", PHI + 0.05),
        ("φ - 0.1      ", PHI - 0.1),
        ("φ + 0.1      ", PHI + 0.1),
        ("√2           ", math.sqrt(2)),
        ("√3           ", math.sqrt(3)),
        ("√5           ", math.sqrt(5)),
        ("π            ", math.pi),
        ("e            ", math.e),
        ("13/8 (Fib)   ", 13.0 / 8.0),
        ("21/13 (Fib)  ", 21.0 / 13.0),
        ("3/2          ", 1.5),
        ("2            ", 2.0),
    ]

    print(f"{'ω':14s}  {'value':>8s}  {'RMSE_tr':>8s}  {'RMSE_te':>8s}  "
          f"{'rel_tr':>7s}  {'rel_te':>7s}")
    print("-" * 80)
    rows = []
    seeds = [0, 17, 31]   # three seeds, take best train
    for label, omega in sweep:
        best = None
        for s in seeds:
            r = fit_omega(omega, u_grid, h, t_train, Z_train,
                          t_test, Z_test, eps, seed=s)
            if best is None or r[0] < best[0]:
                best = r
        rmse_tr, rmse_te, _p = best
        rel_tr = rmse_tr / null_tr
        rel_te = rmse_te / null_te
        rows.append((label, omega, rmse_tr, rmse_te, rel_tr, rel_te))
        print(f"{label}  {omega:8.5f}  {rmse_tr:8.4f}  {rmse_te:8.4f}  "
              f"{rel_tr:7.3f}  {rel_te:7.3f}")

    print()
    print("Sorted by test RMSE (ascending = better extrapolation):")
    print("-" * 80)
    for label, omega, _tr, te, _rtr, rte in sorted(rows, key=lambda r: r[3]):
        print(f"  {label}  ω={omega:8.5f}  RMSE_te={te:8.4f}  rel_te={rte:5.3f}")

    print()
    print("Is φ locally distinguished?")
    phi_row = next(r for r in rows if abs(r[1] - PHI) < 1e-9)
    nearby = [r for r in rows if abs(r[1] - PHI) < 0.15 and abs(r[1] - PHI) > 1e-9]
    print(f"  φ:                          RMSE_te = {phi_row[3]:.4f}")
    for label, omega, _, te, _, _ in nearby:
        verdict = "WORSE than φ" if te > phi_row[3] else "BETTER than φ"
        print(f"  {label} (ω={omega:.5f}): RMSE_te = {te:.4f}  {verdict}")


if __name__ == "__main__":
    main()
