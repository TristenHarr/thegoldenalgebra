"""
E1: Random-frequency baseline for the φ-hypothesis.

If φ is truly a special frequency for the Mellin/dilation resonance fit,
then it should sit in the *tail* of a distribution of random frequencies'
test errors — not in the middle.

Generate 200 uniform random frequencies in [1.0, 4.0]. For each, run the
same fit + resonance-loss procedure as Step 40/41. Then compute φ's
percentile in the resulting distribution.

If φ's percentile is below 25th (top quartile by RMSE_te), there might be
some signal. If φ is near the median, it's noise.
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
              n_restarts=3, max_iter=2000, seed=0):
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
            options={"xatol": 1e-5, "fatol": 1e-7,
                     "maxiter": max_iter, "adaptive": True},
        )
        if res.fun < best_loss:
            best_loss = res.fun
            best_p = res.x
    eig = positive_eigvals(u_grid, h, omega, best_p)
    R_te = resonance(t_test, eig, eps)
    return float(np.sqrt(np.mean((R_te - Z_test) ** 2)))


def main():
    N_zeros = 60
    N_train_idx = 30
    eps = 0.5
    N_grid = 250
    L = math.pi
    N_random = 200

    targets = zeta_ordinates(N_zeros)
    t_train = np.linspace(max(0.0, targets[0] - 3.0),
                          targets[N_train_idx - 1] + 3.0, 500)
    t_test = np.linspace(targets[N_train_idx] - 1.0,
                         targets[N_zeros - 1] + 3.0, 500)
    Z_train = resonance(t_train, targets[:N_train_idx], eps)
    Z_test = resonance(t_test, targets[N_train_idx:], eps)

    u_grid = np.linspace(0.0, L, N_grid)
    h = u_grid[1] - u_grid[0]

    print(f"Random-frequency baseline: {N_random} ω ∈ [1.0, 4.0]")
    print(f"Grid {N_grid}, split 1-{N_train_idx} | {N_train_idx+1}-{N_zeros}")
    print()

    rng = default_rng(99)
    omegas = rng.uniform(1.0, 4.0, N_random)
    test_errors = []
    for i, omega in enumerate(omegas):
        rmse_te = fit_omega(
            omega, u_grid, h, t_train, Z_train, t_test, Z_test, eps,
            n_restarts=3, max_iter=2000, seed=i)
        test_errors.append(rmse_te)
        if (i + 1) % 20 == 0:
            print(f"  done {i+1}/{N_random}: median RMSE_te so far = "
                  f"{float(np.median(test_errors)):.4f}")

    test_errors = np.array(test_errors)

    # φ's test error
    phi_rmse = fit_omega(PHI, u_grid, h, t_train, Z_train, t_test, Z_test,
                         eps, n_restarts=5, max_iter=3000, seed=0)

    # Percentile of φ in the random distribution
    pct = float(np.mean(test_errors < phi_rmse) * 100)
    print()
    print(f"Random distribution of RMSE_te ({N_random} samples):")
    print(f"  min    = {test_errors.min():.4f}")
    print(f"  10%ile = {np.percentile(test_errors, 10):.4f}")
    print(f"  25%ile = {np.percentile(test_errors, 25):.4f}")
    print(f"  median = {np.median(test_errors):.4f}")
    print(f"  75%ile = {np.percentile(test_errors, 75):.4f}")
    print(f"  90%ile = {np.percentile(test_errors, 90):.4f}")
    print(f"  max    = {test_errors.max():.4f}")
    print()
    print(f"φ RMSE_te = {phi_rmse:.4f}")
    print(f"φ percentile = {pct:.1f}%  (lower = better)")
    print()
    if pct < 5:
        print("VERDICT: φ is in the top 5% — strong signal.")
    elif pct < 25:
        print("VERDICT: φ is in the top quartile — possible signal.")
    elif pct < 50:
        print("VERDICT: φ is above median but not exceptional — weak/no signal.")
    else:
        print("VERDICT: φ is at or below median — NO signal.")


if __name__ == "__main__":
    main()
