"""
Step 38: Numerical regression of the Golden tridiagonal family against
nontrivial Riemann zeta-zero imaginary parts.

Lean target this implements:
    GoldenTridiagonalDiscoveryTarget N tol targets

Honest train/test split: optimize on the first N_train ordinates, then
evaluate held-out error on the next N_test - N_train ordinates.

Compared against four baselines so we can tell whether the Golden features
do any out-of-sample work or just overfit.
"""

import math
import numpy as np
from numpy.random import default_rng
from scipy.linalg import eigh_tridiagonal
from scipy.optimize import minimize
from mpmath import mp, zetazero

# === Golden Algebra constants ===
SQRT5 = math.sqrt(5.0)
PHI = (1.0 + SQRT5) / 2.0
T_GA = (SQRT5 - 1.0) / 4.0
J_GA = (3.0 - SQRT5) / 4.0


def golden_trace(n: int) -> float:
    """Tr(G^n) where G = [[T, -J], [J, T]] — matches the Lean goldenTrace."""
    G = np.array([[T_GA, -J_GA], [J_GA, T_GA]], dtype=float)
    if n == 0:
        return 2.0
    Gn = np.linalg.matrix_power(G, n)
    return float(np.trace(Gn))


def zeta_ordinates(N: int) -> np.ndarray:
    """First N nontrivial Riemann zeta-zero imaginary parts (positive)."""
    mp.dps = 30
    return np.array([float(zetazero(k + 1).imag) for k in range(N)])


# === Feature builders for the tridiagonal family ===
# Each returns (diag, offdiag) of length (N, N-1).

def make_features_full(N: int):
    n = np.arange(N, dtype=float)
    log_term = np.log(n + 1.0)
    cos_term = np.cos(2.0 * math.pi * n / PHI)
    trace_term = np.array([golden_trace(int(k)) for k in n])

    m = np.arange(N - 1, dtype=float)
    inv_term = 1.0 / (m + 1.0)
    sin_term = np.sin(2.0 * math.pi * m / PHI)

    def diag_fn(p):
        a, b, g = p[0], p[1], p[2]
        return a * log_term + b * cos_term + g * trace_term

    def off_fn(p):
        d, e, z = p[3], p[4], p[5]
        return d + e * inv_term + z * sin_term

    return diag_fn, off_fn, 6


def make_features_diag_only_log(N: int):
    n = np.arange(N, dtype=float)
    log_term = np.log(n + 1.0)
    def diag_fn(p): return p[0] * log_term + p[1]
    def off_fn(p): return p[2] * np.ones(N - 1)
    return diag_fn, off_fn, 3


def make_features_no_golden_trace(N: int):
    n = np.arange(N, dtype=float)
    log_term = np.log(n + 1.0)
    cos_term = np.cos(2.0 * math.pi * n / PHI)
    m = np.arange(N - 1, dtype=float)
    inv_term = 1.0 / (m + 1.0)
    sin_term = np.sin(2.0 * math.pi * m / PHI)

    def diag_fn(p): return p[0] * log_term + p[1] * cos_term
    def off_fn(p): return p[2] + p[3] * inv_term + p[4] * sin_term
    return diag_fn, off_fn, 5


def make_features_random_pcount(N: int, rng):
    # Random fixed feature vectors (6 of them), matching Golden model's parameter count.
    n = np.arange(N, dtype=float)
    m = np.arange(N - 1, dtype=float)
    diag_features = [rng.standard_normal(N) for _ in range(3)]
    off_features = [rng.standard_normal(N - 1) for _ in range(3)]
    def diag_fn(p): return sum(p[i] * diag_features[i] for i in range(3))
    def off_fn(p): return sum(p[3 + i] * off_features[i] for i in range(3))
    return diag_fn, off_fn, 6


# === Eigenvalue computation + loss ===

def eigvals_of(diag_fn, off_fn, p, N):
    d = diag_fn(p)
    e = off_fn(p)
    return eigh_tridiagonal(d, e, eigvals_only=True)


def train_loss(p, diag_fn, off_fn, targets_train, N_train):
    w = eigvals_of(diag_fn, off_fn, p, N_train)
    # Compare smallest-N_train ascending eigenvalues to ordinates in order.
    diff = w[:N_train] - targets_train
    return float(np.mean(diff * diff))


def evaluate_test(p, diag_fn, off_fn, targets_test, N_full):
    w = eigvals_of(diag_fn, off_fn, p, N_full)
    diff = w[:len(targets_test)] - targets_test
    return diff


def fit_model(label, diag_fn, off_fn, n_params, targets_full, N_train, seed=0):
    rng = default_rng(seed)
    targets_train = targets_full[:N_train]
    targets_test = targets_full[N_train:]

    best_loss = float("inf")
    best_p = None
    for trial in range(8):
        x0 = rng.standard_normal(n_params) * 1.0
        # Bias initial guess: align overall scale to mean ordinate.
        x0[0] = float(np.mean(targets_train) / math.log(N_train + 1))
        res = minimize(
            train_loss, x0,
            args=(diag_fn, off_fn, targets_train, N_train),
            method="Nelder-Mead",
            options={"xatol": 1e-7, "fatol": 1e-9, "maxiter": 8000, "adaptive": True},
        )
        if res.fun < best_loss:
            best_loss = res.fun
            best_p = res.x

    diff_test = evaluate_test(best_p, diag_fn, off_fn, targets_test, N_train + len(targets_test))
    diff_train = evaluate_test(best_p, diag_fn, off_fn, targets_full[:N_train], N_train)
    rmse_train = float(np.sqrt(np.mean(diff_train ** 2)))
    rmse_test = float(np.sqrt(np.mean(diff_test ** 2)))
    max_test = float(np.max(np.abs(diff_test)))

    print(f"{label:30s}  RMSE_train={rmse_train:8.4f}  RMSE_test={rmse_test:8.4f}  max|test|={max_test:8.4f}")
    return rmse_train, rmse_test, best_p


def main():
    N_train = 40
    N_test = 40
    N_full = N_train + N_test
    print(f"Fetching first {N_full} nontrivial Riemann zeta-zero ordinates...")
    targets_full = zeta_ordinates(N_full)
    print(f"  first  ordinate: {targets_full[0]:.4f}")
    print(f"  last   ordinate: {targets_full[-1]:.4f}")
    print(f"Train on first {N_train}; held-out test on next {N_test}.")
    print()

    diag_full, off_full, n_full = make_features_full(N_full)
    diag_diag, off_diag, n_diag = make_features_diag_only_log(N_full)
    diag_nogt, off_nogt, n_nogt = make_features_no_golden_trace(N_full)
    diag_rand, off_rand, n_rand = make_features_random_pcount(N_full, default_rng(42))

    print(f"{'model':30s}  {'RMSE_train':>10s}  {'RMSE_test':>10s}  {'max|test|':>10s}")
    print("-" * 70)
    _, _, p_full = fit_model("Full Golden (6 params)", diag_full, off_full, n_full, targets_full, N_train)
    fit_model("Golden no goldenTrace (5p)", diag_nogt, off_nogt, n_nogt, targets_full, N_train)
    fit_model("Diag-only log (3 params)", diag_diag, off_diag, n_diag, targets_full, N_train)
    fit_model("Random features (6 params)", diag_rand, off_rand, n_rand, targets_full, N_train)

    # Show what the best Golden model actually predicts on held-out indices
    print()
    print("Full Golden model: predictions vs actual zeta ordinates")
    print(f"  {'idx':>4s}  {'predicted':>12s}  {'actual':>12s}  {'error':>10s}  {'split':>6s}")
    w = eigvals_of(diag_full, off_full, p_full, N_full)
    for k in list(range(0, 5)) + list(range(N_train - 3, N_train + 5)) + list(range(N_full - 5, N_full)):
        split = "train" if k < N_train else "TEST"
        err = w[k] - targets_full[k]
        print(f"  {k+1:4d}  {w[k]:12.4f}  {targets_full[k]:12.4f}  {err:+10.4f}  {split:>6s}")

    print()
    print("Best 6 Golden parameters (α β γ δ ε ζ):")
    print(f"  α (diag log)        = {p_full[0]:+.6f}")
    print(f"  β (diag cos/φ)      = {p_full[1]:+.6f}")
    print(f"  γ (diag goldenTrace)= {p_full[2]:+.6f}")
    print(f"  δ (offdiag const)   = {p_full[3]:+.6f}")
    print(f"  ε (offdiag 1/(n+1)) = {p_full[4]:+.6f}")
    print(f"  ζ (offdiag sin/φ)   = {p_full[5]:+.6f}")


if __name__ == "__main__":
    main()
