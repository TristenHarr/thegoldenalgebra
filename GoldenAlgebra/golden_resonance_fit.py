"""
Step 39: Resonance-profile search for Golden tridiagonal operators.

Don't fit eigenvalues to zero ordinates directly. Fit the *Lorentzian
resonance profile* of the operator to the resonance profile of the
zeta zeros on a dense t-grid. The hypothesis: zeros are sharp features,
and matching the whole bumpy profile is a stronger constraint than
matching a list of points.

Honest train/test split: optimize on a t-range covering the first
N_train ordinates; held-out test on a t-range covering the next
N_test ordinates.
"""

import math
import numpy as np
from numpy.random import default_rng
from scipy.linalg import eigh_tridiagonal
from scipy.optimize import minimize
from mpmath import mp, zetazero

SQRT5 = math.sqrt(5.0)
PHI = (1.0 + SQRT5) / 2.0
T_GA = (SQRT5 - 1.0) / 4.0
J_GA = (3.0 - SQRT5) / 4.0


def golden_trace(n: int) -> float:
    if n == 0:
        return 2.0
    G = np.array([[T_GA, -J_GA], [J_GA, T_GA]], dtype=float)
    return float(np.trace(np.linalg.matrix_power(G, n)))


def zeta_ordinates(N: int) -> np.ndarray:
    mp.dps = 30
    return np.array([float(zetazero(k + 1).imag) for k in range(N)])


def resonance(t_grid: np.ndarray, peaks: np.ndarray, eps: float) -> np.ndarray:
    """Lorentzian sum: R(t) = Σ eps / ((t - p_k)² + eps²). Peak height = 1/eps."""
    diff = t_grid[:, None] - peaks[None, :]
    return np.sum(eps / (diff * diff + eps * eps), axis=1)


# === Feature builders ===

def make_features_full(N):
    n = np.arange(N, dtype=float)
    log_term = np.log(n + 1.0)
    cos_term = np.cos(2.0 * math.pi * n / PHI)
    trace_term = np.array([golden_trace(int(k)) for k in n])
    m = np.arange(N - 1, dtype=float)
    inv_term = 1.0 / (m + 1.0)
    sin_term = np.sin(2.0 * math.pi * m / PHI)

    def diag_fn(p): return p[0] * log_term + p[1] * cos_term + p[2] * trace_term
    def off_fn(p): return p[3] + p[4] * inv_term + p[5] * sin_term
    return diag_fn, off_fn, 6


def make_features_diag_only_log(N):
    n = np.arange(N, dtype=float)
    log_term = np.log(n + 1.0)
    def diag_fn(p): return p[0] * log_term + p[1]
    def off_fn(p): return p[2] * np.ones(N - 1)
    return diag_fn, off_fn, 3


def make_features_no_golden_trace(N):
    n = np.arange(N, dtype=float)
    log_term = np.log(n + 1.0)
    cos_term = np.cos(2.0 * math.pi * n / PHI)
    m = np.arange(N - 1, dtype=float)
    inv_term = 1.0 / (m + 1.0)
    sin_term = np.sin(2.0 * math.pi * m / PHI)
    def diag_fn(p): return p[0] * log_term + p[1] * cos_term
    def off_fn(p): return p[2] + p[3] * inv_term + p[4] * sin_term
    return diag_fn, off_fn, 5


def make_features_random(N, rng):
    diag_features = [rng.standard_normal(N) for _ in range(3)]
    off_features = [rng.standard_normal(N - 1) for _ in range(3)]
    def diag_fn(p): return sum(p[i] * diag_features[i] for i in range(3))
    def off_fn(p): return sum(p[3 + i] * off_features[i] for i in range(3))
    return diag_fn, off_fn, 6


# === Eigenvalues and loss ===

def eigvals_of(diag_fn, off_fn, p):
    return eigh_tridiagonal(diag_fn(p), off_fn(p), eigvals_only=True)


def resonance_loss(p, diag_fn, off_fn, t_train, Z_train, eps):
    eig = eigvals_of(diag_fn, off_fn, p)
    R = resonance(t_train, eig, eps)
    return float(np.mean((R - Z_train) ** 2))


def fit_model(label, diag_fn, off_fn, n_params,
              t_train, Z_train, t_test, Z_test, eps, seed=0):
    rng = default_rng(seed)
    best_loss = float("inf")
    best_p = None
    for trial in range(10):
        x0 = rng.standard_normal(n_params)
        x0[0] = float(np.mean(t_train) / math.log(len(t_train) + 1))
        res = minimize(
            resonance_loss, x0,
            args=(diag_fn, off_fn, t_train, Z_train, eps),
            method="Nelder-Mead",
            options={"xatol": 1e-7, "fatol": 1e-9,
                     "maxiter": 12000, "adaptive": True},
        )
        if res.fun < best_loss:
            best_loss = res.fun
            best_p = res.x

    eig = eigvals_of(diag_fn, off_fn, best_p)
    R_tr = resonance(t_train, eig, eps)
    R_te = resonance(t_test, eig, eps)
    rmse_tr = float(np.sqrt(np.mean((R_tr - Z_train) ** 2)))
    rmse_te = float(np.sqrt(np.mean((R_te - Z_test) ** 2)))
    # Null baselines: predict zero profile
    null_tr = float(np.sqrt(np.mean(Z_train ** 2)))
    null_te = float(np.sqrt(np.mean(Z_test ** 2)))
    rel_tr = rmse_tr / null_tr
    rel_te = rmse_te / null_te
    print(f"{label:30s}  RMSE_tr={rmse_tr:7.4f}  RMSE_te={rmse_te:7.4f}  "
          f"rel_tr={rel_tr:5.3f}  rel_te={rel_te:5.3f}")
    return best_p, eig


def main():
    N = 80
    N_train_idx = 40
    eps = 0.5

    print(f"Fetching first {N} zeta-zero ordinates...")
    targets = zeta_ordinates(N)
    t_train_lo = max(0.0, targets[0] - 3.0)
    t_train_hi = targets[N_train_idx - 1] + 3.0
    t_test_lo = targets[N_train_idx] - 1.0
    t_test_hi = targets[N - 1] + 3.0
    t_train = np.linspace(t_train_lo, t_train_hi, 800)
    t_test = np.linspace(t_test_lo, t_test_hi, 800)

    print(f"Train t-range: [{t_train_lo:.2f}, {t_train_hi:.2f}] "
          f"(ordinates 1..{N_train_idx})")
    print(f"Test  t-range: [{t_test_lo:.2f}, {t_test_hi:.2f}] "
          f"(ordinates {N_train_idx+1}..{N})")
    print(f"Lorentzian width eps={eps}, peak height={1/eps:.2f}")
    print()

    # Build zeta resonance profiles
    Z_train = resonance(t_train, targets[:N_train_idx], eps)
    Z_test = resonance(t_test, targets[N_train_idx:], eps)
    print(f"Zeta profile train: mean={Z_train.mean():.3f}, max={Z_train.max():.3f}")
    print(f"Zeta profile test : mean={Z_test.mean():.3f}, max={Z_test.max():.3f}")
    print()

    diag_full, off_full, n_full = make_features_full(N)
    diag_nogt, off_nogt, n_nogt = make_features_no_golden_trace(N)
    diag_diag, off_diag, n_diag = make_features_diag_only_log(N)
    diag_rand, off_rand, n_rand = make_features_random(N, default_rng(42))

    print(f"{'model':30s}  {'RMSE_tr':>11s}  {'RMSE_te':>11s}  "
          f"{'rel_tr':>8s}  {'rel_te':>8s}")
    print("-" * 80)
    p_full, eig_full = fit_model(
        "Full Golden (6 params)", diag_full, off_full, n_full,
        t_train, Z_train, t_test, Z_test, eps)
    fit_model(
        "Golden no goldenTrace (5p)", diag_nogt, off_nogt, n_nogt,
        t_train, Z_train, t_test, Z_test, eps)
    fit_model(
        "Diag-only log (3 params)", diag_diag, off_diag, n_diag,
        t_train, Z_train, t_test, Z_test, eps)
    fit_model(
        "Random features (6 params)", diag_rand, off_rand, n_rand,
        t_train, Z_train, t_test, Z_test, eps)

    print()
    print("Full Golden eigenvalues in train and test t-ranges:")
    eig_in_train = eig_full[(eig_full >= t_train_lo) & (eig_full <= t_train_hi)]
    eig_in_test = eig_full[(eig_full >= t_test_lo) & (eig_full <= t_test_hi)]
    print(f"  eigenvalues in train range: count={len(eig_in_train)} "
          f"(targets={N_train_idx})")
    print(f"  eigenvalues in test  range: count={len(eig_in_test)} "
          f"(targets={N - N_train_idx})")
    if len(eig_in_test) > 0:
        # Greedy nearest-target match
        targets_test = targets[N_train_idx:]
        errs = []
        for ev in eig_in_test:
            errs.append(min(abs(ev - t) for t in targets_test))
        print(f"  median |nearest-target| error on test eigenvalues: "
              f"{float(np.median(errs)):.3f}")
        print(f"  max    |nearest-target| error on test eigenvalues: "
              f"{float(np.max(errs)):.3f}")


if __name__ == "__main__":
    main()
