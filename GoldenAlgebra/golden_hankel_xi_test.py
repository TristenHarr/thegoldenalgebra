"""
Golden Hankel -> Xi numerical test.

The decisive question for the Golden Algebra RH program:

    Do the Golden Hankel characteristic zeros approach the Riemann
    zeta zero ordinates under any natural q-scaling?

Setup (the "squared-trace moment measure"):

    G  = [[T,-J],[J,T]],   T=(sqrt5-1)/4,  J=(3-sqrt5)/4
    Tr(G^n) = 2 Re((T+iJ)^n)
    mu_q    = sum_{n>=0} (Tr G^n)^2 q^n  * delta_n      (atoms at x=n)
    m_k(q)  = sum_n (Tr G^n)^2 q^n n^k                   (Hankel moments)
    H(q)    = [ m_{i+j} ]                                (positive moment matrix)

The N-point Gaussian quadrature nodes of mu_q are the eigenvalues of
the order-N Jacobi matrix built from the moments (computed stably here
by Lanczos on the discrete measure). In the squared-operator reading
A = H^2, the candidate zeta ordinates are t_k = sqrt(node_k).

We sweep q and N, rescale the nodes by a best-fit affine map (and the
sqrt reading), and measure RMSE against the true zeta ordinates. A
random-positive-measure baseline calibrates whether any match is
signal or noise.

Honest verdict at the end.
"""

import math
import numpy as np
from numpy.random import default_rng
from scipy.linalg import eigh_tridiagonal
from mpmath import mp, zetazero

SQRT5 = math.sqrt(5.0)
T = (SQRT5 - 1.0) / 4.0
J = (3.0 - SQRT5) / 4.0
LAM = complex(T, J)
LAM2 = T * T + J * J          # |lambda|^2  ~ 0.131966
Q_CRIT = 1.0 / LAM2           # moments converge for q < Q_CRIT (~7.578)


def zeta_ordinates(n):
    mp.dps = 30
    return np.array([float(zetazero(k + 1).imag) for k in range(n)])


def golden_trace(nmax):
    """Tr(G^n) = 2 Re(lambda^n) for n = 0..nmax."""
    tr = np.empty(nmax + 1)
    p = complex(1.0, 0.0)
    for n in range(nmax + 1):
        tr[n] = 2.0 * p.real
        p *= LAM
    return tr


def lanczos_nodes(x, w, N):
    """N-point Gauss quadrature nodes for the discrete measure with
    atoms x and weights w>=0, via Lanczos with full reorthogonalization."""
    x = np.asarray(x, dtype=float)
    w = np.asarray(w, dtype=float)
    mass = w.sum()
    if mass <= 0 or not np.isfinite(mass):
        return None
    v_prev = np.zeros_like(x)
    v = np.sqrt(np.maximum(w, 0.0))
    v /= np.linalg.norm(v)
    alpha = np.zeros(N)
    beta_off = np.zeros(max(N - 1, 0))
    Q = []  # store for reorthogonalization
    for k in range(N):
        Q.append(v.copy())
        xv = x * v
        a = float(np.dot(v, xv))
        alpha[k] = a
        r = xv - a * v - (beta_off[k - 1] * v_prev if k > 0 else 0.0)
        # full reorthogonalization (twice for stability)
        for _ in range(2):
            for u in Q:
                r = r - np.dot(u, r) * u
        b = np.linalg.norm(r)
        if k + 1 < N:
            if b < 1e-14:
                # measure exhausted: only k+1 nodes exist
                alpha = alpha[:k + 1]
                beta_off = beta_off[:k]
                break
            beta_off[k] = b
        v_prev = v
        v = r / b if b > 1e-300 else r
    if len(alpha) < 2:
        return None
    try:
        evals = eigh_tridiagonal(alpha, beta_off[:len(alpha) - 1],
                                 eigvals_only=True)
    except Exception:
        return None
    return np.sort(evals)


def best_affine_rmse(pred, target):
    """Best RMSE of  alpha*pred + beta  vs target  (least squares)."""
    pred = np.asarray(pred, dtype=float)
    target = np.asarray(target, dtype=float)
    m = min(len(pred), len(target))
    if m < 2:
        return float("inf")
    p = pred[:m]
    t = target[:m]
    A = np.vstack([p, np.ones(m)]).T
    coef, _, _, _ = np.linalg.lstsq(A, t, rcond=None)
    fit = A @ coef
    return float(np.sqrt(np.mean((fit - t) ** 2))), coef


def golden_hankel_candidates(q, N, nmax):
    """Return the candidate ordinate sequences from the Golden Hankel
    measure at parameter q with N quadrature points."""
    tr = golden_trace(nmax)
    n = np.arange(nmax + 1, dtype=float)
    w = (tr ** 2) * np.power(q, n)
    w = np.where(np.isfinite(w), w, 0.0)
    nodes = lanczos_nodes(n, w, N)
    if nodes is None:
        return None
    # nodes lie in [0, nmax]; positive-operator reading A=H^2 gives sqrt
    direct = nodes
    sqrtread = np.sqrt(np.maximum(nodes, 0.0))
    return {"direct": direct, "sqrt": sqrtread}


def main():
    n_zeros = 10
    targets = zeta_ordinates(n_zeros)
    print("Golden Hankel -> Xi test")
    print(f"  T={T:.8f}  J={J:.8f}  |lambda|^2={LAM2:.6f}  "
          f"q_crit={Q_CRIT:.4f}")
    print(f"  first {n_zeros} zeta ordinates: "
          + ", ".join(f"{t:.3f}" for t in targets))
    print()

    N = 10
    nmax = 4000
    qs = [0.5, 1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 7.3, 7.5, 7.55]

    print(f"Sweep: N={N} quadrature points, nmax={nmax} atoms")
    print(f"{'q':>7} {'reading':>8} {'RMSE_te':>10} {'alpha':>11} "
          f"{'beta':>10}  first-3 rescaled vs zeta")
    best = (float("inf"), None)
    for q in qs:
        cand = golden_hankel_candidates(q, N, nmax)
        if cand is None:
            print(f"{q:7.2f}   (measure degenerate / non-summable)")
            continue
        for tag in ("direct", "sqrt"):
            pred = cand[tag]
            res = best_affine_rmse(pred, targets)
            if res == float("inf"):
                continue
            rmse, coef = res
            fit = coef[0] * pred[:3] + coef[1]
            shown = ", ".join(f"{v:.2f}" for v in fit)
            print(f"{q:7.2f} {tag:>8} {rmse:10.4f} {coef[0]:11.4f} "
                  f"{coef[1]:10.3f}   [{shown}] vs "
                  f"[{targets[0]:.2f}, {targets[1]:.2f}, {targets[2]:.2f}]")
            if rmse < best[0]:
                best = (rmse, (q, tag, coef))
    print()
    print(f"Best Golden Hankel RMSE = {best[0]:.4f}  at {best[1]}")
    print()

    # ---- Baseline: random positive measures on the same atoms ----
    print("Random-positive-measure baseline (200 samples)")
    rng = default_rng(20260521)
    n = np.arange(nmax + 1, dtype=float)
    base = []
    for s in range(200):
        # random geometric-ish positive weights, random decay
        decay = rng.uniform(0.3, 0.95)
        mod = rng.uniform(0.0, 1.0, size=nmax + 1)
        w = mod * np.power(decay, n)
        nodes = lanczos_nodes(n, w, N)
        if nodes is None:
            continue
        r1 = best_affine_rmse(nodes, targets)
        r2 = best_affine_rmse(np.sqrt(np.maximum(nodes, 0.0)), targets)
        rr = min(r1[0] if r1 != float("inf") else 1e9,
                 r2[0] if r2 != float("inf") else 1e9)
        base.append(rr)
    base = np.array(sorted(base))
    if len(base):
        print(f"  baseline RMSE: min={base.min():.4f}  "
              f"10%={np.percentile(base,10):.4f}  "
              f"median={np.median(base):.4f}  "
              f"90%={np.percentile(base,90):.4f}")
        pct = float(np.mean(base < best[0]) * 100)
        print(f"  Golden Hankel best percentile = {pct:.1f}%  "
              f"(lower = better; <25% would be a signal)")
    print()

    # ---- Convergence check: do the first nodes stabilize? ----
    print("Convergence of first 3 quadrature nodes as N grows (q=7.5):")
    for Ntest in (6, 10, 16, 24, 32):
        cand = golden_hankel_candidates(7.5, Ntest, nmax)
        if cand is None:
            print(f"  N={Ntest}: degenerate")
            continue
        d = cand["direct"][:3]
        print(f"  N={Ntest:3d}: first nodes = "
              + ", ".join(f"{v:.4f}" for v in d))
    print()

    # ---- Verdict ----
    print("=" * 64)
    if len(base):
        if pct < 5:
            print("VERDICT: Golden Hankel beats >95% of random measures")
            print("  -> possible genuine signal; pull the thread.")
        elif pct < 25:
            print("VERDICT: top quartile vs random -> weak possible signal.")
        else:
            print("VERDICT: Golden Hankel is NOT better than generic")
            print("  positive measures at matching zeta ordinates.")
            print("  The Golden Hankel family is a real-rooted system but")
            print("  there is no evidence it is the RH system.")
    print("=" * 64)


if __name__ == "__main__":
    main()
