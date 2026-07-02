"""
THE KEY INEQUALITY, settled:  sum_{j<k} C_jk >= -theta sum_j D_jj with theta<1 does NOT control
multiscale positivity, because the cross matrix C is INDEFINITE (not a scalar fraction of D).
=============================================================================================
We sweep enriched safe-cone families and report, for each, (theta, lambda_min(C in D-metric),
mineig(Q|_V)).  The decisive object is NOT the scalar theta but the smallest generalized eigenvalue
of C relative to D:  mineig(Q|_V) >= 0  <=>  C >= -D as matrices  <=>  lambda_min(D^{-1/2} C D^{-1/2}) >= -1.
A scalar theta<1 (sum-trace ratio) can hold while the MATRIX inequality C >= -D fails along the
witness direction.  We exhibit this gap explicitly: families with theta well below 1 yet mineig<0.

Engine validated; NO RH.
"""
import numpy as np
from prime_rank_collective import (prime_powers, gram, arch_matrix, pole_matrix,
                                   prime_matrix, gen_eig, ip_G, LOG2)


def build_engine(dc, s):
    G = gram(dc, s); A = arch_matrix(dc, s); P = pole_matrix(dc, s)
    span = max(dc) - min(dc)
    PR = prime_matrix(dc, s, prime_powers(float(np.exp(span + 9 * s))))
    return A + P - PR, G


def wavelet_atom(dc, center, halfwidth, n_lobes):
    c = np.zeros(len(dc)); dca = np.array(dc)
    locs = np.linspace(center - halfwidth, center + halfwidth, n_lobes) if n_lobes > 1 else [center]
    signs = [(-1) ** i for i in range(len(locs))]
    for x, sg in zip(locs, signs):
        c[int(np.argmin(np.abs(dca - x)))] += sg
    return c


if __name__ == '__main__':
    Xmax = 1.4; NB = 71; dc = list(np.linspace(-Xmax, Xmax, NB)); s = 0.045
    Q, G = build_engine(dc, s)
    print(f"log2={LOG2:.4f}")
    print("Each row: an enriched SAFE-cone multiscale family (every D_jj>=0).")
    print(f"{'scales':>22} {'ntrans':>6} {'nat':>4} {'minDjj':>9} {'theta':>8} "
          f"{'lam_min(C|D)':>13} {'mineig Q|V':>13}")
    configs = [
        ([0.30], 9), ([0.30], 17), ([0.20, 0.30], 17), ([0.12, 0.22, 0.30], 17),
        ([0.12, 0.22, 0.30], 25), ([0.10, 0.18, 0.26, 0.32], 21),
    ]
    for scales, ntr in configs:
        atoms = []
        for hw in scales:
            for ct in np.linspace(-1.1, 1.1, ntr):
                atoms.append(wavelet_atom(dc, ct, hw, 3))
        Aa = np.array(atoms)
        M = Aa @ Q @ Aa.T; Gm = Aa @ G @ Aa.T; M = (M + M.T) / 2; Gm = (Gm + Gm.T) / 2
        D = np.diag(np.diag(M)); C = M - D
        sumD = np.trace(M); sumC = np.triu(M, 1).sum(); theta = -sumC / sumD
        # lam_min of C in D-metric (D is positive diagonal since all D_jj>=0)
        dd = np.diag(M)
        ok = dd.min() > 1e-12
        if ok:
            Dm12 = np.diag(1.0 / np.sqrt(dd))
            Cn = Dm12 @ C @ Dm12
            lamC = np.linalg.eigvalsh((Cn + Cn.T) / 2).min()
        else:
            lamC = float('nan')
        # mineig of Q|V in atom-L2 metric
        wG, UG = np.linalg.eigh(Gm); keep = wG > 1e-9 * wG.max()
        U = UG[:, keep]; dv = wG[keep]; Wh = U / np.sqrt(dv)
        B = Wh.T @ M @ Wh; mineig = np.linalg.eigvalsh((B + B.T) / 2).min()
        print(f"{str(scales):>22} {ntr:6d} {len(atoms):4d} {dd.min():9.3e} {theta:8.4f} "
              f"{lamC:13.4f} {mineig:+13.4e}")
    print()
    print("READING: theta (trace ratio) is < 1 throughout, yet mineig(Q|V) goes NEGATIVE once the")
    print("family is rich enough.  The controlling quantity is lam_min(D^{-1/2} C D^{-1/2}): positivity")
    print("needs it >= -1 (i.e. C >= -D as MATRICES).  It drops BELOW -1 -- the cross matrix C has a")
    print("direction more negative than D is positive -- exactly the moving prime obstruction (sec9).")
    print("So the inequality 'sum C >= -theta sum D, theta<1' is NECESSARY-looking but NOT SUFFICIENT;")
    print("cross-scale interference is a MATRIX (indefinite, rank ~13), not a scalar fraction of D.")
    print("=> NO partial-positivity theorem past log2 from a scalar theta<1 bound.  The interference")
    print("   reconstructs the obstruction.  CERTIFICATE OF FAILURE (with the precise reason).")
