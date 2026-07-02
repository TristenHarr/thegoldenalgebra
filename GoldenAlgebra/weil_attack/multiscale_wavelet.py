"""
MULTISCALE WAVELET WEIL  -- does the safe-cone atom span RECONSTRUCT the negative direction?
=============================================================================================
DECISIVE test.  On a fat fine dictionary (support past log2) the validated ARCH+POLE-PRIME
engine is INDEFINITE (min-eig < 0, the genuine obstruction).  Question:

  We build a multiscale family {phi_j} of atoms each SELF-SAFE: g_j = phi_j*phi_j~ supported in
  (-log2,log2) => D_jj = Q(g_j) >= 0 (Yoshida).  Let V = span{phi_j}.  Two outcomes:
    (1) Q|_V is PSD  => multiscale gives genuine positivity on V PAST log2 (atoms tile support
        beyond log2 but Q restricted to their span stays >=0).  PARTIAL POSITIVITY -- flag LOUD.
    (2) Q|_V is INDEFINITE => the cross terms reconstruct the obstruction inside the atom span;
        multiscale does NOT tame it.  Certificate of failure (and WHY).

We make atoms SIGNED (oscillatory wavelets: each atom carries +/- lobes) so the family is rich
enough to potentially synthesize the obstruction's moving direction v_T.  This is the honest
version: a 2-positive-bump family is trivially PSD and proves nothing; a wavelet family that
can build the negative eigenvector is the real test.

The negative eigenvector v* of the full engine is computed and we measure how much of it lives
in the atom span V (projection norm).  If V captures v*, Q|_V inherits the negativity.

Engine: validated numpy float ARCH+POLE-PRIME (matched zero-sum ~1e-16).  NO RH; zero-sum unused.
"""
import numpy as np
import mpmath as mp
from prime_rank_collective import (prime_powers, gram, arch_matrix, pole_matrix,
                                   prime_matrix, gen_eig, ip_G, LOG2)
mp.mp.dps = 30


def build_engine(dict_centers, s):
    G = gram(dict_centers, s)
    A = arch_matrix(dict_centers, s)
    P = pole_matrix(dict_centers, s)
    span = max(dict_centers) - min(dict_centers)
    PP = prime_powers(float(np.exp(span + 9 * s)))
    PR = prime_matrix(dict_centers, s, PP)
    return A + P - PR, G, PP


def gauss_kernel(dc, x, sig):
    return np.exp(-(np.array(dc) - x) ** 2 / (2 * sig ** 2))


def wavelet_atom(dc, center, halfwidth, n_lobes, s, sign_pattern=None):
    """A SIGNED atom (wavelet-like) of half-support `halfwidth` centered at `center`.
       n_lobes sub-bumps with alternating (or given) signs => oscillatory atom.  Expressed as a
       coefficient vector over the shared dictionary.  Its self-correlation g=phi*phi~ has support
       in [-2 halfwidth, 2 halfwidth]; choose 2*halfwidth < log2 to keep the DIAGONAL safe."""
    c = np.zeros(len(dc))
    locs = np.linspace(center - halfwidth, center + halfwidth, n_lobes) if n_lobes > 1 else [center]
    if sign_pattern is None:
        signs = [(-1) ** i for i in range(len(locs))]
    else:
        signs = sign_pattern
    sub_sig = max(halfwidth / max(n_lobes, 1), s)
    dca = np.array(dc)
    for x, sg in zip(locs, signs):
        k = int(np.argmin(np.abs(dca - x)))
        c[k] += sg
    return c


def restrict(Q, G, atoms):
    """Build the multiscale Gram M_ab=Q(phi_a,phi_b) and L2 Gram Gm_ab=<phi_a,phi_b>, then the
       generalized spectrum of Q restricted to span{atoms}."""
    m = len(atoms)
    M = np.array([[float(atoms[a] @ Q @ atoms[b]) for b in range(m)] for a in range(m)])
    Gm = np.array([[float(atoms[a] @ G @ atoms[b]) for b in range(m)] for a in range(m)])
    M = (M + M.T) / 2; Gm = (Gm + Gm.T) / 2
    wG = np.linalg.eigvalsh(Gm)
    if wG.min() > 1e-10:
        R = np.linalg.cholesky(Gm); Ri = np.linalg.inv(R)
        B = Ri @ M @ Ri.T; B = (B + B.T) / 2
        wM, _ = np.linalg.eigh(B)
    else:
        # atom set is rank-deficient; use pseudo: project to range of Gm
        wM = np.linalg.eigvalsh(M)
    return M, Gm, wM, wG


if __name__ == '__main__':
    print("=" * 92)
    print("MULTISCALE WAVELET: does the safe-cone atom span reconstruct the obstruction?")
    print("=" * 92)
    Xmax = 1.3; NB = 53; dc = list(np.linspace(-Xmax, Xmax, NB)); s = 0.05
    Q, G, PP = build_engine(dc, s)
    w_full, V_full = gen_eig(Q, G)
    order = np.argsort(w_full)
    w_full = w_full[order]; V_full = V_full[:, order]
    vstar = V_full[:, 0]                      # most-negative eigenvector of the FULL engine
    vstar = vstar / np.sqrt(ip_G(vstar, vstar, G))
    print(f"FULL engine: min-eig={w_full[0]:+.4e}, 2nd={w_full[1]:+.4e}, "
          f"n_neg={int((w_full<-1e-9).sum())}  (#pp={len(PP)})")
    print(f"vstar = full negative direction (the obstruction).\n")

    HW = 0.30        # atom half-width => self-correlation support 0.60 < log2=0.693 (SAFE diagonal)
    print(f"Atom half-width HW={HW} => atom self-support 2*HW={2*HW:.3f} < log2={LOG2:.3f} (SAFE).")
    print(f"=> every diagonal D_jj=Q(g_j) is in the Yoshida cone and >= 0.\n")

    for n_lobes in [1, 2, 3, 4]:
        print("#" * 92)
        print(f"# WAVELET FAMILY with {n_lobes} lobe(s) per atom "
              f"({'positive bump' if n_lobes==1 else 'signed/oscillatory'})")
        print("#" * 92)
        # tile centers across [-1.0,1.0] so atom centers (and thus cross separations) reach past log2
        n_atoms = 9
        centers = np.linspace(-1.0, 1.0, n_atoms)
        atoms = [wavelet_atom(dc, ct, HW, n_lobes, s) for ct in centers]
        M, Gm, wM, wG = restrict(Q, G, atoms)
        diag = np.diag(M)
        # project vstar onto atom span (in G-metric): how much of the obstruction lives in V?
        # build G-orthonormal basis of span{atoms}
        A = np.array(atoms).T                 # columns = atoms (dict-coords)
        # Gram in G-metric: Gm; orthonormalize via cholesky of Gm (if full rank)
        captured = np.nan
        if wG.min() > 1e-10:
            R = np.linalg.cholesky(Gm); Ri = np.linalg.inv(R)
            # G-orthonormal atom basis E = A @ Ri.T  (columns); coords y = E^T G vstar
            E = A @ Ri.T
            y = E.T @ (G @ vstar)
            captured = float(np.sqrt(np.sum(y ** 2)))   # ||P_V vstar||_G  (vstar is unit)
        print(f"  atoms={n_atoms}, centers in [-1,1] (cross seps up to {centers[-1]-centers[0]:.2f} >log2)")
        print(f"  diagonal D_jj (all should be >=0): "
              f"{np.array2string(diag, precision=4, suppress_small=True)}")
        print(f"  sum_j D_jj        = {diag.sum():+.6e}")
        offsum = (np.triu(M, 1)).sum()
        print(f"  sum_{{j<k}} C_jk    = {offsum:+.6e}   theta = {(-offsum/diag.sum()):+.4f}")
        print(f"  Q|_V spectrum min-eig = {wM.min():+.6e}   "
              f"({'INDEFINITE: obstruction reconstructed' if wM.min()<-1e-7 else 'PSD: positive past log2'})")
        print(f"  Q|_V all eigs: {np.array2string(np.sort(wM), precision=5, suppress_small=True)}")
        print(f"  ||P_V vstar||_G (obstruction captured by atom span) = {captured:.4f}  "
              f"(1=fully captured, 0=atom span avoids the obstruction)")
        print(f"  cond(Gm atom-metric) = {wG.max()/max(wG.min(),1e-300):.2e}\n")
