"""
MULTISCALE / WAVELET WEIL POSITIVITY  -- cross-scale interference attack on the Yoshida cone.
=============================================================================================
SERIOUS new route.  The Yoshida cone {supp g subset (-log2,log2)} is sharp (FINDINGS sec 4-9).
Idea: decompose phi = sum_j phi_j into ATOMS, each living in a SMALL safe window, so that the
SELF-correlation g_j = phi_j * phi_j~ stays inside (-log2,log2) [its own prime sum empty/safe],
while the UNION of atom supports exceeds log2.  Then (Q polarized, bilinear):

    Q(g) = Q(sum_j phi_j) = sum_{j,k} Q(phi_j, phi_k) = sum_j D_jj + 2 sum_{j<k} C_jk,
        D_jj = Q(phi_j, phi_j) = Q(g_j) >= 0   (each atom in a safe cone -> diagonal POSITIVE),
        C_jk = Q(phi_j, phi_k)                 (CROSS-SCALE interference -- the whole difficulty).

This file builds the multiscale family on the VALIDATED ARCH+POLE-PRIME engine (numpy float
engine from prime_rank_collective, matched to the zero-sum ~1e-16; mpmath ARCH quadrature),
computes the cross Gram, and tests the KEY INEQUALITY
        sum_{j<k} C_jk  >=  - theta * sum_j D_jj    with theta < 1
which (if it held for a structured class) would give partial positivity PAST log2.

NO RH assumed.  Q built only from ARCH (digamma) + POLE (cosh) - PRIME (Lambda/sqrt n).  The
zero-sum is NEVER used to define Q.
"""
import numpy as np
import mpmath as mp
from prime_rank_collective import (prime_powers, gram, arch_matrix, pole_matrix,
                                   prime_matrix, gen_eig, ip_G, LOG2)

mp.mp.dps = 30


# ---------------------------------------------------------------------------------------------
# The polarized Weil form as a matrix Q on a SHARED fine bump dictionary.  An ATOM is then a
# coefficient vector over this dictionary.  Q(atom_a, atom_b) = c_a^T Q c_b.
# We build ONE fine dictionary wide enough to host every atom, so all atoms share coordinates.
# ---------------------------------------------------------------------------------------------
def build_engine(dict_centers, s):
    """Return (Q, G, A, P, PR_full) on the shared fine dictionary, full prime sum to the
       largest separation the dictionary can realize."""
    G = gram(dict_centers, s)
    A = arch_matrix(dict_centers, s)
    P = pole_matrix(dict_centers, s)
    span = max(dict_centers) - min(dict_centers)
    upto = float(np.exp(span + 9 * s))          # all primes reachable by any separation
    PP = prime_powers(upto)
    PR = prime_matrix(dict_centers, s, PP)
    Q = A + P - PR
    return Q, G, A, P, PR, PP


def make_atom(dict_centers, center, halfwidth, s, n_sub=5):
    """A localized atom = small Gaussian-bump cluster centered at `center`, of half-support
       `halfwidth`, expressed as a coefficient vector over the SHARED dictionary.  We realize it
       by placing n_sub sub-bumps in [center-halfwidth, center+halfwidth] with unit positive
       weights, then projecting onto the dictionary (nearest-center assignment).  The atom's
       SELF-correlation g = atom*atom~ then has support ~ [-2*halfwidth, 2*halfwidth]."""
    c = np.zeros(len(dict_centers))
    sub = np.linspace(center - halfwidth, center + halfwidth, n_sub)
    dc = np.array(dict_centers)
    for x in sub:
        k = int(np.argmin(np.abs(dc - x)))
        c[k] += 1.0
    return c


def atom_self_support(halfwidth):
    """g_j = phi_j*phi_j~ lives in [-2 halfwidth, 2 halfwidth] (autocorrelation doubles width)."""
    return 2.0 * halfwidth


# ---------------------------------------------------------------------------------------------
# MAIN ANALYSIS
# ---------------------------------------------------------------------------------------------
def cross_scale_analysis(atoms, Q, G):
    """Given a list of atom coefficient vectors, compute the multiscale Weil Gram
       M_ab = Q(atom_a, atom_b).  Returns M, the diagonal D, the off-diagonal C, and PSD data."""
    m = len(atoms)
    M = np.zeros((m, m))
    Gm = np.zeros((m, m))   # L2 Gram of atoms (for normalization / Rayleigh)
    for a in range(m):
        for b in range(m):
            M[a, b] = float(atoms[a] @ Q @ atoms[b])
            Gm[a, b] = float(atoms[a] @ G @ atoms[b])
    D = np.diag(np.diag(M))
    C = M - D
    return M, D, C, Gm


def report(M, D, C, Gm, label=""):
    m = M.shape[0]
    diag = np.diag(M)
    sumD = diag.sum()
    sumC = (np.triu(C, 1)).sum()          # sum_{j<k} C_jk
    # generalized min eig of full multiscale form in atom-L2 metric
    wG = np.linalg.eigvalsh(Gm)
    if wG.min() > 1e-12:
        R = np.linalg.cholesky(Gm); Ri = np.linalg.inv(R)
        B = Ri @ M @ Ri.T; B = (B + B.T) / 2
        wM = np.linalg.eigvalsh(B)
    else:
        wM = np.linalg.eigvalsh((M + M.T) / 2)   # fall back to plain
    theta = (-sumC / sumD) if sumD != 0 else np.inf
    print(f"--- {label} ---")
    print(f"  atoms={m}  diag D_jj (each should be >=0, safe cone):")
    print("   ", np.array2string(diag, precision=4, suppress_small=True))
    print(f"  sum_j D_jj          = {sumD:+.6e}")
    print(f"  sum_{{j<k}} C_jk      = {sumC:+.6e}")
    print(f"  KEY: sum C / sum D   = {-theta:+.4f}   => theta = {theta:+.4f}"
          f"   ({'PASS theta<1' if 0 <= theta < 1 else 'FAIL'} for full positivity)")
    print(f"  min eig (full Q, atom metric) = {wM.min():+.6e}   "
          f"(>=0 => MULTISCALE POSITIVE past log2!)")
    print(f"  all eigs: {np.array2string(wM, precision=4, suppress_small=True)}")
    return dict(sumD=sumD, sumC=sumC, theta=theta, mineig=float(wM.min()),
                diag=diag.tolist(), eigs=wM.tolist())


if __name__ == '__main__':
    print("=" * 92)
    print("MULTISCALE WEIL: atoms in safe self-cones, union support PAST log2")
    print("=" * 92)
    print(f"log2={LOG2:.4f}  log3={float(mp.log(3)):.4f}  log4={float(mp.log(4)):.4f}")

    # Shared fine dictionary wide enough to host atoms spread out to centers ~ +-1.2
    Xmax = 1.3
    NB = 53
    dict_centers = list(np.linspace(-Xmax, Xmax, NB))
    s = 0.05
    print(f"\nShared dictionary: NB={NB} in [{-Xmax},{Xmax}], s={s}, cond(G)={np.linalg.cond(gram(dict_centers,s)):.2e}")
    Q, G, A, P, PR, PP = build_engine(dict_centers, s)
    print(f"prime powers in full sum: {len(PP)} (up to log {int(np.exp(max(dict_centers)-min(dict_centers))):d})")

    # ---- Experiment 1: TWO atoms, each self-safe (2*hw < log2), separated so the UNION exceeds log2
    # halfwidth hw small => g_j support 2hw < log2 (safe).  Place atoms at +-d/2, so the cross
    # correlation reaches separation ~ d which we push past log2.
    print("\n" + "#" * 92)
    print("# EXPERIMENT 1: two equal atoms at +-d/2, self-support 2*hw < log2, union span = d+2hw")
    print("#" * 92)
    hw = 0.15                      # self support 2*hw=0.30 < log2 (SAFE diagonal)
    for d in [0.3, 0.5, 0.7, 0.9, 1.2, 1.6, 2.0]:
        a1 = make_atom(dict_centers, -d / 2, hw, s)
        a2 = make_atom(dict_centers, +d / 2, hw, s)
        M, D, C, Gm = cross_scale_analysis([a1, a2], Q, G)
        # the cross correlation reaches separation up to d+2hw; report whether it crosses log2
        maxsep = d + 2 * hw
        tag = f"d={d:.2f} (atom self-supp {2*hw:.2f}<log2; cross sep up to {maxsep:.2f}" \
              f" {'>log2 ACTIVE' if maxsep>LOG2 else '<log2 empty'})"
        report(M, D, C, Gm, tag)
        print()
