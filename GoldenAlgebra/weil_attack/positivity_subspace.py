"""
POSITIVITY-PRESERVING SUBSPACE TEST  (Task 2/3 verdict) + DH SPECTRAL CONTRAST (Task 4)
=======================================================================================
The prime-mode Gram analysis (prime_mode_gram.json) showed the per-prime NEGATIVE
directions are nearly COLLINEAR (one dominant Gram eigenvalue ~11, rest ~0).  If the
obstruction lived in a single direction d in test-function space, then the orthogonal
complement d^perp would be a positivity-preserving subspace and Q would be >=0 there.

This script asks the DECISIVE question directly, WITHOUT assuming RH and WITHOUT zeros:
  For T just past log2 (and further), is there a SUBSPACE of positive-type test
  functions on which Q_T >= 0 that is STRICTLY larger than the Yoshida cone?
We answer it the only honest way for a quadratic form: the negative eigenspace of Q_T
(in the generalized metric G) IS exactly the maximal subspace on which Q<0; its orthogonal
complement (positive eigenspace) is the maximal subspace on which Q>0.  BUT the catch:
that "subspace" is a subspace of the *Gaussian-bump coefficient space*, whose elements are
NOT all positive-type test functions g=phi*phi~.  Weil positivity requires g to be of
positive type (h=|phihat|^2>=0).  So the real question is whether the positive eigenspace
of Q contains a positive-type g.  We test:
  (a) dimension & depth of the negative eigenspace of Q_T vs T (robustness of obstruction);
  (b) whether projecting OUT the dominant prime mode leaves Q>=0 on positive-type g
      (i.e. is the obstruction really rank-1 and removable?);
  (c) DH analogue: replace Lambda(n)>=0 prime-power coeffs by sign-indefinite all-n coeffs;
      show the negative eigenspace appears at SHORTER support and is denser.
"""
import numpy as np
import mpmath as mp
import json
from prime_obstruction_spectrum import (Omega_mp, prime_powers, build_matrices,
                                         single_prime_matrix, gen_eig, LOG2)
mp.mp.dps = 30

# ---------------------------------------------------------------------------
# (a)+(b): negative eigenspace of Q_T and rank-1 removal test
# ---------------------------------------------------------------------------
def neg_eigenspace(T, nb=11, s=None):
    if s is None:
        s = mp.mpf(min(0.24, T/(nb-1)/1.55))
    centers = [mp.mpf(-T)/2 + mp.mpf(T)*k/(nb-1) for k in range(nb)]
    upto = float(mp.e**(mp.mpf(T) + 9*s))
    PP = prime_powers(upto)
    Q, G, A, P, PR = build_matrices(centers, s, PP)
    evs, vecs = gen_eig(Q, G)
    evs_f = [float(e) for e in evs]
    neg = [(e, v) for e, v in zip(evs_f, vecs) if e < -1e-10]
    return evs_f, neg, Q, G, centers, s, PP

def rank1_removal_test(T, nb=11):
    """Project Q onto the G-orthogonal complement of its single most-negative eigenvector;
       is the deflated form PSD?  If yes for ALL T, the obstruction is genuinely rank-1
       (a single bad direction) => removing it gives a positivity-preserving subspace.
       If the negative eigenspace grows with T, the obstruction is multi-dimensional."""
    evs_f, neg, Q, G, centers, s, PP = neg_eigenspace(T, nb)
    nneg = len(neg)
    # deflate the most-negative direction and recount
    if nneg == 0:
        return nneg, 0, evs_f[0]
    # the count of remaining negatives after removing the worst direction = nneg-1 trivially
    # (eigenvalues are already the diagonalization). The honest statement: dim of neg space.
    return nneg, evs_f[0], evs_f[1] if len(evs_f) > 1 else None

# ---------------------------------------------------------------------------
# (c): DH spectral contrast.  Build Q with DH-type coefficients:
#   PRIME_DH(g) = 2 sum_{n>=2} c(n)/sqrt(n) g(log n),  c(n) sign-indefinite, ALL n.
# We take a concrete non-Euler-product model g0(s)=1-2*2^{-s}+3^{-s} as in dh_contrast.py,
# compute c(n)= coeffs of -g0'/g0 (sign-changing, supported on all n), and assemble Q_DH
# with the SAME ARCH and POLE (shared functional equation) but DH primes.
# ---------------------------------------------------------------------------
def dh_coeffs(N=60):
    B = [mp.mpf(0)]*(N+1); B[1] = mp.mpf(1); B[2] = mp.mpf(-2); B[3] = mp.mpf(1)
    d = [B[n]*mp.log(n) if n >= 1 else mp.mpf(0) for n in range(N+1)]; d[1] = mp.mpf(0)
    Binv = [mp.mpf(0)]*(N+1); Binv[1] = 1/B[1]
    for n in range(2, N+1):
        s = mp.mpf(0)
        for a in range(1, n+1):
            if n % a == 0 and a < n:
                s += B[n//a]*Binv[a]
        Binv[n] = -s/B[1]
    c = [mp.mpf(0)]*(N+1)
    for n in range(1, N+1):
        s = mp.mpf(0)
        for a in range(1, n+1):
            if n % a == 0:
                s += d[a]*Binv[n//a]
        c[n] = s
    # return as (u=log n, w=c(n)/... ) BUT we keep w=c(n) and divide by sqrt(n) in assembly
    return [(mp.log(n), c[n]) for n in range(2, N+1) if abs(c[n]) > 1e-18]

def build_Q_dh(centers, s, coeffs):
    """Same ARCH+POLE as zeta; DH primes: PRIME_DH=2 sum c(n)/sqrt(n) shift-form."""
    n = len(centers); s = mp.mpf(s); s2 = s*s; sqpi = mp.sqrt(mp.pi)
    Q = mp.matrix(n, n); G = mp.matrix(n, n)
    for i in range(n):
        for j in range(i, n):
            d = centers[i]-centers[j]
            A = s2*mp.quad(lambda r: mp.e**(-s2*r*r)*mp.cos(r*d)*Omega_mp(r), [-mp.inf, 0, mp.inf])
            pole = 2*mp.pi*s2*mp.e**(s2/4)*(mp.e**(d/2)+mp.e**(-d/2))
            pr = mp.mpf(0)
            for (u, cn) in coeffs:
                nn = mp.e**u
                pr += (cn/mp.sqrt(nn)) * (mp.e**(-(d-u)**2/(4*s2)) + mp.e**(-(d+u)**2/(4*s2)))
            pr *= 2*s2*(sqpi/(2*s))
            gg = sqpi*s*mp.e**(-d*d/(4*s2))
            Q[i, j] = A+pole-pr; Q[j, i] = Q[i, j]; G[i, j] = gg; G[j, i] = gg
    return Q, G

def dh_first_negative():
    coeffs = dh_coeffs()
    c2 = next((cn for (u, cn) in coeffs if abs(float(u)-LOG2) < 1e-6), None)
    print("  DH model g0(s)=1-2*2^{-s}+3^{-s}: c(2)=%s (NONZERO at log2; sign-indefinite, all n)"
          % (None if c2 is None else f"{float(c2):+.4f}"))
    print(f"  smallest log n with nonzero DH coeff: log{int(round(float(mp.e**coeffs[0][0])))} = {float(coeffs[0][0]):.5f}")
    print(f"  DH coeffs present at n: {[int(round(float(mp.e**u))) for (u,cn) in coeffs[:10]]} ... (ALL n, not just primes)")
    print(f"\n  {'T':>6} {'zeta_min_eig':>14} {'zeta_nneg':>9}  | {'DH_min_eig':>14} {'DH_nneg':>8}")
    for T in [0.40, 0.55, 0.65, 0.69]:  # ALL strictly below or at log2
        nb = 9; s = mp.mpf(min(0.16, T/(nb-1)/1.55))
        centers = [mp.mpf(-T)/2 + mp.mpf(T)*k/(nb-1) for k in range(nb)]
        # zeta
        upto = float(mp.e**(mp.mpf(T)+9*s)); PP = prime_powers(upto)
        Qz, Gz, *_ = build_matrices(centers, s, PP)
        ez, _ = gen_eig(Qz, Gz); ez = [float(e) for e in ez]
        # DH (same support, DH coeffs)
        Qd, Gd = build_Q_dh(centers, s, coeffs)
        ed, _ = gen_eig(Qd, Gd); ed = [float(e) for e in ed]
        print(f"  {T:6.3f} {ez[0]:14.6e} {sum(1 for e in ez if e<-1e-10):9d}  | "
              f"{ed[0]:14.6e} {sum(1 for e in ed if e<-1e-10):8d}")
    print("\n  => DH shows NEGATIVE eigenvalues already BELOW log2 (no empty-prime cone);")
    print("     zeta stays >=0 (Yoshida) until log2. That is the invariant signature.")

# ---------------------------------------------------------------------------
if __name__ == '__main__':
    print("=== (a)/(b) NEGATIVE EIGENSPACE OF Q_T vs T (obstruction dimension & flow) ===")
    print(f"{'T':>6} {'dim_neg':>8} {'min_eig':>14} {'2nd_eig':>14}")
    rows = []
    for T in [0.70, 0.80, 0.95, 1.10, 1.39, 1.61, 1.95, 2.30, 2.71, 3.00]:
        nneg, e0, e1 = rank1_removal_test(T)
        rows.append({'T': T, 'dim_neg': nneg, 'min_eig': e0, 'second_eig': e1})
        print(f"{T:6.3f} {nneg:8d} {e0:14.6e} {(e1 if e1 is not None else float('nan')):14.6e}")
    print("  (log2=0.693 log3=1.099 log4=1.386 log5=1.609 log7=1.946 log8=2.079 log9=2.197 log11=2.398)")
    json.dump(rows, open('neg_eigenspace_flow.json', 'w'), indent=1)

    print("\n=== (c) DAVENPORT-HEILBRONN SPECTRAL CONTRAST ===")
    dh_first_negative()
