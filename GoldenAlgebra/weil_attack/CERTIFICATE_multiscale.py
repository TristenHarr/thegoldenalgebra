"""
=============================================================================================
CERTIFICATE (multiscale route): cross-scale interference RECONSTRUCTS the prime obstruction.
The Yoshida cone is sharp even against a wavelet/Calderon decomposition.  NO partial positivity
past log2 from a scalar theta<1 bound; the controlling object is a MATRIX inequality C >= -D that
is saturated EXACTLY at the moving prime obstruction.
=============================================================================================
All experiments UNCONDITIONAL: Q built from the validated ARCH(digamma)+POLE(cosh)-PRIME(Lambda/
sqrt n) engine (matched to the zero-sum ~1e-16).  NO RH.  Zero-sum used only as an independent
witness check (Q(phi) matrix = direct prime sum to full precision -- multiscale_verdict.py II).

THE SETUP.  Decompose phi = sum_j phi_j into ATOMS (translated+dilated signed wavelets) each
SELF-SAFE: g_j = phi_j*phi_j~ supported in (-log2,log2)  =>  D_jj = Q(g_j) >= 0 (Yoshida diagonal).
Bilinearity:  Q(sum phi_j) = sum_j D_jj + 2 sum_{j<k} C_jk,   C_jk = Q(phi_j, phi_k).
All difficulty is the cross-scale interference C.  Atoms tile total support PAST log2.

THE FIVE FACTS (scripts: multiscale_weil.py, multiscale_wavelet.py, multiscale_saturate.py,
multiscale_crossterm.py, multiscale_theta.py, multiscale_verdict.py, multiscale_moving_mode.py,
multiscale_dh.py):

(1) DIAGONAL IS SAFE, BUT NOT ENOUGH.  Every D_jj >= 0 (min D_jj = +0.13 in the enriched family).
    A LOW-dimensional safe family (e.g. 9 atoms) gives Q|_V PSD past log2 -- but the SAME holds for
    an unsafe control of equal dim (multiscale_saturate.py): the low-dim positivity is RESOLUTION,
    not the safe-cone constraint.  Captured fraction of the obstruction grows 0.03 -> 0.79 with dim.

(2) ENRICHED SAFE FAMILY GOES NEGATIVE.  75-atom safe family (3 scales x 25 translations, every
    D_jj >= +0.13):  min-eig Q|_V = -8.25e-3 < 0.  The witness is GENUINE (multiscale_verdict.py II):
    its matrix Q value equals the direct ARCH+POLE-PRIME computation to full precision, and the
    prime part matches the explicit 2*sum Lambda(n)/sqrt(n) g(log n).  A real Weil-negative test
    function built ENTIRELY from safe-diagonal atoms.

(3) THE MECHANISM -- cross terms ARE the prime obstruction re-indexed by SEPARATION
    (multiscale_crossterm.py).  C_jk involves the cross-correlation phi_j*phi_k~ near separation
    |c_k-c_j|; its prime part activates exactly when that separation crosses log2.  Min-eig leaves
    the 0+ floor precisely as the cross REACH (max separation + atom width) passes log2.  The
    interference is a SECOND copy of the prime sum, now over inter-atom separations.

(4) NO DIAGONALIZATION OF THE MOVING MODE (multiscale_moving_mode.py).  Q_prime restricted to the
    multiscale span has effective rank 14.09 (cf. FINDINGS sec9 ~13) and its dominant obstruction
    eigenvector spreads over 17.9 of 23 atoms.  The multiscale family does NOT localize one prime
    per scale; the cross terms RE-ASSEMBLE the full high-rank moving packet across scales.

(5) THE EXACT INEQUALITY -- theta<1 is NECESSARY-LOOKING but NOT SUFFICIENT (multiscale_theta.py).
    Positivity of Q|_V  <=>  C >= -D as MATRICES  <=>  lam_min(D^{-1/2} C D^{-1/2}) >= -1.
        family                    theta   lam_min(C|D)   mineig Q|V
        [0.3] x9                  0.4347    -0.9387        +8.42e-2   (PSD)
        [0.3] x17                 0.3088    -0.9890        +3.42e-3   (PSD, near edge)
        [0.2,0.3] x17             0.3395    -1.0005        -4.37e-4   (NEG)
        [0.12,0.22,0.3] x25       0.3535    -1.0013        -8.25e-3   (NEG)
        [0.1..0.32] x21           0.4257    -1.0016        -1.27e+0   (NEG)
    theta (trace ratio) stays ~0.2-0.43 < 1 throughout, while lam_min(C|D) crosses -1 EXACTLY when
    min-eig crosses 0.  The cross matrix C is INDEFINITE (rank ~13, the moving obstruction), not a
    scalar fraction of D.  A scalar theta<1 cannot deliver positivity; the matrix bound C >= -D is
    SATURATED at the obstruction direction (lam_min -> -1.00...).

(6) ZETA vs DH (multiscale_dh.py).  The whole route rests on the SAFE DIAGONAL D_jj >= 0, which is
    Yoshida = the empty (-log2,log2) prime gap.  For Davenport-Heilbronn (real c(n) of -g0'/g0,
    g0=1-2*2^-s+3^-s; c(2)=-1.386, sign-changing, ALL n) the diagonal FAILS: an atom whose self-
    correlation reaches log2 has D_jj(DH) = -0.217 < 0 (vs D_jj(zeta)=+0.57).  The multiscale
    DIAGONAL positivity -- the foundation of the decomposition -- EXISTS for zeta and EVAPORATES for
    DH.  It is itself the Euler-product (zeta-vs-DH) distinction.

VERDICT (multiscale).  The wavelet/Calderon decomposition does NOT beat the Yoshida cone.  The
diagonal D is safe by construction, but the cross-scale interference C is the SAME moving, high-rank
(~13) prime obstruction, re-indexed by inter-atom separation.  It saturates the matrix inequality
C >= -D exactly (lam_min -> -1) and breaks it as soon as the multiscale family resolves the
obstruction, driving Q < 0 on genuine safe-diagonal test functions.  There is no structured class
on which sum_{j<k} Q(g_j,g_k) >= -theta sum_j Q(g_j) with theta<1 forces positivity, because the
controlling object is a matrix, not a scalar.  Multiscale localizes each prime BAND but the cross
terms couple the bands back into the moving collective coordinate -- exactly the wall of FINDINGS
sec9.  Consistent with Bombieri (negatives track off-line zeros once support resolves them) and
Connes-Consani (no positivity subspace beyond the prolate/Yoshida scale).  The Yoshida cone is SHARP
against multiscale decomposition.

Run:  python3 multiscale_weil.py ; python3 multiscale_wavelet.py ; python3 multiscale_saturate.py ;
      python3 multiscale_crossterm.py ; python3 multiscale_theta.py ; python3 multiscale_verdict.py ;
      python3 multiscale_moving_mode.py ; python3 multiscale_dh.py
"""
print(__doc__)
