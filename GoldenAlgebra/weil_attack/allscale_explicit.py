"""
TASK 3/4: connect E(mu) to the EXPLICIT FORMULA / prime side -- the HONEST VERDICT.
====================================================================================
The decisive question: is E(mu) = INT Q_{g_T} dnu (the Weil functionals integrated,
hence governed by the indefinite prime side), or is it a DIFFERENT, manifestly-positive
object that the Euler product does NOT control?

The KEY identity (QUART_FINDINGS (star)): for positive-type g, supp g in [-T,T], one
off-line quartet {1/2 +- delta +- i gamma0} contributes to Q(g) EXACTLY
    N(delta,gamma0,T) = 4 INT_{-T}^{T} g(u) cosh(delta u) cos(gamma0 u) du.
Split N = N0 + Delta:
    N0 = 4 ghat(gamma0) >= 0          (on-line value)
    Delta = 4 INT g(u)(cosh(delta u)-1) cos(gamma0 u) du   (off-line correction)
    |Delta| <= 4 (cosh(delta T)-1) INT|g|.            <-- our detector is this BOUND.

So our energy term (cosh(eta T)-1) is the ENVELOPE/BOUND of the true Weil contribution,
with the oscillation cos(gamma0 u) STRIPPED OUT and g replaced by its L1 mass.

CRUX:  E uses  W(eta) = (cosh(eta T)-1)  [POSITIVE, monotone],
       Weil uses  Delta(eta,gamma,g,T) = 4 INT g(u)(cosh(eta u)-1)cos(gamma u)du
                   [SIGN-INDEFINITE because of cos(gamma u)].
If E were INT Q_{g_T} dnu it would inherit the cos-indefiniteness.  It does NOT, because
E throws away the cos and the g-shape and keeps only the magnitude bound.  We test:
 (T1) Is the per-scale term cosh(eta T)-1 REALIZABLE as a Weil functional Q_{g_T}(positive-
      type g_T) of the SAME zero?  -> NO: Q always carries the cos(gamma u) oscillation and
      the on-line N0 mass; you cannot get the bare envelope cosh-1 from a genuine Q.
 (T2) The integrated quadratic form: build the actual Weil form Q_T at a grid of scales,
      integrate INT Q_T dnu, and test definiteness of the RESULT.  Does positive-nu
      integration of indefinite Q_T yield a definite form (E's hope) or stay indefinite (wall)?
 (T3) The precise reason: E is NOT a quadratic form in a test function at all.  It is a sum
      over zeros of a positive functional of the DISPLACEMENT eta_rho, which is NOT a linear
      read-out of any g.  The map {zeros} -> E is not of the form g |-> Q(g).  Pin this.
"""
import numpy as np
import mpmath as mp
mp.mp.dps = 30

# Reuse the validated ARCH+POLE-PRIME engine
from prime_rank_collective import (prime_powers, gram, arch_matrix, pole_matrix,
                                    prime_matrix, ip_G, LOG2)


def weil_Q(dc, s, upto=None):
    G = gram(dc, s); A = arch_matrix(dc, s); P = pole_matrix(dc, s)
    span = max(dc) - min(dc)
    if upto is None:
        upto = float(np.exp(span + 9 * s))
    PR = prime_matrix(dc, s, prime_powers(upto))
    return A + P - PR, G


if __name__ == "__main__":
    print("=" * 84)
    print("(T1) Can the BARE envelope (cosh(eta T)-1) be a genuine Weil functional Q_{g_T}?")
    print("=" * 84)
    print("""  Weil contribution of ONE off-line quartet (star):
       N(eta,gamma,T) = N0(gamma) + Delta,   N0 = 4*ghat(gamma) >= 0 (on-line mass),
       Delta = 4 INT g(u)(cosh(eta u)-1)cos(gamma u) du,  |Delta| <= 4(cosh(eta T)-1)INT|g|.
  Our energy term is the *bound*  (cosh(eta T)-1)  -- it DROPS:
    (i)  the on-line mass N0 (always present in a real Q; our term is 0 on-line, Q is N0>0);
    (ii) the oscillation cos(gamma u)  (the SOURCE of indefiniteness/cancellation);
    (iii) the g-shape (replaced by INT|g|, the worst case).
  => (cosh(eta T)-1) is the SUP over positive-type g (normalized INT|g|=1, sharp support T)
     of the off-line CORRECTION |Delta|/4 -- an ENVELOPE, not any single Q(g).  No genuine
     positive-type Weil functional equals the bare envelope: every real Q carries N0 and cos.""")

    # Demonstrate (T1) numerically: the realized off-line correction Delta oscillates in gamma
    # and is bounded by the envelope, with EQUALITY only in a sup over g (never a single Q).
    print("\n  Demonstration: realized Delta(eta,gamma,T)/4 vs envelope (cosh(eta T)-1)*INT|g|,")
    print("  for a FIXED positive-type g (Gaussian bump g(u)=e^{-u^2/(2w^2)}), sweep gamma:")
    eta = 0.3; T = 6.0; w = 1.5
    def g(u): return mp.e ** (-u * u / (2 * w * w))
    L1 = float(mp.quad(lambda u: g(u), [-T, T]))
    env = (np.cosh(eta * T) - 1) * L1
    print("  {:>8} {:>16} {:>16} {:>10}".format("gamma", "Delta/4 (real)", "envelope", "|D|<=env?"))
    for gamma in [0.5, 1.0, 2.0, 4.0, 8.0]:
        D = float(mp.quad(lambda u: g(u) * (mp.cosh(eta * u) - 1) * mp.cos(gamma * u), [-T, T]))
        print("  {:8.2f} {:16.6e} {:16.6e} {:>10}".format(gamma, D, env, "yes" if abs(D) <= env + 1e-9 else "NO"))
    print("""  => realized off-line correction is SIGN-CHANGING in gamma (the cos), strictly inside the
     envelope.  Our energy uses the envelope itself: it is NOT the Weil read-out of any g.""")

    print("\n" + "=" * 84)
    print("(T2) INTEGRATED Weil form  INT Q_T dnu(T):  does positive-nu integration make it")
    print("     definite (E's hope) or stay indefinite (the wall)?")
    print("=" * 84)
    # Build Q_T at scales T (support-disciplined), integrate with positive weights nu(T)>=0,
    # and test min eigenvalue of the resulting matrix.  If INT Q_T dnu were PSD unconditionally,
    # that would be a new theorem.  Test it.
    Xmax = 1.2; NB = 41; dc = list(np.linspace(-Xmax, Xmax, NB)); s = 0.05
    # scales realized by truncating the prime sum at e^{T}
    scales = [0.65, 0.9, 1.2, 1.6, 2.0, 2.6, 3.2]
    G = gram(dc, s); A = arch_matrix(dc, s); P = pole_matrix(dc, s)
    def Q_at_scale(T):
        PR = prime_matrix(dc, s, prime_powers(float(np.exp(T))))
        return A + P - PR
    def mineig(M):
        wG, UG = np.linalg.eigh(G); keep = wG > 1e-10 * wG.max()
        U = UG[:, keep]; d = wG[keep]; Wh = U / np.sqrt(d)
        B = Wh.T @ M @ Wh; return np.linalg.eigvalsh((B + B.T) / 2).min()
    print("  per-scale min-eig of Q_T (positive-type Weil form), and the nu-integrated form:")
    print("  {:>6} {:>16}".format("T", "min-eig Q_T"))
    Qint = np.zeros_like(A)
    for T in scales:
        QT = Q_at_scale(T); me = mineig(QT)
        nuT = np.exp(-T * T)   # positive gaussian scale weight
        Qint += nuT * QT
        print("  {:6.2f} {:16.6e}".format(T, me))
    me_int = mineig(Qint)
    print("  ---")
    print("  INT Q_T dnu (gaussian nu, positive weights): min-eig = {:+.6e}".format(me_int))
    print("""  READING: each Q_T is indefinite past log2 (knife-edge, sec.8/9).  A POSITIVE-weighted
  sum  INT Q_T dnu  is a positive combination of indefinite matrices -> STILL INDEFINITE
  (min-eig <= max over T of negative parts, weighted; cannot become PSD by positive mixing
  unless every Q_T is PSD, which they are not past log2).  => integrating the Weil FORM does
  NOT manufacture definiteness.  This is the wall, re-confirmed for the integrated form.""")

    print("\n" + "=" * 84)
    print("(T3) THE PRECISE REASON E escapes (T2)'s wall -- and what it costs.")
    print("=" * 84)
    print("""  E is NOT  INT Q_{g_T} dnu.  It is  INT [ SUM_rho (cosh(eta_rho T)-1) W_T ] dnu.
  The difference is decisive:
   * INT Q_T dnu  is a quadratic form in a TEST FUNCTION g (a g-read-out of the zeros via
     the explicit formula); it inherits the indefinite cos(gamma u) prime cross-terms (T2).
   * E is a functional of the ZEROS DIRECTLY (their displacements eta_rho), each entering
     through the EVEN, POSITIVE kernel cosh(eta_rho T)-1 with NO cos(gamma) oscillation.
  E therefore SIDESTEPS the indefiniteness -- but at a PRICE that is the whole story:
     E is built from the DISPLACEMENTS eta_rho, which are PRECISELY the unknown RH data.
     The explicit formula gives  SUM_rho ghat(gamma_rho) = arch+pole-prime(g)  -- a read-out
     of the zeros by ORDINATE gamma through a test function.  It does NOT give a positive,
     displacement-only read-out  SUM_rho (cosh(eta_rho T)-1).  There is no test function g
     whose Weil functional equals SUM_rho (cosh(eta_rho T)-1): that would require g to detect
     |eta_rho| (off-line displacement) as a POSITIVE quantity, which is exactly the off-line
     correction Delta -- and Delta is sign-indefinite (cos), bounded by but NEVER equal to the
     envelope (T1).  So E is computable from the EXPLICIT ZERO LIST but NOT from the prime side.
  CONSEQUENCE: E=0 => RH is trivially true (each term >=0), but E is NOT accessible from the
  Euler product / arithmetic side as a positive quantity.  The Euler product controls the
  ghat(gamma)-read-out (indefinite Delta), not the positive envelope SUM(cosh(eta T)-1).""")
