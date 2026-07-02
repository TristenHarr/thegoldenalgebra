"""
THE KEY QUESTION: does the scale-integration produce STRUCTURE invisible at fixed T?
====================================================================================
Three structural tests on E(mu) = INT (cosh(eta T)-1) dnu(T) (gaussian nu = e^{-T^2}):

  (S1) CLOSED FORM. INT_0^inf (cosh(eta T)-1) e^{-T^2} dT has an EXACT evaluation.
       => E(eta) is an explicit ANALYTIC function of eta.  Compute it; identify its shape.

  (S2) CONVEXITY in T of the integrand S(T)=cosh(eta T)-1 (and the multi-zero sum):
       is T |-> S(T) monotone / convex?  (cosh is convex+increasing on T>0.)

  (S3) CONVEXITY of E as a FUNCTIONAL of the displacement profile {eta_rho}:
       is E({eta}) convex / a sum of 1-D convex pieces?  Any cross-zero coupling?

  (S4) CANCELLATION ACROSS SCALES: introduce an OSCILLATING window W_T (signed) and
       test whether INT dnu can go NEGATIVE (lose the per-term positivity) -- i.e. is the
       all-scale positivity ROBUST or does a signed scale-weight destroy it (=back to Weil)?
"""
import numpy as np
import mpmath as mp

mp.mp.dps = 40


# ---- (S1) EXACT closed form of E(eta) for gaussian nu ----------------------
def E_single_exact(eta):
    """INT_0^inf (cosh(eta T) - 1) e^{-T^2} dT, closed form.
    INT_0^inf cosh(aT) e^{-T^2} dT = (sqrt(pi)/2) e^{a^2/4}.
    INT_0^inf e^{-T^2} dT = sqrt(pi)/2.
    => E = (sqrt(pi)/2)(e^{eta^2/4} - 1)."""
    return (mp.sqrt(mp.pi) / 2) * (mp.e ** (eta * eta / 4) - 1)


def E_single_numeric(eta):
    return mp.quad(lambda T: (mp.cosh(eta * T) - 1) * mp.e ** (-T * T), [0, mp.inf])


if __name__ == "__main__":
    print("=" * 80)
    print("(S1) CLOSED FORM of the single-zero scale-integrated energy")
    print("=" * 80)
    print("  E(eta) = INT_0^inf (cosh(eta T)-1) e^{-T^2} dT  =  (sqrt(pi)/2)(e^{eta^2/4} - 1)")
    print(f"  {'eta':>6} {'exact':>20} {'numeric':>20} {'match':>8}")
    for eta in [0.0, 0.1, 0.5, 1.0, 2.0, 4.0]:
        ex = E_single_exact(eta); nu = E_single_numeric(eta)
        print(f"  {eta:6.2f} {mp.nstr(ex,12):>20} {mp.nstr(nu,12):>20} "
              f"{'OK' if abs(ex-nu)<1e-15 else 'X'}")
    print("""
  ** STRUCTURE FOUND (closed form): E(eta) = (sqrt(pi)/2)(e^{eta^2/4} - 1). **
  This is an explicit, real-analytic, EVEN, strictly-convex, strictly-increasing-in-|eta|
  function vanishing ONLY at eta=0.  The Gaussian scale-integral COLLAPSES the whole
  cosh-tower into  e^{eta^2/4} - 1  -- a GAUSSIAN-of-the-displacement.  The all-scale
  energy of a profile {eta_rho} (no height window) is
        E = (sqrt(pi)/2) SUM_rho (e^{eta_rho^2/4} - 1),
  a SEPARABLE SUM of identical strictly-convex 1-D potentials V(eta)=e^{eta^2/4}-1.
""")

    # ---- (S2) monotonicity / convexity of the per-scale integrand in T -------
    print("=" * 80)
    print("(S2) Is T |-> S(T) = SUM (cosh(eta_rho T)-1) MONOTONE / CONVEX in T?")
    print("=" * 80)
    etas = [0.2, -0.5, 0.3]   # a signed displacement profile (eta can be +/-, cosh is even)
    Ts = np.linspace(0.01, 5, 12)
    print(f"  profile etas={etas}")
    print("  {:>6} {:>14} {:>14} {:>14}".format("T","S(T)","S'(T)","S''(T)"))
    def S(T): return sum(np.cosh(e*T)-1 for e in etas)
    for T in Ts:
        h=1e-5
        d1=(S(T+h)-S(T-h))/(2*h); d2=(S(T+h)-2*S(T)+S(T-h))/h**2
        print(f"  {T:6.2f} {S(T):14.6e} {d1:14.6e} {d2:14.6e}")
    print("""
  S(T) is a finite sum of (cosh(eta_rho T)-1), each = SUM_k (eta T)^{2k}/(2k)!,
  ALL Taylor coefficients >= 0.  Hence S(T), S'(T), S''(T) are ALL >= 0 for T>=0:
  S is NONNEGATIVE, INCREASING, and CONVEX in T -- with NO sign changes, for EVERY
  displacement profile.  => the per-scale integrand has NO cross-scale cancellation
  on its own (it is a Hausdorff/absolutely-monotone function of T).  STRUCTURE: the
  integrand is ABSOLUTELY MONOTONE in T (all derivatives >=0).
""")

    # ---- (S3) convexity of E as a functional of {eta} ------------------------
    print("=" * 80)
    print("(S3) Is E a CONVEX functional of the displacement profile {eta_rho}?")
    print("=" * 80)
    # V(eta)=e^{eta^2/4}-1 ; check V''>0 everywhere and separability
    def V(eta): return float(mp.e**(eta*eta/4)-1)
    print("  V(eta)=e^{{eta^2/4}}-1 ;  {:>6} {:>12} {:>12}".format("eta","V","V''"))
    for eta in [-3,-1,-0.3,0,0.3,1,3]:
        h=1e-4
        d2=(V(eta+h)-2*V(eta)+V(eta-h))/h**2
        print(f"  {'':>6} {eta:6.2f} {V(eta):12.5e} {d2:12.5e}")
    print("""
  V''(eta) = (1/4)(1 + eta^2/2) e^{eta^2/4} > 0 EVERYWHERE => V strictly convex.
  E({eta}) = (sqrt(pi)/2) SUM_rho V(eta_rho) is a SUM OF CONVEX functions => E is a
  CONVEX functional of the displacement profile, with its UNIQUE GLOBAL MINIMUM (=0)
  at eta=0 (=RH).  No coupling between zeros: SEPARABLE convex.  This convexity is
  REAL and is NOT a fixed-T property (fixed T gives cosh(eta T)-1, also convex in eta,
  but the SCALE INTEGRAL is what gives the clean Gaussian potential e^{eta^2/4}-1).
""")

    # ---- (S4) cancellation across scales with a SIGNED window ----------------
    print("=" * 80)
    print("(S4) CANCELLATION: can a SIGNED scale-weight w(T) make INT w(T)S(T)dT < 0 ?")
    print("=" * 80)
    eta = 1.0
    def integrand_signed(T, freq): return float((mp.cosh(eta*T)-1)*mp.cos(freq*T)*mp.e**(-T*T))
    print(f"  single zero eta={eta}; nu_signed = cos(freq*T) e^{{-T^2}} (oscillating)")
    print(f"  {'freq':>8} {'INT cos(freq T)(cosh-1)e^{-T^2}dT':>34}")
    for freq in [0,1,2,3,5,8]:
        val=mp.quad(lambda T: integrand_signed(float(T),freq),[0,mp.inf])
        print(f"  {freq:8.1f} {mp.nstr(val,10):>34}")
    print("""
  With an OSCILLATING (signed) scale-weight the integral CAN go negative (freq>~2):
  signed nu DESTROYS the per-term positivity -- that is EXACTLY re-introducing the
  indefinite Weil cross-terms (sec.10).  The all-scale POSITIVITY of E is bought
  PRECISELY by nu>=0 (a positive scale measure).  With nu>=0, E>=0 with equality iff
  RH; with signed nu, E is indefinite (=back to the wall).  So nu>=0 is the structural
  dividing line: E is a POSITIVE all-scale invariant exactly on the positive nu cone.
""")
