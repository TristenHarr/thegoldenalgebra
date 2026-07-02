"""
SCALE-INTEGRATED DISPLACEMENT-ENERGY FUNCTIONAL  E(mu)
=====================================================
The object:
    E(mu) = INT_0^inf  [ SUM_rho (cosh(eta_rho * T) - 1) * W_T(gamma_rho) ]  dnu(T)
for a positive scale-measure nu and per-scale window W_T >= 0.

Per-scale integrand  S(T) = SUM_rho (cosh(eta_rho T) - 1) W_T(gamma_rho).
Each summand >= 0 (cosh x - 1 >= x^2/2 >= 0), = 0 iff eta_rho = 0.  So:
    E(mu) = 0  <=>  every term 0  <=>  eta_rho = 0 for all rho  =  RH.
That is the easy direction (proven in Lean). This script studies CONVERGENCE,
DISPLACEMENT-COMPLETENESS, and the KEY QUESTION: does INT dnu(T) produce
structure (monotone/convex in T, convex in {eta}, cancellation) invisible at fixed T?

We work with FINITE displacement profiles {(gamma_rho, eta_rho)} (models) and the
ACTUAL low zeta zeros (eta=0) as a control.  No RH assumed: we are testing the
FUNCTIONAL's structure on arbitrary displacement profiles, including off-line ones.

Design choices for nu and W_T:
 (A) dnu = dT / T^2   on [1,inf)   (the mission's first suggestion)  -- needs W_T cutoff
 (B) dnu = exp(-T^2) dT  (Gaussian scale measure) -- convergent for ANY bounded eta set
 (C) W_T(gamma) = exp(-(gamma/Gamma_T)^2) height window, Gamma_T = c*T (band-limited)
     or W_T = 1 (no height window; pure displacement).
"""
import numpy as np
import mpmath as mp

mp.mp.dps = 30


# ----------------------------------------------------------------------------
# The per-scale displacement energy  S(T; profile, W, nu-independent)
# ----------------------------------------------------------------------------
def S_of_T(T, etas, gammas=None, W=None):
    """SUM_rho (cosh(eta_rho T) - 1) * W_T(gamma_rho).
    W: callable (T, gamma) -> weight >=0, or None (=1)."""
    tot = 0.0
    for i, eta in enumerate(etas):
        c = np.cosh(eta * T) - 1.0
        w = 1.0 if (W is None) else W(T, gammas[i])
        tot += c * w
    return tot


# ----------------------------------------------------------------------------
# nu measures
# ----------------------------------------------------------------------------
def nu_gaussian(T, alpha=1.0):
    return np.exp(-alpha * T * T)

def nu_invsq_cutoff(T, T0=1.0):
    # dT/T^2 on [T0, inf); 0 below T0
    return 0.0 if T < T0 else 1.0 / (T * T)

def nu_exp(T, beta=1.0):
    return np.exp(-beta * T)


# ----------------------------------------------------------------------------
# E(mu) by numerical integration over T
# ----------------------------------------------------------------------------
def E_functional(etas, gammas=None, W=None, nu=nu_gaussian, Tmax=40.0):
    f = lambda T: S_of_T(T, etas, gammas, W) * nu(T)
    val = mp.quad(lambda T: mp.mpf(f(float(T))), [0, Tmax])
    return float(val)


if __name__ == "__main__":
    print("=" * 80)
    print("E(mu): SCALE-INTEGRATED DISPLACEMENT ENERGY -- convergence & completeness")
    print("=" * 80)

    # ---- 1. CONVERGENCE test: cosh(eta T) ~ e^{|eta|T}/2 ; nu must beat it. ----
    print("\n[1] CONVERGENCE of E for a single off-line zero eta>0, various nu:")
    print(f"{'nu':>22} {'eta=0.1':>12} {'eta=0.3':>12} {'eta=1.0':>12} {'eta=3.0':>12}")
    for name, nu, Tm in [
        ("gaussian e^{-T^2}", nu_gaussian, 40),
        ("exp e^{-T}", nu_exp, 200),          # converges only if |eta|<beta=1
        ("invsq 1/T^2 [1,inf)", nu_invsq_cutoff, 200),  # DIVERGES for any eta>0
    ]:
        row = []
        for eta in [0.1, 0.3, 1.0, 3.0]:
            try:
                v = E_functional([eta], nu=nu, Tmax=Tm)
                row.append(f"{v:12.4e}")
            except Exception as e:
                row.append(f"{'DIV/err':>12}")
        print(f"{name:>22} " + " ".join(row))

    print("""
  READING:
   * gaussian e^{-T^2}: CONVERGES for EVERY eta (super-exponential decay beats cosh).
     And E>0 strictly for eta>0, =0 for eta=0  => CONVERGENT + DISPLACEMENT-COMPLETE.
   * exp e^{-T}: converges only for |eta|<1 (cosh(eta T)e^{-T}=e^{(|eta|-1)T} integrable
     iff |eta|<1).  NOT displacement-complete: blind to eta>=1 (integral diverges -> must
     cap, and large eta saturate).  A FIXED exponential rate has a displacement HORIZON.
   * 1/T^2 on [1,inf): DIVERGES for any eta>0 (cosh grows, 1/T^2 cannot tame it).
     The mission's dnu=dT/T^2 FAILS convergence unless W_T provides an exp cutoff.
""")

    # ---- 2. The RIGHT PAIRING: gaussian nu is the convergent-and-complete choice ----
    print("[2] E(eta) for gaussian nu = e^{-T^2}, single zero, sweep eta (completeness):")
    print(f"{'eta':>8} {'E':>16} {'E/eta^2 (small-eta slope)':>28}")
    for eta in [0.0, 0.01, 0.05, 0.1, 0.3, 0.5, 1.0, 2.0, 5.0, 10.0]:
        v = E_functional([eta], nu=nu_gaussian, Tmax=60)
        ratio = v / (eta * eta) if eta > 0 else float('nan')
        print(f"{eta:8.2f} {v:16.6e} {ratio:28.6e}")
    print("""
  E(eta)=0 iff eta=0; strictly increasing in |eta|; finite for ALL eta (even eta=10).
  E/eta^2 -> const as eta->0 (the cosh-1 ~ (eta T)^2/2 leading term integrated):
  E(eta) ~ eta^2 * INT (T^2/2) e^{-T^2} dT  for small eta.  DISPLACEMENT-COMPLETE
  (every eta>0 detected) AND CONVERGENT.  This is the (nu=gaussian) functional we bank.
""")
