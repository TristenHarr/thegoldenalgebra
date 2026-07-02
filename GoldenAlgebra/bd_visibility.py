"""
bd_visibility.py — THE DECISIVE COMPUTATION.

The Báez-Duarte / Balazard-Landreau-Saias (BLLS) spectral-over-zeros expansion, and the
displacement (eta = beta - 1/2) sensitivity / visibility threshold, compared against the
universal uncertainty gates (Weil delta*T~1, Li n~t^2/delta, Yoshida log2).

------------------------------------------------------------------------------------------
SPECTRAL EXPANSION OVER ZEROS (BLLS 2000, Burnol 2002).
------------------------------------------------------------------------------------------
Báez-Duarte's continuous companion to d_N^2 is the Beurling-Nyman distance

    D(lambda)^2 = dist^2_{L^2(0,inf)}( chi_(0,1) , closed span of dilations of {1/x} at
                  scales >= lambda ).

The fundamental lower bound (BLLS, Eq. for the approximation problem; refined by Burnol):

    liminf_{lambda->0}  D(lambda)^2 * log(1/lambda)  >=  Sum_rho  m(rho)^2 / |rho|^2 ,

and the discrete Báez-Duarte form has the SAME leading order with log(1/lambda) ~ log N:

    liminf_{N->inf}  d_N^2 * log N  >=  Sum_rho  1/|rho|^2 .

Under RH every rho = 1/2 + i*gamma so |rho|^2 = 1/4 + gamma^2, and

    Sum_rho 1/|rho|^2 = 2 + gamma_Euler - log(4 pi) = 0.0461914...   (closed form).

KEY STRUCTURAL POINT for the displacement framework.  Write a zero as rho = beta + i*gamma
= (1/2 + eta) + i*gamma,  eta = beta - 1/2 the DISPLACEMENT.  Its contribution to the
spectral sum is the PER-ZERO WEIGHT

    w(rho) = 1 / |rho|^2 = 1 / ( (1/2 + eta)^2 + gamma^2 ).

This is the BD "visibility" of a single zero.  Compare:

  * Weil/explicit-formula quadratic form:  a zero contributes  hat-h(gamma - i*eta) type
    terms; an off-line PAIR rho, 1-conj(rho) contributes with the archimedean kernel.
  * Li coefficients:  lambda_n = Sum_rho [1 - (1-1/rho)^n], off-line zero visible at
    n ~ t^2/delta  (the (1-1/rho)^n geometric amplification).
  * BD weight:  w(rho) = 1/|rho|^2 — NO n or N dependence in the WEIGHT itself; the only
    N/lambda dependence is the universal 1/log N prefactor SHARED by every zero.

This is the crux we test below.
------------------------------------------------------------------------------------------
"""
import mpmath as mp
import numpy as np

mp.mp.dps = 30

# ---- The three universal gates (for a single off-line zero: displacement delta, height t) ----

def weil_gate_support(delta, t):
    """Weil/Guinand explicit-formula support gate. A test function of band-support [-X,X]
    in log-scale 'sees' a zero pair at displacement delta only once the support resolves
    the OFF-LINE shift, i.e. when delta * (effective resolution) ~ 1.  The Weil quadratic
    form's archimedean kernel separates an off-line pair from the line at support length
    X ~ 1/delta (independent of t to leading order: the 'delta*T~1' wall, T<->support).
    Returns the required support length X."""
    return 1.0/float(delta)

def li_gate_n(delta, t):
    """Li-coefficient visibility: lambda_n = sum_rho [1-(1-1/rho)^n]. An off-line zero at
    rho=1/2+delta+it makes |1-1/rho| differ from the on-line value by ~ delta/t^2, and the
    deviation becomes O(1) (visible) at  n ~ t^2/delta."""
    return float(t)**2/float(delta)

def yoshida_gate(delta, t):
    """Yoshida log2 gate (the 'log 2' threshold for sign change in the relevant kernel).
    Provided for completeness as a constant-scale comparison."""
    return float(mp.log(2))

# ---- The BD per-zero weight and its displacement sensitivity ----

def bd_weight(eta, gamma):
    """w(rho) = 1/|rho|^2 = 1/((1/2+eta)^2 + gamma^2)."""
    eta = mp.mpf(eta); gamma = mp.mpf(gamma)
    return 1/((mp.mpf('0.5')+eta)**2 + gamma**2)

def bd_weight_displacement_derivative(eta, gamma):
    """d w / d eta  at displacement eta.  = -2(1/2+eta)/((1/2+eta)^2+gamma^2)^2.
    The SIGN and SIZE of how an off-line zero perturbs the spectral sum vs the on-line one."""
    eta = mp.mpf(eta); gamma = mp.mpf(gamma)
    s = mp.mpf('0.5')+eta
    return -2*s/((s*s+gamma**2)**2)

def bd_pair_weight(eta, gamma):
    """A zero OFF the line comes in a functional-equation quadruple {rho, 1-rho, conj}.
    The reflected zero 1-rho has beta'=1/2-eta, i.e. displacement -eta, SAME |gamma|.
    BD sums over all nontrivial zeros once each, so an off-line pair contributes
       1/((1/2+eta)^2+gamma^2) + 1/((1/2-eta)^2+gamma^2).
    Compare to the on-line value 2/(1/4+gamma^2)."""
    return bd_weight(eta,gamma) + bd_weight(-eta,gamma)

def bd_excess(eta, gamma):
    """How much MORE (or less) an off-line pair at displacement eta contributes to the BD
    spectral sum than the same pair on the line.  This is the displacement-SENSITIVE part
    of d_N^2 * log N."""
    onl = 2*bd_weight(0,gamma)
    return bd_pair_weight(eta,gamma) - onl

if __name__ == "__main__":
    print("="*78)
    print("BD per-zero weight w(rho)=1/|rho|^2 and displacement sensitivity")
    print("="*78)
    # first zero height
    t1 = mp.mpf('14.134725')
    print(f"\nFirst zero height t = {float(t1):.4f}")
    print(f"{'eta(=delta)':>12} {'w_pair':>14} {'on-line':>14} {'BD excess':>16} {'rel excess':>12}")
    for delta in [0, 1e-4, 1e-3, 1e-2, 1e-1, 0.25, 0.49]:
        wp = bd_pair_weight(delta, t1)
        onl = 2*bd_weight(0,t1)
        exc = bd_excess(delta, t1)
        rel = exc/onl
        print(f"{delta:>12} {float(wp):>14.8f} {float(onl):>14.8f} {float(exc):>16.3e} {float(rel):>12.3e}")

    print("\nLeading-order in delta (Taylor):  BD excess ~ C(gamma)*delta^2, C= d^2/deta^2 of pair/2")
    # second derivative of w(eta)+w(-eta) at eta=0 = 2 w''(0)
    for t in [mp.mpf('14.13'), mp.mpf('100'), mp.mpf('1000')]:
        h = mp.mpf('1e-6')
        d2 = (bd_pair_weight(h,t) - 2*bd_pair_weight(0,t) + bd_pair_weight(-h,t))/h**2
        # analytic: pair''(0) = 2*w''(0); w(eta)=1/((1/2+eta)^2+t^2)
        print(f"  t={float(t):>8.2f}:  C(t)=pair''(0) ~ {float(d2):>14.6e}   (so excess ~ {float(d2/2):.4e}*delta^2)")

    print("\n" + "="*78)
    print("VISIBILITY THRESHOLD COMPARISON: at what 'support length' / N does an")
    print("off-line zero (delta, t) become measurable in each criterion?")
    print("="*78)
    print(f"{'delta':>8} {'t':>8} | {'Weil X~1/d':>12} {'Li n~t^2/d':>14} {'BD: see below':>16}")
    for (delta,t) in [(1e-3,14),(1e-3,100),(1e-2,14),(1e-2,100),(1e-1,1000)]:
        print(f"{delta:>8} {t:>8} | {weil_gate_support(delta,t):>12.1f} {li_gate_n(delta,t):>14.1f} {'N-independent w':>16}")

    print("""
INTERPRETATION (printed; full analysis in the report):
 - Weil gate:  support X ~ 1/delta  (T<->support => delta*T~1).  t-INDEPENDENT.
 - Li gate:    n ~ t^2/delta.  STRONGLY t-dependent (high zeros need huge n).
 - BD weight:  w(rho)=1/|rho|^2.  The displacement enters as eta^2/|rho|^4 EXCESS,
               with NO N or lambda in the per-zero weight; the ONLY scale is the
               universal 1/log N prefactor shared by ALL zeros.
""")
