"""
osc_phase_diagram.py
====================
POSITIVITY PHASE DIAGRAM of the height-oscillation continuation W_{alpha,a}(g),
interpolating between the POSITIVE DISPLACEMENT ENVELOPE (alpha=0) and the TRUE
WEIL READOUT (alpha=1), with heat-damping e^{-a*gamma^2} of high zeros.

THE OBJECT (mission):
   W_{alpha,a}(g) = SUM_rho e^{-a*gamma_rho^2} * INT_{-T}^{T} g(u)(cosh(eta_rho u)-1) cos(alpha*gamma_rho u) du
 - alpha=1 : true Weil oscillation (the cos(gamma u) of identity (star)) -- INDEFINITE.
 - alpha=0 : positive displacement envelope INT g(u)(cosh(eta u)-1) du -- POSITIVE for positive-type g.
 - a>0    : heat damping of high zeros (low zeros verified on-line => safe). a=0: full problem.

This is EXACTLY the interpolation between the ALLSCALE positive envelope (cosh-1, no cos)
and the cos-carrying indefinite Delta of QUART_FINDINGS identity (star). We map sign(W),
trace the obstruction boundary a0(alpha), test connectivity to (1,0), test alpha-monotonicity,
and check whether the obstruction encodes the SAME delta*T ~ 1 gate (ScratchResolutionTheory).

We use a smooth positive-type g and its closed-form u-integral for speed/exactness, plus a
g-BASIS (several widths) so we can take the MIN-EIGENVALUE of the W-quadratic form over the
basis (the honest "is W>=0 as a form, not just one g" test).

NO RH assumed. The "zeros" of the off-line population are a FAKE quartet model with prescribed
displacements eta_rho; the on-line low zeros (eta=0) contribute 0 to W by construction (cosh(0)-1=0)
so they are trivially safe and we focus on the fake off-line population, which is the adversary.
"""
import numpy as np
import mpmath as mp
mp.mp.dps = 30

# ----------------------------------------------------------------------------
# g basis: positive-type Gaussians g_w(u) = exp(-u^2/(2 w^2)).  g_w = f*f~ with
# f Gaussian, so g_w IS positive-type (ghat = w sqrt(2pi) exp(-w^2 xi^2/2) >= 0).
# We FORMALLY truncate to [-T,T]; for w << T the truncation error is negligible
# and the closed form below (infinite-line Gaussian integral) is exact to O(e^{-T^2/2w^2}).
# We also provide the TRUE truncated integral via mpmath for validation.
# ----------------------------------------------------------------------------

def I_closed(eta, w, beta):
    """INT_{-inf}^{inf} exp(-u^2/(2w^2)) (cosh(eta u)-1) cos(beta u) du, closed form.
       INT exp(-u^2/2w^2) cosh(eta u) cos(beta u) du
         = w sqrt(2pi) * exp(-w^2(beta^2-eta^2)/2) * cos(w^2 eta beta)   [Re part]
       INT exp(-u^2/2w^2) cos(beta u) du = w sqrt(2pi) exp(-w^2 beta^2/2).
       So the (cosh-1) version = first - second.
       Derivation: cosh(eta u)cos(beta u) = (1/4) sum_{s,s'} exp((s eta + i s' beta)u);
       gaussian moment INT exp(-u^2/2w^2) exp(c u) du = w sqrt(2pi) exp(w^2 c^2/2).
       Summing the four c = +-eta +- i beta gives the cos(w^2 eta beta) closed form."""
    s2pi = w * np.sqrt(2*np.pi)
    cosh_part = s2pi * np.exp(-0.5*w*w*(beta*beta - eta*eta)) * np.cos(w*w*eta*beta)
    one_part  = s2pi * np.exp(-0.5*w*w*beta*beta)
    return cosh_part - one_part

def I_trunc(eta, w, beta, T):
    """True truncated integral over [-T,T] (mpmath), for validation only."""
    f = lambda u: mp.e**(-u*u/(2*w*w)) * (mp.cosh(eta*u)-1) * mp.cos(beta*u)
    return float(mp.quad(f, [-T, 0, T]))

# ----------------------------------------------------------------------------
# Off-line FAKE quartet population.  Each quartet {1/2 +- eta +- i gamma}.
# We build a realistic adversary: a spread of ordinates gamma and displacements eta.
# ----------------------------------------------------------------------------

def fake_population(kind="adversary", n=40, seed=0):
    rng = np.random.default_rng(seed)
    if kind == "adversary":
        # ordinates spread over a realistic high range; small-ish displacements
        gammas = np.linspace(10.0, 200.0, n)
        etas   = 0.15*np.ones(n)            # uniform displacement (the cleanest signal)
        return gammas, etas
    if kind == "single":
        return np.array([100.0]), np.array([0.2])
    if kind == "lowzeros_offline":
        # take the actual low zeta ordinates but PRETEND they are off-line (worst-case adversary)
        gammas = np.array([float(mp.im(mp.zetazero(k))) for k in range(1, n+1)])
        etas   = 0.15*np.ones(len(gammas))
        return gammas, etas
    if kind == "mixed_eta":
        gammas = np.linspace(10.0, 200.0, n)
        etas   = rng.uniform(0.05, 0.30, n)
        return gammas, etas
    raise ValueError(kind)

# ----------------------------------------------------------------------------
# W_{alpha,a}(g_w):  for a single width w.
#   = SUM_rho e^{-a gamma_rho^2} * I(eta_rho, w, alpha*gamma_rho)
# ----------------------------------------------------------------------------

def W_scalar(alpha, a, gammas, etas, w):
    beta = alpha*gammas
    damp = np.exp(-a*gammas*gammas)
    terms = np.array([I_closed(etas[i], w, beta[i]) for i in range(len(gammas))])
    return float(np.sum(damp*terms))

# ----------------------------------------------------------------------------
# Form version: W as a quadratic form is NOT directly available (W is linear in g),
# but the HONEST "is W>=0 over a positive-type cone" test is: minimize W over the
# positive-type g-cone.  A finite proxy: take a basis of positive-type g's (widths)
# and combine with nonneg coefficients c_w >= 0 (cone), W(sum c_w g_w) = sum c_w W(g_w).
# A nonneg combination is >=0 iff EVERY basis value W(g_w) >= 0 (since coeffs>=0).
# So min over the cone = min_w W(g_w) (taking the single worst width, coeff 1).
# Hence the cone-positivity indicator is  min_w W(alpha,a,g_w).
# This is the correct "min over positive-type g basis" the mission asks for.
# ----------------------------------------------------------------------------

WIDTHS = [0.5, 0.8, 1.2, 1.8, 2.6, 3.6, 5.0]

def W_minbasis(alpha, a, gammas, etas, widths=WIDTHS):
    vals = [W_scalar(alpha, a, gammas, etas, w) for w in widths]
    return min(vals), vals

if __name__ == "__main__":
    print("="*88)
    print("VALIDATION: closed-form I vs truncated mpmath integral (must agree for w<<T)")
    print("="*88)
    T = 12.0
    for (eta,w,beta) in [(0.15,1.2,30.0),(0.2,2.0,5.0),(0.15,0.8,100.0),(0.3,1.5,0.0)]:
        c = I_closed(eta,w,beta); t = I_trunc(eta,w,beta,T)
        print(f"  eta={eta} w={w} beta={beta:6.1f}:  closed={c:+.6e}  trunc={t:+.6e}  rel.err={abs(c-t)/(abs(t)+1e-30):.2e}")

    print("\n  (alpha=0 sanity: beta=0 => I = w sqrt(2pi)(exp(w^2 eta^2/2)-1) > 0, the ENVELOPE)")
    for w in WIDTHS:
        print(f"    w={w:4.1f}: I(eta=.15,beta=0)={I_closed(0.15,w,0.0):+.4e}")

    print("\n"+"="*88)
    print("PHASE DIAGRAM: sign of min_w W(alpha,a) over (alpha,a) grid, adversary population")
    print("="*88)
    gammas, etas = fake_population("adversary", n=40)
    NA, NW = 41, 41
    alphas = np.linspace(0.0, 1.0, NA)
    # Damping must reach gamma_eff ~ 1/(alpha*w_max) at the gate; for the gate to be visible
    # across alpha in [0,1] with gamma down to 10 we need a up to ~ (ln scale)/10^2.  Use a
    # LOG grid in the *effective cutoff* so the alpha^2 boundary curve a0(alpha) is visible.
    # gamma_min=10 => a that damps gamma_min is a~ (a few)/100.  Sweep a in [0, 0.05] on the
    # damped axis AND show the boundary curve a0(alpha)=(alpha*w_max/0.987)^2/gamma_scaling.
    a_max = 0.05
    avals  = np.linspace(0.0, a_max, NW)

    sign = np.zeros((NW, NA))
    Wmin = np.zeros((NW, NA))
    for i,a in enumerate(avals):
        for j,al in enumerate(alphas):
            m,_ = W_minbasis(al, a, gammas, etas)
            Wmin[i,j] = m
            sign[i,j] = 1.0 if m >= 0 else -1.0
    np.save("osc_Wmin.npy", Wmin)
    np.save("osc_alphas.npy", alphas)
    np.save("osc_avals.npy", avals)

    # ASCII map: rows = a (top a_max -> bottom 0), cols = alpha (0 -> 1)
    print(f"  grid: alpha in [0,1] (cols, 0=envelope -> 1=Weil), a in [0,{a_max}] (rows, top=a_max)")
    print("  '+' = W>=0 (POSITIVE/safe),  '.' = W<0 (positivity DEAD)")
    print("  alpha:     0" + " "*(NA-6) + "1")
    for i in range(NW-1, -1, -1):
        row = "".join("+" if sign[i,j] >= 0 else "." for j in range(NA))
        print(f"  a={avals[i]:.4f} {row}")

    # boundary curve a0(alpha): largest a where it is still positive going up? Actually
    # find for each alpha the threshold a where sign flips (positivity dies as a DECREASES).
    print("\n  OBSTRUCTION BOUNDARY a0(alpha): smallest a that is still POSITIVE")
    print("  (a >= a0 => safe; a < a0 => positivity dead).  '---' = positive for all a (incl 0).")
    print(f"  {'alpha':>8} {'a0(alpha)':>12} {'W(alpha,0)':>14}")
    for j in range(NA):
        col = sign[:,j]   # avals increasing
        # find smallest a index that is positive AND all above positive
        a0 = None
        for i in range(NW):
            if col[i] >= 0 and all(col[i:] >= 0):
                a0 = avals[i]; break
        w0 = Wmin[0,j]
        a0s = f"{a0:.5f}" if a0 is not None and a0 > 0 else ("---" if (a0==0.0) else "NEVER")
        if j % 4 == 0 or j==NA-1:
            print(f"  {alphas[j]:8.3f} {a0s:>12} {w0:+14.5e}")

    # connectivity test: is there a positive path from (0,a_max) to (1,0)?
    print("\n  CONNECTIVITY: positive at (0,a_max)? ", sign[-1,0] >= 0,
          " | positive at (1,0)? ", sign[0,-1] >= 0)
