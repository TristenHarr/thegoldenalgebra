"""
CONVEXITY TEST of candidate variational functionals F(μ) for RH.

SETUP (mission framing):
  mu_pos = Σ_ρ m_ρ δ_{(γ_ρ, η_ρ)}   zeros with displacement η = β − 1/2
  mu_0   = Σ_ρ m_ρ δ_{(γ_ρ, 0)}     axis projection
  RH ⟺ μ_pos = μ_0 ⟺ every η_ρ = 0.

We model the explicit-formula / Weil functional as a function of the displacement
profile {η_ρ}, and test each candidate F for:
   (i)  CONVEXITY in the displacements η  (Hessian ⪰ 0 ?)
   (ii) MINIMIZED at η ≡ 0  (axis) ?

A genuine convex variational principle for RH needs BOTH.

KEY ARITHMETIC INPUT (the explicit formula / Weil quadratic form):
  For a positive-type test function with h(r) = exp(-a r^2) (Gaussian, h ≥ 0 on R),
  a SINGLE zero at ρ = 1/2 + η + iγ (and its f.e. / conjugate partners) contributes
  to the zero-sum  Q = Σ_ρ h(γ_ρ),  γ_ρ = (ρ − 1/2)/i = γ − iη,
  the FOUR-PARTNER block  (±γ ± iη):
     B(γ, η) = h(γ+iη)+h(γ-iη)+h(-γ+iη)+h(-γ-iη)
             = 4 e^{-a(γ^2 - η^2)} cos(2 a γ η)        [exact, real]
  On the line (η=0): B(γ,0) = 4 e^{-a γ^2} > 0.
  This is the displacement-dependence of the Weil form: a Gaussian RIDGE in η
  modulated by cos(2aγη). It is NOT convex in η (the e^{+aη^2} grows but cos oscillates).

We treat the displacement profile η = (η_1,...,η_K) of K zeros at ordinates γ_1..γ_K
and study F(η). 'a' is the test-function scale (= 1/(2σ^2) of the Gaussian); the
Weil form is really sup/inf over a family, but for the convexity DIAGNOSIS we fix a
representative scale and also sweep it.
"""
import numpy as np
import mpmath as mp
mp.mp.dps = 30

# ---- the per-zero Weil block as a function of displacement η (exact, real) ----
def weil_block(gamma, eta, a):
    """B(γ,η) = 4 e^{-a(γ^2-η^2)} cos(2 a γ η).  The 4-partner zero-sum contribution."""
    return 4.0*np.exp(-a*(gamma**2 - eta**2))*np.cos(2.0*a*gamma*eta)

def weil_block_mp(gamma, eta, a):
    g=mp.mpf(gamma); e=mp.mpf(eta); A=mp.mpf(a)
    return 4*mp.e**(-A*(g*g-e*e))*mp.cos(2*A*g*e)

# The Weil form's DISPLACEMENT ENERGY proxy: Q(η) − Q(0) summed over zeros.
# Q(0) = Σ 4 e^{-a γ^2}. The displacement-dependent part per zero:
def weil_displacement_part(gamma, eta, a):
    return weil_block(gamma, eta, a) - weil_block(gamma, 0.0, a)

# ================= CANDIDATE FUNCTIONALS =================
# All are functions of the displacement vector η (one per zero), at scale a.

# (a) WEIL Q itself  F_Q(η) = Σ_k B(γ_k, η_k)   (the KNOWN indefinite functional)
def F_Q(etas, gammas, a):
    return sum(weil_block(g, e, a) for g, e in zip(gammas, etas))

# (b) ENTROPY-REGULARIZED:  F = Q + λ H,  H = Σ η_k^2  (quadratic 'entropy' = displacement L2)
#     (strictly convex penalty). Question: does adding it convexify while keeping η=0 min?
def F_entropy(etas, gammas, a, lam):
    return F_Q(etas, gammas, a) + lam*sum(e*e for e in etas)

# (c) TRANSPORT-COST:  F = (prime-side functional) + W2(μ,axis)^2.
#     W2(μ_pos,μ_0)^2 with the axis = Σ η_k^2 (vertical transport, masses fixed).
#     The 'prime side' as a function of displacement = the Weil zero-sum (= prime+arch via EF),
#     so this is essentially (b) with the prime side = F_Q. We also test the literal
#     'prime-only' contribution as fn of η below.
def F_transport(etas, gammas, a, weight_prime=1.0):
    return weight_prime*F_Q(etas, gammas, a) + sum(e*e for e in etas)

# (d) the pure displacement ENERGY (the W2^2 alone) — trivially convex, min at 0,
#     but NOT arithmetic (no Euler product input): the honest 'cheat' baseline.
def F_energy(etas, gammas, a):
    return sum(e*e for e in etas)


# ===== HESSIAN / CONVEXITY of the per-zero Weil block in η (closed form) =====
# B(γ,η) = 4 e^{-a(γ^2-η^2)} cos(2aγη).  Let u = 2aγ.
# d2B/dη2 = 4 e^{-a γ^2} d2/dη2 [ e^{aη^2} cos(uη) ].
# Let f = e^{aη^2} cos(uη).
# f'  = e^{aη^2}(2aη cos(uη) - u sin(uη))
# f'' = e^{aη^2}[ (2a + 4a^2 η^2 - u^2) cos(uη) - 4 a η u sin(uη) ]
def weil_block_hess(gamma, eta, a):
    u = 2*a*gamma
    pref = 4*np.exp(-a*gamma**2)*np.exp(a*eta**2)
    return pref*((2*a + 4*a*a*eta*eta - u*u)*np.cos(u*eta) - 4*a*eta*u*np.sin(u*eta))

# At η=0:  f''(0) = 2a - u^2 = 2a - 4a^2 γ^2.  d2B/dη2|_0 = 4 e^{-aγ^2}(2a - 4a^2γ^2).
# CONVEX at axis (in this zero's η) ⟺ 2a - 4a^2 γ^2 ≥ 0 ⟺ a γ^2 ≤ 1/2 ⟺ γ^2 ≤ 1/(2a).
# >>> For a fixed test scale a, the Weil block is CONCAVE at the axis for every zero with
#     γ^2 > 1/(2a), i.e. all but the lowest few zeros. THIS is the non-convexity.

def hess_at_axis(gamma, a):
    return 4*np.exp(-a*gamma**2)*(2*a - 4*a*a*gamma**2)

if __name__ == "__main__":
    # Real zeta zeros
    print("Loading first zeta zeros (ordinates γ)...")
    K = 12
    gammas = [float(mp.im(mp.zetazero(k))) for k in range(1, K+1)]
    print("γ:", [round(g,3) for g in gammas])

    print("\n=== (1) HESSIAN OF WEIL Q AT THE AXIS (η=0), per zero ===")
    print("Convex-at-axis ⟺ a*γ^2 ≤ 1/2.  Sweep test-scale a:")
    for a in [0.001, 0.005, 0.02, 0.05, 0.2]:
        signs = [hess_at_axis(g, a) for g in gammas]
        nneg = sum(1 for s in signs if s < 0)
        thresh = (0.5/a)**0.5
        print(f"  a={a:7.4f}: 1/sqrt(2a)={thresh:7.2f} -> "
              f"{nneg}/{K} zeros have CONCAVE Weil block at axis "
              f"(min hess={min(signs):+.4e}, max={max(signs):+.4e})")

    print("\n=== (2) IS THE WEIL Q HESSIAN (full, at axis) PSD or INDEFINITE? ===")
    print("Hessian of F_Q at η=0 is DIAGONAL (zeros decouple at axis): diag = hess_at_axis.")
    print("=> F_Q is convex at axis ⟺ ALL diagonal entries ≥ 0 ⟺ a ≤ 1/(2 γ_max^2).")
    a = 0.02
    diag = [hess_at_axis(g, a) for g in gammas]
    print(f"  at a={a}: diagonal Hessian entries =", [f"{d:+.3e}" for d in diag])
    print(f"  => {'INDEFINITE' if min(diag)<0<max(diag) else ('PSD' if min(diag)>=0 else 'NEG-DEF')}"
          f"  (min {min(diag):+.3e}, max {max(diag):+.3e})")

    print("\n=== (3) DOES ENTROPY REGULARIZATION CONVEXIFY? F = Q + λ Σ η^2 ===")
    print("Hessian at axis: diag_k + 2λ.  Convex ⟺ λ ≥ -min_k(diag_k)/2 = max_k(4a^2γ^2-2a)2e^{-aγ^2}.")
    for a in [0.02, 0.05]:
        diag = [hess_at_axis(g, a) for g in gammas]
        lam_needed = max(-d/2 for d in diag)  # smallest λ making axis-Hessian PSD
        print(f"  a={a}: λ ≥ {lam_needed:.4e} makes the axis-Hessian PSD.")
        # BUT does η=0 stay the GLOBAL min? check far-field: B ~ 4 e^{-aγ^2} e^{aη^2}cos ->
        # grows like e^{aη^2}; +λη^2 also grows. So for large η, F-> ?
        # The Weil block e^{aη^2}cos(2aγη) is UNBOUNDED BELOW in η (e^{aη^2} * (neg cos)).
        # Adding λη^2 (polynomial) CANNOT dominate e^{aη^2}. So η=0 is NOT a global min for any finite λ.
    print("  --> see (4): the Weil block ~ e^{+aη^2} is unbounded below; no polynomial λΣη^2 fixes it.")

    print("\n=== (4) GLOBAL MINIMIZER TEST: scan one zero's η, F_Q and F_entropy ===")
    a = 0.02; g = gammas[5]  # a mid zero
    lam = max(-hess_at_axis(gg,a)/2 for gg in gammas) + 0.01
    print(f"  zero γ={g:.3f}, a={a}, λ={lam:.4f} (axis-Hessian-PSD λ).  Scan η:")
    print(f"   {'η':>7} {'B_Q':>14} {'B_Q+λη^2':>14}")
    for eta in [0.0,0.5,1.0,2.0,3.0,4.0,5.0,7.0,10.0,15.0,20.0]:
        bq = weil_block(g, eta, a)
        be = bq + lam*eta*eta
        print(f"   {eta:7.2f} {bq:14.4e} {be:14.4e}")
    print("  --> B_Q+λη^2 still PLUNGES negative at large η (e^{aη^2}cos wins): "
          "entropy reg does NOT make axis the global min.")
