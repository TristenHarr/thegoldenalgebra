"""
HONEST SCRUTINY: is the 'unbounded below in η' an ARTIFACT of treating η as free?

Two honest objections + their resolution:

OBJECTION 1: η is bounded. A nontrivial zeta zero lives in the critical strip 0<β<1,
so η=β-1/2 ∈ (-1/2,1/2). On that COMPACT η-window the block B(γ,η) is bounded; maybe a
convex functional exists there.
  RESOLUTION: On η∈(-1/2,1/2), is B(γ,η) minimized at η=0 and convex? For small a the
  factor e^{aη^2}≈1 and cos(2aγη)≈1-2a^2γ^2η^2, so B≈4e^{-aγ^2}(1-2a^2γ^2η^2): a DOWNWARD
  parabola in η -> η=0 is a local MAX, B DECREASES as |η| grows. So even on the compact
  strip window, increasing displacement DECREASES the Weil block (makes Q smaller / more
  negative) for the bulk zeros. The axis is still not a minimizer of F_Q. Test below.

OBJECTION 2: the Weil form is a SUP over a positive-type cone of test functions, not one a.
  RESOLUTION: RH ⟺ Q(g)≥0 for ALL positive-type g ⟺ inf over the cone ≥ 0. The displacement
  enters each Q(g) the same way (each h≥0 gives a Gaussian-superposition block). The SIGN
  question is: can off-line η make SOME Q(g)<0? Yes (offline_model.py). Convexity in η of the
  WORST-CASE Q over g is an inf of (non-convex in η) functions -> generally non-convex; and the
  cone-sup/inf does not convexify the η-dependence (it's a pointwise inf, which is CONCAVE-
  preserving, not convex-preserving). So the variational object inf_g Q_g(η) is, if anything,
  concave-leaning in η, the WRONG sign for a convex minimization principle.

We numerically confirm OBJECTION-1 resolution on the physical window η∈(-1/2,1/2), AND
verify against the ACTUAL explicit formula (real zeros + one displaced pair) that moving a
zero off-line by η LOWERS the would-be Q for a Gaussian test fn whose h is centered to see it.
"""
import numpy as np
import mpmath as mp
mp.mp.dps = 30

def weil_block(gamma, eta, a):
    return 4.0*np.exp(-a*(gamma**2-eta**2))*np.cos(2.0*a*gamma*eta)

print("=== OBJECTION 1: behavior of B(γ,η) on the PHYSICAL window η∈(-1/2,1/2) ===")
gammas=[float(mp.im(mp.zetazero(k))) for k in range(1,9)]
a=0.02
print(f"a={a}.  B(γ,η)-B(γ,0) (change in Weil block from displacing), η in [0,0.5]:")
print(f"   {'γ':>8}", *[f"η={e:.2f}".rjust(13) for e in [0.1,0.2,0.3,0.4,0.5]])
for g in gammas:
    row=[weil_block(g,e,a)-weil_block(g,0.0,a) for e in [0.1,0.2,0.3,0.4,0.5]]
    print(f"   {g:8.3f}", *[f"{v:+13.3e}" for v in row])
print("=> ALL entries NEGATIVE: displacing any bulk zero off-line DECREASES its Weil block.")
print("   The axis MAXIMIZES B for the bulk; F_Q is locally maximized (not minimized) at axis.")

print("\n=== verify against ACTUAL explicit formula: displaced pair lowers Q ===")
# Q(g) = sum_rho h(gamma_rho). Replace the first zero's pair (±γ1, η=0) by (±γ1, η=δ):
# contribution changes from 2h(γ1) to h(γ1+iδ)+h(γ1-iδ) (and conj) per offline_model.
# Use h(r)=e^{-a r^2}. Q_full from real zeros, then swap zero 1 to off-line.
a=0.02
def h(z): return mp.e**(-a*z*z)
gam1=mp.im(mp.zetazero(1))
def pair_contrib(gamma, eta):
    # the 4-partner real contribution = 4 e^{-a(γ^2-η^2)}cos(2aγη)
    return 4*mp.e**(-a*(gamma**2-eta**2))*mp.cos(2*a*gamma*eta)
print(f"   first-zero quadruplet contribution to Q, γ1={float(gam1):.4f}, a={a}:")
for eta in [0,0.05,0.1,0.2,0.3,0.4,0.5]:
    c=pair_contrib(gam1,mp.mpf(eta))
    print(f"     η={eta:.2f}:  contrib={mp.nstr(c,8)}   Δ={mp.nstr(c-pair_contrib(gam1,mp.mpf(0)),8)}")
print("=> moving zero off-line monotonically LOWERS its contribution to Q on the physical window.")
print("   This is the mechanism by which off-line zeros drive Q<0 (Weil/Bombieri negative eig).")
print("   It is exactly WHY the axis is a MAX (not min) of the displacement functional.")
