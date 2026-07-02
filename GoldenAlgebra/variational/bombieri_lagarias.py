"""
THE STRONGEST CANDIDATE: the Bombieri–Lagarias functional (the basis of Li's criterion).

BL general lemma: for a multiset of complex numbers {ρ} (closed under conjugation, in a
suitable convergence class), with the Li-type sums
   λ_n = Σ_ρ [ 1 − (1 − 1/ρ)^n ],
RH-type statement: Re ρ ≥ 1/2 for all ρ  ⟺  λ_n ≥ 0 for all n ≥ 1  (and a weighted version).
This IS a "positivity by a family of linear functionals" criterion. The per-zero kernel is
   k_n(ρ) = 1 − (1 − 1/ρ)^n.
Equivalently with w = 1 − 1/ρ:  Re ρ ≥ 1/2 ⟺ |w| ≤ 1 (the zero is inside/on the unit disk
under the Möbius map ρ ↦ 1−1/ρ sending the line Re=1/2 to the unit circle, Re>1/2 to |w|<1).

THE TRANSPORT / CONVEXITY READING. Map each zero by the Möbius transform
   Φ(ρ) = 1 − 1/ρ.   Re ρ = 1/2  ↦  |Φ(ρ)| = 1  (unit circle);  Re ρ > 1/2 ↦ |Φ|<1.
So RH ⟺ ALL transformed zeros land ON the unit circle |w|=1; off-line (Re>1/2) ⟺ INSIDE.
[For zeros with Re<1/2, |w|>1; conjugate symmetry pairs Re>1/2 and Re<1/2.]

CANDIDATE CONVEX FUNCTIONAL in this chart:
   G(μ) = Σ_ρ ( |Φ(ρ)|^2 − 1 )       (a "radius defect" energy in the disk chart)
or its log version Σ -log|Φ(ρ)|. RH ⟺ all on circle. Question: is the on-circle (axis)
configuration the MINIMIZER of a CONVEX functional of the displacement η?

WE TEST: parametrize ρ = 1/2 + η + iγ, compute |Φ(ρ)|^2 as a function of η at fixed γ,
and check convexity + which η extremizes it.
"""
import numpy as np
import mpmath as mp
mp.mp.dps=30

def Phi(rho):
    return 1 - 1/rho

def absPhi2(eta, gamma):
    rho = complex(0.5+eta, gamma)
    w = 1-1/rho
    return abs(w)**2

print("=== |Φ(ρ)|^2 as a function of displacement η, ρ=1/2+η+iγ ===")
print("RH (on line) is η=0 -> |Φ|^2 = 1 EXACTLY (unit circle). Test convexity & extremum:")
for gamma in [14.135, 30.0, 5.0, 1.0]:
    print(f"\n  γ={gamma}:")
    print(f"   {'η':>8} {'|Φ|^2':>14} {'|Φ|^2-1':>14}")
    for eta in [-0.4,-0.2,-0.1,0.0,0.1,0.2,0.4]:
        v=absPhi2(eta,gamma)
        print(f"   {eta:8.2f} {v:14.8f} {v-1:+14.3e}")

print("\n=== sign of |Φ|^2-1: which side of the axis? ===")
# Re ρ>1/2 (η>0) -> |Φ|<1 -> |Φ|^2-1<0 ; η<0 -> >0. So |Φ|^2-1 is ODD-ish in η near 0:
# it CHANGES SIGN at η=0. => η=0 is NOT a min of |Φ|^2-1 (it's a sign-change / inflection).
# The radius defect is monotone DECREASING in η (not a convex well). CONFIRM derivative:
print("  d/dη |Φ(1/2+η+iγ)|^2 at η=0:")
for gamma in [14.135,30.0,5.0,1.0]:
    f=lambda e: absPhi2(e,gamma)
    d=(f(1e-6)-f(-1e-6))/2e-6
    d2=(f(1e-4)-2*f(0)+f(-1e-4))/1e-8
    print(f"   γ={gamma:7.2f}: f'(0)={d:+.5e}  f''(0)={d2:+.5e}  "
          f"({'min' if d2>0 and abs(d)<1e-6 else 'NOT a min (f≠0 or concave)'})")

print("""
=> |Φ|^2 has NONZERO slope f'(0)≠0 at η=0: the axis is NOT a critical point of the radius
   defect, let alone a minimum. |Φ|^2-1 changes sign through η=0 (Re>1/2 inside disk,
   Re<1/2 outside). The BL/Li positivity is a HALF-SPACE (one-sided) condition Re ρ≥1/2,
   i.e. |Φ|≤1, NOT a 'distance-to-axis = 0' minimization. Its natural functional is the
   one-sided λ_n≥0 (a CONE/positivity condition), which is the SAME indefinite-cone object
   as Weil — not a convex well with the axis at the bottom.""")

# The Li sum itself: λ_n = Σ_ρ (1-(1-1/ρ)^n). For a single conj pair off-line, is λ_n
# convex in η and minimized at η=0? λ_n for a pair {1/2+η±iγ}:
def lambda_n_pair(n, eta, gamma):
    s=0
    for sgn in (1,-1):
        rho=complex(0.5+eta, sgn*gamma)
        s+= 1-(1-1/rho)**n
    return s.real
print("\n=== Li λ_n of a single conjugate pair vs η (n=1,5,20) ===")
for n in [1,5,20]:
    print(f"  n={n}: ", end="")
    row=[(eta, lambda_n_pair(n,eta,14.135)) for eta in [-0.4,-0.2,0.0,0.2,0.4]]
    print("  ".join(f"η={e:+.1f}:{v:+.3e}" for e,v in row))
print("""  -> λ_n(η) is NOT a convex well at η=0; for off-line η>0 it can stay positive (BL: the
     positivity is about Re ρ≥1/2, satisfied on a HALF-LINE η≥0, not pinned at η=0).
     Li/BL positivity is a one-sided CONE condition, structurally the same indefinite-cone
     wall as Weil — there is no convex functional with the axis as a strict unique minimum.""")
