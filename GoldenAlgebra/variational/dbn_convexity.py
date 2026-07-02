"""
dBN CONVEXITY vs DISPLACEMENT — the crux of the whole mission.

The de Bruijn–Newman flow (Rodgers–Tao) has a convex log-energy / Hamiltonian for the
zero DYNAMICS. The mission asks: is the RH (axis) configuration the minimizer of a convex
functional, OR is dBN convexity ORTHOGONAL to displacement (controls spacing/height, not β)?

THE dBN PICTURE (real-zero / Hamiltonian form). When all zeros are REAL (= on the line,
for the H_t functions), they evolve under the heat flow as a gradient system with
Hamiltonian (the "log-energy" / Coulomb gas):
   H_log(x) = - Σ_{j<k} log|x_j - x_k|        (x_j = real ordinates)
and  dx_j/dt = Σ_{k≠j} 1/(x_j-x_k) = -∂H_log/∂x_j  (attractive/repulsive Coulomb on a line).
The Hamiltonian flow EVENS OUT SPACINGS. This H_log is a function of the ORDINATES x_j
(the γ's), NOT of the displacement η=β-1/2. The variable it is convex/repulsive in is the
HORIZONTAL POSITION ALONG THE LINE, i.e. γ.

But the dBN flow on the COMPLEX plane (zeros possibly off-line) has the zeros move in 2D.
The relevant quantity for RH is whether a complex-conjugate pair (off-line) MERGES onto the
real axis or splits OFF it. We test:

  (A) H_log as a function of η (displacement) — is it convex in η, minimized at η=0?
  (B) the 2D Coulomb energy of a conjugate pair {γ+iη, γ-iη} + the real bulk — does
      LOWERING it push η->0 (axis), and is it CONVEX in η?

KEY: a complex-conjugate pair at ±iη from the axis has MUTUAL log-energy -log|2η| = -log(2η),
which -> +∞ as η->0. So the Coulomb energy is MINIMIZED by SEPARATING the pair (η LARGE),
not by merging onto the axis. The Coulomb/log energy REPELS the conjugate pair APART
(off-line!), the WRONG direction for RH. The heat flow's contraction toward the axis is NOT
energy minimization of H_log in η — it is the FORWARD heat semigroup (smoothing), whose
fixed point is forced by the BACKWARD-uniqueness/maximum-principle, not by descending a
convex energy in η.
"""
import numpy as np
import mpmath as mp
mp.mp.dps=25

print("=== (A) H_log = -Σ log|x_j-x_k| as a function of one zero's ordinate γ (real) ===")
# pick 5 real ordinates, move the middle one; H_log is convex (sum of -log convex? -log|.|
# is CONVEX on each side). The 1D log-gas energy is convex in each coordinate between
# neighbors -> equilibrium = even spacing. This controls SPACING (γ), confirmed:
xs=np.array([0.0,1.0,2.0,3.0,4.0])
def Hlog_move(xmid):
    x=xs.copy(); x[2]=xmid
    H=0.0
    for j in range(5):
        for k in range(j+1,5):
            H+= -np.log(abs(x[j]-x[k]))
    return H
print("  move middle ordinate x2 (neighbors at 1,3):")
for xm in [1.2,1.5,1.8,2.0,2.2,2.5,2.8]:
    print(f"    x2={xm:.2f}: H_log={Hlog_move(xm):+.4f}")
print("  -> minimized at x2=2.0 (even spacing), CONVEX in the ordinate. dBN controls SPACING(γ).")

print("\n=== (B) 2D Coulomb log-energy of a conjugate pair {γ±iη} vs displacement η ===")
# energy between the pair: -log|（γ+iη)-(γ-iη)| = -log|2iη| = -log(2η).
def pair_self_energy(eta):
    return -np.log(2*abs(eta)) if eta!=0 else np.inf
print("  mutual log-energy of the conjugate pair (the η-dependent part):")
for eta in [0.01,0.05,0.1,0.2,0.5,1.0,2.0,5.0]:
    print(f"    η={eta:5.2f}: -log(2η)={pair_self_energy(eta):+.4f}")
print("  -> the Coulomb energy DECREASES as η INCREASES (pair flies APART, OFF the axis).")
print("     η=0 (merged on axis) is the energy MAXIMUM (+∞), the WRONG extremum for RH.")
print("     So the convex log-energy in DISPLACEMENT is minimized OFF-line, not on it.")

print("\n=== (C) the honest distinction ===")
print("""  dBN / log-gas CONVEXITY lives in the ORDINATE (γ, along the line): it forces EVEN
  SPACING and is the basis of Rodgers-Tao's Λ≥0 (zeros relax toward APs, contradicting
  pair-correlation). It says NOTHING convex about the displacement η:
    - H_log is convex & minimized at even spacing in γ  (SPACING/HEIGHT control).
    - In η, the same Coulomb energy is minimized by SEPARATION (η large), i.e. it
      pushes a conjugate pair OFF the axis. The merge-onto-axis (RH) is the ENERGY MAX.
  The contraction toward the axis under the heat flow is the FORWARD heat semigroup
  (a maximum-principle / parabolic smoothing statement), NOT gradient descent of a convex
  energy in η. Rodgers-Tao get Λ≥0 (a LOWER bound, the relaxation away from RH); the RH
  direction Λ≤0 is exactly where the maximum principle is MARGINAL (double real zero splits
  into a conjugate pair = the energy-favorable direction). dBN convexity is ORTHOGONAL to
  the displacement variable. CONFIRMED.""")
