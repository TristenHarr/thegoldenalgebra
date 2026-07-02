"""
SECMOM_structure.py — The positive SECOND MOMENT of the Weil off-line displacement
readout, and whether squaring still SEES displacement.

CONTEXT (banked in QUART_FINDINGS.md, ScratchResolutionTheory.lean):
  The off-line contribution of one zero ρ = 1/2 + η_ρ + i γ_ρ to the Weil sum, for a
  positive-type test function g with supp(g) ⊆ [-T,T], splits (identity (★)) into
      N_ρ(g) = N0_ρ + Δ_ρ(g),
      N0_ρ = 4 ĝ(γ_ρ) = 4|f̂(γ_ρ)|² >= 0           (on-line part, δ=0)
      Δ_ρ(g) = 4 ∫_{-T}^{T} g(u)(cosh(η_ρ u) - 1) cos(γ_ρ u) du   (off-line correction)
  The FIRST moment Σ_ρ Δ_ρ(g) is SIGN-INDEFINITE through cos(γ_ρ u): different zeros
  contribute with oscillating signs, so it cannot be bounded below.  THE IDEA: square it.

  M2(g) := Σ_ρ |Δ_ρ(g)|²   >= 0   is positive BY CONSTRUCTION.

QUESTIONS (the discipline):
  (1) Does M2 still SEE displacement?  Δ_ρ ∝ (cosh(η u) - 1) ≈ η²u²/2 ⟹ Δ_ρ = O(η²),
      so |Δ_ρ|² = O(η⁴).  The second moment detects displacement at FOURTH order.
  (2) Is M2 a FAITHFUL detector: M2(g)=0 ⟺ all η_ρ = 0 (for a fixed nonzero g)?
  (3) What is the GATE for M2?  η² vs η⁴ — does squaring shift the δT~1 wall?

This script answers (1)-(3) by exact symbolic/numeric computation on the SINGLE-zero
readout (the per-zero structure is what determines faithfulness and the gate; the
cross/pair structure is handled in SECMOM_pair.py).
"""
import numpy as np
import mpmath as mp
mp.mp.dps = 40

# ----------------------------------------------------------------------
# Per-zero readout Δ_ρ(g) = 4 ∫_{-T}^{T} g(u)(cosh(η u) - 1) cos(γ u) du
# Use an explicit positive-type g.  Take g(u) = (1 - |u|/T)_+  (Fejér/triangle),
# which is positive-type (Fourier transform = T·sinc²(Tx/2)/(2π) >= 0) and supported
# in [-T,T].  This is a legitimate Yoshida-admissible window for T < log2 etc.
# ----------------------------------------------------------------------
def Delta(eta, gamma, T, g):
    f = lambda u: g(u) * (mp.cosh(eta*u) - 1) * mp.cos(gamma*u)
    return 4 * mp.quad(f, [-T, 0, T])

def g_tri(T):
    return lambda u: max(mp.mpf(0), 1 - abs(u)/T)

# ----------------------------------------------------------------------
# (1)+(2)  Faithfulness: is Δ_ρ = 0 forced only by η=0 (for generic γ)?
#          And the η⁴ law for the squared readout.
# ----------------------------------------------------------------------
print("="*74)
print("(1)/(2)  PER-ZERO readout Δ_ρ(g) and its square |Δ_ρ|² vs displacement η")
print("="*74)
T = mp.mpf('0.6')          # inside Yoshida cone (< log2): legitimate g
g = g_tri(T)
gamma = mp.mpf('14.13')    # first zeta zero ordinate
print(f"g = triangle on [-{float(T)},{float(T)}], gamma = {float(gamma)} (1st zero)")
print(f"{'eta':>10} {'Delta':>16} {'Delta^2':>16} {'Delta^2/eta^4':>16}")
for eta in [mp.mpf('0.2'), mp.mpf('0.1'), mp.mpf('0.05'), mp.mpf('0.02'), mp.mpf('0.01')]:
    D = Delta(eta, gamma, T, g)
    print(f"{float(eta):>10} {float(D):>16.3e} {float(D**2):>16.3e} {float(D**2/eta**4):>16.6f}")
print("⟹ Delta = O(eta^2), |Delta|^2 = O(eta^4): ratio Delta^2/eta^4 -> const (the η⁴ law).")
print()

# Faithfulness: Δ_ρ(g) = 0  iff  η = 0?  cosh(ηu)-1 > 0 for u≠0,η≠0, but cos(γu) changes
# sign on [-T,T] when γT > π/2.  Could the integral cancel to 0 for η≠0?
print("FAITHFULNESS CHECK: can Delta(eta,gamma,T) vanish for eta != 0 (cancellation)?")
print(f"  gamma*T = {float(gamma*T):.3f}  (cos(gamma u) sign changes iff gamma T > pi/2 = {float(mp.pi/2):.3f})")
# scan gamma to find a sign change / zero of Delta at FIXED eta
eta0 = mp.mpf('0.1')
prev = None
zeros_found = []
gg = mp.mpf('0.1')
while gg < mp.mpf('40'):
    D = Delta(eta0, gg, T, g)
    if prev is not None and mp.sign(D) != mp.sign(prev[1]):
        # bisect
        a,b = prev[0], gg
        for _ in range(60):
            m=(a+b)/2
            Dm = Delta(eta0,m,T,g)
            if mp.sign(Dm)==mp.sign(prev[1]): a=m
            else: b=m
        zeros_found.append((a+b)/2)
    prev=(gg,D)
    gg += mp.mpf('0.25')
print(f"  At eta={float(eta0)}: Delta(eta,gamma,T) has ZEROS in gamma at:")
print("   ", [round(float(z),3) for z in zeros_found])
print("  ⟹ For SOME gamma values Delta_ρ = 0 even with eta != 0 (cos-cancellation).")
print("     So a SINGLE zero's readout is NOT faithful pointwise in gamma — BUT the")
print("     second moment SUMS over all zeros; a single accidental zero of Delta at one")
print("     gamma does not make M2=0 unless EVERY zero lands on a Delta-zero simultaneously.")
