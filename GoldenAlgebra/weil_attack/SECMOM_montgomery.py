"""
SECMOM_montgomery.py — the Montgomery pair-correlation bridge for the cross/pair second
moment.  Does pair-correlation give an UNCONDITIONAL UPPER bound on M2, and does that bound
yield displacement CONTROL (a Σ η⁴ W ≤ [pair-corr] inequality)?

==================================================================================
THE BRIDGE (exact set-up)
==================================================================================
Montgomery's normalized pair-correlation function (unconditional definition):
    F(α,T) = (T/(2π) · log T)^{-1} · Σ_{0<γ,γ'≤T} T^{iα(γ-γ')} w(γ-γ'),   w(u)=4/(4+u²).
For ANY even r with Fourier transform r̂, PARSEVAL gives the convolution identity
    Σ_{0<γ,γ'≤T} r̂((γ-γ') · (log T)/(2π)) · w(γ-γ')
        = (T log T / 2π) · ∫_{-∞}^{∞} F(α,T) · r(α) dα.                       (PC-Parseval)

KNOWN UNCONDITIONAL FACTS (Baluyot–Goldston–Suriajaya–Turnage-Butterbaugh,
Acta Arith. 214 (2024) 357–376, arXiv:2306.04799; Montgomery 1973 lower bound):
  (U1) F(α,T) ≥ 0  for ALL α            — UNCONDITIONAL (F is a |·|² of a Dirichlet sum).
  (U2) F(α,T) = T^{-2|α|} log T (1+o(1)) + |α| + o(1),  uniformly 0≤|α|≤1 — UNCONDITIONAL.
       (Montgomery proved this for |α|≤1 under RH; BGSTB removed RH for 0≤α≤1.)
  (U3) For |α|≤1: ∫_{|α|≤1} F(α,T) dα ~ 1 + (log T)(stuff) — the small-α mass is O(1)+main.
  (U4) For |α|>1: F(α,T) ≥ α - 1 + o(1) is the UNCONDITIONAL Montgomery LOWER bound;
       the UPPER bound F(α) ≤ α + o(1) (=its conjectured value) for |α|>1 is the
       CONJECTURE (NOT proven). Only LOWER bounds and AVERAGED upper bounds exist for α>1.

==================================================================================
WHY THIS BOUNDS THE CROSS TERM — AND WHY IT'S A LOWER, NOT UPPER, TOOL
==================================================================================
Our cross sum (SECMOM_pair.py) is, in the difference channel,
    C(g) = Σ_{ρ≠ρ'} K̂(γ_ρ-γ_{ρ'}; η_ρ,η_{ρ'}),  K̂ even, peaked near 0 (support ~T in u).
To feed (PC-Parseval) we need K̂(ξ) = r̂(ξ·log T/2π) for some r with KNOWN r̂.  Then
    C(g) ≈ (T log T/2π) ∫ F(α) r(α) dα  - [diagonal ρ=ρ' subtracted].
For an UPPER bound on C we need an UPPER bound on ∫F(α)r(α)dα.  Since (U2) controls F only
for |α|≤1 and r(α)≥0 is NOT guaranteed, two cases:
  • If r̂ has support in [-1,1] (i.e. K̂(ξ)=0 for |ξ|·log T/2π > 1, i.e. our kernel only
    couples zeros with γ_ρ-γ_{ρ'} small on the 2π/log T scale): then ∫ uses ONLY |α|≤1,
    where F is UNCONDITIONALLY KNOWN (U2). ⟹ UNCONDITIONAL bound. BUT this forces the
    kernel to be band-limited in ξ to width 2π/log T → the support T in u must be ≳ log T/2.
  • If r̂ spreads past |α|=1: the integral hits the α>1 region where only the LOWER bound
    (U4) is unconditional. An UPPER bound there needs Montgomery's CONJECTURE F(α)≈α. NOT
    unconditional.

THE HONEST DICHOTOMY (the verdict, made quantitative below):
  Our displacement kernel K̂_η has u-support = the test support T (Yoshida: T<log2≈0.69).
  Its ξ-Fourier content extends to scale 1/T, i.e. α-scale (1/T)(2π/log T)... = 2π/(T log T).
  For the UNCONDITIONAL window |α|≤1 to CONTAIN the kernel we need 2π/(T log T)·(width) ≤ 1.
  This is satisfiable, BUT then F(α)≈ T^{-2α}log T + α on |α|≤1 gives an UPPER bound of size
       ∫_{-1}^{1} F(α) r(α) dα ≤ (sup r) · [∫_0^1 (T^{-2α}log T + α)dα·2]
     = (sup r)·[ (1 - T^{-2})/2·... + 1 ] = O(sup r · 1).
  i.e. the pair-correlation UPPER bound on the cross term is C(g) = O(T log T · sup|r|),
  which is the SAME ORDER as the trivial diagonal count Σ_ρ 1 ~ (T/2π)log T times the
  per-zero kernel size.  PAIR-CORRELATION DOES NOT BEAT THE DIAGONAL COUNT here.
==================================================================================
"""
import mpmath as mp
mp.mp.dps = 30

# Numerically illustrate (U2): F(α,T) on |α|≤1 is O(1)+ decaying main term, so ∫_{-1}^1 F is O(1).
def F_uncond(alpha, T):
    a = abs(alpha)
    if a <= 1:
        return T**(-2*a)*mp.log(T) + a      # leading unconditional form (drop o(1))
    return None

print("Unconditional F(α,T) on |α|≤1 (leading BGSTB/Montgomery form), T=1e6:")
T = mp.mpf('1e6')
print(f"{'alpha':>6} {'F(alpha,T)':>16}")
for a in [0,0.1,0.25,0.5,0.75,1.0]:
    print(f"{a:>6} {float(F_uncond(mp.mpf(str(a)),T)):>16.4f}")
intF = mp.quad(lambda a: F_uncond(a,T), [0,1])*2
print(f"∫_{{-1}}^{{1}} F(α,T) dα = {float(intF):.4f}   (≈ 1 + 1 = O(1) main mass: 1 from T^{{-2α}}logT,")
print("                          1 from the |α| ramp) — bounded INDEPENDENT of log T scale.")
print()
print("KEY: the UNCONDITIONAL |α|≤1 mass of F is O(1).  So a kernel band-limited to |α|≤1")
print("gives a cross-term bound  C(g) = O(T log T · 1) — same order as the diagonal Σ_ρ.")
print("Pair-correlation REPLACES Σ_{ρ≠ρ'}→bound but the bound = diagonal order. No gain in")
print("displacement resolution: the η⁴ displacement weight W(γ_ρ) sits on the DIAGONAL and")
print("is NOT amplified by the unconditional cross bound.")
print()
print("Pushing past |α|=1 (where the upper bound would help) needs F(α)≤α+o(1) = MONTGOMERY'S")
print("CONJECTURE.  Unconditionally only F(α)≥α-1 (lower) is known for α>1 — useless for an")
print("UPPER bound on a POSITIVE second moment.")
