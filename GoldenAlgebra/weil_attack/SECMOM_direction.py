"""
SECMOM_direction.py — the DIRECTION audit. The mission asks: does bounding M2 ABOVE +
its positivity yield displacement control (a `Σ η⁴ W ≤ [pair-correlation]` bound)?

This script pins the logical direction, which is the crux of the verdict.

WHAT WE WANT FOR RH-PROGRESS:
   A LOWER bound on a displacement functional that FORCES η=0, i.e.
        (something computable, unconditional)  ≥  c · Σ_ρ η_ρ⁴ W(γ_ρ) ≥ 0
   with the LHS provably 0 (or small) ⟹ all η=0 ⟹ RH.  That needs an UPPER bound on
   Σ η⁴ W by a vanishing computable quantity.  M2_diag = Σ_ρ|Δ_ρ|² IS ≈ Σ η⁴ W, so we'd
   need an UPPER bound on M2_diag that is unconditionally small.  But M2_diag is built FROM
   the (unknown) η's — there is no independent handle forcing it small.  The explicit formula
   gives M2 in terms of PRIMES, but |Δ_ρ|² is a SQUARE, and the prime side of a squared
   readout is a double prime sum (a length-2 correlation), NOT sign-definite — squaring the
   readout squares the prime side too.

WHAT PAIR-CORRELATION ACTUALLY GIVES:
   An UPPER bound  Σ_{ρ,ρ'} K̂(γ-γ') ≤ B(T)  (B = O(T log T), unconditional on |α|≤1).
   Since every term of M2^cross is η_ρ²η_{ρ'}²·(oscillatory), an upper bound on the
   (η-independent) pair sum does NOT translate to Σ η⁴ W ≤ small: the η-weights are INSIDE
   the kernel, and an upper bound on a sum with sign-indefinite η-weighted terms cannot lower
   bound the diagonal positive part.  Concretely:
        M2_diag = M2^cross − (off-diagonal cross terms),
   and the off-diagonal terms are sign-indefinite, so an UPPER bound on M2^cross gives
        M2_diag ≤ M2^cross + |off-diag|  — an UPPER bound on the POSITIVE detector, i.e.
   it bounds Σ η⁴ W ABOVE by a NONZERO O(T log T) quantity.  That is the WRONG DIRECTION:
   it never forces Σ η⁴ W = 0.  An upper bound on a positive displacement detector is
   VACUOUS for RH (consistent with QUART_FINDINGS Task-3: positivity floor carries no info).

THE FATAL GAP (made explicit): to detect displacement you need the detector to be LARGE when
η≠0 and to have an unconditional SMALL CEILING — contradictory unless the ceiling itself
encodes η.  The first moment had a sign problem (can't lower-bound).  Squaring fixes the sign
(M2_diag ≥ 0) but converts the goal into needing a LOWER bound on M2_diag by something
computable-and-forced-small — which pair-correlation, an UPPER-bound tool, cannot supply.

CONCLUSION (verdict (a)+(c) of the mission):
  - Squaring does NOT lose the displacement signal (M2_diag ∝ Σ η⁴ W is faithful, SECMOM_pair).
  - But it lands in the WRONG inequality direction: RH needs Σ η⁴ W bounded ABOVE by 0;
    pair-correlation/large-sieve give UPPER bounds on M2 (a POSITIVE quantity), i.e. a
    nonzero CEILING, never a floor that forces η=0.
  - The only place pair-correlation gives a genuine UPPER bound is |α|≤1 (unconditional),
    where the bound is O(T log T) = diagonal order (no resolution gain). Beating it needs
    F(α)≈α for α>1 = Montgomery's CONJECTURE (RH-strength). Verdict (c).
  - And the gate is UNCHANGED (ηT~1) with a STEEPER η⁴ blindness (SECMOM_gate): below the
    gate the second moment is strictly WORSE than the first.

This is a clean NEGATIVE result: squaring + pair-correlation is NOT a new unconditional
displacement bound. It (i) keeps the signal but at η⁴, (ii) keeps the SAME δT~1 gate, and
(iii) reduces — for an UPPER bound — to the same O(T log T) diagonal density, needing
Montgomery's conjecture to do better.  No `Σ η⁴ W ≤ [vanishing]` bank.
"""
import mpmath as mp
mp.mp.dps = 30

# Numerical sanity: show an UPPER bound on M2 is consistent with arbitrary nonzero η on a
# FIXED short support — i.e. the ceiling does not force η→0.
def g_tri(T): return lambda u: max(mp.mpf(0),1-abs(u)/T)
def Delta(eta,gamma,T,g): return mp.quad(lambda u: 4*g(u)*(mp.cosh(eta*u)-1)*mp.cos(gamma*u),[-T,0,T])

T=mp.mpf('0.6'); g=g_tri(T)
zeros=[mp.mpf(str(x)) for x in [14.134725,21.022040,25.010858,30.424876,32.935062]]
print("Demonstration: M2_diag stays BELOW a fixed O(1) ceiling for a RANGE of η — the upper")
print("bound never forces η=0 (the ceiling is the wrong-direction obstruction):")
print(f"{'eta(all)':>10} {'M2_diag':>16} {'ceiling≈(#zeros)·max|Δ|²':>26}")
ceil = len(zeros)*float(Delta(mp.mpf('0.3'),zeros[0],T,g)**2)
for eta in [mp.mpf('0.3'),mp.mpf('0.2'),mp.mpf('0.1'),mp.mpf('0.0')]:
    M2=sum(Delta(eta,gm,T,g)**2 for gm in zeros)
    print(f"{float(eta):>10} {float(M2):>16.3e} {ceil:>26.3e}")
print("M2_diag ≤ ceiling for all these η (incl. large η=0.3): an UPPER bound is compatible")
print("with η≠0.  To conclude RH you'd need M2_diag forced to 0 — an upper bound cannot.")
