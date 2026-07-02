# Second Moment + Pair Correlation Route — Findings

MISSION: the Weil FIRST moment off-line displacement readout is sign-indefinite via
`cos(γ_ρ u)`. SQUARE it — study the positive SECOND moment and try to bound it
unconditionally via pair-correlation / large-sieve. Bank a real result or a clean reason
squaring doesn't help. Scripts: `SECMOM_*.py` (this dir). Lean: `ScratchSecondMoment.lean`.

Builds on the banked first-moment work: `QUART_FINDINGS.md` identity `(★)`,
`ScratchResolutionTheory.lean` (`cosh_minus_one_resolution`, the `δT~1` gate),
`ScratchDisplacement.lean` (the displacement obstruction `Σ_ρ [trueAtom−heightAtom]`).

## 0. The readout and its square (explicit)

For positive-type `g`, `supp g ⊆ [−T,T]`, zero `ρ = ½ + η_ρ + i γ_ρ`, identity `(★)`:

    Δ_ρ(g) = 4 ∫_{−T}^{T} g(u) (cosh(η_ρ u) − 1) cos(γ_ρ u) du.

Write `k_η(u) := 4 g(u)(cosh(η u) − 1)` and the readout vector `r_ρ(u) := k_{η_ρ}(u) cos(γ_ρ u)`.
Then `Δ_ρ(g) = ∫ r_ρ`. Two positive second-moment objects:

* **Diagonal**  `M₂(g) := Σ_ρ |Δ_ρ(g)|²`  — positive by construction (each term a square).
* **Cross / Hilbert–Schmidt (Gram)**  `M₂^cross(g) := Σ_{ρ,ρ'} ⟨r_ρ, r_{ρ'}⟩_{L²[−T,T]}`
  `= (½) Σ_{ρ,ρ'} [ K̂(γ_ρ−γ_{ρ'}; η_ρ,η_{ρ'}) + K̂(γ_ρ+γ_{ρ'}; η_ρ,η_{ρ'}) ]`,
  where `K̂(ξ;η,η') := ∫_{−T}^{T} k_η k_{η'} cos(ξ u) du` (even, peaked at ξ=0, u-support T).
  The **difference** channel `Σ_{ρ,ρ'} K̂(γ_ρ−γ_{ρ'})` is EXACTLY the object Montgomery's
  pair-correlation `F(α,T)` controls. (Gram identity `⟨r_ρ,r_ρ⟩ = ½[K̂(0)+K̂(2γ)]` checked
  to full precision, `SECMOM_pair.py` (A).)

## 1. Does the second moment still SEE displacement?  YES, at FOURTH order.

`Δ_ρ ∝ (cosh(η u) − 1) ≈ η²u²/2`, so `Δ_ρ = O(η²)` and `|Δ_ρ|² = O(η⁴)`.
NUMERICALLY (`SECMOM_structure.py`, triangle g, T=0.6, γ=14.13): `Δ_ρ/η² → 0.01004…` and
`Δ_ρ²/η⁴ → 0.000101…` constant to 6 digits ⟹ the exact `η⁴` law. So

    M₂(g) = ( Σ_ρ W(γ_ρ,T) ) · (η-scale)⁴ + O(η⁶),   W(γ,T) = ( 2 ∫ g(u) u² cos(γu) du )² ≥ 0.

`M₂` is a **faithful** displacement detector: `M₂(g)=0 ⟺ Δ_ρ=0 ∀ρ` (each term ≥0).
CAVEAT (`SECMOM_weight.py`): the per-zero weight `W(γ,T)` HAS real zeros in γ (cos-cancellation,
e.g. γ≈4.34, 12.36, 17.60, … for T=0.6) and DECAYS like `γ⁻⁴` (band-limited, two IBPs). So a
single zero sitting on a W-zero contributes nothing; faithfulness is COLLECTIVE, and the same
short-support band-limitation that caps the first moment caps `M₂` (`W` tiny for `γT ≳ 1`).

## 2. The gate: η⁴ vs η² — SAME δT~1 wall, STEEPER blindness (p: 2 → 4)

The squared edge kernel `R₂(δ,T) = (cosh(δT)−1)²` obeys (`SECMOM_gate.py`, PROVEN in Lean):

    (cosh(δT)−1)²  ≤  (δT)⁴ · cosh(δT)²          — O((δT)⁴): INVISIBLE below the gate (p=4)
    1 ≤ δT  ⟹  ¼(δT)⁴ ≤ (cosh(δT)−1)²            — O(1):     VISIBLE  above the gate

Obtained by SQUARING the first-moment law `cosh_minus_one_resolution`. The gate is
**unchanged** at `δT ≍ 1`; only the invisibility exponent steepens `2 → 4`. Consequence
(quantified): to reach a fixed detectable floor ε, first moment needs `δT ≳ √ε`, second moment
needs `δT ≳ ε^{1/4}` (LARGER). **Below the gate the second moment is a STRICTLY WORSE detector.**

## 3. The Montgomery pair-correlation bound (UNCONDITIONAL part only)

Montgomery's `F(α,T) = (T/(2π)·log T)^{-1} Σ_{0<γ,γ'≤T} T^{iα(γ-γ')} w(γ-γ')`, `w(u)=4/(4+u²)`.
Parseval bridge: `Σ_{γ,γ'} r̂((γ-γ')·log T/2π) w(γ-γ') = (T log T/2π) ∫ F(α,T) r(α) dα`.

UNCONDITIONAL facts used (Baluyot–Goldston–Suriajaya–Turnage-Butterbaugh, *Acta Arith.* 214
(2024) 357–376, arXiv:2306.04799; Montgomery 1973):
* (U1) `F(α,T) ≥ 0` for all α (it is `|Dirichlet sum|²`).
* (U2) `F(α,T) = T^{-2|α|} log T (1+o(1)) + |α| + o(1)` uniformly for `0 ≤ |α| ≤ 1` —
  **UNCONDITIONAL** (Montgomery proved it under RH; BGSTB removed RH for `0≤α≤1`).
* (U4) For `|α| > 1`: only the LOWER bound `F(α) ≥ α − 1 + o(1)` is unconditional. The UPPER
  bound `F(α) ≤ α + o(1)` (≈ its conjectured value) is **Montgomery's CONJECTURE — NOT proven.**

Bounding the cross-difference channel needs an UPPER bound on `∫ F(α) r(α) dα`:
* If the kernel `K̂` is band-limited to `|α| ≤ 1` (i.e. only couples zeros with
  `(γ_ρ−γ_{ρ'})·log T/2π ≤ 1`): the integral uses ONLY the unconditional region (U2). The
  total `|α|≤1` mass is `∫_{−1}^{1} F dα ≈ 1 + 1 = O(1)` independent of `log T`
  (`SECMOM_montgomery.py`). ⟹ UNCONDITIONAL bound `C(g) = O(T log T · sup|r|)` —
  **the SAME ORDER as the trivial diagonal zero-count** `Σ_ρ 1 ~ (T/2π) log T`. NO gain.
* Past `|α| = 1` (where an upper bound would beat the diagonal): unconditionally only the
  LOWER bound (U4) is known — useless for an UPPER bound on a POSITIVE sum. The needed UPPER
  bound IS Montgomery's CONJECTURE.

## 4. Does it yield displacement control?  NO — wrong inequality direction.

RH-progress needs a LOWER bound forcing `Σ_ρ η_ρ⁴ W(γ_ρ) = 0`, i.e. an UPPER bound on the
positive detector `M₂` by a VANISHING computable quantity. Pair-correlation / large-sieve are
UPPER-bound tools on positive sums: they give `M₂ ≤ B(T)` with `B = O(T log T) ≠ 0` (a nonzero
CEILING). DEMONSTRATED (`SECMOM_direction.py`): `M₂` stays below a fixed O(1) ceiling for a
whole RANGE of η (including η=0.3) — an upper bound is fully compatible with η≠0 and never
forces η→0. Squaring fixed the FIRST-moment SIGN problem (`M₂ ≥ 0`) but converted the goal into
needing a LOWER bound on `M₂`, which pair-correlation cannot supply. (Consistent with
`QUART_FINDINGS.md` Task-3: a positivity floor / ceiling carries no zero-location information.)
Note also: squaring the readout SQUARES the prime side of the explicit formula into a length-2
prime correlation (double prime sum), itself sign-indefinite — no free positivity there either.

## VERDICT

Squaring is verdicts **(a)-keeps-signal + (c)-needs-conjecture**, NOT a new unconditional bound:

1. **Squaring does NOT lose the signal.** `M₂(g) = Σ_ρ |Δ_ρ|² ∝ Σ_ρ η_ρ⁴ W(γ_ρ)` is a
   faithful displacement detector (PROVEN η⁴ law; `M₂=0 ⟺ all η=0` collectively).
2. **SAME gate, steeper blindness.** Detection gate is the SAME `δT ≍ 1` as the first moment;
   the invisibility exponent steepens `2 → 4`, so below the gate `M₂` is STRICTLY WORSE.
3. **Pair-correlation gives only the WRONG-DIRECTION (upper) bound, at diagonal order.** The
   unconditional region `|α| ≤ 1` (U2) bounds the cross terms ABOVE by `O(T log T)` = the
   diagonal zero-count — no resolution gain. An upper bound on a POSITIVE detector never forces
   `η = 0` (numerically demonstrated), so it is VACUOUS for RH.
4. **Beating the diagonal needs Montgomery's CONJECTURE** `F(α) ≈ α` for `α > 1` (RH-strength),
   which we do NOT assume. Unconditionally only `F(α) ≥ α−1` (lower) is available for `α>1`.

**No `Σ η⁴ W ≤ [vanishing]` unconditional bound is bankable.** The second-moment + pair-
correlation route is a clean NEGATIVE result. What IS banked (rigorous, no-sorry, axiom-clean
in `ScratchSecondMoment.lean`): the **squared uncertainty law** `cosh_sub_one_sq_resolution`
and `secondMoment_same_gate` — the formal proof that squaring keeps the `δT~1` wall and only
steepens the invisibility exponent `2 → 4`. This extends the `ScratchResolutionTheory`
universality (all linear fixed-scale criteria share the gate) to the second-moment detector.

## Relation to `ScratchDisplacementMoment` (a DIFFERENT second moment)

`ScratchDisplacementMoment.lean` already banks an unconditional second moment, but of a
DIFFERENT object: `Σ_{γ≤T} η_ρ²` bounded via Selberg's zero-density `N(σ,T)` (layer-cake) by
`≤ 64 T/log T`. That is a moment of the displacements THEMSELVES (not of a test-function
readout), and its bound GROWS like `T/log T` — vacuous for RH, `=0 ⟺ RH`. The present route is
the squared TEST-FUNCTION readout `Σ_ρ |Δ_ρ(g)|²` analysed through pair-correlation `F(α,T)`.
The two are complementary and reach the SAME negative verdict from independent objects (a
density-driven `Σ η²` ceiling that grows; a pair-correlation `Σ|Δ_ρ|²` ceiling at diagonal
order) — both upper bounds on positive quantities, neither forcing `η=0`. This strengthens the
structural conclusion: every unconditional second-moment handle on displacement is an
upper/ceiling bound, the wrong direction for RH.

## Sources

* Montgomery, "The pair correlation of zeros of the zeta function" (1973),
  https://websites.umich.edu/~hlm/paircor1.pdf
* Baluyot, Goldston, Suriajaya, Turnage-Butterbaugh, "An unconditional Montgomery theorem for
  pair correlation of zeros of the Riemann zeta function," *Acta Arith.* 214 (2024) 357–376,
  https://arxiv.org/abs/2306.04799
* Wikipedia, "Montgomery's pair correlation conjecture,"
  https://en.wikipedia.org/wiki/Montgomery's_pair_correlation_conjecture
* (banked, this repo) `QUART_FINDINGS.md` identity `(★)`; `ScratchResolutionTheory.lean`
  `cosh_minus_one_resolution`; `FINDINGS.md` §9 (δT~1 gate), §10 (multiscale).
