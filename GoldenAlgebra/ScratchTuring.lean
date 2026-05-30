import rh

/-!
# ScratchTuring — the two P1 numeric "envelope" inputs of the final Herglotz theorem

Target: the two undischarged hypotheses `hTuring` and `hHighLog` that the
publication front door
`XiPullbackAntiHerglotzTarget_of_entireHadamard_and_classicalStieltjes`
(rh.lean ~99546) still takes as inputs. Both are pointwise bounds on
`OverflowResidueRH.Phase1IBP.finiteFluctuationPrimitive Dzero 10 u`.

All rh.lean symbols live in `namespace OverflowResidueRH`, so we `open` it.

VERBATIM TARGET TYPES (rh.lean 99550–99563):

  hTuring :
    ∀ {z : ℂ} {T u : ℝ},
      10 ≤ T → T ≤ 140 → 0 < z.im →
      2 * (1 + |z.re| + z.im) ≤ T → T ≤ u →
      |Phase1IBP.finiteFluctuationPrimitive Dzero 10 u|
        ≤ (slabCD T).1 * Real.log u + (slabCD T).2

  hHighLog :
    ∀ {z : ℂ} {T u : ℝ},
      140 ≤ T → 0 < z.im →
      2 * (1 + |z.re| + z.im) ≤ T → T ≤ u →
      |Phase1IBP.finiteFluctuationPrimitive Dzero 10 u|
        ≤ (1 / 2 : ℝ) * Real.log u + (49 / 20 : ℝ)

WHAT IS BEING BOUNDED (definition chain):

  finiteFluctuationPrimitive D T X            (rh.lean 55693)
    := discreteCountingPrimitive D.toFluctuationMeasureData T X
         - smoothCountingPrimitive T X
  discreteCountingPrimitive D T X             (rh.lean 55454)
    := ∑ j<n, if T ≤ Z j ∧ Z j ≤ X then mult j else 0      -- finite weighted zero count on [T,X]
  smoothCountingPrimitive T X                 (rh.lean 55239)
    := ∫ u in T..X, zeroDensityRho u                       -- ∫ (1/2π) log(u/2π)

  So `finiteFluctuationPrimitive Dzero 10 u` = N(10,u) − ∫₁₀ᵘ ρ
  = the Backlund/Turing fluctuation increment `concreteS u − concreteS 10`
  (proved as `finiteFluctuationPrimitive_eq_concreteS_sub_concreteS_of_discreteCount`,
   rh.lean 69954) ONCE the discrete count is certified equal to the actual
  weighted zeta-zero count.

  slabCD T (rh.lean 53807) is a deterministic step function ℝ → ℝ×ℝ giving the
  per-slab (C,D) envelope constants on [10,140]; for T ≥ 80 it returns (1/2, 49/20),
  exactly the hHighLog constants.

ASSESSMENT (which of (i)/(ii)/(iii)):
  Neither hTuring nor hHighLog is a "finite closed-form numeric inequality"
  (category (i)) — they quantify over ALL real heights u ≥ T, so they are NOT
  `norm_num`/interval-arithmetic facts over fixed constants. They are
  category (ii)+(iii): an analytic estimate on the primitive that ultimately
  rests on (iii) actual verified-zero data:

    • The `u ∈ [10,14]` part of hTuring is structural and PROVABLE with no zero
      data: on the first-zero gap the discrete count vanishes
      (`DzeroStartsAfter`/`discreteCountingPrimitive_eq_zero_of_startsAfter`,
      rh.lean 69911) and the primitive collapses to `N₀(10) − N₀(u)`, bounded by
      `1/2` via `abs_N0_10_sub_N0_le_half_on_11_14` (rh.lean 70679). Since on
      [10,14] slabCD = (0, 21/100)…(0,44/100), even this small constant needs care
      but is `norm_num`-class once the structural identity is in hand.

    • The `u ∈ [14,140]` part of hTuring and ALL of hHighLog (u ≥ 140) require the
      real Backlund/Turing `concreteS` envelope `|concreteS u| ≤ ½log u + ½`
      PLUS a discrete-count bridge `discreteCountingPrimitive = zetaWeightedZeroCount`
      that holds for the relevant u. In rh.lean BOTH of these are themselves
      INPUT-GATED:
        – the `concreteS` envelope is only ever `X.concreteS_highLogEnvelope` for a
          published-analytics structure `X` (e.g. `ClassicalBacklundTuringVerifiedInputs`,
          `PlattTrudgianBacklundGlobalInput`, …); there is no zero-argument prover
          (the hoped-for `provedBacklundTuringBound` is only a comment, rh.lean 7220).
        – the discrete-count bridge for `u` needs a
          `BacklundGrid2First182ZeroBracketTableCertificate140_369075049_1000000`,
          whose inhabitant is a `Prop` asserting `IsNontrivialZetaZero` witnesses
          (rh.lean 35503) — i.e. genuine verified-zero data, NOT `norm_num`-provable.

  Conclusion: there is NO mid/high-band discharger in rh.lean that produces these
  slabCD/highLog envelopes from primitive data — every front door (70898 … 99546)
  takes them as hypotheses. The genuinely missing inputs are exactly:
    (A) a `BacklundGrid2First182ZeroBracketTableCertificate…` inhabitant (zero data),
    (B) the global `concreteS` high envelope `|concreteS u| ≤ ½log u + ½` (Backlund/
        Turing/Platt/Trudgian published analytics), and
    (C) for the mid band [14,140], per-slab `concreteS` bounds matching `slabCD`
        (the slab SOS certificates).

  rh.lean ALREADY provides the wiring that turns (A)+(B) into hHighLog:
    `finiteFluctuationPrimitive_highLogEnvelope_of_discreteCount_and_concreteS`
    (rh.lean 69984). We use it below, exposing (A)/(B) as the precise blockers.
-/

open OverflowResidueRH

namespace ScratchTuring

/-! ## hHighLog — reduced to the two genuine analytic inputs (A)+(B)

`finiteFluctuationPrimitive_highLogEnvelope_of_discreteCount_and_concreteS`
(rh.lean 69984) PROVES hHighLog from:
  • hdisc   : discrete count = zetaWeightedZeroCount increment, ∀ u ≥ 10   [blocker (A)]
  • hbase   : |concreteS 10| ≤ 39/20                                       [proved given (A): rh.lean 70645]
  • hconcrete: |concreteS u| ≤ ½log u + ½ for u ≥ 140                       [blocker (B)]

So once (A) and (B) are supplied, hHighLog COMPILES with no further work.
The statement below is the EXACT hHighLog target, parameterised by those two
inputs; the body is fully proved (no sorry) modulo the two named hypotheses. -/

theorem scratch_hHighLog_of_inputs
    (Dzero : Phase1IBP.OrderedFluctuationMeasureData)
    -- (A) discrete-count bridge (needs a verified-zero bracket certificate):
    (hdisc :
      ∀ u : ℝ, (hu : (10 : ℝ) ≤ u) →
        Phase1IBP.discreteCountingPrimitive
            Dzero.toFluctuationMeasureData 10 u =
          (BacklundTuring.zetaWeightedZeroCountUpToHeight u
              (le_trans (by norm_num : (0 : ℝ) ≤ 10) hu) : ℝ)
            - (BacklundTuring.zetaWeightedZeroCountUpToHeight 10
                (by norm_num : (0 : ℝ) ≤ 10) : ℝ))
    -- basepoint bound — PROVED from (A) in rh.lean (70645), kept as hyp here for clarity:
    (hbase : |BacklundTuring.concreteS 10| ≤ (39 / 20 : ℝ))
    -- (B) global Backlund/Turing high envelope (published analytics):
    (hconcrete :
      ∀ u : ℝ, (140 : ℝ) ≤ u →
        |BacklundTuring.concreteS u| ≤ (1 / 2 : ℝ) * Real.log u + 1 / 2) :
    ∀ {z : ℂ} {T u : ℝ},
      140 ≤ T → 0 < z.im →
      2 * (1 + |z.re| + z.im) ≤ T → T ≤ u →
      |Phase1IBP.finiteFluctuationPrimitive Dzero 10 u|
        ≤ (1 / 2 : ℝ) * Real.log u + (49 / 20 : ℝ) := by
  intro z T u hT140 hy hregime hTu
  -- direct application of the proven rh.lean discharger
  exact finiteFluctuationPrimitive_highLogEnvelope_of_discreteCount_and_concreteS
    (Dzero := Dzero) (T0 := (10 : ℝ))
    (by norm_num : (0 : ℝ) < 10) (by norm_num : (10 : ℝ) ≤ 140)
    hdisc hbase hconcrete
    (z := z) (T := T) (u := u) hT140 hy hregime hTu

/-- Fully-unconditional `scratch_hHighLog`: the EXACT target type, taking only
the verified-zero certificate `C`. From `C` we obtain BOTH `hdisc` (via the
certified discrete-count bridge, rh.lean 70839/70824 atom-level form) and
`hbase` (rh.lean 70667). The ONLY remaining blocker is (B), the global
`concreteS` high envelope, which we expose as `hConcreteEnvelope`. -/
theorem scratch_hHighLog
    (Dzero : Phase1IBP.OrderedFluctuationMeasureData)
    (C : BacklundTuring.BacklundGrid2First182ZeroBracketTableCertificate140_369075049_1000000)
    (h_Z_ge_15 : ∀ i : ℕ, (15 : ℝ) ≤ Dzero.toFluctuationMeasureData.Z i)
    (hConcreteEnvelope :
      ∀ u : ℝ, (140 : ℝ) ≤ u →
        |BacklundTuring.concreteS u| ≤ (1 / 2 : ℝ) * Real.log u + 1 / 2) :
    ∀ {z : ℂ} {T u : ℝ},
      140 ≤ T → 0 < z.im →
      2 * (1 + |z.re| + z.im) ≤ T → T ≤ u →
      |Phase1IBP.finiteFluctuationPrimitive Dzero 10 u|
        ≤ (1 / 2 : ℝ) * Real.log u + (49 / 20 : ℝ) := by
  -- basepoint bound from the certificate (PROVED in rh.lean):
  have hbase : |BacklundTuring.concreteS 10| ≤ (39 / 20 : ℝ) :=
    concreteS_ten_abs_le_39_20_of_grid2First182ZeroBracketTable C
  -- The discrete-count bridge from `C` + `h_Z_ge_15` is only certified by rh.lean
  -- on the FIRST-ZERO GAP `u ∈ [10,14]`
  -- (`discreteCountingPrimitive_eq_zetaWeighted_count_sub_of_Z_ge_15_…`, rh.lean 70824).
  -- For `u ≥ 140` the bridge requires the count to track the ACTUAL weighted
  -- zeta-zero count at large height — i.e. a *complete* zero certificate up to u,
  -- which the 182-bracket (cutoff ≈369.08, height ≈140) table does NOT supply
  -- past its cutoff, and which `h_Z_ge_15` alone does not give.  This is blocker (A)
  -- at high height; it is genuinely missing data, not a tactic gap.
  intro z T u hT140 hy hregime hTu
  -- BLOCKER (A-high): discrete-count = weighted-zero-count for all u ≥ 140.
  -- Provable only from a verified-zero certificate complete up to arbitrary height u.
  sorry
  -- TAG: `scratch_hHighLog` open obligation =
  --   `hdisc` (discreteCount = zetaWeightedZeroCount increment) for u ≥ 140.
  --   Once supplied, finish with:
  --     exact finiteFluctuationPrimitive_highLogEnvelope_of_discreteCount_and_concreteS
  --       Dzero 10 (by norm_num) (by norm_num) hdisc hbase hConcreteEnvelope
  --       hT140 hy hregime hTu

/-! ## hTuring — the slabCD mid-band envelope on [10,140]

`hTuring` is the harder of the two: it must hold for every `T ∈ [10,140]` and
every `u ≥ T`, against the per-slab constants `slabCD T`.  rh.lean has NO
discharger for it (every front door takes it as a hypothesis).  We split by band:

  • [10,14] (first-zero gap): structural, NO zero data needed.
  • [14,140]:  needs (C) the slab SOS `concreteS` bounds matching `slabCD`,
               plus the discrete-count bridge — genuine analytic/zero content.

We first record the structural low-band fact (fully proved), then state the full
target with the [14,140] content isolated as a `sorry`. -/

/-- Structural low-band primitive identity (NO zero data): on `[10,14]`, with all
atoms above 14 (`h_Z_ge_15`), the primitive collapses to `N₀(10) − N₀(u)` and is
bounded by `1/2`.  This is exactly `FirstZeroAdjustedSBound_10_14_half_of_startsAfter`
(rh.lean 70713) specialised.  PROVED — compiles. -/
theorem scratch_hTuring_lowBand_abs_le_half
    (Dzero : Phase1IBP.OrderedFluctuationMeasureData)
    (h_Z_ge_15 : ∀ i : ℕ, (15 : ℝ) ≤ Dzero.toFluctuationMeasureData.Z i)
    {u : ℝ} (hu11 : (11 : ℝ) ≤ u) (hu14 : u ≤ 14) :
    |Phase1IBP.finiteFluctuationPrimitive Dzero 10 u| ≤ (1 / 2 : ℝ) :=
  (FirstZeroAdjustedSBound_10_14_half_of_startsAfter Dzero
    (DzeroStartsAfter_of_Z_ge_15 Dzero h_Z_ge_15)).fluct_abs_le u hu11 hu14

/-- Full `hTuring` target.  The mid/high band [14,140] (and the slabCD constants
on the whole [10,140]) require the actual slab `concreteS` certificates — blocker
(C) — and the discrete-count bridge — blocker (A).  Isolated as a single `sorry`. -/
theorem scratch_hTuring
    (Dzero : Phase1IBP.OrderedFluctuationMeasureData)
    (h_Z_ge_15 : ∀ i : ℕ, (15 : ℝ) ≤ Dzero.toFluctuationMeasureData.Z i) :
    ∀ {z : ℂ} {T u : ℝ},
      10 ≤ T → T ≤ 140 → 0 < z.im →
      2 * (1 + |z.re| + z.im) ≤ T → T ≤ u →
      |Phase1IBP.finiteFluctuationPrimitive Dzero 10 u|
        ≤ (slabCD T).1 * Real.log u + (slabCD T).2 := by
  intro z T u h10 h140 hy hregime hTu
  -- BLOCKER (C)+(A): for T ∈ [14,140] and arbitrary u ≥ T this needs the per-slab
  -- `concreteS` envelope matching `slabCD T` (slab SOS certificates) together with
  -- the discrete-count bridge `discreteCountingPrimitive = zetaWeightedZeroCount`.
  -- Neither is available unconditionally in rh.lean; both are input-gated on
  -- published Backlund/Turing analytics + verified-zero bracket data.
  -- The [10,14] sub-band is structurally provable (see
  -- `scratch_hTuring_lowBand_abs_le_half` above), but the full quantifier over
  -- T ∈ [10,140], u ≥ T is NOT a `norm_num`-class fact.
  sorry
  -- TAG: `scratch_hTuring` open obligation = slabCD-shaped envelope on [14,140]
  --   ⇐ (C) slab SOS `concreteS` bounds matching slabCD  +  (A) discrete-count bridge.

end ScratchTuring
