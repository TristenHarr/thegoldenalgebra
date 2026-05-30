/-
================================================================================
ScratchStieltjes.lean — Reconnaissance + draft skeleton for the P3 / final-target
Stieltjes explicit-formula bundle `ClassicalStieltjesExplicitFormulaInputs`.

DO NOT take this file as load-bearing for the build of `rh.lean` — it imports
`rh` and only assembles a *draft* inhabitant with clearly-tagged `sorry`s for the
deep analytic obligations. Everything algebraic / definitional compiles; the
`sorry`s are exactly the genuinely-hard Stieltjes limit facts.

--------------------------------------------------------------------------------
FIELD MAP — `structure ClassicalStieltjesExplicitFormulaInputs` (rh.lean:78384)
--------------------------------------------------------------------------------
    structure ClassicalStieltjesExplicitFormulaInputs
        (Dzero : Phase1IBP.OrderedFluctuationMeasureData) (T0 : ℝ)
        (ZC : ℂ → ℂ) (finiteCloud tail : ℂ → ℂ) : Prop where
      mid  : StieltjesMidTailEqualityAFZ  Dzero T0 ZC
      high : StieltjesHighTailEqualityAFZ Dzero T0 ZC
      low  : LowCloudTailSplitAFZ         Dzero T0 ZC finiteCloud tail

  Parameters:
    • Dzero      : the ordered fluctuation-measure data (Riemann-zero list +
                   smooth density), `Phase1IBP.OrderedFluctuationMeasureData`.
    • T0         : the IBP cutoff; the publication theorem fixes `T0 = 10`
                   (the "constant 10" — left endpoint of the Turing band,
                   `finiteFluctuationPrimitive Dzero 10 u`).
    • ZC         : the (pulled-back) zero-contribution function `ℂ → ℂ`.
                   In the final theorem it is
                     `pullbackZeroContribution Hhad...toCompletedXiSourceAFZ`,
                   i.e. `z ↦ I · xiZeroContribution (1/2 + I·z)` (rh.lean:73780).
    • finiteCloud, tail : the two `ℂ → ℂ` summands used only by the LOW field
                   (`ZC = finiteCloud + tail` on the low compact region).

--------------------------------------------------------------------------------
PER-FIELD MATHEMATICAL CONTENT
--------------------------------------------------------------------------------
  mid  (StieltjesMidTailEqualityAFZ, rh.lean:75990):
        For 0<z.im, XiPullback z ≠ 0, some adaptive T∈[10,140] with
        2(1+|z.re|+z.im)≤T, and L the named fluctuation tail value at
        `canonicalAdaptiveT z`:
            ZC z = cloudModel zeros100ceil z
                 + zeroDensitySmoothTailModel (2π) _ z + L.
        ⇒ The Stieltjes explicit formula in the MID band: zero-contribution =
          finite cloud (first ~100 zeros) + smooth density tail + fluctuation L.

  high (StieltjesHighTailEqualityAFZ, rh.lean:76007):
        Same equality with T ≥ 140 (fixed cutoff, non-adaptive); L is the named
        tail value at `T`.  ⇒ same explicit formula in the HIGH band.

  low  (LowCloudTailSplitAFZ, rh.lean:77471): three identity-shaped subfields
        on the low compact region (`lowCompactRegion z`):
          • cloud_exact : finiteCloud z = cloudModel zeros100ceil z
          • tail_exact  : tail z = lowTailZeroContribution Dzero T0 z
                          (under XiPullback z ≠ 0 + LowFirstZeroGapNoAtoms Dzero)
          • split       : ZC z = finiteCloud z + tail z (same guards).
        ⇒ On the bounded low band, ZC literally splits as cloud + low-tail.

--------------------------------------------------------------------------------
SMART CONSTRUCTORS (intended inputs) + FINAL CONSUMER
--------------------------------------------------------------------------------
  The bundle has NO dedicated `.of_…`; it is the anonymous constructor
  `⟨mid, high, low⟩`.  The three fields each have rich producer chains:

  MID/HIGH equality — algebraic & analytic routes:
    • StieltjesMid/HighTailEqualityAFZ.of_residualIdentity  (rh.lean:76165/76199)
        — pure algebra: from the bare residual form `ZC - cloud - smooth = L`.
    • StieltjesMidTailEqualityAFZ.of_expAffineHadamardResidualTailConvergence
        (rh.lean:83473) and the High analogue (rh.lean:83515)
        — the REAL analytic route.  Requires
            ExpAffineHadamardResidualTailConvergenceMid/HighAFZ Dzero T0 H b
          whose sole field is a `Tendsto` of finite Hadamard partial-product
          residual tails to the named fluctuation tail value `L`
          (rh.lean:82722 / 82741).  This forces `ZC =
          expAffineHadamardPullbackZeroContribution H.zeroSystem.zeroLoc b`.
    • stieltjes_limit_identity_of_finite_decompositions (rh.lean:82628) is the
      glue lemma turning finite decompositions + two limits into the equality.

  LOW split — definitional / data-side routes:
    • LowCloudTailSplitAFZ.explicit_lowModel (rh.lean:77516) — trivially inhabits
      the split when `ZC := cloud + lowTail`, `finiteCloud := cloud`,
      `tail := lowTailZeroContribution Dzero T0` (all by `rfl`).
    • LowCloudTailSplitAFZ.of_fun_sum (rh.lean:77492) / .of_zeroContributionSplit
      (rh.lean:77551) — for an externally-supplied ZC.
    • StieltjesLowEqualityAFZ.explicit_lowModel_of_Z_ge_15 (rh.lean:77609) — the
      LOW *equality* (different field) from `∀ i, 15 ≤ Dzero.…Z i`.

  FINAL CONSUMER (rh.lean:78405):
    theorem XiPullbackAntiHerglotzTarget_of_classicalHadamard_and_classicalStieltjes
        (Dzero) (h_Z_ge_15) (hTuring) (hHighLog)
        (Hhad : CompletedXiClassicalHadamardTheorem ι)
        (Hst  : ClassicalStieltjesExplicitFormulaInputs Dzero 10
                  (pullbackZeroContribution
                    Hhad.toConcreteInputs.toCompletedXiSourceAFZ)
                  finiteCloud tail) :
        XiPullbackAntiHerglotzTarget
      It unpacks `Hst.mid / .high / .low` and feeds them, with the Turing/HighLog
      finite envelopes, into
      `XiPullbackAntiHerglotzTarget_of_concreteHadamard_midHigh_cloudTailLow`.

--------------------------------------------------------------------------------
ASSESSMENT — difficulty tiers
--------------------------------------------------------------------------------
  (i)  PURE ALGEBRA / DEFINITIONAL (free):
       • `low` via `explicit_lowModel` — all three subfields are `rfl`.
       • equality ⇄ residual-identity wrappers (`linear_combination`).
       • `pullbackZeroContribution` chain-rule plumbing.

  (ii) FINITE NUMERIC / IBP ENVELOPE (the `T0 = 10` Turing/high-log bounds):
       NOTE: these are NOT fields of this bundle — they are the SEPARATE
       `hTuring` / `hHighLog` hypotheses of the final theorem, bounding
       `|Phase1IBP.finiteFluctuationPrimitive Dzero 10 u|` by `½ log u + c`.
       They are finite Backlund/Turing-style envelopes (`slabCD T`, the
       49/20 high constant).  Tractable with explicit numeric certificates;
       independent of this bundle's three fields.

  (iii) DEEP ANALYTIC IDENTITY (the genuine gap, in `mid`/`high`):
       The Stieltjes explicit-formula equality itself = a `Tendsto` of finite
       Hadamard partial-product residual tails to the named fluctuation tail
       value `L` (`ExpAffineHadamardResidualTailConvergenceMid/HighAFZ`).
       This is improper Abel-summation / IBP-to-infinity: interchanging the
       Hadamard zero sum (`Σ_ρ 1/(s−ρ)+1/ρ`) with the Stieltjes integral
       `∫ k dS_total` against the fluctuation primitive, and showing both
       converge to the same `L`.
       • Mathlib `Mathlib/NumberTheory/AbelSummation.lean`
         (`sum_mul_eq_sub_integral_mul`, summation-by-parts) supplies the
         FINITE Abel step.
       • Mathlib improper IBP (`integral_Ioi_…deriv…`, `MeasureTheory.integral_…
         _of_hasDerivAt`) supplies the boundary→∞ step.
       GENUINELY HARD beyond Mathlib lemmas: (a) the uniform tail control letting
       the two `atTop` limits be exchanged / identified (needs the (ii) envelopes
       as the dominating bound), and (b) matching the Hadamard finite residual
       `expAffineHadamardFiniteResidualTail` to the Stieltjes
       `complexDensityTailPartial` kernel partial — i.e. the kernel/measure
       bookkeeping in `stieltjes_limit_identity_of_finite_decompositions`.
================================================================================
-/

import rh

-- All the Stieltjes-bundle machinery lives inside `OverflowResidueRH`, with the
-- fluctuation-measure types under `OverflowResidueRH.Phase1IBP`.
open OverflowResidueRH
open OverflowResidueRH.Phase1IBP

namespace ScratchStieltjes

/-
DRAFT inhabitant.  We target the canonical "explicit low model" so the LOW field
is `rfl`-discharged, and we expose the two MID/HIGH analytic obligations as the
exp-affine residual-tail convergence sources (the real intended inputs).

Because the LOW `explicit_lowModel` route fixes
  ZC = (fun z => cloudModel zeros100ceil z + lowTailZeroContribution Dzero T0 z)
while the MID/HIGH analytic route fixes
  ZC = expAffineHadamardPullbackZeroContribution H.zeroSystem.zeroLoc b,
a *single* concrete inhabitant must use one common `ZC`.  In the real assembly
`ZC = pullbackZeroContribution Hhad.…toCompletedXiSourceAFZ`, and BOTH routes are
shown (elsewhere in rh.lean) to reduce to that same pullback.  Here we keep the
common `ZC` abstract and discharge each field through its own producer, marking
the residual mismatch / convergence as the gap.
-/

/-- DRAFT smart constructor: assemble `ClassicalStieltjesExplicitFormulaInputs`
from the three split sources.  This is just the anonymous constructor and
compiles given the three fields. -/
def scratch_of_mid_high_low
    {Dzero : Phase1IBP.OrderedFluctuationMeasureData} {T0 : ℝ}
    {ZC finiteCloud tail : ℂ → ℂ}
    (mid  : StieltjesMidTailEqualityAFZ Dzero T0 ZC)
    (high : StieltjesHighTailEqualityAFZ Dzero T0 ZC)
    (low  : LowCloudTailSplitAFZ Dzero T0 ZC finiteCloud tail) :
    ClassicalStieltjesExplicitFormulaInputs Dzero T0 ZC finiteCloud tail :=
  ⟨mid, high, low⟩

/-
================================================================================
DRAFT `scratch_Hst` — the most minimal smart-constructor instantiation.
Uses the analytic exp-affine route for mid/high (the genuine inputs) and the
definitional `explicit_lowModel` route for low.

We carry the entire-ξ Hadamard theorem `H`, its bridge `Hbridge`, and the
prefactor exponent `b`, exactly as the analytic producers demand.  The common
`ZC` is `expAffineHadamardPullbackZeroContribution H.zeroSystem.zeroLoc b`.

Remaining obligations:
  • `Hmid?`  : ExpAffineHadamardResidualTailConvergenceMidAFZ  Dzero T0 H b
               — DEEP (tier iii): finite Hadamard residual tails → L.
  • `Hhigh?` : ExpAffineHadamardResidualTailConvergenceHighAFZ Dzero T0 H b
               — DEEP (tier iii): same in the high band.
  • `low`    : here the canonical ZC for LOW is the explicit low model, which is
               a DIFFERENT function than the exp-affine pullback.  In the real
               assembly these coincide (both equal `pullbackZeroContribution …`).
               Marked as the ZC-reconciliation gap.
================================================================================
-/
noncomputable def scratch_Hst
    (Dzero : Phase1IBP.OrderedFluctuationMeasureData) (T0 : ℝ)
    {ι : Type} (H : EntireXiClassicalHadamardTheorem ι)
    (Hbridge : EntireXiToCompletedXiLogDerivBridge) (b : ℂ) :
    ClassicalStieltjesExplicitFormulaInputs Dzero T0
      (expAffineHadamardPullbackZeroContribution H.zeroSystem.zeroLoc b)
      (fun z : ℂ => cloudModel zeros100ceil z)
      (lowTailZeroContribution Dzero T0) :=
  scratch_of_mid_high_low
    -- MID: from exp-affine residual-tail convergence (the analytic input).
    (StieltjesMidTailEqualityAFZ.of_expAffineHadamardResidualTailConvergence
      (Hbridge := Hbridge)
      (H := H) (b := b)
      (Hconv := by
        -- DEEP ANALYTIC GAP (tier iii): the Stieltjes/Abel-summation limit
        -- `Tendsto (finite Hadamard residual tails) atTop (𝓝 L)` in the mid band.
        -- Discharged by: ExpAffineHadamardResidualTailConvergenceMidAFZ.of_…
        --   .of_finiteProductResidualTailConvergence (rh.lean:82778), itself
        -- needing Mathlib AbelSummation + improper IBP + the (ii) envelopes.
        sorry))
    -- HIGH: from exp-affine residual-tail convergence (high band).
    (StieltjesHighTailEqualityAFZ.of_expAffineHadamardResidualTailConvergence
      (Hbridge := Hbridge)
      (H := H) (b := b)
      (Hconv := by
        -- DEEP ANALYTIC GAP (tier iii): same `Tendsto` in the high band (T ≥ 140).
        sorry))
    -- LOW: explicit-low-model split is `rfl` on all three subfields — BUT its
    -- canonical ZC is `cloud + lowTail`, not the exp-affine pullback used by
    -- mid/high.  ZC-RECONCILIATION GAP: in the real assembly both equal
    -- `pullbackZeroContribution Hhad.…toCompletedXiSourceAFZ`; here we cannot
    -- make the `ZC` arguments coincide definitionally, so we mark it.
    (by
      -- Once the common ZC is fixed to the real pullback, this is
      -- `LowCloudTailSplitAFZ.of_zeroContributionSplit` applied to the proved
      -- `LowZeroContributionSplitAFZ` (rh.lean:77537/77551), which is
      -- definitional for the explicit low model.
      sorry)

/-
================================================================================
ALTERNATIVE DRAFT — fully `rfl`/definitional LOW + abstract MID/HIGH equalities.
This version COMPILES except for the two analytic `sorry`s: it takes the mid and
high equalities as hypotheses (representing the discharged analytic agent output)
and builds the bundle with the canonical explicit-low ZC, so the LOW field is the
genuine `explicit_lowModel` (no ZC-reconciliation gap, because here ZC IS the
explicit low model).
================================================================================
-/
noncomputable def scratch_Hst_explicitLowZC
    (Dzero : Phase1IBP.OrderedFluctuationMeasureData) (T0 : ℝ)
    (mid  : StieltjesMidTailEqualityAFZ Dzero T0
              (fun z : ℂ =>
                cloudModel zeros100ceil z + lowTailZeroContribution Dzero T0 z))
    (high : StieltjesHighTailEqualityAFZ Dzero T0
              (fun z : ℂ =>
                cloudModel zeros100ceil z + lowTailZeroContribution Dzero T0 z)) :
    ClassicalStieltjesExplicitFormulaInputs Dzero T0
      (fun z : ℂ =>
        cloudModel zeros100ceil z + lowTailZeroContribution Dzero T0 z)
      (fun z : ℂ => cloudModel zeros100ceil z)
      (lowTailZeroContribution Dzero T0) :=
  scratch_of_mid_high_low
    mid
    high
    -- LOW: pure `rfl` — compiles, no sorry.  (rh.lean:77516)
    (LowCloudTailSplitAFZ.explicit_lowModel Dzero T0)

end ScratchStieltjes
