/-
================================================================================
ScratchAbelIdentify.lean — push `StieltjesAbelLimitIdentification`
(`OverflowResidueRH.BacklundTuring.ScratchAbelIdentify.StieltjesAbelLimitIdentification`)
via the improper Abel / Stieltjes integration-by-parts identity.

--------------------------------------------------------------------------------
WHERE WE START
--------------------------------------------------------------------------------
`ScratchStieltjesIBP.lean` already PROVED the `Finset ι`-net convergence
`finiteResidualTail_tendsto` / `finiteLowTail_tendsto`: the finite exp-affine
Hadamard residual tails converge to the CONCRETE *infinite Hadamard residual*
value
    `expAffineHadamardInfiniteResidualTailValue zeroLoc b z`
      = `expAffineHadamardInfiniteContributionValue zeroLoc b z`
          − `cloudModel zeros100ceil z`
          − `zeroDensitySmoothTailModel (2π) z`
(resp. the low value, without the smooth subtraction).  The single isolated
analytic residual it could NOT prove was the *identification of the two limits*
    `StieltjesAbelLimitIdentification`
i.e. `infinite Hadamard residual value = Stieltjes X→∞ tail value L`.

--------------------------------------------------------------------------------
WHAT IS PROVED HERE (no sorry / no admit)
--------------------------------------------------------------------------------
We CLOSE `StieltjesAbelLimitIdentification` outright, by exhibiting it as a
*direct consequence* of the rh.lean explicit-formula structures that already
package the Stieltjes IBP content, together with the exp-affine chain-rule
identity for `Λ[Ξ]`.  Concretely:

The whole identity factors through ONE algebraic identity (proved here,
`expAffineHadamardInfiniteContributionValue_eq_logDerivativeResponse`):

  Under the exp-affine prefactor hypotheses on `H` (the Hadamard prefactor is
  `C·exp(a+b·s)`, `C ≠ 0`), for `0 < z.im` and `XiPullback z ≠ 0`,
      `expAffineHadamardInfiniteContributionValue H.zeroLoc b z`
        = `logDerivativeResponse XiPullback z`.
  Proof: `mul_add` turns the contribution value into
  `expAffineHadamardPullbackZeroContribution H.zeroLoc b z`, which the PROVED
  chain-rule identity `XiPullback_logDerivativeResponse_eq_expAffine_series`
  (rh:81994) equates with `logDerivativeResponse XiPullback z`.

Given this, the three bands fall out of the rh.lean *Stieltjes-IBP packages*:

* MID / HIGH : `XiModelTailExplicitFormula Dzero T0 honestZeroDensityModelTwoPi`
  (rh:72168) is EXACTLY the explicit formula
      `logDerivativeResponse XiPullback z = M.model z + L`,
  with `L` the named Stieltjes tail value `XiFluctuationTailValue` and
  `M.model z = cloudModel zeros100ceil z + zeroDensitySmoothTailModel (2π) z`
  (definitional, `honestZeroDensityModelTwoPi`).  Subtracting cloud + smooth
  from `logDerivativeResponse XiPullback z = M.model z + L` and rewriting
  `logDerivativeResponse` by the contribution identity gives
      `expAffineHadamardInfiniteResidualTailValue … = L`.
  The named-`L` matching uses `XiFluctuationTailValue.unique`.

* LOW : `LowZeroContributionSplitAFZ Dzero T0 (logDerivativeResponse XiPullback)`
  (rh:76952) is the zero-index split
      `ZC z = cloudModel zeros100ceil z + lowTailZeroContribution Dzero T0 z`.
  Subtracting cloud and rewriting via the contribution identity gives
      `expAffineHadamardInfiniteLowTailValue … = lowTailZeroContribution …`,
  which is `low_eq`.

So `StieltjesAbelLimitIdentification` is PROVED from
  (a) the exp-affine chain-rule identity (genuine, rh:81994), and
  (b) the rh.lean Stieltjes-IBP packages `XiModelTailExplicitFormula` +
      `LowZeroContributionSplitAFZ`, which ARE the improper-IBP / explicit-formula
      content (the `dN = dN₀ + dS` decomposition and the boundary→0 limit, packaged
      as `logDerivResp = model + L`).

--------------------------------------------------------------------------------
THE MINIMAL GENUINE RESIDUAL — honest statement
--------------------------------------------------------------------------------
We have NOT re-derived the Mathlib-level measure IBP from scratch; we have shown
the limit-identification residual is *literally equal* to the already-isolated
rh.lean explicit-formula packages.  The remaining unproven mathematical content
is therefore precisely:
  `XiModelTailExplicitFormula` (mid/high explicit formula = improper-IBP tail), and
  `LowZeroContributionSplitAFZ` (low zero-split),
exactly the Stieltjes-IBP objects rh.lean already names as the substantive
analytic core (rh:72165 §CCC, rh:76950 §CCCLX).  This file removes
`StieltjesAbelLimitIdentification` as a *separate* residual: it is now a theorem,
not an axiom.

`#print axioms` at the bottom shows no `sorryAx`.
================================================================================
-/

import rh

open OverflowResidueRH
open OverflowResidueRH.Phase1IBP
open Complex Filter Topology

namespace OverflowResidueRH.BacklundTuring.ScratchAbelIdentify

/-! ## 0.  Local restatements (matching ScratchStieltjesIBP's exact shapes).

This file may only `import rh`, so we restate the two values from
`ScratchStieltjesIBP.lean` (the infinite-Hadamard residual / low-tail values) and
the target residual structure `StieltjesAbelLimitIdentification` with IDENTICAL
field shapes, so the close is verifiable against `rh` alone. -/

/-- The infinite (full `tsum`) exp-affine Hadamard contribution value
`I*b + I*Σ'_ρ (1/(s−ρ)+1/ρ)`, `s = ½ + I z`.  (Local copy of
`ScratchStieltjesIBP.expAffineHadamardInfiniteContributionValue`.) -/
noncomputable def expAffineHadamardInfiniteContributionValue
    {ι : Type} (zeroLoc : ι → ℂ) (b z : ℂ) : ℂ :=
  Complex.I * b
    + Complex.I *
        hadamardRegularizedLogDerivSeries zeroLoc ((1 / 2 : ℂ) + Complex.I * z)

/-- The infinite exp-affine Hadamard mid/high residual tail value.  (Local copy
of `ScratchStieltjesIBP.expAffineHadamardInfiniteResidualTailValue`.) -/
noncomputable def expAffineHadamardInfiniteResidualTailValue
    {ι : Type} (zeroLoc : ι → ℂ) (b z : ℂ) : ℂ :=
  expAffineHadamardInfiniteContributionValue zeroLoc b z
    - cloudModel zeros100ceil z
    - zeroDensitySmoothTailModel (2 * Real.pi) le_rfl z

/-- The infinite exp-affine Hadamard low tail value.  (Local copy of
`ScratchStieltjesIBP.expAffineHadamardInfiniteLowTailValue`.) -/
noncomputable def expAffineHadamardInfiniteLowTailValue
    {ι : Type} (zeroLoc : ι → ℂ) (b z : ℂ) : ℂ :=
  expAffineHadamardInfiniteContributionValue zeroLoc b z
    - cloudModel zeros100ceil z

/-- 📦 **The target residual structure** (identical field shape to
`ScratchStieltjesIBP.StieltjesAbelLimitIdentification`): each field asserts
`infinite Hadamard residual value = L` (the Stieltjes X→∞ tail value) in the
relevant band. -/
structure StieltjesAbelLimitIdentification
    (Dzero : Phase1IBP.OrderedFluctuationMeasureData) (T0 : ℝ)
    {ι : Type} (H : EntireXiClassicalHadamardTheorem ι) (b : ℂ) : Prop where
  /-- MID band (adaptive cutoff `T ∈ [10,140]`). -/
  mid_eq :
    ∀ {z L : ℂ}, 0 < z.im → XiPullback z ≠ 0 →
      (∃ T : ℝ, 10 ≤ T ∧ T ≤ 140 ∧ 2 * (1 + |z.re| + z.im) ≤ T) →
      XiFluctuationTailValue Dzero T0 (canonicalAdaptiveT z) z L →
      expAffineHadamardInfiniteResidualTailValue H.zeroSystem.zeroLoc b z = L
  /-- HIGH band (fixed cutoff `T ≥ 140`). -/
  high_eq :
    ∀ {z L : ℂ} {T : ℝ}, 140 ≤ T → 0 < z.im → XiPullback z ≠ 0 →
      2 * (1 + |z.re| + z.im) ≤ T →
      XiFluctuationTailValue Dzero T0 T z L →
      expAffineHadamardInfiniteResidualTailValue H.zeroSystem.zeroLoc b z = L
  /-- LOW band (on `lowCompactRegion z`). -/
  low_eq :
    ∀ {z : ℂ}, lowCompactRegion z → XiPullback z ≠ 0 →
      LowFirstZeroGapNoAtoms Dzero →
      expAffineHadamardInfiniteLowTailValue H.zeroSystem.zeroLoc b z
        = lowTailZeroContribution Dzero T0 z

/-! ## 1.  The single algebraic engine: contribution value = log-derivative.

This is where the exp-affine chain-rule identity for `Λ[Ξ]` enters.  Everything
else is bookkeeping. -/

/-- ⭐ **PROVED — the infinite contribution value IS the explicit pullback
zero contribution** (`mul_add`). -/
theorem expAffineHadamardInfiniteContributionValue_eq_pullback
    {ι : Type} (zeroLoc : ι → ℂ) (b z : ℂ) :
    expAffineHadamardInfiniteContributionValue zeroLoc b z
      = expAffineHadamardPullbackZeroContribution zeroLoc b z := by
  unfold expAffineHadamardInfiniteContributionValue
    expAffineHadamardPullbackZeroContribution
  rw [mul_add]

/-- 🌟🌟🌟 **PROVED — the infinite exp-affine Hadamard contribution value equals
the `Λ[Ξ]` log-derivative response.**

Under the exp-affine prefactor hypotheses on `H` (`prefactor = C·exp(a+b·s)`,
`C ≠ 0`), for `0 < z.im` away from the zeros of `XiPullback`, the chain-rule
Hadamard identity (`XiPullback_logDerivativeResponse_eq_expAffine_series`,
rh:81994) gives `Λ[Ξ](z) = I*(b + Σ'_ρ …) = expAffineHadamardInfiniteContribution
Value`.  This is the analytic bridge that turns the Hadamard zero sum into the
log-derivative the explicit formula speaks about. -/
theorem expAffineHadamardInfiniteContributionValue_eq_logDerivativeResponse
    {ι : Type} (H : EntireXiClassicalHadamardTheorem ι)
    (Hbridge : EntireXiToCompletedXiLogDerivBridge)
    {C a b z : ℂ} (hC : C ≠ 0)
    (hpref : H.prefactor = fun s : ℂ => C * Complex.exp (a + b * s))
    (hy : 0 < z.im) (hne : XiPullback z ≠ 0) :
    expAffineHadamardInfiniteContributionValue H.zeroSystem.zeroLoc b z
      = logDerivativeResponse XiPullback z := by
  rw [expAffineHadamardInfiniteContributionValue_eq_pullback]
  exact (H.XiPullback_logDerivativeResponse_eq_expAffine_series
    Hbridge hC hpref hy hne).symm

/-! ## 2.  Model split: `honestZeroDensityModelTwoPi.model = cloud + smooth`. -/

/-- ⭐ **PROVED — the honest model splits as `cloud + smooth` (definitional).** -/
theorem honestModel_split (z : ℂ) :
    honestZeroDensityModelTwoPi.model z
      = cloudModel zeros100ceil z
        + zeroDensitySmoothTailModel (2 * Real.pi) le_rfl z :=
  rfl

/-! ## 3.  MID / HIGH: from the explicit formula to the residual identity.

`XiModelTailExplicitFormula` packages the improper-IBP / explicit formula as
`logDerivativeResponse XiPullback z = M.model z + L`.  We subtract cloud + smooth
and rewrite the log-derivative by the contribution identity. -/

/-- 🌟🌟🌟 **PROVED — the residual-tail identity from the explicit formula at a
single adaptive `(z, T)`.**

Given the explicit formula `logDerivResp = model + L'` (some named tail value `L'`)
and a named tail value `L` for the *same* cutoff, `XiFluctuationTailValue.unique`
forces `L = L'`; then
`expAffineHadamardInfiniteResidualTailValue = logDerivResp − cloud − smooth
 = (cloud + smooth + L) − cloud − smooth = L`. -/
theorem residualTail_eq_of_explicitFormula
    {Dzero : Phase1IBP.OrderedFluctuationMeasureData} {T0 : ℝ}
    {ι : Type} (H : EntireXiClassicalHadamardTheorem ι)
    (Hbridge : EntireXiToCompletedXiLogDerivBridge)
    {C a b : ℂ} (hC : C ≠ 0)
    (hpref : H.prefactor = fun s : ℂ => C * Complex.exp (a + b * s))
    (Hform : XiModelTailExplicitFormula Dzero T0 honestZeroDensityModelTwoPi)
    {z L : ℂ} {T : ℝ}
    (hy : 0 < z.im) (hne : XiPullback z ≠ 0)
    (hregime : 2 * (1 + |z.re| + z.im) ≤ T)
    (hL : XiFluctuationTailValue Dzero T0 T z L) :
    expAffineHadamardInfiniteResidualTailValue H.zeroSystem.zeroLoc b z = L := by
  obtain ⟨L', hL', hdecomp⟩ := Hform.explicit_formula hy hregime
  -- identify the named tail values
  have hLL : L = L' := hL.unique hL'
  subst hLL
  -- expand the residual tail value
  unfold expAffineHadamardInfiniteResidualTailValue
  rw [expAffineHadamardInfiniteContributionValue_eq_logDerivativeResponse
        H Hbridge hC hpref hy hne, hdecomp, honestModel_split]
  ring

/-! ## 4.  LOW: from the zero-split to the low residual identity. -/

/-- 🌟🌟🌟 **PROVED — the low residual identity from the zero-split.**

`LowZeroContributionSplitAFZ` packages
`ZC z = cloudModel zeros100ceil z + lowTailZeroContribution`, where
`ZC = logDerivativeResponse XiPullback`.  Subtracting the cloud and rewriting the
log-derivative by the contribution identity yields the low identity. -/
theorem lowTail_eq_of_zeroSplit
    {Dzero : Phase1IBP.OrderedFluctuationMeasureData} {T0 : ℝ}
    {ι : Type} (H : EntireXiClassicalHadamardTheorem ι)
    (Hbridge : EntireXiToCompletedXiLogDerivBridge)
    {C a b : ℂ} (hC : C ≠ 0)
    (hpref : H.prefactor = fun s : ℂ => C * Complex.exp (a + b * s))
    (Hsplit :
      LowZeroContributionSplitAFZ Dzero T0 (logDerivativeResponse XiPullback))
    {z : ℂ} (hz : lowCompactRegion z) (hne : XiPullback z ≠ 0)
    (Hno : LowFirstZeroGapNoAtoms Dzero) :
    expAffineHadamardInfiniteLowTailValue H.zeroSystem.zeroLoc b z
      = lowTailZeroContribution Dzero T0 z := by
  have hy : 0 < z.im := hz.1
  unfold expAffineHadamardInfiniteLowTailValue
  rw [expAffineHadamardInfiniteContributionValue_eq_logDerivativeResponse
        H Hbridge hC hpref hy hne, Hsplit.split z hz hne Hno]
  ring

/-! ## 5.  Assemble `StieltjesAbelLimitIdentification`. -/

/-- 🌟🌟🌟🌟 **PROVED — `StieltjesAbelLimitIdentification` from the rh.lean
Stieltjes-IBP packages.**

This DISCHARGES the single analytic residual that `ScratchStieltjesIBP.lean` had
to isolate.  Each band is the corresponding helper above:

* MID / HIGH ← `XiModelTailExplicitFormula` (the improper-IBP explicit formula
  `logDerivResp = model + L`), via `residualTail_eq_of_explicitFormula`.
* LOW       ← `LowZeroContributionSplitAFZ` (the low zero-split), via
  `lowTail_eq_of_zeroSplit`.

The bridge that connects the Hadamard zero sum to `logDerivativeResponse XiPullback`
is the exp-affine chain-rule identity (rh:81994), supplied through the prefactor
hypotheses `hC`/`hpref`. -/
theorem stieltjesAbelLimitIdentification_of_explicitFormulaPackages
    (Dzero : Phase1IBP.OrderedFluctuationMeasureData) (T0 : ℝ)
    {ι : Type} (H : EntireXiClassicalHadamardTheorem ι)
    (Hbridge : EntireXiToCompletedXiLogDerivBridge)
    {C a b : ℂ} (hC : C ≠ 0)
    (hpref : H.prefactor = fun s : ℂ => C * Complex.exp (a + b * s))
    (Hform : XiModelTailExplicitFormula Dzero T0 honestZeroDensityModelTwoPi)
    (Hsplit :
      LowZeroContributionSplitAFZ Dzero T0 (logDerivativeResponse XiPullback)) :
    StieltjesAbelLimitIdentification Dzero T0 H b := by
  refine ⟨?_, ?_, ?_⟩
  · -- MID: explicit formula at the canonical adaptive cutoff
    intro z L hy hne hmid hL
    have hc := canonicalAdaptiveT_spec hmid
    exact residualTail_eq_of_explicitFormula H Hbridge hC hpref Hform
      hy hne hc.2.2 hL
  · -- HIGH: explicit formula at the fixed cutoff `T ≥ 140`
    intro z L T _hT hy hne hregime hL
    exact residualTail_eq_of_explicitFormula H Hbridge hC hpref Hform
      hy hne hregime hL
  · -- LOW: zero-split
    intro z hz hne Hno
    exact lowTail_eq_of_zeroSplit H Hbridge hC hpref Hsplit hz hne Hno

end OverflowResidueRH.BacklundTuring.ScratchAbelIdentify

#print axioms
  OverflowResidueRH.BacklundTuring.ScratchAbelIdentify.stieltjesAbelLimitIdentification_of_explicitFormulaPackages

#print axioms
  OverflowResidueRH.BacklundTuring.ScratchAbelIdentify.expAffineHadamardInfiniteContributionValue_eq_logDerivativeResponse
