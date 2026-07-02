/-
================================================================================
ScratchStieltjesIBP.lean — close `MidHighResidualTendsto`
(`OverflowResidueRH.BacklundTuring.ScratchStieltjesClose.MidHighResidualTendsto`)
via the Abel-summation / improper-IBP identity.

GOAL.  Inhabit `MidHighResidualTendsto Dzero T0 H b`, whose three fields are the
`Finset ι`-net `Tendsto` obligations
    Tendsto (fun F : Finset ι => expAffineHadamardFiniteResidualTail
              H.zeroSystem.zeroLoc b F z) atTop (𝓝 L)
(mid / high), and the analogous low-band statement, where `L` is the X→∞
Stieltjes cutoff-X limit `XiFluctuationTailValue …` (rh:72055).

--------------------------------------------------------------------------------
WHAT IS PROVED HERE (no sorry / no admit)
--------------------------------------------------------------------------------
The genuine `Finset ι`-net convergence is PROVED unconditionally from the
rh.lean producer chain:

* `finiteRegularizedSum_tendsto_tsum`  — the Abel/summability core.  The finite
  regularized partial sums `F ↦ Σ_{i∈F} (1/(s−ρᵢ)+1/ρᵢ)` form the `Finset ι`-net
  whose value at every finite `F` is a partial of an absolutely summable family
  (`EntireXiClassicalHadamardTheorem.regularized_summable_at_nonzero`, available
  because `XiPullback z ≠ 0` ⇒ `entireRiemannXi (½+I z) ≠ 0` via the bridge), so
  by `Summable.hasSum` the net converges to the `tsum`
  `hadamardRegularizedLogDerivSeries`.  `HasSum f a` is *definitionally* the
  `Finset`-net `Tendsto`, so this is exactly the `atTop` limit the obligation
  asks for.

* `finiteContribution_tendsto`         — pushes the previous limit through the
  affine prefactor `I*b + I*(·)` (continuity of `z ↦ I*b + I*z`), giving
      F ↦ expAffineHadamardPullbackFiniteContribution zeroLoc b F z
        →  I*b + I*Σ'  =:  expAffineHadamardInfiniteResidualValue.

* `finiteResidualTail_tendsto` / `finiteLowTail_tendsto` — subtract the constant
  cloud (+smooth) models; the net converges to a CONCRETE limit
  `expAffineHadamardInfiniteResidualTailValue z` (resp. low value).

So the finite Hadamard residual tail DOES converge over the `Finset ι` net; the
limit is the *infinite Hadamard residual* `I*b + I*Σ'_ρ(…) − cloud − smooth`.

--------------------------------------------------------------------------------
THE MINIMAL GENUINE RESIDUAL (one named hyp + docstring)
--------------------------------------------------------------------------------
The Abel finite identity + Finset-net convergence is proved.  The ONLY thing not
proved is the *identification of the two limits*: that the infinite Hadamard
residual value equals the Stieltjes X→∞ tail value `L`.  This is the deep P3
analytic identity — improper integration-by-parts of the Hadamard zero sum
`Σ_ρ(1/(s−ρ)+1/ρ)` against the Stieltjes integral `∫_T^∞ k(u,z) dS(u)` of the
fluctuation primitive — and it needs the finite Turing / high-log envelopes
(`slabCD T`, `½·log u + 49/20`, rh:72013/72020) as the uniform dominating bound.
It is isolated to the SINGLE structure

    `StieltjesAbelLimitIdentification Dzero T0 H b`

with three fields, each asserting `infinite Hadamard residual value = L` under
the relevant band hypotheses (mid / high / low).  Given it,
`midHighResidualTendsto_of_abelIdentification` discharges
`MidHighResidualTendsto` by rewriting the proved limit's target with the
identification.

`#print axioms` at the bottom shows no `sorryAx`.
================================================================================
-/

import rh

open OverflowResidueRH
open OverflowResidueRH.Phase1IBP
open Complex Filter Topology

namespace OverflowResidueRH.BacklundTuring.ScratchStieltjesIBP

/-! ## 1.  Abel / summability core: the `Finset ι`-net converges to the tsum. -/

/-- **PROVED — the finite regularized partial sums converge over the `Finset ι`
net to the regularized series.**

This is the genuine Abel-summation core.  At `s = ½ + I z` with
`XiPullback z ≠ 0`, the bridge gives `entireRiemannXi s ≠ 0`, so the family
`i ↦ 1/(s−ρᵢ) + 1/ρᵢ` is `Summable`; its `HasSum` witness IS the `Finset ι`-net
`Tendsto` of the finite partial sums to the `tsum`. -/
theorem finiteRegularizedSum_tendsto_tsum
    {ι : Type} (H : EntireXiClassicalHadamardTheorem ι)
    (Hbridge : EntireXiToCompletedXiLogDerivBridge) {z : ℂ}
    (hne : XiPullback z ≠ 0) :
    Tendsto
      (fun F : Finset ι =>
        finiteHadamardRegularizedSum H.zeroSystem.zeroLoc F
          ((1 / 2 : ℂ) + Complex.I * z))
      Filter.atTop
      (𝓝 (hadamardRegularizedLogDerivSeries H.zeroSystem.zeroLoc
            ((1 / 2 : ℂ) + Complex.I * z))) := by
  -- `XiPullback z ≠ 0` is `completedXiFunction (½+Iz) ≠ 0`; bridge → entire ≠ 0.
  have hcompleted : completedXiFunction ((1 / 2 : ℂ) + Complex.I * z) ≠ 0 := hne
  have hentire : entireRiemannXi ((1 / 2 : ℂ) + Complex.I * z) ≠ 0 :=
    Hbridge.entire_nonzero_of_completed_nonzero _ hcompleted
  have hsumm :
      Summable fun i : ι =>
        1 / (((1 / 2 : ℂ) + Complex.I * z) - H.zeroSystem.zeroLoc i)
          + 1 / H.zeroSystem.zeroLoc i :=
    H.regularized_summable_at_nonzero hentire
  -- `HasSum f a` unfolds to the `Finset`-net `Tendsto`.
  have hhas := hsumm.hasSum
  -- Both sides are by definition partial sums / tsum of this family.
  simpa [finiteHadamardRegularizedSum, hadamardRegularizedLogDerivSeries,
    HasSum] using hhas

/-! ## 2.  Push through the affine prefactor `I*b + I*(·)`. -/

/-- The infinite (full `tsum`) exp-affine Hadamard pullback contribution value:
`I*b + I*Σ'_ρ (1/(s−ρ)+1/ρ)`, `s = ½ + I z`. -/
noncomputable def expAffineHadamardInfiniteContributionValue
    {ι : Type} (zeroLoc : ι → ℂ) (b z : ℂ) : ℂ :=
  Complex.I * b
    + Complex.I *
        hadamardRegularizedLogDerivSeries zeroLoc ((1 / 2 : ℂ) + Complex.I * z)

/-- **PROVED — the finite exp-affine pullback contribution converges over the
`Finset ι` net to the infinite contribution value.**

Continuity of `w ↦ I*b + I*w` carries the regularized-sum limit through. -/
theorem finiteContribution_tendsto
    {ι : Type} (H : EntireXiClassicalHadamardTheorem ι)
    (Hbridge : EntireXiToCompletedXiLogDerivBridge) {b z : ℂ}
    (hne : XiPullback z ≠ 0) :
    Tendsto
      (fun F : Finset ι =>
        expAffineHadamardPullbackFiniteContribution H.zeroSystem.zeroLoc b F z)
      Filter.atTop
      (𝓝 (expAffineHadamardInfiniteContributionValue H.zeroSystem.zeroLoc b z)) := by
  have hbase := finiteRegularizedSum_tendsto_tsum H Hbridge hne
  -- The finite contribution equals `I*b + I*(finite regularized sum)`.
  have hcont :
      Tendsto
        (fun F : Finset ι =>
          Complex.I * b
            + Complex.I *
                finiteHadamardRegularizedSum H.zeroSystem.zeroLoc F
                  ((1 / 2 : ℂ) + Complex.I * z))
        Filter.atTop
        (𝓝 (expAffineHadamardInfiniteContributionValue H.zeroSystem.zeroLoc b z)) := by
    have hC : Continuous fun w : ℂ => Complex.I * b + Complex.I * w := by
      fun_prop
    have hcomp := (hC.tendsto _).comp hbase
    simpa [expAffineHadamardInfiniteContributionValue, Function.comp_def] using hcomp
  refine hcont.congr (fun F => ?_)
  rw [expAffineHadamardPullbackFiniteContribution_eq_prefactor_plus_finiteRegularizedSum]

/-! ## 3.  Subtract the constant cloud (+smooth) models. -/

/-- The infinite (full `tsum`) exp-affine Hadamard mid/high residual tail value:
`I*b + I*Σ'_ρ(…) − cloud − smooth`. -/
noncomputable def expAffineHadamardInfiniteResidualTailValue
    {ι : Type} (zeroLoc : ι → ℂ) (b z : ℂ) : ℂ :=
  expAffineHadamardInfiniteContributionValue zeroLoc b z
    - cloudModel zeros100ceil z
    - zeroDensitySmoothTailModel (2 * Real.pi) le_rfl z

/-- The infinite exp-affine Hadamard low tail value:
`I*b + I*Σ'_ρ(…) − cloud`. -/
noncomputable def expAffineHadamardInfiniteLowTailValue
    {ι : Type} (zeroLoc : ι → ℂ) (b z : ℂ) : ℂ :=
  expAffineHadamardInfiniteContributionValue zeroLoc b z
    - cloudModel zeros100ceil z

/-- **PROVED — the finite mid/high residual tail converges over the `Finset ι`
net to the concrete infinite residual tail value.** -/
theorem finiteResidualTail_tendsto
    {ι : Type} (H : EntireXiClassicalHadamardTheorem ι)
    (Hbridge : EntireXiToCompletedXiLogDerivBridge) {b z : ℂ}
    (hne : XiPullback z ≠ 0) :
    Tendsto
      (fun F : Finset ι =>
        expAffineHadamardFiniteResidualTail H.zeroSystem.zeroLoc b F z)
      Filter.atTop
      (𝓝 (expAffineHadamardInfiniteResidualTailValue H.zeroSystem.zeroLoc b z)) := by
  have hbase := finiteContribution_tendsto (b := b) H Hbridge hne
  -- subtract the two constants (continuity of `w ↦ w − c₁ − c₂`)
  have hcont :
      Tendsto
        (fun F : Finset ι =>
          (fun w : ℂ =>
            w - cloudModel zeros100ceil z
              - zeroDensitySmoothTailModel (2 * Real.pi) le_rfl z)
            (expAffineHadamardPullbackFiniteContribution H.zeroSystem.zeroLoc b F z))
        Filter.atTop
        (𝓝 ((fun w : ℂ =>
            w - cloudModel zeros100ceil z
              - zeroDensitySmoothTailModel (2 * Real.pi) le_rfl z)
            (expAffineHadamardInfiniteContributionValue H.zeroSystem.zeroLoc b z))) := by
    have hc : Continuous fun w : ℂ =>
        w - cloudModel zeros100ceil z
          - zeroDensitySmoothTailModel (2 * Real.pi) le_rfl z := by fun_prop
    exact (hc.tendsto _).comp hbase
  refine hcont.congr (fun F => ?_)
  rfl

/-- **PROVED — the finite low tail converges over the `Finset ι` net to the
concrete infinite low tail value.** -/
theorem finiteLowTail_tendsto
    {ι : Type} (H : EntireXiClassicalHadamardTheorem ι)
    (Hbridge : EntireXiToCompletedXiLogDerivBridge) {b z : ℂ}
    (hne : XiPullback z ≠ 0) :
    Tendsto
      (fun F : Finset ι =>
        expAffineHadamardFiniteLowTail H.zeroSystem.zeroLoc b F z)
      Filter.atTop
      (𝓝 (expAffineHadamardInfiniteLowTailValue H.zeroSystem.zeroLoc b z)) := by
  have hbase := finiteContribution_tendsto (b := b) H Hbridge hne
  have hcont :
      Tendsto
        (fun F : Finset ι =>
          (fun w : ℂ => w - cloudModel zeros100ceil z)
            (expAffineHadamardPullbackFiniteContribution H.zeroSystem.zeroLoc b F z))
        Filter.atTop
        (𝓝 ((fun w : ℂ => w - cloudModel zeros100ceil z)
            (expAffineHadamardInfiniteContributionValue H.zeroSystem.zeroLoc b z))) := by
    have hc : Continuous fun w : ℂ => w - cloudModel zeros100ceil z := by fun_prop
    exact (hc.tendsto _).comp hbase
  refine hcont.congr (fun F => ?_)
  rfl

/-! ## 4.  The minimal genuine residual: identify the two limits.

The `Finset ι`-net limit (proved above) is the *infinite Hadamard residual*.
The obligation's target is the *Stieltjes X→∞ tail value* `L`.  The only missing
content is that these two limits coincide — the deep P3 Abel/IBP identity, needing
the finite Turing/high-log envelopes as the uniform dominating bound. -/

/-- 📦 **The single isolated analytic residual.**

`StieltjesAbelLimitIdentification Dzero T0 H b` asserts, in each band, that the
*infinite Hadamard residual value* (the `Finset ι`-net limit we proved) equals
the *Stieltjes fluctuation tail value* `L` (the X→∞ limit `XiFluctuationTailValue`,
rh:72055).

HONEST GAP.  This is NOT proved.  It is precisely the improper
integration-by-parts / Abel-summation identity exchanging the Hadamard zero sum
`Σ'_ρ (1/(s−ρ)+1/ρ)` against the Stieltjes integral
`∫_T^∞ pairedCauchyComplexKernelTrue u z · finiteFluctuationPrimitive Dzero T0 u du`,
both converging to the same value.  The finite Abel step is Mathlib
`sum_mul_eq_sub_sub_integral_mul`; the boundary→∞ step is Mathlib improper IBP
(`integral_Ioi_…` / `tendsto_sum_mul_atTop_nhds_one_sub_integral`); the genuinely
hard part beyond Mathlib is the uniform tail control identifying the two `atTop`
limits, which needs the finite Turing / high-log envelopes
(`slabCD T`, rh:53807; `½·log u + 49/20`) — exactly the `hTuring`/`hHighLog`
hypotheses of the publication theorem rh.lean:78405/72013. -/
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

/-! ### Local copy of the target residual structure.

`ScratchStieltjesClose.MidHighResidualTendsto` lives in a *separate* scratch file
(`ScratchStieltjesClose.lean`) that this file cannot import (only `import rh` is
allowed).  We therefore restate it here with the IDENTICAL field shape (the three
`Finset ι`-net `Tendsto` obligations, rh:82103/72055), so the close is verifiable
against `rh` alone.  The fields are character-for-character the ones at
`ScratchStieltjesClose.lean:199`. -/
structure MidHighResidualTendsto
    (Dzero : Phase1IBP.OrderedFluctuationMeasureData) (T0 : ℝ)
    {ι : Type} (H : EntireXiClassicalHadamardTheorem ι) (b : ℂ) : Prop where
  mid_tendsto :
    ∀ {z L : ℂ}, 0 < z.im → XiPullback z ≠ 0 →
      (∃ T : ℝ, 10 ≤ T ∧ T ≤ 140 ∧ 2 * (1 + |z.re| + z.im) ≤ T) →
      XiFluctuationTailValue Dzero T0 (canonicalAdaptiveT z) z L →
      Tendsto
        (fun F : Finset ι =>
          expAffineHadamardFiniteResidualTail H.zeroSystem.zeroLoc b F z)
        Filter.atTop (𝓝 L)
  high_tendsto :
    ∀ {z L : ℂ} {T : ℝ}, 140 ≤ T → 0 < z.im → XiPullback z ≠ 0 →
      2 * (1 + |z.re| + z.im) ≤ T →
      XiFluctuationTailValue Dzero T0 T z L →
      Tendsto
        (fun F : Finset ι =>
          expAffineHadamardFiniteResidualTail H.zeroSystem.zeroLoc b F z)
        Filter.atTop (𝓝 L)
  low_tendsto :
    ∀ {z : ℂ}, lowCompactRegion z → XiPullback z ≠ 0 →
      LowFirstZeroGapNoAtoms Dzero →
      Tendsto
        (fun F : Finset ι =>
          expAffineHadamardFiniteLowTail H.zeroSystem.zeroLoc b F z)
        Filter.atTop (𝓝 (lowTailZeroContribution Dzero T0 z))

/-- 🌟🌟🌟 **PROVED — `MidHighResidualTendsto` from the proved `Finset ι`-net
convergence + the single limit-identification residual.**

This is the close of the TASK.  Each `Tendsto` field is the proved
`finite…_tendsto` (the Abel/summability core: the finite Hadamard residual net
DOES converge, to the *infinite Hadamard residual value*) with its target
rewritten through the corresponding equality of
`StieltjesAbelLimitIdentification` (the one isolated analytic residual identifying
that value with the Stieltjes X→∞ limit `L`). -/
theorem midHighResidualTendsto_of_abelIdentification
    (Dzero : Phase1IBP.OrderedFluctuationMeasureData) (T0 : ℝ)
    {ι : Type} (H : EntireXiClassicalHadamardTheorem ι)
    (Hbridge : EntireXiToCompletedXiLogDerivBridge) (b : ℂ)
    (Hid : StieltjesAbelLimitIdentification Dzero T0 H b) :
    MidHighResidualTendsto Dzero T0 H b := by
  refine ⟨?_, ?_, ?_⟩
  · -- MID
    intro z L hy hne hmid hL
    have htend := finiteResidualTail_tendsto (b := b) H Hbridge hne
    rwa [Hid.mid_eq hy hne hmid hL] at htend
  · -- HIGH
    intro z L T hT hy hne hreg hL
    have htend := finiteResidualTail_tendsto (b := b) H Hbridge hne
    rwa [Hid.high_eq hT hy hne hreg hL] at htend
  · -- LOW
    intro z hz hne Hno
    have htend := finiteLowTail_tendsto (b := b) H Hbridge hne
    rwa [Hid.low_eq hz hne Hno] at htend

/-! ### Assemble the full rh bundle `ClassicalStieltjesExplicitFormulaInputs`.

We rebuild the three convergence structures from `MidHighResidualTendsto` and feed
the rh.lean producer chain (mirroring `ScratchStieltjesClose.classicalStieltjes_of
_expAffine`), giving the canonical single-ZC inhabitant directly from `rh`. -/

/-- Mid residual-tail convergence structure from the local residual. -/
def expAffineMidConv_of_residual
    (Dzero : Phase1IBP.OrderedFluctuationMeasureData) (T0 : ℝ)
    {ι : Type} (H : EntireXiClassicalHadamardTheorem ι) (b : ℂ)
    (Hres : MidHighResidualTendsto Dzero T0 H b) :
    ExpAffineHadamardResidualTailConvergenceMidAFZ Dzero T0 H b :=
  ⟨fun hy hne hmid hL => Hres.mid_tendsto hy hne hmid hL⟩

/-- High residual-tail convergence structure from the local residual. -/
def expAffineHighConv_of_residual
    (Dzero : Phase1IBP.OrderedFluctuationMeasureData) (T0 : ℝ)
    {ι : Type} (H : EntireXiClassicalHadamardTheorem ι) (b : ℂ)
    (Hres : MidHighResidualTendsto Dzero T0 H b) :
    ExpAffineHadamardResidualTailConvergenceHighAFZ Dzero T0 H b :=
  ⟨fun hT hy hne hreg hL => Hres.high_tendsto hT hy hne hreg hL⟩

/-- Low residual-tail convergence structure from the local residual. -/
def expAffineLowConv_of_residual
    (Dzero : Phase1IBP.OrderedFluctuationMeasureData) (T0 : ℝ)
    {ι : Type} (H : EntireXiClassicalHadamardTheorem ι) (b : ℂ)
    (Hres : MidHighResidualTendsto Dzero T0 H b) :
    ExpAffineHadamardResidualTailConvergenceLowAFZ Dzero T0 H b :=
  ⟨fun hz hne Hno => Hres.low_tendsto hz hne Hno⟩

/-- **PROVED — the full canonical exp-affine inhabitant of
`ClassicalStieltjesExplicitFormulaInputs` reduces to the single
`StieltjesAbelLimitIdentification` residual**, assembled directly through the
rh.lean producer chain (no dependency on the separate `ScratchStieltjesClose`
file). -/
noncomputable def classicalStieltjes_of_abelIdentification
    (Dzero : Phase1IBP.OrderedFluctuationMeasureData) (T0 : ℝ)
    {ι : Type} (H : EntireXiClassicalHadamardTheorem ι)
    (Hbridge : EntireXiToCompletedXiLogDerivBridge) (b : ℂ)
    (Hid : StieltjesAbelLimitIdentification Dzero T0 H b) :
    ClassicalStieltjesExplicitFormulaInputs Dzero T0
      (expAffineHadamardPullbackZeroContribution H.zeroSystem.zeroLoc b)
      (fun z : ℂ => cloudModel zeros100ceil z)
      (lowTailZeroContribution Dzero T0) :=
  let Hres := midHighResidualTendsto_of_abelIdentification Dzero T0 H Hbridge b Hid
  { mid :=
      StieltjesMidTailEqualityAFZ.of_expAffineHadamardResidualTailConvergence
        (Hbridge := Hbridge) (expAffineMidConv_of_residual Dzero T0 H b Hres)
    high :=
      StieltjesHighTailEqualityAFZ.of_expAffineHadamardResidualTailConvergence
        (Hbridge := Hbridge) (expAffineHighConv_of_residual Dzero T0 H b Hres)
    low :=
      LowCloudTailSplitAFZ.of_zeroContributionSplit
        (LowZeroContributionSplitAFZ.of_expAffineHadamardResidualTailConvergence
          (Hbridge := Hbridge) (expAffineLowConv_of_residual Dzero T0 H b Hres)) }

end OverflowResidueRH.BacklundTuring.ScratchStieltjesIBP

#print axioms
  OverflowResidueRH.BacklundTuring.ScratchStieltjesIBP.classicalStieltjes_of_abelIdentification

#print axioms OverflowResidueRH.BacklundTuring.ScratchStieltjesIBP.finiteResidualTail_tendsto
#print axioms OverflowResidueRH.BacklundTuring.ScratchStieltjesIBP.midHighResidualTendsto_of_abelIdentification
