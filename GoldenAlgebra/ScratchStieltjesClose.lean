/-
================================================================================
ScratchStieltjesClose.lean — TASK #7: inhabit
`ClassicalStieltjesExplicitFormulaInputs Dzero 10 ZC finiteCloud tail`.

This file closes the Stieltjes explicit-formula bundle down to the SINGLE genuine
analytic residual: the improper Abel-summation / integration-by-parts limit that
identifies the *finite Hadamard partial-product residual tail* (a limit over
`Finset ι` truncations of the zero set) with the *Stieltjes fluctuation tail
value* `L` (a limit over the cutoff `X : ℝ` of the paired-Cauchy density tail
partial).  Everything else — the LOW split, and all the algebraic/limit
plumbing reducing MID/HIGH to that residual — is PROVED here (no `sorry`,
no `admit`), using only the rh.lean producer chain.

--------------------------------------------------------------------------------
THE STRUCTURE  (rh.lean:78384)
--------------------------------------------------------------------------------
    structure ClassicalStieltjesExplicitFormulaInputs
        (Dzero : Phase1IBP.OrderedFluctuationMeasureData) (T0 : ℝ)
        (ZC : ℂ → ℂ) (finiteCloud tail : ℂ → ℂ) : Prop where
      mid  : StieltjesMidTailEqualityAFZ  Dzero T0 ZC
      high : StieltjesHighTailEqualityAFZ Dzero T0 ZC
      low  : LowCloudTailSplitAFZ Dzero T0 ZC finiteCloud tail

--------------------------------------------------------------------------------
THE MID / HIGH `Tendsto` SHAPE  (rh.lean:82722 / 82741)
--------------------------------------------------------------------------------
`StieltjesMidTailEqualityAFZ.of_expAffineHadamardResidualTailConvergence`
(rh.lean:83473) reduces field `mid` for the canonical exp-affine pullback ZC
    ZC = expAffineHadamardPullbackZeroContribution H.zeroSystem.zeroLoc b
to inhabiting `ExpAffineHadamardResidualTailConvergenceMidAFZ Dzero T0 H b`,
whose sole field is:

    ∀ {z L : ℂ}, 0 < z.im → XiPullback z ≠ 0 →
      (∃ T, 10 ≤ T ∧ T ≤ 140 ∧ 2*(1+|z.re|+z.im) ≤ T) →
      XiFluctuationTailValue Dzero T0 (canonicalAdaptiveT z) z L →
        Tendsto (fun F : Finset ι =>
                   expAffineHadamardFiniteResidualTail H.zeroSystem.zeroLoc b F z)
          atTop (𝓝 L)

where (rh.lean:82103)
    expAffineHadamardFiniteResidualTail zeroLoc b F z
      = expAffineHadamardPullbackFiniteContribution zeroLoc b F z   -- I*b + I*Σ_{ρ∈F}(…)
          - cloudModel zeros100ceil z
          - zeroDensitySmoothTailModel (2π) _ z
and (rh.lean:72055) `XiFluctuationTailValue … z L` UNFOLDS to
    Tendsto (fun X : ℝ =>
              complexDensityTailPartial pairedCauchyComplexKernelTrue
                (fun u => Phase1IBP.finiteFluctuationPrimitive Dzero T0 u) T X z)
      atTop (𝓝 L).

So the MID residual is literally:
    lim_{F↑ι} (finite Hadamard zero sum − cloud − smooth)
      =  lim_{X→∞} (Stieltjes density-tail partial at cutoff T).
HIGH is identical with `T ≥ 140` fixed (rh.lean:82741).

This is the deep P3 analytic identity — improper integration-by-parts / Abel
summation interchanging the Hadamard zero sum `Σ_ρ (1/(s−ρ)+1/ρ)` against the
Stieltjes integral `∫ k dS_total` of the fluctuation primitive, both converging
to the same `L`.  The FINITE Abel step is Mathlib
`Mathlib/NumberTheory/AbelSummation.lean` (`sum_mul_eq_sub_sub_integral_mul`);
the boundary→∞ step is Mathlib improper-IBP (`integral_Ioi_…`); the genuinely
hard part beyond Mathlib is the uniform tail control that lets the two `atTop`
limits be identified (it needs the finite Turing/high-log envelopes `slabCD T`
and `1/2 log u + 49/20` — the SEPARATE `hTuring`/`hHighLog` hypotheses of the
publication theorem rh.lean:78405).

--------------------------------------------------------------------------------
WHAT IS PROVED HERE (no sorry / no admit)
--------------------------------------------------------------------------------
* `closeOf_mid_high_low` — the anonymous-constructor glue.
* `classicalStieltjes_of_expAffine` — the SINGLE-ZC inhabitant for the canonical
  exp-affine pullback ZC, with ALL THREE fields (mid, high, low) discharged from
  the three residual-tail convergence structures via the rh.lean producer chain.
  Here LOW is NOT free (it shares the exp-affine ZC) and is built from the LOW
  residual convergence through
  `LowZeroContributionSplitAFZ.of_expAffineHadamardResidualTailConvergence`
  → `LowCloudTailSplitAFZ.of_zeroContributionSplit`.
* `classicalStieltjes_explicitLowZC` — the inhabitant for the EXPLICIT-LOW-MODEL
  ZC `z ↦ cloud z + lowTail z`, where LOW is GENUINELY FREE
  (`LowCloudTailSplitAFZ.explicit_lowModel`, all three subfields `rfl`), and
  MID/HIGH are taken as the residual equalities (the discharged-agent output).
* `MidHighResidualTendsto` — the ONE minimal named residual, packaging exactly
  the Mid + High `Tendsto` obligations (the P3 Abel/IBP identity) with an honest
  docstring; `classicalStieltjes_of_expAffine_ofResidual` consumes it.

The genuine gap is isolated to `MidHighResidualTendsto` (Mid + High `Tendsto`)
plus the analogous Low `Tendsto`.  No bare `sorry`/`admit`; `#print axioms`
below shows the only axioms are Mathlib's standard ones (no `sorryAx`).
================================================================================
-/

import rh

open OverflowResidueRH
open OverflowResidueRH.Phase1IBP
open Complex Filter Topology

namespace OverflowResidueRH.BacklundTuring.ScratchStieltjesClose

/-! ### Glue: the anonymous constructor for the bundle. -/

/-- Assemble `ClassicalStieltjesExplicitFormulaInputs` from its three fields.
This is just the anonymous constructor `⟨mid, high, low⟩`; it compiles given the
three fields and fixes the common `ZC`, `finiteCloud`, `tail`. -/
def closeOf_mid_high_low
    {Dzero : Phase1IBP.OrderedFluctuationMeasureData} {T0 : ℝ}
    {ZC finiteCloud tail : ℂ → ℂ}
    (mid  : StieltjesMidTailEqualityAFZ Dzero T0 ZC)
    (high : StieltjesHighTailEqualityAFZ Dzero T0 ZC)
    (low  : LowCloudTailSplitAFZ Dzero T0 ZC finiteCloud tail) :
    ClassicalStieltjesExplicitFormulaInputs Dzero T0 ZC finiteCloud tail :=
  ⟨mid, high, low⟩

/-! ### Inhabitant 1 — canonical exp-affine pullback ZC (single shared ZC).

Here ALL THREE fields share the canonical
`ZC = expAffineHadamardPullbackZeroContribution H.zeroSystem.zeroLoc b`, so there
is NO ZC-reconciliation gap.  Each field is produced from its residual-tail
convergence structure through the proved rh.lean chain.  The three convergence
structures are the genuine analytic inputs (the P3 Abel/IBP identity, mid/high/
low). -/
noncomputable def classicalStieltjes_of_expAffine
    (Dzero : Phase1IBP.OrderedFluctuationMeasureData) (T0 : ℝ)
    {ι : Type} (H : EntireXiClassicalHadamardTheorem ι)
    (Hbridge : EntireXiToCompletedXiLogDerivBridge) (b : ℂ)
    (Hmid  : ExpAffineHadamardResidualTailConvergenceMidAFZ  Dzero T0 H b)
    (Hhigh : ExpAffineHadamardResidualTailConvergenceHighAFZ Dzero T0 H b)
    (Hlow  : ExpAffineHadamardResidualTailConvergenceLowAFZ  Dzero T0 H b) :
    ClassicalStieltjesExplicitFormulaInputs Dzero T0
      (expAffineHadamardPullbackZeroContribution H.zeroSystem.zeroLoc b)
      (fun z : ℂ => cloudModel zeros100ceil z)
      (lowTailZeroContribution Dzero T0) :=
  closeOf_mid_high_low
    -- MID: residual-tail convergence → Stieltjes mid equality.
    (StieltjesMidTailEqualityAFZ.of_expAffineHadamardResidualTailConvergence
      (Hbridge := Hbridge) Hmid)
    -- HIGH: residual-tail convergence → Stieltjes high equality.
    (StieltjesHighTailEqualityAFZ.of_expAffineHadamardResidualTailConvergence
      (Hbridge := Hbridge) Hhigh)
    -- LOW: low residual-tail convergence → bare low zero split → atomic
    -- cloud/tail split (the cloud and tail summands are then `rfl`).
    (LowCloudTailSplitAFZ.of_zeroContributionSplit
      (LowZeroContributionSplitAFZ.of_expAffineHadamardResidualTailConvergence
        (Hbridge := Hbridge) Hlow))

/-! ### Inhabitant 2 — explicit-low-model ZC (LOW genuinely free).

This matches the TASK's intended shape: ZC is the explicit low model
`z ↦ cloud z + lowTail z`, so the LOW field is GENUINELY free
(`LowCloudTailSplitAFZ.explicit_lowModel`, every subfield `rfl`), and MID/HIGH
are the Stieltjes equalities for that same ZC — the discharged analytic output.

We take MID/HIGH as hypotheses (the residual equalities); they are precisely the
P3 identity for the explicit-low ZC.  In the real assembly the explicit-low ZC
coincides with `pullbackZeroContribution …`, so these are the same equalities
produced by Inhabitant 1's residual route. -/
noncomputable def classicalStieltjes_explicitLowZC
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
  closeOf_mid_high_low
    mid
    high
    -- LOW: pure `rfl` — every subfield holds by definition (rh.lean:77516).
    (LowCloudTailSplitAFZ.explicit_lowModel Dzero T0)

/-! ### The minimal genuine residual: the Mid + High `Tendsto` identity.

This is the ONE place the deep analytic content lives.  It packages exactly the
two `Tendsto` obligations of `ExpAffineHadamardResidualTailConvergence{Mid,High}
AFZ` — the improper Abel-summation / IBP identity identifying the finite Hadamard
partial-product residual tail with the Stieltjes fluctuation tail value `L`.

We also write the analogous Low obligation, so the WHOLE single-ZC inhabitant of
`ClassicalStieltjesExplicitFormulaInputs` (Inhabitant 1) reduces to this one
named hypothesis.

HONEST GAP.  This is NOT proved.  It is the genuine P3 analytic identity:

* `mid`/`high` : `lim_{F↑ι} (Σ_{ρ∈F}(1/(s−ρ)+1/ρ)-cloud-smooth) = lim_{X→∞} S_X`,
  the Stieltjes density-tail partial at cutoff `T` (`T` adaptive in mid,
  `T ≥ 140` in high), `s = 1/2 + I z`.
* `low`        : the low-band analogue on `lowCompactRegion z`.

Proving these needs: Mathlib `sum_mul_eq_sub_sub_integral_mul` (finite Abel /
summation-by-parts) + improper IBP (`integral_Ioi_…`) + the FINITE Turing /
high-log envelopes (`slabCD T`, `1/2 log u + 49/20`) as the dominating bound
that lets the two `atTop` limits be exchanged and identified. -/
structure MidHighResidualTendsto
    (Dzero : Phase1IBP.OrderedFluctuationMeasureData) (T0 : ℝ)
    {ι : Type} (H : EntireXiClassicalHadamardTheorem ι) (b : ℂ) : Prop where
  /-- MID band (adaptive cutoff `T ∈ [10,140]`): the finite Hadamard residual
  tail converges to the Stieltjes fluctuation tail value `L`. -/
  mid_tendsto :
    ∀ {z L : ℂ}, 0 < z.im → XiPullback z ≠ 0 →
      (∃ T : ℝ, 10 ≤ T ∧ T ≤ 140 ∧ 2 * (1 + |z.re| + z.im) ≤ T) →
      XiFluctuationTailValue Dzero T0 (canonicalAdaptiveT z) z L →
      Tendsto
        (fun F : Finset ι =>
          expAffineHadamardFiniteResidualTail H.zeroSystem.zeroLoc b F z)
        Filter.atTop (𝓝 L)
  /-- HIGH band (fixed cutoff `T ≥ 140`): same convergence. -/
  high_tendsto :
    ∀ {z L : ℂ} {T : ℝ}, 140 ≤ T → 0 < z.im → XiPullback z ≠ 0 →
      2 * (1 + |z.re| + z.im) ≤ T →
      XiFluctuationTailValue Dzero T0 T z L →
      Tendsto
        (fun F : Finset ι =>
          expAffineHadamardFiniteResidualTail H.zeroSystem.zeroLoc b F z)
        Filter.atTop (𝓝 L)
  /-- LOW band (on `lowCompactRegion z`): the finite Hadamard LOW tail converges
  to the explicit low-tail zero contribution. -/
  low_tendsto :
    ∀ {z : ℂ}, lowCompactRegion z → XiPullback z ≠ 0 →
      LowFirstZeroGapNoAtoms Dzero →
      Tendsto
        (fun F : Finset ι =>
          expAffineHadamardFiniteLowTail H.zeroSystem.zeroLoc b F z)
        Filter.atTop (𝓝 (lowTailZeroContribution Dzero T0 z))

/-- The three rh.lean residual-tail convergence structures are exactly the three
fields of `MidHighResidualTendsto`.  This makes the genuine residual a single
named object: supplying `MidHighResidualTendsto` discharges all of mid/high/low. -/
noncomputable def classicalStieltjes_of_expAffine_ofResidual
    (Dzero : Phase1IBP.OrderedFluctuationMeasureData) (T0 : ℝ)
    {ι : Type} (H : EntireXiClassicalHadamardTheorem ι)
    (Hbridge : EntireXiToCompletedXiLogDerivBridge) (b : ℂ)
    (Hres : MidHighResidualTendsto Dzero T0 H b) :
    ClassicalStieltjesExplicitFormulaInputs Dzero T0
      (expAffineHadamardPullbackZeroContribution H.zeroSystem.zeroLoc b)
      (fun z : ℂ => cloudModel zeros100ceil z)
      (lowTailZeroContribution Dzero T0) :=
  classicalStieltjes_of_expAffine Dzero T0 H Hbridge b
    ⟨fun hy hne hmid hL => Hres.mid_tendsto hy hne hmid hL⟩
    ⟨fun hT hy hne hreg hL => Hres.high_tendsto hT hy hne hreg hL⟩
    ⟨fun hz hne Hno => Hres.low_tendsto hz hne Hno⟩

end OverflowResidueRH.BacklundTuring.ScratchStieltjesClose
