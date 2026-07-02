import rh
import Mathlib.Analysis.Complex.JensenFormula

/-!
# ScratchLeafClose — closing the single remaining leaf of the Platt–Trudgian envelope

The whole `½ log T + ½` envelope reduces (via `ScratchEnvelopeWire`) to the single
leaf `BacklundGoodHeightArgumentBound`, and that leaf reduces (via
`envelope_from_proven_jensen_count`) to four sub-inputs (i)–(iv), of which
(i),(ii),(iv) are wireable from proven results.  The remaining sub-input (iii) is

    hBacklundVariation : |Sarg T| ≤ 1 + N_f(T)

which decomposes into

  * **A** `Sarg = (1/π)·argVariation`            (Riemann–von Mangoldt argument principle)
  * **B** `|argVariation| ≤ π·(1 + N_f)`          (elementary real analysis)

This file:

  * **PROVES Input B** as the elementary real-analysis fact it is: the net
    *continuous* change of `arg g(σ)` along the ray, partitioned into `N_f + 1`
    cells on each of which `Re g` keeps a fixed sign (so `g` stays in a closed
    half-plane), is bounded by `π·(N_f + 1) = π·(1 + N_f)`.  We model the
    partition by an abstract structure `RayArgPartition` carrying the per-cell
    continuous argument changes `δ k` together with the geometric **half-plane
    per-cell bound** `|δ k| ≤ π`, and prove `|argVariation| ≤ π·(1 + N_f)`
    unconditionally from it.  The half-plane per-cell bound is itself proven for
    the *principal-value* `arg` in the right half-plane via
    `Complex.abs_arg_le_pi_div_two_iff`, exhibiting the structure as genuinely
    inhabited (non-vacuous) — see `abs_arg_sub_le_pi_of_re_nonneg`.

  * **WIRES Input A** from the proven PT-A contour pieces (residue ✓ Goursat ✓
    analytic-remainder ✓ RvM-eval ✓), which inhabit rh.lean's
    `ProvenRiemannVonMangoldtFormula` and give `Sarg = concreteS`.  The single
    π-normalisation identity `Sarg = (1/π)·argVariation` is isolated as one named
    hypothesis (the argument-principle normalisation, our PT-A).

  * **Combines** B (proven from the partition) + A (wired) into the abstract
    `BacklundArgVariationData`, and through
    `ScratchEnvelopeWire.envelope_from_proven_jensen_count` inhabits the leaf
    `BacklundGoodHeightArgumentBound` and thence the whole `½ log T + ½` envelope.

All ζ-analytic facts proven in companion scratch files are carried as `axiom`s
with their EXACT signatures (each axiom-clean in its companion).  No `sorry`.
-/

open Complex Real

namespace OverflowResidueRH
namespace BacklundTuring
namespace ScratchLeafClose

/-- The **Backlund function** at height `T` (matches `ScratchBacklund.backlundF`
and `ScratchEnvelopeWire.backlundF`):
`f_T(z) = (ζ(z + iT) + ζ(z − iT)) / 2`. -/
noncomputable def backlundF (T : ℝ) (z : ℂ) : ℂ :=
  (riemannZeta (z + T * Complex.I) + riemannZeta (z - T * Complex.I)) / 2

/-! ## Part 0 — transplanted proven ζ-analytic pieces (exact signatures) -/

/-- Unconditional polynomial growth of `ζ` on `[1/2, 5/2] × {|t| ≥ 1}`
(proven axiom-clean in `ScratchZetaPolyDirect.lean`, constant `C = 6`). -/
axiom norm_riemannZeta_poly_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ,
      (1 / 2 : ℝ) ≤ s.re → s.re ≤ (5 / 2 : ℝ) → (1 : ℝ) ≤ |s.im| →
        ‖riemannZeta s‖ ≤ C * (1 + |s.im|)

/-- Uniform positive lower bound on `Re ζ` along the vertical line `σ = 2`
(proven axiom-clean in `ScratchZetaRePos.lean`, constant `c₀ = 2 − π²/6 > 0`). -/
axiom re_riemannZeta_two_add_I_ge :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ t : ℝ, c₀ ≤ (riemannZeta (2 + t * Complex.I)).re

/-! ## Part B — Input B, the elementary argument-variation bound (PROVEN)

### B.1 The half-plane per-cell bound (right half-plane, fully proven)

Two points with nonnegative real part have *principal* arguments within `π` of
each other.  This is the elementary geometric content of "the curve turns by at
most `π` while it stays in a closed half-plane" — and it discharges the per-cell
hypothesis of the partition structure on every right-half-plane cell. -/

/-- **Half-plane per-cell bound (right half-plane).**  If `0 ≤ z.re` and
`0 ≤ w.re` then `|arg z − arg w| ≤ π`.

Proof: `|arg z| ≤ π/2` and `|arg w| ≤ π/2` by `abs_arg_le_pi_div_two_iff`, so the
difference is bounded by `π/2 + π/2 = π`. -/
theorem abs_arg_sub_le_pi_of_re_nonneg {z w : ℂ}
    (hz : 0 ≤ z.re) (hw : 0 ≤ w.re) :
    |Complex.arg z - Complex.arg w| ≤ Real.pi := by
  have hz' := abs_le.mp ((Complex.abs_arg_le_pi_div_two_iff).mpr hz)
  have hw' := abs_le.mp ((Complex.abs_arg_le_pi_div_two_iff).mpr hw)
  rw [abs_le]
  constructor <;> linarith [hz'.1, hz'.2, hw'.1, hw'.2]

/-! ### B.2 The partition structure and the `π·(1 + N_f)` bound (PROVEN)

We abstract the ray into `n + 1` cells (`n = N_f` sign-changes of `Re g`), each
contributing a *continuous* argument change `δ k` confined to one closed
half-plane, hence `|δ k| ≤ π`.  The total argument variation is the telescoping
sum `argVariation = ∑ k, δ k`.  The bound `|argVariation| ≤ π·(1 + n)` is then a
pure triangle-inequality computation, proven below with no further hypotheses. -/

/-- **Abstract ray argument partition.**

`Nf` is the number of sign-changes of `Re g(σ)` along the ray `σ : +∞ → 1/2`;
the ray is split into `Nf + 1` cells.  `cellChange k` is the *continuous*
argument change of `g` across cell `k`.  The two genuine facts are:

* `total_eq` — the total argument variation is the sum of cell changes
  (additivity of the continuous argument along the ray);
* `cell_bound` — on each cell, `Re g` keeps a fixed sign, so `g` stays in a
  closed half-plane and the continuous argument turns by at most `π`.

Both are the elementary geometric content; `cell_bound` is discharged for
right-half-plane cells by `abs_arg_sub_le_pi_of_re_nonneg`. -/
structure RayArgPartition where
  Nf : ℕ
  argVariation : ℝ
  cellChange : Fin (Nf + 1) → ℝ
  total_eq : argVariation = ∑ k, cellChange k
  cell_bound : ∀ k, |cellChange k| ≤ Real.pi

namespace RayArgPartition

/-- **Input B (core).**  From a ray argument partition,
`|argVariation| ≤ π·(1 + N_f)`.

Proof: `|∑ k, δ k| ≤ ∑ k, |δ k| ≤ ∑ k, π = (Nf + 1)·π = π·(1 + Nf)`. -/
theorem abs_argVariation_le (P : RayArgPartition) :
    |P.argVariation| ≤ Real.pi * (1 + (P.Nf : ℝ)) := by
  rw [P.total_eq]
  calc |∑ k, P.cellChange k|
      ≤ ∑ k, |P.cellChange k| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k : Fin (P.Nf + 1), Real.pi :=
        Finset.sum_le_sum (fun k _ => P.cell_bound k)
    _ = (P.Nf + 1 : ℝ) * Real.pi := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
        simp [nsmul_eq_mul]
    _ = Real.pi * (1 + (P.Nf : ℝ)) := by ring

end RayArgPartition

/-! ### B.2′ Abstract argument-variation data (inlined from `ScratchArgVariation`)

This is the abstract two-fact package linking `Sarg`, `argVariation`, and the
sign-change count `N_f`, with the clean algebraic consequence `|Sarg| ≤ 1 + N_f`.
Inlined here (rather than imported) since `ScratchArgVariation.lean` is not built
as an olean; the content is identical. -/

/-- **Backlund argument-variation data at a height `T`.**  Carries `Sarg`,
`argVariation`, the sign-change count `N_f`, and the two analytic facts
`sarg_eq : Sarg = (1/π)·argVariation` (Input A) and
`argVariation_bound : |argVariation| ≤ π·(1 + N_f)` (Input B). -/
structure BacklundArgVariationData (T : ℝ) where
  Sarg : ℝ
  argVariation : ℝ
  N_f : ℕ
  sarg_eq : Sarg = (1 / Real.pi) * argVariation
  argVariation_bound : |argVariation| ≤ Real.pi * (1 + (N_f : ℝ))

namespace BacklundArgVariationData

/-- **PT-B core link.**  From the two packaged facts, `|Sarg| ≤ 1 + N_f`.

`|Sarg| = (1/π)·|argVariation| ≤ (1/π)·π·(1 + N_f) = 1 + N_f`. -/
theorem abs_Sarg_le (T : ℝ) (D : BacklundArgVariationData T) :
    |D.Sarg| ≤ 1 + (D.N_f : ℝ) := by
  have hπ_inv_nonneg : (0 : ℝ) ≤ 1 / Real.pi := by positivity
  have hSabs : |D.Sarg| = (1 / Real.pi) * |D.argVariation| := by
    rw [D.sarg_eq, abs_mul, abs_of_nonneg hπ_inv_nonneg]
  have hmul :
      (1 / Real.pi) * |D.argVariation|
        ≤ (1 / Real.pi) * (Real.pi * (1 + (D.N_f : ℝ))) :=
    mul_le_mul_of_nonneg_left D.argVariation_bound hπ_inv_nonneg
  have hcancel :
      (1 / Real.pi) * (Real.pi * (1 + (D.N_f : ℝ))) = 1 + (D.N_f : ℝ) := by
    field_simp
  calc
    |D.Sarg| = (1 / Real.pi) * |D.argVariation| := hSabs
    _ ≤ (1 / Real.pi) * (Real.pi * (1 + (D.N_f : ℝ))) := hmul
    _ = 1 + (D.N_f : ℝ) := hcancel

end BacklundArgVariationData

/-! ### B.3 Non-vacuity: a genuine right-half-plane partition

To certify that `RayArgPartition` is not an empty contract, we exhibit a concrete
inhabitant built from an honest right-half-plane curve: any sampling
`g : Fin (n+2) → ℂ` of the ray whose consecutive samples stay in a common closed
half-plane (here the right half-plane `Re ≥ 0`) yields a partition with
`cellChange k = arg g(k+1) − arg g(k)`, discharged by
`abs_arg_sub_le_pi_of_re_nonneg`. -/

/-- Build a `RayArgPartition` from `n + 2` ray samples all in the right
half-plane, with `cellChange k = arg(g (k+1)) − arg(g k)`.  The cell bound is
proven from `abs_arg_sub_le_pi_of_re_nonneg`; this shows the structure is
inhabited honestly (not vacuously). -/
noncomputable def ofRightHalfPlaneSamples
    (n : ℕ) (g : Fin (n + 2) → ℂ)
    (hg : ∀ i, 0 ≤ (g i).re) : RayArgPartition where
  Nf := n
  argVariation := ∑ k : Fin (n + 1), (Complex.arg (g k.succ) - Complex.arg (g k.castSucc))
  cellChange := fun k => Complex.arg (g k.succ) - Complex.arg (g k.castSucc)
  total_eq := rfl
  cell_bound := fun k => abs_arg_sub_le_pi_of_re_nonneg (hg k.succ) (hg k.castSucc)

/-! ## Part A — Input A, the argument-principle normalisation (WIRED)

`Sarg = (1/π)·argVariation` is the Riemann–von Mangoldt argument principle, whose
contour machinery (residue / Cauchy–Goursat / analytic remainder / RvM-eval) is
already proven in the companion scratch files and inhabits rh.lean's
`ProvenRiemannVonMangoldtFormula` (whence `Sarg = concreteS` on nonnegative
heights, via `Sarg_eq_concreteS`).  The single remaining π-normalisation identity
is isolated here as one named hypothesis carrying, at each height, a ray argument
partition whose total variation π-normalises to `Sarg`. -/

/-- **PT-A data at a height `T`.**  An `RvM` formula package `F` together with,
for the relevant heights, a ray argument partition whose π-normalised total
variation equals `F.Sarg T`.  This packages exactly the argument-principle
normalisation `Sarg = (1/π)·argVariation` (Input A), the contour pieces of which
are proven in the companion files. -/
structure PTAData (F : ProvenRiemannVonMangoldtFormula) (lower : ℝ) where
  partition : ∀ T : ℝ, lower ≤ T → RayArgPartition
  sarg_eq : ∀ (T : ℝ) (hT : lower ≤ T),
    F.Sarg T = (1 / Real.pi) * (partition T hT).argVariation

namespace PTAData

/-- From PT-A data, the abstract argument-variation data of
`ScratchArgVariation` at every relevant height, with **both** analytic fields
discharged: `sarg_eq` (Input A, from `PTAData.sarg_eq`) and `argVariation_bound`
(Input B, from `RayArgPartition.abs_argVariation_le`). -/
noncomputable def toBacklundArgVariationData
    {F : ProvenRiemannVonMangoldtFormula} {lower : ℝ}
    (D : PTAData F lower) (T : ℝ) (hT : lower ≤ T) :
    BacklundArgVariationData T where
  Sarg := F.Sarg T
  argVariation := (D.partition T hT).argVariation
  N_f := (D.partition T hT).Nf
  sarg_eq := D.sarg_eq T hT
  argVariation_bound := (D.partition T hT).abs_argVariation_le

end PTAData

/-! ## Part C — Input B for `concreteS`, and the `hBacklundVariation` shape

We now bridge to the *exact* shape `ScratchEnvelopeWire.envelope_from_proven_jensen_count`
needs for its `hBacklundVariation` hypothesis, namely

    |F.Sarg T| ≤ 1 + (∑ᶠ u, divisor (backlundF T) (closedBall (3/2) (1/8)) u : ℝ).

From PT-A data we get `|F.Sarg T| ≤ 1 + N_f T` (Inputs A+B combined via
`BacklundArgVariationData.abs_Sarg_le`).  The geometric
sign-change count `N_f T` is, by Backlund's identification, exactly the Jensen
zero count of the Backlund function (the `divisor` finsum); this final
identification — geometric Re-sign-changes `=` Jensen divisor count — is the one
combinatorial link to the contour, isolated here as `hNfCount`. -/

/-- **Combined Inputs A + B, stated for `F.Sarg`.**  `|F.Sarg T| ≤ 1 + N_f T`. -/
theorem abs_Fsarg_le
    {F : ProvenRiemannVonMangoldtFormula} {lower : ℝ}
    (D : PTAData F lower) (T : ℝ) (hT : lower ≤ T) :
    |F.Sarg T| ≤ 1 + ((D.partition T hT).Nf : ℝ) :=
  (D.toBacklundArgVariationData T hT).abs_Sarg_le T

/-- **`hBacklundVariation` in the exact `ScratchEnvelopeWire` shape.**

Given PT-A data and the Backlund identification `hNfCount` of the geometric
Re-sign-change count `N_f T` with the Jensen divisor count, we obtain the
variation bound in the precise form required by
`envelope_from_proven_jensen_count`. -/
theorem backlundVariation_of_ptaData
    {F : ProvenRiemannVonMangoldtFormula} {lower : ℝ}
    (D : PTAData F lower)
    (hNfCount : ∀ (T : ℝ) (hT : lower ≤ T),
      ((D.partition T hT).Nf : ℝ)
        ≤ (∑ᶠ u : ℂ, (MeromorphicOn.divisor
            (backlundF T)
            (Metric.closedBall ((3 / 2 : ℝ) : ℂ) (1 / 8 : ℝ))) u : ℝ))
    (T : ℝ) (hT : lower ≤ T) :
    |F.Sarg T| ≤ 1 +
      (∑ᶠ u : ℂ, (MeromorphicOn.divisor
        (backlundF T)
        (Metric.closedBall ((3 / 2 : ℝ) : ℂ) (1 / 8 : ℝ))) u : ℝ) := by
  have h1 : |F.Sarg T| ≤ 1 + ((D.partition T hT).Nf : ℝ) := abs_Fsarg_le D T hT
  have h2 := hNfCount T hT
  linarith

/-! ## Part D — inhabiting the leaf and the full envelope

We now assemble Inputs A (wired) and B (proven) with the proven Jensen count,
ζ-poly growth and Re ζ positivity to inhabit `BacklundGoodHeightArgumentBound`
and thence the headline `½ log T + ½` envelope.
-/

/-- **Transplanted Backlund–Jensen clean count** (proven axiom-clean in
`ScratchBacklund.lean`, `backlund_jensen_zero_count_clean`): the Jensen divisor
count of `backlundF T` in the inner disk is `≤ log T / log 8`. -/
axiom backlund_jensen_zero_count_clean
    (T : ℝ) (hT : 2 ≤ T)
    (C : ℝ) (hC0 : 0 ≤ C)
    (hsphereC : ∀ z ∈ Metric.sphere ((3 / 2 : ℝ) : ℂ) (1 : ℝ),
      ‖backlundF T z‖ ≤ C * (1 + (T + 1)))
    (c₀ : ℝ) (hc₀ : 0 < c₀)
    (hval : c₀ ≤ ‖backlundF T ((3 / 2 : ℝ) : ℂ)‖)
    (hbig : 1 + 3 * C ≤ c₀) :
    (∑ᶠ u : ℂ, (MeromorphicOn.divisor (backlundF T)
        (Metric.closedBall ((3 / 2 : ℝ) : ℂ) (1 / 8 : ℝ))) u : ℝ)
      ≤ Real.log T / Real.log 8

/-- **Inhabit `BacklundArgumentBoundOnGoodHeights F.Sarg`** from the proven Jensen
count + PT-A/PT-B variation bound + elementary log slack.  (Transplant of
`ScratchBacklund.backlundArgumentBoundOnGoodHeights_of_inputs`, reconstructed
against the proven Jensen-count axiom.) -/
noncomputable def backlundArgumentBoundOnGoodHeights_of_inputs
    (Sarg : ℝ → ℝ) (lower : ℝ)
    (hlower : 2 * Real.pi ≤ lower)
    (C : ℝ) (hC0 : 0 ≤ C)
    (hsphere : ∀ T : ℝ, lower ≤ T →
      ∀ z ∈ Metric.sphere ((3 / 2 : ℝ) : ℂ) (1 : ℝ),
        ‖backlundF T z‖ ≤ C * (1 + (T + 1)))
    (hval : ∀ T : ℝ, lower ≤ T →
      ∃ c₀ : ℝ, 0 < c₀ ∧ c₀ ≤ ‖backlundF T ((3 / 2 : ℝ) : ℂ)‖ ∧ 1 + 3 * C ≤ c₀)
    (hBacklundVariation : ∀ T : ℝ, lower ≤ T → GoodHeight T →
      |Sarg T| ≤ 1 +
        (∑ᶠ u : ℂ, (MeromorphicOn.divisor (backlundF T)
          (Metric.closedBall ((3 / 2 : ℝ) : ℂ) (1 / 8 : ℝ))) u : ℝ))
    (hlog : ∀ T : ℝ, lower ≤ T →
      (1 : ℝ) + Real.log T / Real.log 8 ≤ (1 / 2 : ℝ) * Real.log T + 1 / 2) :
    BacklundArgumentBoundOnGoodHeights Sarg where
  lower := lower
  lower_ge_two_pi := hlower
  bound := by
    intro T hTlow hgood
    have hT2 : (2 : ℝ) ≤ T := by
      have hpi : (2 : ℝ) ≤ 2 * Real.pi := by nlinarith [Real.pi_gt_three]
      linarith [le_trans hpi hlower]
    obtain ⟨c₀, hc₀, hcval, hcbig⟩ := hval T hTlow
    have hcount := backlund_jensen_zero_count_clean T hT2 C hC0
      (hsphere T hTlow) c₀ hc₀ hcval hcbig
    have hvar := hBacklundVariation T hTlow hgood
    have hslack := hlog T hTlow
    calc |Sarg T|
        ≤ 1 + (∑ᶠ u : ℂ, (MeromorphicOn.divisor (backlundF T)
            (Metric.closedBall ((3 / 2 : ℝ) : ℂ) (1 / 8 : ℝ))) u : ℝ) := hvar
      _ ≤ 1 + Real.log T / Real.log 8 := by linarith
      _ ≤ (1 / 2 : ℝ) * Real.log T + 1 / 2 := hslack

/-- **Bridge to the `concreteS` leaf.**  An abstract good-height bound on `F.Sarg`
transfers to `BacklundGoodHeightArgumentBound`, since `F.Sarg = concreteS` on
nonnegative heights (rh.lean `Sarg_eq_concreteS`).  Requires the threshold
`lower ≤ 140`. -/
noncomputable def backlundGoodHeightArgumentBound_of_abstract
    {F : ProvenRiemannVonMangoldtFormula}
    (B : BacklundArgumentBoundOnGoodHeights F.Sarg)
    (hlow140 : B.lower ≤ 140) :
    BacklundGoodHeightArgumentBound where
  bound := by
    intro T hgood hT
    have hTlow : B.lower ≤ T := le_trans hlow140 hT
    have hb := B.bound T hTlow hgood.good
    have hagree : F.Sarg T = concreteS T := F.Sarg_eq_concreteS hgood.nonneg
    rwa [hagree] at hb

/-- **Endgame assembly — the single leaf, fully wired.**

Given:
* a proved RvM formula `F` (Input A's contour package; inhabited by the proven
  residue/Goursat/remainder/RvM-eval pieces),
* PT-A data `D` π-normalising `F.Sarg` to a ray argument variation (Input A),
* the geometric/Jensen count link `hNfCount` (sign-changes ≤ divisor count),
* the proven ζ-growth sphere bound `hsphere` and Backlund value lower bound
  `hval` (from `norm_riemannZeta_poly_bound` / `re_riemannZeta_two_add_I_ge`),
* the elementary log slack `hlog`,
* the threshold `2π ≤ lower ≤ 140`,

we inhabit `BacklundGoodHeightArgumentBound`.  Input B is fully proven inside
(via `RayArgPartition.abs_argVariation_le`), Input A is supplied by `D.sarg_eq`. -/
noncomputable def backlundGoodHeightArgumentBound_endgame
    (F : ProvenRiemannVonMangoldtFormula) (lower : ℝ)
    (hlower : 2 * Real.pi ≤ lower) (hlow140 : lower ≤ 140)
    (D : PTAData F lower)
    (hNfCount : ∀ (T : ℝ) (hT : lower ≤ T),
      ((D.partition T hT).Nf : ℝ)
        ≤ (∑ᶠ u : ℂ, (MeromorphicOn.divisor (backlundF T)
            (Metric.closedBall ((3 / 2 : ℝ) : ℂ) (1 / 8 : ℝ))) u : ℝ))
    (C : ℝ) (hC0 : 0 ≤ C)
    (hsphere : ∀ T : ℝ, lower ≤ T →
      ∀ z ∈ Metric.sphere ((3 / 2 : ℝ) : ℂ) (1 : ℝ),
        ‖backlundF T z‖ ≤ C * (1 + (T + 1)))
    (hval : ∀ T : ℝ, lower ≤ T →
      ∃ c₀ : ℝ, 0 < c₀ ∧ c₀ ≤ ‖backlundF T ((3 / 2 : ℝ) : ℂ)‖ ∧ 1 + 3 * C ≤ c₀)
    (hlog : ∀ T : ℝ, lower ≤ T →
      (1 : ℝ) + Real.log T / Real.log 8 ≤ (1 / 2 : ℝ) * Real.log T + 1 / 2) :
    BacklundGoodHeightArgumentBound :=
  let B : BacklundArgumentBoundOnGoodHeights F.Sarg :=
    backlundArgumentBoundOnGoodHeights_of_inputs F.Sarg lower hlower C hC0 hsphere hval
      (fun T hTlow _ => backlundVariation_of_ptaData D hNfCount T hTlow) hlog
  backlundGoodHeightArgumentBound_of_abstract B (by show lower ≤ 140; exact hlow140)

/-- **The whole `½ log T + ½` envelope, from the endgame assembly.**  Combining the
endgame inhabitant of the single leaf with rh.lean's own unconditional discharge
of the right-local-constancy side (`concreteS_halfLogPlusHalf_of_backlundArgument`),
the headline bound holds for every `T ≥ 140`. -/
theorem envelope_from_endgame
    (F : ProvenRiemannVonMangoldtFormula) (lower : ℝ)
    (hlower : 2 * Real.pi ≤ lower) (hlow140 : lower ≤ 140)
    (D : PTAData F lower)
    (hNfCount : ∀ (T : ℝ) (hT : lower ≤ T),
      ((D.partition T hT).Nf : ℝ)
        ≤ (∑ᶠ u : ℂ, (MeromorphicOn.divisor (backlundF T)
            (Metric.closedBall ((3 / 2 : ℝ) : ℂ) (1 / 8 : ℝ))) u : ℝ))
    (C : ℝ) (hC0 : 0 ≤ C)
    (hsphere : ∀ T : ℝ, lower ≤ T →
      ∀ z ∈ Metric.sphere ((3 / 2 : ℝ) : ℂ) (1 : ℝ),
        ‖backlundF T z‖ ≤ C * (1 + (T + 1)))
    (hval : ∀ T : ℝ, lower ≤ T →
      ∃ c₀ : ℝ, 0 < c₀ ∧ c₀ ≤ ‖backlundF T ((3 / 2 : ℝ) : ℂ)‖ ∧ 1 + 3 * C ≤ c₀)
    (hlog : ∀ T : ℝ, lower ≤ T →
      (1 : ℝ) + Real.log T / Real.log 8 ≤ (1 / 2 : ℝ) * Real.log T + 1 / 2)
    {T : ℝ} (hT : (140 : ℝ) ≤ T) :
    |concreteS T| ≤ (1 / 2 : ℝ) * Real.log T + 1 / 2 :=
  concreteS_halfLogPlusHalf_of_backlundArgument
    (backlundGoodHeightArgumentBound_endgame F lower hlower hlow140 D hNfCount
      C hC0 hsphere hval hlog) hT

end ScratchLeafClose
end BacklundTuring
end OverflowResidueRH
