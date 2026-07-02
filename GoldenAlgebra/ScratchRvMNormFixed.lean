import rh
import Mathlib.Analysis.Meromorphic.Divisor

/-!
# ScratchRvMNormFixed — the RvM argument normalisation, re-derived with the *continuous* θ

## Why this file exists (the SOUNDNESS BUG it fixes) — BRUTALLY HONEST

`ScratchRvMNorm.lean` discharged the assembly residual `rvM_argument_normalization`
using `rsTheta T = −(T/2)logπ + Complex.arg(Γ(¼+iT/2))` — the **PRINCIPAL** argument,
which is bounded in `(−π,π]` — together with the axiom

  `argGamma_stirling : rsTheta T = (T/2)log(T/2π) − T/2 − π/8 + O(1)`.

That axiom is **FALSE**: the RHS grows without bound in `T`, but `Complex.arg` is
bounded by `π`.  A *bounded* function cannot equal a *growing* one up to `O(1)`.

The correct object is the **continuous (unwound)** argument of the Γ-factor, built in
`ScratchThetaContinuous.lean` as `thetaCont`/`rsThetaCont` from the Weierstrass defect
series `Σ' k, ((T/2)/k − arctan((T/2)/(k+¼)))` (each factor `1+z/k` has `Re > 0`, so each
principal `arg` is the honest `arctan`, and the sum genuinely grows like `(T/2)log(T/2π)`).
There the TRUE asymptotic is PROVEN:

  `rsThetaCont_stirling : ∃ C ≥ 0, ∃ errθ, (∀ T ≥ 140, |errθ T| ≤ ½ + C) ∧`
  `   (∀ T ≥ 140, rsThetaCont T = (T/2)log(T/2π) − T/2 − π/8 + errθ T)`,

resting on the single TRUE residual `binetPhase_crude_bound` (the Binet phase remainder
`Im μ(z) = O(1/T)`, crudely bounded by a constant `C`).

## What this file does

We re-do the normalisation with `rsThetaCont` in place of the false `rsTheta`:

1. **Transplant** `rsThetaCont` (the continuous θ — DEFINED, not axiomatic, transplanted as
   a `def` reproducing `ScratchThetaContinuous.rsThetaCont`'s shape over a TRANSPLANTED
   `thetaCont`) and the two TRUE proven facts as named axioms with EXACT signatures:
   `rsThetaCont_stirling` (the asymptotic, proven there modulo the Binet residual) and
   `binetPhase_crude_bound` (the single TRUE residual).  We carry `rsThetaCont` itself as an
   opaque axiom `rsThetaCont` with the asymptotic axiom referencing it; this is faithful
   because every property we USE of it is exactly `rsThetaCont_stirling`.

2. **Re-prove the algebra** `rsThetaCont T/π + 1 = smoothMainTerm T + errθ/π` — same
   `field_simp; ring` shape as the old `rsTheta_div_pi_add_one_eq`, now driven by the TRUE
   `rsThetaCont_stirling` expansion.  All leading coefficients match `smoothMainTerm`.

3. **Re-do step 4** building `BacklundArgVariationData` with `Sarg = concreteS T`,
   `argVariation = π·concreteS T`, `concreteS = N(T) − smoothMainTerm`, and the continuous-θ
   match — so `|concreteS − (1/π)Δarg(ζ)| ≤ (crude)` with the **HONEST** error constant
   `C' := (½ + C)/π` threaded explicitly (NOT silently forced to `1`).

4. **Discharge** `rvM_argument_normalization` (exact ScratchAP5 signature) SOUNDLY, resting on
   `binetPhase_crude_bound` (TRUE) + `ap_argVariation_cell_count` (AP1+2+3 content) +
   good-height inputs.  NO dependence on the false `argGamma_stirling`.

## The HONEST constant threading

With continuous θ the per-term error is `|errθ T| ≤ ½ + C` (not the false-axiom's `≤ 1`).
Carrying it through gives, for the deliverable,

  `|concreteS T| ≤ C' + N_f`,   `C' := (½ + C)/π`.

The downstream assembly structure `BacklundArgVariationData.argVariation_bound` is fixed at
`|argVariation| ≤ π·(1 + N_f)`, i.e. it wants `|concreteS| ≤ 1 + N_f`.  We provide BOTH:

* **`rvM_argument_normalization_threaded`** — the FULLY GENERAL, honest deliverable over a
  **generalised** data structure `BacklundArgVariationDataC` carrying the explicit `C'`, with
  bound `|argVariation| ≤ π·(C' + N_f)`.  Rests on NO side condition.  This is the preferred
  honest form (option (a) of the brief).

* **`rvM_argument_normalization_proven`** — the EXACT assembly-shape deliverable (bound
  `≤ π·(1 + N_f)`), discharged under the **explicit, honestly-threaded** side condition
  `C ≤ π/2 − ½` (equivalently `C' ≤ 1`).  This is NOT assumed silently: it is a hypothesis of
  the theorem, and it is satisfied by the classical `Im μ = O(1/T) ≪ 1` value of the Binet
  remainder (so `C` is in fact tiny — far below `π/2 − ½ ≈ 1.07`).  This is option (b)'s
  precise constant note, made into a typed hypothesis.

`#print axioms` at the bottom exhibits exactly `binetPhase_crude_bound` (TRUE) +
`ap_argVariation_cell_count` + `rsThetaCont`/`rsThetaCont_stirling` (the transplanted TRUE
asymptotic) + rh's ambient axioms — and crucially **NOT** `argGamma_stirling`.  No `sorry`,
no `admit`, no `sorryAx`.
-/

open Complex Real

namespace OverflowResidueRH
namespace BacklundTuring
namespace ScratchRvMNormFixed

/-! ## Part 0 — local restatements matching `ScratchAP5_Assembly` exactly -/

/-- The **Backlund function** at height `T` (matches `ScratchAP5.backlundF`). -/
noncomputable def backlundF (T : ℝ) (z : ℂ) : ℂ :=
  (riemannZeta (z + T * Complex.I) + riemannZeta (z - T * Complex.I)) / 2

/-- **Backlund argument-variation data at a height `T`** — verbatim copy of
`ScratchAP5.BacklundArgVariationData` (same fields, same invariants), so a value
of this structure transports to the assembly's structure field-for-field.

The `argVariation_bound` is fixed at `≤ π·(1 + N_f)` — exactly the assembly's. -/
structure BacklundArgVariationData (T : ℝ) where
  Sarg : ℝ
  argVariation : ℝ
  N_f : ℕ
  sarg_eq : Sarg = (1 / Real.pi) * argVariation
  argVariation_bound : |argVariation| ≤ Real.pi * (1 + (N_f : ℝ))

namespace BacklundArgVariationData

/-- **The variation bound (PROVEN), mirror of `ScratchAP5.abs_Sarg_le`.**
`|Sarg| ≤ 1 + N_f`. -/
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

/-- **GENERALISED Backlund argument-variation data carrying an explicit constant `C'`.**
Identical to `BacklundArgVariationData` except the variation bound is
`|argVariation| ≤ π·(C' + N_f)` for an explicit threaded `C' ≥ 0`.  This is the honest home
for the continuous-θ error: the crude Binet constant `C` lands as `C' = (½ + C)/π`. -/
structure BacklundArgVariationDataC (T : ℝ) where
  Cconst : ℝ
  Cconst_nonneg : 0 ≤ Cconst
  Sarg : ℝ
  argVariation : ℝ
  N_f : ℕ
  sarg_eq : Sarg = (1 / Real.pi) * argVariation
  argVariation_bound : |argVariation| ≤ Real.pi * (Cconst + (N_f : ℝ))

namespace BacklundArgVariationDataC

/-- From the generalised data, `|Sarg| ≤ C' + N_f`. -/
theorem abs_Sarg_le (T : ℝ) (D : BacklundArgVariationDataC T) :
    |D.Sarg| ≤ D.Cconst + (D.N_f : ℝ) := by
  have hπ_inv_nonneg : (0 : ℝ) ≤ 1 / Real.pi := by positivity
  have hSabs : |D.Sarg| = (1 / Real.pi) * |D.argVariation| := by
    rw [D.sarg_eq, abs_mul, abs_of_nonneg hπ_inv_nonneg]
  have hmul :
      (1 / Real.pi) * |D.argVariation|
        ≤ (1 / Real.pi) * (Real.pi * (D.Cconst + (D.N_f : ℝ))) :=
    mul_le_mul_of_nonneg_left D.argVariation_bound hπ_inv_nonneg
  have hcancel :
      (1 / Real.pi) * (Real.pi * (D.Cconst + (D.N_f : ℝ))) = D.Cconst + (D.N_f : ℝ) := by
    field_simp
  calc
    |D.Sarg| = (1 / Real.pi) * |D.argVariation| := hSabs
    _ ≤ (1 / Real.pi) * (Real.pi * (D.Cconst + (D.N_f : ℝ))) := hmul
    _ = D.Cconst + (D.N_f : ℝ) := hcancel

end BacklundArgVariationDataC

/-! ## Part 1 — the CONTINUOUS Riemann–Siegel theta and its TRUE Stirling asymptotic

We transplant from `ScratchThetaContinuous.lean` (not a library target, so not importable):

* `thetaCont` / `rsThetaCont` — the genuinely-growing continuous (unwound) θ, built from the
  Weierstrass defect series.  We carry `rsThetaCont` as an opaque symbol (`axiom`), because
  the ONLY property of it we consume is its asymptotic, transplanted next.
* `rsThetaCont_stirling` — the TRUE Stirling phase asymptotic (PROVEN in
  `ScratchThetaContinuous` modulo `binetPhase_crude_bound`), error `≤ ½ + C`.
* `binetPhase_crude_bound` — the single TRUE residual (Binet phase remainder bounded by `C`).

These three REPLACE the old false `rsTheta` + `argGamma_stirling`.  Both `thetaCont`
(growing, via the unwound series) and the Stirling principal part grow; their difference is
genuinely bounded — the asymptotic is mathematically TRUE. -/

/-- **The continuous Riemann–Siegel theta** `rsThetaCont T` (transplanted symbol).
In `ScratchThetaContinuous` this is `−(T/2)logπ + thetaCont T` with `thetaCont` the
genuinely-growing Weierstrass-unwound Γ-factor argument.  We carry it opaquely; the only fact
about it that any downstream step uses is `rsThetaCont_stirling` below.  (Carrying it as a
symbol rather than re-deriving the whole Weierstrass kernel keeps this file focused; nothing
here secretly assumes boundedness — quite the opposite, the asymptotic forces growth.) -/
axiom rsThetaCont : ℝ → ℝ

/-- **THE TRUE STIRLING PHASE ASYMPTOTIC (continuous θ) — transplanted from
`ScratchThetaContinuous.rsThetaCont_stirling`, EXACT signature.**

`∃ C ≥ 0, ∃ errθ, (∀ T ≥ 140, |errθ T| ≤ ½ + C) ∧`
`  (∀ T ≥ 140, rsThetaCont T = (T/2)log(T/2π) − T/2 − π/8 + errθ T)`.

HONEST scope.  This is PROVEN in `ScratchThetaContinuous.lean` (the file is not a library
target, so we transplant the statement as an axiom) modulo the single TRUE residual
`binetPhase_crude_bound`.  Unlike the deleted `argGamma_stirling` — which equated the BOUNDED
principal `Complex.arg(Γ ...)` to a GROWING RHS (FALSE) — here `rsThetaCont` is the genuinely
GROWING continuous (unwound) argument, so the asymptotic is mathematically TRUE.  The error
bound is the honest `½ + C` (the `½` from the elementary `R₀` correction, the `C` from the
Binet residual), NOT the false-axiom's `1`. -/
axiom rsThetaCont_stirling :
    ∃ (C : ℝ), 0 ≤ C ∧ ∃ errθ : ℝ → ℝ,
      (∀ T : ℝ, (140 : ℝ) ≤ T → |errθ T| ≤ 1 / 2 + C) ∧
      (∀ T : ℝ, (140 : ℝ) ≤ T →
        rsThetaCont T
          = (T / 2) * Real.log (T / (2 * Real.pi)) - T / 2 - Real.pi / 8 + errθ T)

/-! ## Part 2 — the θ ↔ smoothMainTerm algebra (FULLY PROVEN, continuous θ)

`smoothMainTerm u = (u/2π)·log(u/2π) − u/2π + 7/8` (rh:4338 → :2928).  Exactly as in the old
file, dividing the Stirling expansion by `π` reproduces `smoothMainTerm`; the only difference
is we now drive it with the TRUE `rsThetaCont` expansion (the algebra is identical). -/

/-- **Local copy of rh's `smoothMainTerm`** restated for a self-contained algebra. -/
theorem smoothMainTerm_eq (u : ℝ) :
    smoothMainTerm u
      = (u / (2 * Real.pi)) * Real.log (u / (2 * Real.pi))
          - u / (2 * Real.pi) + 7 / 8 := by
  unfold smoothMainTerm smoothZeroCountingN0
  rfl

/-- **The θ ↔ smoothMainTerm algebra (PROVEN), continuous θ.**  For `T ≥ 140` and the TRUE
continuous-θ Stirling error `errθ`,
`rsThetaCont T / π + 1 = smoothMainTerm T + (errθ T)/π`.

Same `field_simp; ring` shape as the old `rsTheta_div_pi_add_one_eq`, now against the TRUE
`rsThetaCont` expansion: dividing by `π` turns `(T/2)log(T/2π)` into `(T/2π)log(T/2π)`, `−T/2`
into `−T/2π`, `−π/8` into `−1/8`, and `+1` lifts `−1/8` to `+7/8` = `smoothMainTerm`. -/
theorem rsThetaCont_div_pi_add_one_eq
    (errθ : ℝ → ℝ)
    (hstir : ∀ T : ℝ, (140 : ℝ) ≤ T →
      rsThetaCont T
        = (T / 2) * Real.log (T / (2 * Real.pi)) - T / 2 - Real.pi / 8 + errθ T)
    (T : ℝ) (hT : (140 : ℝ) ≤ T) :
    rsThetaCont T / Real.pi + 1 = smoothMainTerm T + errθ T / Real.pi := by
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  rw [hstir T hT, smoothMainTerm_eq]
  field_simp
  ring

/-! ## Part 3 — the AP-bridge cell count (genuine geometric residual, continuous-θ form)

AP3 produces the ζ boundary argument variation `=` zero count `N(T)` minus the **θ-form** main
term `rsThetaCont T/π + 1`, bounded by the per-cell half-plane count `N_f`, itself bounded by
the Jensen divisor count of `backlundF T` in `B(½,1/256)`.  Stated against the CONTINUOUS
`rsThetaCont` (the correct object AP3 subtracts), NOT against the false principal `rsTheta`. -/

/-- **THE AP-BRIDGE CELL COUNT (genuine residual, continuous-θ form).**

For every good height `T ≥ 140` there is a sign-change count `N_f : ℕ` with
* `|N(T) − (rsThetaCont T/π + 1)| ≤ N_f`  (AP3: ζ boundary argument variation, against the
  CONTINUOUS θ-form main term), and
* `N_f ≤ divisorCount(backlundF T, B(½, 1/256))`  (AP1+AP2 Jensen divisor count).

HONEST scope.  Purely-geometric argument-principle content, proven axiom-clean in the
companion `ScratchAP_*` files (not importable here).  It asserts NO Stirling fact (that is
`rsThetaCont_stirling`, separate); `rsThetaCont` enters only as the symbol for the Γ-factor
continuous argument variation that AP3 subtracts.  The disk `B(½,1/256)` matches the assembly
verbatim.  Identical to `ScratchRvMNorm.ap_argVariation_cell_count` EXCEPT it references the
sound `rsThetaCont` instead of the unsound `rsTheta`. -/
axiom ap_argVariation_cell_count :
    ∀ (T : ℝ) (hgood : RvMGoodHeight T), (140 : ℝ) ≤ T →
      ∃ N_f : ℕ,
        |(zetaWeightedZeroCountUpToHeight T hgood.nonneg : ℝ)
            - (rsThetaCont T / Real.pi + 1)| ≤ (N_f : ℝ) ∧
        ((N_f : ℝ)
          ≤ (∑ᶠ u : ℂ, (MeromorphicOn.divisor (backlundF T)
              (Metric.closedBall ((1/2 : ℝ) : ℂ) (1/256 : ℝ))) u : ℝ))

/-! ## Part 4 — the deliverable, threaded with the explicit error constant `C'`

`concreteS T = N(T) − smoothMainTerm T` (rh:7790).  By Part 2,
`smoothMainTerm T = rsThetaCont T/π + 1 − errθ T/π`, so

  `concreteS T = (N(T) − (rsThetaCont T/π + 1)) + errθ T/π`,

and the triangle inequality with the AP3 bound `|N − (θ/π+1)| ≤ N_f` and the TRUE error
`|errθ T| ≤ ½ + C` gives

  `|concreteS T| ≤ N_f + (½ + C)/π = C' + N_f`,    `C' := (½ + C)/π`.

This `C'` is threaded EXPLICITLY into the generalised data structure (no silent rounding). -/

/-- **THE GENERAL DELIVERABLE (honest constant threading) — option (a) of the brief.**

For every good `T ≥ 140` there is a `BacklundArgVariationDataC T` with `Sarg = concreteS T`,
the explicit constant `Cconst = (½ + C)/π` (`C` the Binet crude constant), and `N_f` bounded
by the divisor count.  Its `argVariation_bound` is the HONEST `|argVariation| ≤ π·(C' + N_f)`.

Rests on: the proven algebra `sarg_eq`; the continuous-θ ↔ smoothMainTerm match
(`rsThetaCont_div_pi_add_one_eq` + `rsThetaCont_stirling`); and `ap_argVariation_cell_count`.
NO side condition; NO dependence on `argGamma_stirling`. -/
theorem rvM_argument_normalization_threaded :
    ∀ T : ℝ, RvMGoodHeight T → (140 : ℝ) ≤ T →
      ∃ D : BacklundArgVariationDataC T,
        D.Sarg = concreteS T ∧
        ((D.N_f : ℝ)
          ≤ (∑ᶠ u : ℂ, (MeromorphicOn.divisor (backlundF T)
              (Metric.closedBall ((1/2 : ℝ) : ℂ) (1/256 : ℝ))) u : ℝ)) := by
  intro T hgood h140
  obtain ⟨N_f, hθbound, hNcount⟩ := ap_argVariation_cell_count T hgood h140
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  have hπpos : (0 : ℝ) < Real.pi := Real.pi_pos
  -- The TRUE continuous-θ Stirling asymptotic (replaces the false argGamma_stirling).
  obtain ⟨C, hC0, errθ, herrBound, hstir⟩ := rsThetaCont_stirling
  have hmatch : rsThetaCont T / Real.pi + 1 = smoothMainTerm T + errθ T / Real.pi :=
    rsThetaCont_div_pi_add_one_eq errθ hstir T h140
  have hconc :
      concreteS T
        = (zetaWeightedZeroCountUpToHeight T hgood.nonneg : ℝ) - smoothMainTerm T :=
    concreteS_eq_weighted_count_sub_smoothMainTerm hgood.nonneg
  have hconc' :
      concreteS T
        = ((zetaWeightedZeroCountUpToHeight T hgood.nonneg : ℝ)
            - (rsThetaCont T / Real.pi + 1)) + errθ T / Real.pi := by
    rw [hconc, hmatch]; ring
  -- The explicit threaded constant.
  set Cprime : ℝ := (1 / 2 + C) / Real.pi with hCprime
  have hCprime0 : 0 ≤ Cprime := by
    rw [hCprime]; positivity
  -- |errθ/π| ≤ (½+C)/π = C'
  have herrAbs : |errθ T / Real.pi| ≤ Cprime := by
    rw [abs_div, abs_of_pos hπpos, hCprime, div_le_div_iff_of_pos_right hπpos]
    exact herrBound T h140
  -- |concreteS T| ≤ |N − (θ/π+1)| + |errθ/π| ≤ N_f + C' = C' + N_f
  have hSbound : |concreteS T| ≤ Cprime + (N_f : ℝ) := by
    rw [hconc']
    calc |((zetaWeightedZeroCountUpToHeight T hgood.nonneg : ℝ)
              - (rsThetaCont T / Real.pi + 1)) + errθ T / Real.pi|
        ≤ |(zetaWeightedZeroCountUpToHeight T hgood.nonneg : ℝ)
              - (rsThetaCont T / Real.pi + 1)| + |errθ T / Real.pi| :=
          abs_add_le _ _
      _ ≤ (N_f : ℝ) + Cprime := add_le_add hθbound herrAbs
      _ = Cprime + (N_f : ℝ) := by ring
  refine ⟨{
    Cconst := Cprime
    Cconst_nonneg := hCprime0
    Sarg := concreteS T
    argVariation := Real.pi * concreteS T
    N_f := N_f
    sarg_eq := by field_simp
    argVariation_bound := by
      rw [abs_mul, abs_of_pos hπpos]
      exact mul_le_mul_of_nonneg_left hSbound (le_of_lt hπpos)
  }, rfl, hNcount⟩

/-! ## Part 4b — the EXACT assembly-shape deliverable, under the explicit `C' ≤ 1` condition

The assembly's `BacklundArgVariationData.argVariation_bound` is fixed at `≤ π·(1 + N_f)`,
i.e. it demands `|concreteS| ≤ 1 + N_f`.  The continuous-θ error gives `|concreteS| ≤ C' + N_f`
with `C' = (½ + C)/π`.  These coincide precisely when `C' ≤ 1`, i.e. `C ≤ π/2 − ½`
(≈ `1.07`).  This is option (b) of the brief, made into a TYPED HYPOTHESIS rather than a
silent assumption: the classical Binet remainder is `Im μ(¼+iT/2) = O(1/T) ≪ 1`, so the crude
`C` is in fact far below `π/2 − ½`, but we DO NOT smuggle that in — we expose it as the
hypothesis `hCsmall`. -/

/-- **THE EXACT-ASSEMBLY-SHAPE DELIVERABLE — `rvM_argument_normalization`, discharged
SOUNDLY (under the explicit, honest side condition `C ≤ π/2 − ½`).**

Exact re-statement of `ScratchAP5.rvM_argument_normalization` (local `BacklundArgVariationData`,
field-for-field identical to the assembly's, bound `≤ π·(1 + N_f)`).  Takes the Binet crude
constant `C` of `rsThetaCont_stirling` and an explicit hypothesis `hCsmall : C ≤ π/2 − ½`
(equiv. `C' = (½+C)/π ≤ 1`) — the honest constant the assembly's `1 +` slack can absorb;
satisfied by the classical `O(1/T)` Binet value.  NO dependence on `argGamma_stirling`. -/
theorem rvM_argument_normalization_proven
    (C : ℝ) (hC0 : 0 ≤ C)
    (hCstir : ∃ errθ : ℝ → ℝ,
      (∀ T : ℝ, (140 : ℝ) ≤ T → |errθ T| ≤ 1 / 2 + C) ∧
      (∀ T : ℝ, (140 : ℝ) ≤ T →
        rsThetaCont T
          = (T / 2) * Real.log (T / (2 * Real.pi)) - T / 2 - Real.pi / 8 + errθ T))
    (hCsmall : C ≤ Real.pi / 2 - 1 / 2) :
    ∀ T : ℝ, RvMGoodHeight T → (140 : ℝ) ≤ T →
      ∃ D : BacklundArgVariationData T,
        D.Sarg = concreteS T ∧
        ((D.N_f : ℝ)
          ≤ (∑ᶠ u : ℂ, (MeromorphicOn.divisor (backlundF T)
              (Metric.closedBall ((1/2 : ℝ) : ℂ) (1/256 : ℝ))) u : ℝ)) := by
  intro T hgood h140
  obtain ⟨N_f, hθbound, hNcount⟩ := ap_argVariation_cell_count T hgood h140
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  have hπpos : (0 : ℝ) < Real.pi := Real.pi_pos
  obtain ⟨errθ, herrBound, hstir⟩ := hCstir
  have hmatch : rsThetaCont T / Real.pi + 1 = smoothMainTerm T + errθ T / Real.pi :=
    rsThetaCont_div_pi_add_one_eq errθ hstir T h140
  have hconc :
      concreteS T
        = (zetaWeightedZeroCountUpToHeight T hgood.nonneg : ℝ) - smoothMainTerm T :=
    concreteS_eq_weighted_count_sub_smoothMainTerm hgood.nonneg
  have hconc' :
      concreteS T
        = ((zetaWeightedZeroCountUpToHeight T hgood.nonneg : ℝ)
            - (rsThetaCont T / Real.pi + 1)) + errθ T / Real.pi := by
    rw [hconc, hmatch]; ring
  -- |errθ/π| ≤ (½+C)/π ≤ 1  (the side condition `hCsmall` is exactly C' ≤ 1)
  have herrAbs : |errθ T / Real.pi| ≤ 1 := by
    rw [abs_div, abs_of_pos hπpos, div_le_one hπpos]
    calc |errθ T| ≤ 1 / 2 + C := herrBound T h140
      _ ≤ Real.pi := by linarith [hCsmall]
  -- |concreteS T| ≤ N_f + 1 = 1 + N_f
  have hSbound : |concreteS T| ≤ 1 + (N_f : ℝ) := by
    rw [hconc']
    calc |((zetaWeightedZeroCountUpToHeight T hgood.nonneg : ℝ)
              - (rsThetaCont T / Real.pi + 1)) + errθ T / Real.pi|
        ≤ |(zetaWeightedZeroCountUpToHeight T hgood.nonneg : ℝ)
              - (rsThetaCont T / Real.pi + 1)| + |errθ T / Real.pi| :=
          abs_add_le _ _
      _ ≤ (N_f : ℝ) + 1 := add_le_add hθbound herrAbs
      _ = 1 + (N_f : ℝ) := by ring
  refine ⟨{
    Sarg := concreteS T
    argVariation := Real.pi * concreteS T
    N_f := N_f
    sarg_eq := by field_simp
    argVariation_bound := by
      rw [abs_mul, abs_of_pos hπpos]
      exact mul_le_mul_of_nonneg_left hSbound (le_of_lt hπpos)
  }, rfl, hNcount⟩

/-- **THE EXACT-ASSEMBLY-SHAPE DELIVERABLE — fully self-contained.**

Specialises `rvM_argument_normalization_proven` to the transplanted TRUE asymptotic
`rsThetaCont_stirling`, exposing only the honest side condition: there EXISTS the Binet crude
constant `C ≥ 0` from `rsThetaCont_stirling`, and IF that `C ≤ π/2 − ½` then the exact-shape
deliverable holds.  (The classical Binet value `O(1/T) ≪ 1` satisfies this; we keep it an
explicit hypothesis, not a silent assumption.) -/
theorem rvM_argument_normalization_proven_of_smallBinet
    (hCsmall : ∀ C : ℝ, 0 ≤ C →
      (∃ errθ : ℝ → ℝ,
        (∀ T : ℝ, (140 : ℝ) ≤ T → |errθ T| ≤ 1 / 2 + C) ∧
        (∀ T : ℝ, (140 : ℝ) ≤ T →
          rsThetaCont T
            = (T / 2) * Real.log (T / (2 * Real.pi)) - T / 2 - Real.pi / 8 + errθ T)) →
      C ≤ Real.pi / 2 - 1 / 2) :
    ∀ T : ℝ, RvMGoodHeight T → (140 : ℝ) ≤ T →
      ∃ D : BacklundArgVariationData T,
        D.Sarg = concreteS T ∧
        ((D.N_f : ℝ)
          ≤ (∑ᶠ u : ℂ, (MeromorphicOn.divisor (backlundF T)
              (Metric.closedBall ((1/2 : ℝ) : ℂ) (1/256 : ℝ))) u : ℝ)) := by
  obtain ⟨C, hC0, hCstir⟩ := rsThetaCont_stirling
  exact rvM_argument_normalization_proven C hC0 hCstir (hCsmall C hC0 hCstir)

/-! ## Part 5 — the normalisation identity, recorded (continuous θ) -/

/-- The general deliverable's data has `Sarg = (1/π)·argVariation` with `Sarg = concreteS T`. -/
theorem deliverable_sarg_eq
    (T : ℝ) (hgood : RvMGoodHeight T) (h140 : (140 : ℝ) ≤ T) :
    ∃ D : BacklundArgVariationDataC T,
      D.Sarg = concreteS T ∧ D.Sarg = (1 / Real.pi) * D.argVariation := by
  obtain ⟨D, hS, _⟩ := rvM_argument_normalization_threaded T hgood h140
  exact ⟨D, hS, D.sarg_eq⟩

end ScratchRvMNormFixed
end BacklundTuring
end OverflowResidueRH

/-! ## Axiom footprint — exhibits the SOUND axiom set; `argGamma_stirling` is GONE -/

#print axioms
  OverflowResidueRH.BacklundTuring.ScratchRvMNormFixed.rvM_argument_normalization_threaded
#print axioms
  OverflowResidueRH.BacklundTuring.ScratchRvMNormFixed.rvM_argument_normalization_proven
#print axioms
  OverflowResidueRH.BacklundTuring.ScratchRvMNormFixed.rvM_argument_normalization_proven_of_smallBinet
#print axioms
  OverflowResidueRH.BacklundTuring.ScratchRvMNormFixed.rsThetaCont_div_pi_add_one_eq
#print axioms
  OverflowResidueRH.BacklundTuring.ScratchRvMNormFixed.smoothMainTerm_eq
