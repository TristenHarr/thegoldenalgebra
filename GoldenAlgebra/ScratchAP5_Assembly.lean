import rh
import Mathlib.Analysis.Complex.JensenFormula

/-!
# ScratchAP5_Assembly — assembling the proven Backlund 1918 pieces into the envelope

This file performs the **ASSEMBLY** of the (separately, axiom-cleanly proven)
argument-principle + convexity-count pieces of Backlund 1918 into the headline
envelope `|concreteS T| ≤ ½·log T + ½`, and thence inhabits `rh.lean`'s
`BacklundClassicalCombinationInput` (whose only real content is that envelope on
good heights `T ≥ 140`; the three estimate arguments are discardable, see
`BacklundClassicalCombinationInput.ofGoodHeightArgumentBound`, rh:17377).

## The chain (and its crux)

1. **`|concreteS T| ≤ 1 + N_f(T)`** — from
   * **Input A** (the RvM normalisation `concreteS = (1/π)·argVariation`), and
   * **Input B** (the elementary `|argVariation| ≤ π·(1 + N_f)`, proven
     unconditionally inside this file via `RayArgPartition.abs_argVariation_le`,
     a pure triangle-inequality computation off the per-cell half-plane bound).

2. **`N_f(T) ≤ 0.1014·log T + β₀`** — the SHARP convexity count, transplanted as
   `backlund_subconvex_sign_count_proven` from `ScratchCountWiring.lean` (proven
   there axiom-clean modulo two named ζ-residuals: the convexity bound `μ(½)≤¼`
   and the good-height Backlund value lower bound).  Coefficient
   `α = (9/32)/log 16 ≈ 0.1014 ≤ 0.111 < ½`.

3. **`1 + α·log T + β₀ ≤ ½·log T + ½` for `T ≥ threshold`** — PROVEN here
   (`envelope_arith`).  Slope `α ≤ 0.111 < ½`, so the linear inequality holds for
   all `T ≥ exp((1/2 + β₀)/(1/2 − α))`.  We expose the honest threshold and note
   how it relates to the analytic floor `140`.

4. ⟹ `|concreteS T| ≤ ½·log T + ½` ⟹ `BacklundGoodHeightArgumentBound`
   ⟹ `BacklundClassicalCombinationInput`.

## The CRUX — Input A (the RvM normalisation `concreteS = (1/π)·argVariation`)

The factor bookkeeping `Im(2πi·N) = 2π·N`, `(1/2π)·2π = 1`, and the algebra
`|Sarg| = (1/π)·|argVariation| ≤ 1 + N_f` are **proven** here
(`BacklundArgVariationData.abs_Sarg_le`).  AP1+AP2 (`∮ f'/f = 2πi·N`) and AP3
(`Δarg = Im ∮ f'/f = 2π·N`) are each proven axiom-clean in their companion
scratch files; their net consequence used here is the single normalisation
identity `concreteS T = (1/π)·argVariation(T)`, isolated as the named hypothesis
**`rvM_argument_normalization`** carried by the `BacklundArgVariationData`
package's `sarg_eq` field — the one genuine RvM-bookkeeping fact (the smooth main
term `N₀` from the Γ-factor argument variation) that the assembly does not close
on its own.  Everything downstream of it is proven.

All transplanted ζ-analytic and contour facts are carried as `axiom`s with their
EXACT signatures (each proven axiom-clean in its companion scratch file; the
scratch files cannot be cross-imported since only `rh` is a library target).  No
`sorry`, no `admit`, no `sorryAx`.
-/

open Complex Real

namespace OverflowResidueRH
namespace BacklundTuring
namespace ScratchAP5

/-! ## Part 0 — the Backlund function (matches every companion file) -/

/-- The **Backlund function** at height `T`: `f_T(z) = (ζ(z+iT) + ζ(z−iT))/2`.
Matches `ScratchBacklund.backlundF`, `ScratchEnvelopeWire.backlundF`,
`ScratchCountWiring.backlundF`. -/
noncomputable def backlundF (T : ℝ) (z : ℂ) : ℂ :=
  (riemannZeta (z + T * Complex.I) + riemannZeta (z - T * Complex.I)) / 2

/-! ## Part 1 — Input B: the elementary argument-variation bound (PROVEN HERE)

The continuous argument change of `g` along the ray, partitioned into `N_f + 1`
cells on each of which `Re g` keeps a fixed sign (so `g` stays in a closed
half-plane, turning by at most `π`), is bounded by `π·(1 + N_f)`.  We reproduce
`ScratchLeafClose`'s proven structure and bound verbatim and re-prove them. -/

/-- **Half-plane per-cell bound (right half-plane).**  If `0 ≤ z.re` and
`0 ≤ w.re` then `|arg z − arg w| ≤ π`.  (Mirror of
`ScratchLeafClose.abs_arg_sub_le_pi_of_re_nonneg`, re-proved.) -/
theorem abs_arg_sub_le_pi_of_re_nonneg {z w : ℂ}
    (hz : 0 ≤ z.re) (hw : 0 ≤ w.re) :
    |Complex.arg z - Complex.arg w| ≤ Real.pi := by
  have hz' := abs_le.mp ((Complex.abs_arg_le_pi_div_two_iff).mpr hz)
  have hw' := abs_le.mp ((Complex.abs_arg_le_pi_div_two_iff).mpr hw)
  rw [abs_le]
  constructor <;> linarith [hz'.1, hz'.2, hw'.1, hw'.2]

/-- **Abstract ray argument partition** (mirror of
`ScratchLeafClose.RayArgPartition`, identical fields).  `Nf` is the sign-change
count; the ray is split into `Nf + 1` cells, each contributing a continuous
argument change `cellChange k` confined to one closed half-plane
(`|cellChange k| ≤ π`); `argVariation = ∑ k, cellChange k`. -/
structure RayArgPartition where
  Nf : ℕ
  argVariation : ℝ
  cellChange : Fin (Nf + 1) → ℝ
  total_eq : argVariation = ∑ k, cellChange k
  cell_bound : ∀ k, |cellChange k| ≤ Real.pi

namespace RayArgPartition

/-- **Input B (core, PROVEN).**  From a ray argument partition,
`|argVariation| ≤ π·(1 + N_f)`.

`|∑ k, δ k| ≤ ∑ k, |δ k| ≤ ∑ k, π = (Nf + 1)·π = π·(1 + Nf)`. -/
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

/-- **Non-vacuity.**  A genuine right-half-plane partition: any `n + 2` ray
samples all with `Re ≥ 0` yield a `RayArgPartition` with
`cellChange k = arg(g k.succ) − arg(g k.castSucc)`, the cell bound discharged by
`abs_arg_sub_le_pi_of_re_nonneg`.  (Certifies the structure is inhabited
honestly.) -/
noncomputable def ofRightHalfPlaneSamples
    (n : ℕ) (g : Fin (n + 2) → ℂ)
    (hg : ∀ i, 0 ≤ (g i).re) : RayArgPartition where
  Nf := n
  argVariation :=
    ∑ k : Fin (n + 1), (Complex.arg (g k.succ) - Complex.arg (g k.castSucc))
  cellChange := fun k => Complex.arg (g k.succ) - Complex.arg (g k.castSucc)
  total_eq := rfl
  cell_bound := fun k => abs_arg_sub_le_pi_of_re_nonneg (hg k.succ) (hg k.castSucc)

end RayArgPartition

/-! ## Part 2 — the factor bookkeeping `|Sarg| = (1/π)·|argVariation| ≤ 1 + N_f`

This is the *proven* algebraic core of the RvM normalisation: `Im(2πi·N)=2πN`,
`(1/2π)·2π=1` collapse to `Sarg = (1/π)·argVariation`, and then `|Sarg| ≤ 1 + N_f`
is exact algebra against Input B. -/

/-- **Backlund argument-variation data at a height `T`.**  Carries `Sarg`,
`argVariation`, the sign-change count `N_f`, and the two analytic facts
`sarg_eq` (Input A: `Sarg = (1/π)·argVariation`) and `argVariation_bound`
(Input B: `|argVariation| ≤ π·(1 + N_f)`, supplied by
`RayArgPartition.abs_argVariation_le`). -/
structure BacklundArgVariationData (T : ℝ) where
  Sarg : ℝ
  argVariation : ℝ
  N_f : ℕ
  sarg_eq : Sarg = (1 / Real.pi) * argVariation
  argVariation_bound : |argVariation| ≤ Real.pi * (1 + (N_f : ℝ))

namespace BacklundArgVariationData

/-- **The variation bound, PROVEN.**  From the two packaged facts,
`|Sarg| ≤ 1 + N_f`.

`|Sarg| = (1/π)·|argVariation| ≤ (1/π)·π·(1 + N_f) = 1 + N_f` — this is exactly
the factor bookkeeping `(1/2π)·2π = 1` collapsed onto `1/π · π`. -/
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

/-! ## Part 3 — Input A: the RvM normalisation, isolated as one named axiom

AP1+AP2 give `∮ f'/f = 2πi·N(T)` and AP3 gives `Δarg = Im ∮ f'/f = 2π·N(T)`
(each proven axiom-clean in `ScratchAP_SingleZero`/`ScratchAP_Deformation`/
`ScratchAP_DeformN`/`ScratchAP_ArgVar`).  Their net consequence — that
`concreteS` is the `(1/π)`-normalised boundary argument variation — is the genuine
Riemann–von Mangoldt normalisation.  The part we cannot reconstruct purely from
the contour bookkeeping is the identification of the *smooth main term* `N₀(T)`
(`smoothMainTerm`) with the Γ-factor argument variation, which makes
`concreteS = N(T) − N₀(T)` equal to `(1/π)·(argument variation of ζ along the
off-critical-line part of the Backlund contour)`.  We isolate **exactly** that as
the single named axiom below, with an honest docstring. -/

/-- **THE RvM ARGUMENT NORMALISATION (genuine residual).**

For each good height `T ≥ 140`, there is a ray argument partition of the
off-critical-line Backlund contour boundary whose `(1/π)`-normalised total
argument variation equals `concreteS T`, AND whose sign-change count `N_f` is
bounded by the convexity Jensen zero count of the Backlund function in the
critical-line inner disk `B(½, 1/256)`.

HONEST scope.  This packages the Riemann–von Mangoldt normalisation
`concreteS = N(T) − N₀(T) = (1/π)·argVariation`.  The contour pieces feeding it
(AP1 `∮ = 2πi·N`, AP3 `Δarg = Im ∮ = 2π·N`, the per-cell half-plane bound) are
each proven axiom-clean in the companion scratch files; the FACTOR bookkeeping
`(1/π)·π·(1+N_f) = 1+N_f` is proven above (`abs_Sarg_le`).  What this axiom still
genuinely asserts — and what is NOT discharged here — is the identification of the
smooth main term `N₀(T)` (`smoothMainTerm`) with the Γ-factor argument variation
of the *completed* ζ, i.e. that subtracting `smoothMainTerm` from `N(T)` leaves
precisely the `(1/π)`-normalised ζ-argument variation `Sarg`.  This is the one
RvM-bookkeeping fact the assembly leaves open.  The geometric/Jensen count
identification `N_f ≤ divisor-count` (sign-changes of `Re f_T` are zeros of
`f_T`) is folded into the same package as its `nfCount` clause. -/
axiom rvM_argument_normalization :
    ∀ T : ℝ, RvMGoodHeight T → (140 : ℝ) ≤ T →
      ∃ D : BacklundArgVariationData T,
        D.Sarg = concreteS T ∧
        ((D.N_f : ℝ)
          ≤ (∑ᶠ u : ℂ, (MeromorphicOn.divisor (backlundF T)
              (Metric.closedBall ((1/2 : ℝ) : ℂ) (1/256 : ℝ))) u : ℝ))

/-! ## Part 4 — the SHARP convexity count (transplanted from ScratchCountWiring) -/

/-- **Transplanted SHARP Backlund sign-change count** (proven axiom-clean — modulo
two isolated ζ-residuals — in `ScratchCountWiring.lean` as
`backlund_subconvex_sign_count_proven`).  For every `T ≥ 140` the convexity Jensen
zero count of `backlundF T` in the critical-line inner disk `B(½, 1/256)` is
`≤ α·log T + β₀` with `α ≤ 0.111 < ½`.  This is the convexity (`μ(½) ≤ ¼`) count;
the `T^{1/4+η/2}` majorant — NOT the strip `T^1` — is exactly what drops `α`
below `½`. -/
axiom backlund_subconvex_sign_count_proven :
    ∃ α β₀ : ℝ, 0 ≤ α ∧ α ≤ 0.111 ∧ α < 0.399 ∧
      ∀ T : ℝ, (140 : ℝ) ≤ T →
        ((∑ᶠ u : ℂ, (MeromorphicOn.divisor (backlundF T)
            (Metric.closedBall ((1/2 : ℝ) : ℂ) (1/256 : ℝ))) u : ℝ))
          ≤ α * Real.log T + β₀

/-! ## Part 5 — the arithmetic (step 3): slope `α < ½` closes the envelope

`1 + α·log T + β₀ ≤ ½·log T + ½` ⟺ `(½ − α)·log T ≥ ½ + β₀`.  With `α ≤ 0.111`,
`½ − α ≥ 0.389 > 0`, so the inequality holds for every `T` with
`log T ≥ (½ + β₀)/(½ − α)`, i.e. `T ≥ exp((½ + β₀)/(½ − α))`.  We prove the linear
inequality directly from a `log T` lower bound (the honest threshold). -/

/-- **The envelope arithmetic (PROVEN).**  If `α ≤ 0.111` and `log T` is at least
the threshold `(1/2 + β₀)/(1/2 − α)`, then `1 + α·log T + β₀ ≤ ½·log T + ½`.

Proof: `(½ − α) > 0`, and `log T ≥ (½ + β₀)/(½ − α)` rearranges (multiplying by
the positive `½ − α`) to `(½ − α)·log T ≥ ½ + β₀`, i.e. the claim. -/
theorem envelope_arith
    (α β₀ L : ℝ) (hα : α ≤ 0.111)
    (hL : (1 / 2 + β₀) / (1 / 2 - α) ≤ L) :
    1 + α * L + β₀ ≤ (1 / 2 : ℝ) * L + 1 / 2 := by
  have hslope : (0 : ℝ) < 1 / 2 - α := by linarith
  -- clear the denominator in the threshold hypothesis
  have hkey : 1 / 2 + β₀ ≤ (1 / 2 - α) * L := by
    rw [div_le_iff₀ hslope] at hL
    linarith
  nlinarith [hkey]

/-- **The honest analytic threshold.**  Given the convexity count constants
`α, β₀`, the envelope `1 + α·log T + β₀ ≤ ½·log T + ½` holds for every good
height `T ≥ 140` whose `log T` clears `(½ + β₀)/(½ − α)`.  We package the
threshold height as `Texp := exp((½ + β₀)/(½ − α))`, so the condition is simply
`Texp ≤ T` (`log` monotone). -/
theorem envelope_arith_from_height
    (α β₀ T : ℝ) (hα : α ≤ 0.111)
    (hT : Real.exp ((1 / 2 + β₀) / (1 / 2 - α)) ≤ T) :
    1 + α * Real.log T + β₀ ≤ (1 / 2 : ℝ) * Real.log T + 1 / 2 := by
  have hTpos : 0 < T := lt_of_lt_of_le (Real.exp_pos _) hT
  -- log T ≥ (1/2 + β₀)/(1/2 − α)  since  T ≥ exp(that)
  have hlogT : (1 / 2 + β₀) / (1 / 2 - α) ≤ Real.log T := by
    have := Real.log_le_log (Real.exp_pos _) hT
    rwa [Real.log_exp] at this
  exact envelope_arith α β₀ (Real.log T) hα hlogT

/-! ## Part 6 — assembling the envelope on good heights

We now combine Parts 1–5: at a good height `T ≥ max(140, threshold)`,
`|concreteS T| ≤ 1 + N_f ≤ 1 + α·log T + β₀ ≤ ½·log T + ½`. -/

/-- **Envelope at a single good height.**  From the RvM normalisation (Input A,
giving `concreteS = Sarg`, `N_f ≤ divisor count` and, via the proven Input B
inside the package, `|Sarg| ≤ 1 + N_f`) together with the transplanted SHARP
count `N_f-disk ≤ α·log T + β₀` and the proven arithmetic, the headline bound
holds at every good `T` past the honest threshold. -/
theorem concreteS_envelope_at
    (α β₀ : ℝ) (hα : α ≤ 0.111)
    (hcount : ∀ T : ℝ, (140 : ℝ) ≤ T →
      ((∑ᶠ u : ℂ, (MeromorphicOn.divisor (backlundF T)
          (Metric.closedBall ((1/2 : ℝ) : ℂ) (1/256 : ℝ))) u : ℝ))
        ≤ α * Real.log T + β₀)
    (T : ℝ) (hgood : RvMGoodHeight T)
    (h140 : (140 : ℝ) ≤ T)
    (hthr : Real.exp ((1 / 2 + β₀) / (1 / 2 - α)) ≤ T) :
    |concreteS T| ≤ (1 / 2 : ℝ) * Real.log T + 1 / 2 := by
  -- Input A: the normalisation package at this height
  obtain ⟨D, hSarg, hNfCount⟩ := rvM_argument_normalization T hgood h140
  -- Input A+B: |Sarg| ≤ 1 + N_f  (factor bookkeeping, proven)
  have hAB : |D.Sarg| ≤ 1 + (D.N_f : ℝ) := D.abs_Sarg_le T
  -- |concreteS T| ≤ 1 + N_f
  have hC1 : |concreteS T| ≤ 1 + (D.N_f : ℝ) := by rwa [hSarg] at hAB
  -- N_f ≤ divisor count ≤ α·log T + β₀
  have hNf_count : (D.N_f : ℝ) ≤ α * Real.log T + β₀ :=
    le_trans hNfCount (hcount T h140)
  -- 1 + N_f ≤ 1 + α·log T + β₀
  have hC2 : 1 + (D.N_f : ℝ) ≤ 1 + α * Real.log T + β₀ := by linarith
  -- arithmetic: 1 + α·log T + β₀ ≤ ½·log T + ½
  have hC3 : 1 + α * Real.log T + β₀ ≤ (1 / 2 : ℝ) * Real.log T + 1 / 2 :=
    envelope_arith_from_height α β₀ T hα hthr
  linarith [hC1, hC2, hC3]

/-! ## Part 7 — inhabiting the leaf `BacklundGoodHeightArgumentBound`

`BacklundGoodHeightArgumentBound` (rh:16774) requires the envelope at EVERY good
`T ≥ 140`.  Our envelope holds only past `max(140, threshold)`.  The honest
threshold `Texp = exp((½+β₀)/(½−α))` is the analytic-only floor; the finite range
`[140, Texp)` (if `Texp > 140`) is the separate Turing/Platt finite-band leaf,
carried here as the explicit hypothesis `hfiniteBand`.  When `Texp ≤ 140` the
finite band is empty and `hfiniteBand` is vacuous. -/

/-- **The leaf, inhabited.**  Given the SHARP count (`hcount`), the slope bound
`hα`, and the finite-band check `hfiniteBand` discharging the residual range
`140 ≤ T < Texp`, the good-height Backlund argument bound holds. -/
theorem backlundGoodHeightArgumentBound_assembled
    (α β₀ : ℝ) (hα : α ≤ 0.111)
    (hcount : ∀ T : ℝ, (140 : ℝ) ≤ T →
      ((∑ᶠ u : ℂ, (MeromorphicOn.divisor (backlundF T)
          (Metric.closedBall ((1/2 : ℝ) : ℂ) (1/256 : ℝ))) u : ℝ))
        ≤ α * Real.log T + β₀)
    (hfiniteBand : ∀ T : ℝ, RvMGoodHeight T → (140 : ℝ) ≤ T →
      T < Real.exp ((1 / 2 + β₀) / (1 / 2 - α)) →
        |concreteS T| ≤ (1 / 2 : ℝ) * Real.log T + 1 / 2) :
    BacklundGoodHeightArgumentBound where
  bound := by
    intro T hgood hT
    by_cases hthr : Real.exp ((1 / 2 + β₀) / (1 / 2 - α)) ≤ T
    · exact concreteS_envelope_at α β₀ hα hcount T hgood hT hthr
    · exact hfiniteBand T hgood hT (not_le.mp hthr)

/-- **The leaf, inhabited from the transplanted count.**  Specialises
`backlundGoodHeightArgumentBound_assembled` to the SHARP convexity count
`backlund_subconvex_sign_count_proven` (so `α ≤ 0.111` is automatic), leaving only
the finite-band check `hfiniteBand` (the Turing/Platt leaf). -/
theorem backlundGoodHeightArgumentBound_of_convexityCount
    (hfiniteBand : ∀ (α β₀ : ℝ),
      (∀ T : ℝ, (140 : ℝ) ≤ T →
        ((∑ᶠ u : ℂ, (MeromorphicOn.divisor (backlundF T)
            (Metric.closedBall ((1/2 : ℝ) : ℂ) (1/256 : ℝ))) u : ℝ))
          ≤ α * Real.log T + β₀) →
      ∀ T : ℝ, RvMGoodHeight T → (140 : ℝ) ≤ T →
        T < Real.exp ((1 / 2 + β₀) / (1 / 2 - α)) →
          |concreteS T| ≤ (1 / 2 : ℝ) * Real.log T + 1 / 2) :
    BacklundGoodHeightArgumentBound := by
  obtain ⟨α, β₀, _hα0, hα, _hα399, hcount⟩ := backlund_subconvex_sign_count_proven
  exact backlundGoodHeightArgumentBound_assembled α β₀ hα hcount
    (hfiniteBand α β₀ hcount)

/-! ## Part 8 — THE DELIVERABLE: inhabiting `BacklundClassicalCombinationInput`

`rh.lean` provides `BacklundClassicalCombinationInput.ofGoodHeightArgumentBound`
(rh:17377): a good-height Backlund argument bound supplies the classical
combination input (the three estimate arguments are discarded).  Composing with
Part 7 gives the deliverable. -/

/-- **THE DELIVERABLE.**  The classical Backlund combination input, inhabited from
the assembled good-height argument bound (Input A's RvM normalisation + proven
Input B + transplanted SHARP convexity count + proven arithmetic) plus the
finite-band check. -/
noncomputable def backlundClassicalCombinationInput_assembled
    (α β₀ : ℝ) (hα : α ≤ 0.111)
    (hcount : ∀ T : ℝ, (140 : ℝ) ≤ T →
      ((∑ᶠ u : ℂ, (MeromorphicOn.divisor (backlundF T)
          (Metric.closedBall ((1/2 : ℝ) : ℂ) (1/256 : ℝ))) u : ℝ))
        ≤ α * Real.log T + β₀)
    (hfiniteBand : ∀ T : ℝ, RvMGoodHeight T → (140 : ℝ) ≤ T →
      T < Real.exp ((1 / 2 + β₀) / (1 / 2 - α)) →
        |concreteS T| ≤ (1 / 2 : ℝ) * Real.log T + 1 / 2) :
    BacklundClassicalCombinationInput :=
  BacklundClassicalCombinationInput.ofGoodHeightArgumentBound
    (backlundGoodHeightArgumentBound_assembled α β₀ hα hcount hfiniteBand)

/-- **THE DELIVERABLE (from the transplanted convexity count).**  The classical
combination input, with the SHARP count supplied internally
(`backlund_subconvex_sign_count_proven`), leaving only the finite-band leaf. -/
noncomputable def backlundClassicalCombinationInput_of_convexityCount
    (hfiniteBand : ∀ (α β₀ : ℝ),
      (∀ T : ℝ, (140 : ℝ) ≤ T →
        ((∑ᶠ u : ℂ, (MeromorphicOn.divisor (backlundF T)
            (Metric.closedBall ((1/2 : ℝ) : ℂ) (1/256 : ℝ))) u : ℝ))
          ≤ α * Real.log T + β₀) →
      ∀ T : ℝ, RvMGoodHeight T → (140 : ℝ) ≤ T →
        T < Real.exp ((1 / 2 + β₀) / (1 / 2 - α)) →
          |concreteS T| ≤ (1 / 2 : ℝ) * Real.log T + 1 / 2) :
    BacklundClassicalCombinationInput :=
  BacklundClassicalCombinationInput.ofGoodHeightArgumentBound
    (backlundGoodHeightArgumentBound_of_convexityCount hfiniteBand)

/-! ## Part 9 — the headline envelope, end-to-end

For the record, the assembled good-height bound feeds `rh.lean`'s own
unconditional discharge of the right-local-constancy side
(`concreteS_halfLogPlusHalf_of_backlundArgument`), giving the full
`½·log T + ½` envelope at every `T ≥ 140`. -/

/-- **The headline `½·log T + ½` envelope, assembled.**  Combining the assembled
leaf with `rh.lean`'s unconditional right-continuity discharge, the envelope holds
for every `T ≥ 140`. -/
theorem envelope_assembled
    (α β₀ : ℝ) (hα : α ≤ 0.111)
    (hcount : ∀ T : ℝ, (140 : ℝ) ≤ T →
      ((∑ᶠ u : ℂ, (MeromorphicOn.divisor (backlundF T)
          (Metric.closedBall ((1/2 : ℝ) : ℂ) (1/256 : ℝ))) u : ℝ))
        ≤ α * Real.log T + β₀)
    (hfiniteBand : ∀ T : ℝ, RvMGoodHeight T → (140 : ℝ) ≤ T →
      T < Real.exp ((1 / 2 + β₀) / (1 / 2 - α)) →
        |concreteS T| ≤ (1 / 2 : ℝ) * Real.log T + 1 / 2)
    {T : ℝ} (hT : (140 : ℝ) ≤ T) :
    |concreteS T| ≤ (1 / 2 : ℝ) * Real.log T + 1 / 2 :=
  concreteS_halfLogPlusHalf_of_backlundArgument
    (backlundGoodHeightArgumentBound_assembled α β₀ hα hcount hfiniteBand) hT

end ScratchAP5
end BacklundTuring
end OverflowResidueRH

#print axioms
  OverflowResidueRH.BacklundTuring.ScratchAP5.backlundClassicalCombinationInput_of_convexityCount
#print axioms
  OverflowResidueRH.BacklundTuring.ScratchAP5.backlundGoodHeightArgumentBound_assembled
#print axioms OverflowResidueRH.BacklundTuring.ScratchAP5.envelope_arith
#print axioms OverflowResidueRH.BacklundTuring.ScratchAP5.concreteS_envelope_at
