/-
  RHSharpPL.lean — SEAM 2 of the convexity tower, discharged across the module boundary.

  Producer→consumer seam:
    `phragmenLindelof_flatten` : axiom in `ScratchSharpPL`  ←  THEOREM in `RHConvexityTower`.

  This module IMPORTS `RHConvexityTower` and reuses ITS proven scaffolding
  (`wgt`, `Lbase`, `pExp`, `ellInterp`, `wgt_norm_eq`, `cross_term_bounded`,
  `norm_Lbase_ge/le/rpow_le`, `ellInterp_eq`) so the weight `wgt` appearing in the
  producer theorem `phragmenLindelof_flatten` is THE SAME `wgt` consumed by the
  fully-proven `unwind_sharp`.  Consequently the `ScratchSharpPL.phragmenLindelof_flatten`
  transplant AXIOM is DELETED here: `tWeightedPL_linear_sharp` is proven from the IMPORTED
  theorem `RHConvexityTower.…ScratchHalfStripPL.phragmenLindelof_flatten`.

  The only residual under `tWeightedPL_linear_sharp` is the genuine
  `verticalStrip_lower_reflection` flowing in from the producer.
-/
import RHConvexityTower

open Complex Real Set
open scoped Real
open Complex.HadamardThreeLines

noncomputable section

namespace OverflowResidueRH.BacklundTuring.RHSharpPL

-- Reuse the producer's scaffolding verbatim (same defs ⇒ same `wgt` ⇒ the imported
-- `phragmenLindelof_flatten` feeds `unwind_sharp` with NO def mismatch).
open OverflowResidueRH.BacklundTuring.ScratchHalfStripPL

/-! ## The two-sided cross-factor bound (the only Part-2 lemma not already in the producer). -/

/-- **Two-sided bound on the cross-term exponential factor** (copy of
`ScratchSharpPL.wgt_cross_factor_bounds`, now referencing the producer's `pExp`/`Lbase`). -/
theorem wgt_cross_factor_bounds {l u α β lam : ℝ} (hlu : l < u) {σ t : ℝ}
    (hσl : l ≤ σ) (hσu : σ ≤ u) (ht : 1 ≤ t) (hlam : 1 ≤ lam) :
    Real.exp (-(|β - α| * max |l| |u| / (u - l)))
        ≤ Real.exp ((pExp l u α β ((σ : ℂ) + (t : ℂ) * Complex.I)).im
            * Complex.arg (Lbase σ t lam))
      ∧ Real.exp ((pExp l u α β ((σ : ℂ) + (t : ℂ) * Complex.I)).im
            * Complex.arg (Lbase σ t lam))
          ≤ Real.exp (|β - α| * max |l| |u| / (u - l)) := by
  have hb := cross_term_bounded (l := l) (u := u) (α := α) (β := β) (lam := lam)
    hlu hσl hσu ht hlam
  rw [abs_le] at hb
  exact ⟨Real.exp_le_exp.mpr hb.1, Real.exp_le_exp.mpr hb.2⟩

/-! ## The unwind (PROVEN; copy of `ScratchSharpPL.unwind_sharp`, producer defs). -/

/-- **The unwind (PROVEN).**  From a constant bound `‖Fval·w(σ+iτ)‖ ≤ C_G` to the sharp
interpolated `F`-bound `‖Fval‖ ≤ C_G·exp(K)·D·τ^{ℓ(σ)}`. -/
theorem unwind_sharp {l u α β lam : ℝ} (hlu : l < u) {σ τ : ℝ}
    (hσl : l ≤ σ) (hσu : σ ≤ u) (hτ : 1 ≤ τ) (hlam : 1 ≤ lam)
    (Fval : ℂ) {CG : ℝ}
    (hG : ‖Fval * wgt l u α β lam ((σ : ℂ) + (τ : ℂ) * Complex.I)‖ ≤ CG) :
    ‖Fval‖
      ≤ CG * Real.exp (|β - α| * max |l| |u| / (u - l))
          * max (((2 * (1 + |σ| + lam)) : ℝ) ^ (ellInterp l u α β σ)) 1
          * τ ^ (ellInterp l u α β σ) := by
  set s : ℂ := (σ : ℂ) + (τ : ℂ) * Complex.I with hs
  set ℓ : ℝ := ellInterp l u α β σ with hℓ
  set K : ℝ := |β - α| * max |l| |u| / (u - l) with hK
  set D : ℝ := max (((2 * (1 + |σ| + lam)) : ℝ) ^ ℓ) 1 with hD
  have hwpos : 0 < ‖wgt l u α β lam s‖ := by
    rw [wgt, norm_pos_iff]; exact Complex.exp_ne_zero _
  have hwn : ‖wgt l u α β lam s‖
      = ‖Lbase σ τ lam‖ ^ (-ℓ)
        * Real.exp ((pExp l u α β s).im * Complex.arg (Lbase σ τ lam)) := by
    rw [hℓ, hs]; exact wgt_norm_eq hlu hτ hlam
  have hFnorm : ‖Fval‖ = ‖Fval * wgt l u α β lam s‖ / ‖wgt l u α β lam s‖ := by
    rw [norm_mul, mul_div_assoc, div_self (ne_of_gt hwpos), mul_one]
  have hcrossL : Real.exp (-K)
      ≤ Real.exp ((pExp l u α β s).im * Complex.arg (Lbase σ τ lam)) := by
    rw [hK, hs]; exact (wgt_cross_factor_bounds hlu hσl hσu hτ hlam).1
  have hLnpos : 0 < ‖Lbase σ τ lam‖ ^ (-ℓ) := by
    apply Real.rpow_pos_of_pos
    have : 0 < τ := by linarith
    exact lt_of_lt_of_le this (norm_Lbase_ge hτ hlam)
  have hwlow : ‖Lbase σ τ lam‖ ^ (-ℓ) * Real.exp (-K) ≤ ‖wgt l u α β lam s‖ := by
    rw [hwn]
    apply mul_le_mul_of_nonneg_left hcrossL (le_of_lt hLnpos)
  have hwlow_pos : 0 < ‖Lbase σ τ lam‖ ^ (-ℓ) * Real.exp (-K) := by positivity
  rw [hFnorm]
  have hstep1 : ‖Fval * wgt l u α β lam s‖ / ‖wgt l u α β lam s‖
      ≤ CG / (‖Lbase σ τ lam‖ ^ (-ℓ) * Real.exp (-K)) := by
    apply div_le_div₀ (le_trans (norm_nonneg _) hG) hG hwlow_pos hwlow
  refine le_trans hstep1 ?_
  have hLflip : (‖Lbase σ τ lam‖ ^ (-ℓ))⁻¹ = ‖Lbase σ τ lam‖ ^ ℓ := by
    rw [← Real.rpow_neg (norm_nonneg _), neg_neg]
  have hexpflip : (Real.exp (-K))⁻¹ = Real.exp K := by
    rw [← Real.exp_neg, neg_neg]
  have heq : CG / (‖Lbase σ τ lam‖ ^ (-ℓ) * Real.exp (-K))
      = CG * Real.exp K * ‖Lbase σ τ lam‖ ^ ℓ := by
    rw [div_eq_mul_inv, mul_inv, hLflip, hexpflip]; ring
  rw [heq]
  have hLrpow : ‖Lbase σ τ lam‖ ^ ℓ ≤ D * τ ^ ℓ := norm_Lbase_rpow_le hτ hlam
  have hCGexp_nonneg : 0 ≤ CG * Real.exp K := by
    have hCG0 : 0 ≤ CG := le_trans (norm_nonneg _) hG
    positivity
  calc CG * Real.exp K * ‖Lbase σ τ lam‖ ^ ℓ
      ≤ CG * Real.exp K * (D * τ ^ ℓ) := by
        apply mul_le_mul_of_nonneg_left hLrpow hCGexp_nonneg
    _ = CG * Real.exp K * D * τ ^ ℓ := by ring

/-! ## THE SHARP LINEAR-INTERPOLATION THEOREM — `phragmenLindelof_flatten` axiom DELETED.

Proven from the IMPORTED `RHConvexityTower.…ScratchHalfStripPL.phragmenLindelof_flatten`
(a genuine theorem) plus the fully-proven `unwind_sharp`.  No transplant axiom in this file. -/

/-- **Sharp linear-interpolation Phragmén–Lindelöf** (matches
`ScratchTWeightedPL.tWeightedPL_linear_sharp` byte-for-byte). -/
theorem tWeightedPL_linear_sharp
    (F : ℂ → ℂ) (l u : ℝ) (hlu : l < u) (α β : ℝ)
    (hF : Differentiable ℂ F)
    (hgrowth : ∃ A : ℝ, 0 ≤ A ∧ ∀ s : ℂ, s ∈ verticalClosedStrip l u →
      ‖F s‖ ≤ A * (1 + |s.im|) ^ (max α β))
    (hedgeL : ∃ Cl : ℝ, 0 ≤ Cl ∧ ∀ t : ℝ, 1 ≤ |t| →
      ‖F ((l : ℂ) + (t : ℂ) * Complex.I)‖ ≤ Cl * |t| ^ α)
    (hedgeU : ∃ Cu : ℝ, 0 ≤ Cu ∧ ∀ t : ℝ, 1 ≤ |t| →
      ‖F ((u : ℂ) + (t : ℂ) * Complex.I)‖ ≤ Cu * |t| ^ β) :
    ∀ σ : ℝ, l ≤ σ → σ ≤ u →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 1 ≤ |t| →
        ‖F ((σ : ℂ) + (t : ℂ) * Complex.I)‖
          ≤ C * |t| ^ (α * (u - σ) / (u - l) + β * (σ - l) / (u - l)) := by
  intro σ hσl hσu
  -- weight parameter lam = 1; invoke the IMPORTED PL-flatten THEOREM (not an axiom)
  obtain ⟨CG, hCG0, hCG⟩ :=
    phragmenLindelof_flatten F l u α β 1 hlu (le_refl 1) hF hgrowth hedgeL hedgeU
  set ℓ : ℝ := ellInterp l u α β σ with hℓ
  refine ⟨CG * Real.exp (|β - α| * max |l| |u| / (u - l))
            * max (((2 * (1 + |σ| + 1)) : ℝ) ^ ℓ) 1, by positivity, ?_⟩
  intro t ht
  rw [show α * (u - σ) / (u - l) + β * (σ - l) / (u - l) = ℓ from
    (ellInterp_eq l u α β σ hlu).symm]
  have hτ : (1:ℝ) ≤ |t| := ht
  have hGb := hCG σ t hσl hσu ht
  have hkey := unwind_sharp (l := l) (u := u) (α := α) (β := β) (lam := 1)
    hlu hσl hσu hτ (le_refl 1) (F ((σ : ℂ) + (t : ℂ) * Complex.I)) hGb
  simpa only [hℓ, mul_assoc] using hkey

end OverflowResidueRH.BacklundTuring.RHSharpPL

-- Axiom audit across the import boundary: `tWeightedPL_linear_sharp` must depend ONLY on
-- Mathlib axioms + the single genuine producer residual `verticalStrip_lower_reflection`.
-- The transplant axiom `phragmenLindelof_flatten` is GONE (it is an imported theorem now).
#print axioms OverflowResidueRH.BacklundTuring.RHSharpPL.unwind_sharp
#print axioms OverflowResidueRH.BacklundTuring.RHSharpPL.tWeightedPL_linear_sharp
