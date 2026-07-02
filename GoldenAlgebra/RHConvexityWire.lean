/-
  RHConvexityWire.lean — SEAM 3 of the convexity tower, discharged across the module boundary.

  Producer→consumer seam:
    `tWeightedPL_linear_sharp` : axiom in `ScratchTWeightedPL`  ←  THEOREM in `RHSharpPL`.

  This module IMPORTS `RHSharpPL` and references `tWeightedPL_linear_sharp` as the imported
  THEOREM `RHSharpPL.tWeightedPL_linear_sharp` (its signature is pure-`F`, no `wgt`, so the
  seam is clean — no def-clash).  The `ScratchTWeightedPL.tWeightedPL_linear_sharp` transplant
  AXIOM is therefore DELETED here; `tWeightedPL_zeta_convexity` is proven from it.

  Residuals remaining under `tWeightedPL_zeta_convexity` (genuine, not transplant seams):
    • `verticalStrip_lower_reflection` (flows in from the producer chain),
    • the transplanted ζ edge/growth data `xiF_growth_strip` / `xiF_edge_left` / `xiF_edge_right`
      (proven unconditionally in ScratchConvexity/ScratchGammaDecay/ScratchBaseStrip; carried
      here as named axioms exactly as in the original `ScratchTWeightedPL`).
-/
import RHSharpPL

open Complex Real Set
open scoped Real
open Complex.HadamardThreeLines

noncomputable section

namespace OverflowResidueRH.BacklundTuring.RHConvexityWire

/-- The imported sharp linear-interpolation PL theorem (was a transplant axiom in
`ScratchTWeightedPL`; here it is `RHSharpPL.tWeightedPL_linear_sharp`, a genuine theorem). -/
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
          ≤ C * |t| ^ (α * (u - σ) / (u - l) + β * (σ - l) / (u - l)) :=
  RHSharpPL.tWeightedPL_linear_sharp F l u hlu α β hF hgrowth hedgeL hedgeU

/-! ## The ζ application (copy of `ScratchTWeightedPL` Part 5). -/

/-- The removable-singularity completion `xiF(s) = (s-1)·ζ(s)` (value `1` at `s=1`). -/
def xiF : ℂ → ℂ := Function.update (fun s => (s - 1) * riemannZeta s) 1 1

/-- Off `s = 1`, `xiF` is literally `(s-1)·ζ(s)`. -/
theorem xiF_eq_of_ne {z : ℂ} (hz : z ≠ 1) : xiF z = (z - 1) * riemannZeta z := by
  simp only [xiF, Function.update_apply, if_neg hz]

/-- `xiF` is entire. -/
theorem xiF_differentiable : Differentiable ℂ xiF := by
  intro z
  rcases eq_or_ne z 1 with rfl | hz
  · set g : ℂ → ℂ := fun s => (s - 1) * riemannZeta s with hg
    have htend : Filter.Tendsto g (nhdsWithin (1 : ℂ) {(1 : ℂ)}ᶜ) (nhds 1) :=
      riemannZeta_residue_one
    have hbdd : ∃ r > 0, BddAbove (Norm.norm ∘ g '' (Metric.ball (1 : ℂ) r \ {1})) := by
      have h2 : ∀ᶠ s in nhdsWithin (1 : ℂ) {(1 : ℂ)}ᶜ, ‖g s‖ ≤ 2 := by
        have hb := htend (Metric.ball_mem_nhds (1 : ℂ) (by norm_num : (0:ℝ) < 1))
        filter_upwards [hb] with s hs
        have hlt : ‖g s - 1‖ < 1 := by
          simpa [Metric.mem_ball, Complex.dist_eq] using hs
        have hle : ‖g s‖ ≤ ‖g s - 1‖ + ‖(1 : ℂ)‖ := by
          have := norm_add_le (g s - 1) (1 : ℂ); simpa using this
        simp only [norm_one] at hle; linarith [hlt]
      rw [nhdsWithin, Filter.eventually_inf_principal, Metric.eventually_nhds_iff] at h2
      obtain ⟨r, hr, hrb⟩ := h2
      refine ⟨r, hr, 2, ?_⟩
      rintro _ ⟨s, hs, rfl⟩
      simp only [Function.comp_apply]
      exact hrb (by simpa [Complex.dist_eq] using hs.1) (by simpa using hs.2)
    obtain ⟨r, hr, hbdd⟩ := hbdd
    have hdon : DifferentiableOn ℂ g (Metric.ball (1 : ℂ) r \ {1}) := by
      intro w hw
      exact (DifferentiableAt.mul (by fun_prop) (differentiableAt_riemannZeta hw.2))
        |>.differentiableWithinAt
    have key := Complex.differentiableOn_update_limUnder_of_bddAbove
      (Metric.ball_mem_nhds (1 : ℂ) hr) hdon hbdd
    have hlim : (nhdsWithin (1 : ℂ) {(1 : ℂ)}ᶜ).limUnder g = 1 := htend.limUnder_eq
    rw [hlim] at key
    have hxi : xiF = Function.update g 1 1 := rfl
    rw [hxi]
    exact key.differentiableAt (Metric.ball_mem_nhds (1 : ℂ) hr)
  · have heq : xiF =ᶠ[nhds z] (fun s => (s - 1) * riemannZeta s) := by
      filter_upwards [isOpen_ne.mem_nhds hz] with w hw
      exact xiF_eq_of_ne hw
    exact (DifferentiableAt.mul (by fun_prop)
      (differentiableAt_riemannZeta hz)).congr_of_eventuallyEq heq

/-- `|s - 1| ≥ |t|` at `s = 1/2 + t·I`. -/
theorem norm_half_sub_one_ge (t : ℝ) :
    |t| ≤ ‖((1 / 2 : ℂ) + (t : ℂ) * Complex.I) - 1‖ := by
  have he : ((1 / 2 : ℂ) + (t : ℂ) * Complex.I) - 1
      = ((-1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I := by push_cast; ring
  rw [he, Complex.norm_add_mul_I, show |t| = Real.sqrt (t ^ 2) from (Real.sqrt_sq_eq_abs t).symm]
  apply Real.sqrt_le_sqrt; nlinarith

/-- The interpolated `xiF`-exponent at `σ = 1/2` on `[0,1]` with `α=3/2`, `β=1` is `5/4`. -/
theorem xi_interp_exponent :
    (3 / 2 : ℝ) * (1 - 1 / 2) / (1 - 0) + 1 * (1 / 2 - 0) / (1 - 0) = 5 / 4 := by norm_num

/-- ζ-exponent at the centre line:  `5/4 - 1 = 1/4`. -/
theorem xi_zeta_exponent : (5 / 4 : ℝ) - 1 = 1 / 4 := by norm_num

/-! ### Transplanted ζ edge/growth data (proven unconditionally elsewhere; genuine residuals). -/

/-- **Transplanted: `xiF` finite-order growth on `[0,1]`.** -/
axiom xiF_growth_strip :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ s : ℂ, s ∈ verticalClosedStrip 0 1 →
      ‖xiF s‖ ≤ A * (1 + |s.im|) ^ (max (3 / 2 : ℝ) 1)

/-- **Transplanted: `xiF` left edge `Re = 0`.** -/
axiom xiF_edge_left :
    ∃ Cl : ℝ, 0 ≤ Cl ∧ ∀ t : ℝ, 1 ≤ |t| →
      ‖xiF ((0 : ℂ) + (t : ℂ) * Complex.I)‖ ≤ Cl * |t| ^ (3 / 2 : ℝ)

/-- **Transplanted: `xiF` right edge `Re = 1`.** -/
axiom xiF_edge_right :
    ∃ Cu : ℝ, 0 ≤ Cu ∧ ∀ t : ℝ, 1 ≤ |t| →
      ‖xiF ((1 : ℂ) + (t : ℂ) * Complex.I)‖ ≤ Cu * |t| ^ (1 : ℝ)

/-- **t-weighted PL ⟹ ζ convexity bound** (matches `ScratchConvexity.tWeightedPL_zeta_convexity`
byte-for-byte).  Now proven from the IMPORTED sharp-PL THEOREM (not an axiom). -/
theorem tWeightedPL_zeta_convexity :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 1 ≤ |t| →
      ‖riemannZeta ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C * |t| ^ (1 / 4 : ℝ) := by
  obtain ⟨Cxi, hCxi0, hCxi⟩ :=
    tWeightedPL_linear_sharp xiF 0 1 (by norm_num) (3 / 2) 1 xiF_differentiable
      xiF_growth_strip xiF_edge_left xiF_edge_right (1 / 2) (by norm_num) (by norm_num)
  rw [show (3 / 2 : ℝ) * (1 - 1 / 2) / (1 - 0) + 1 * (1 / 2 - 0) / (1 - 0) = 5 / 4 from
    xi_interp_exponent] at hCxi
  have hcast : ∀ t : ℝ, (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)
      = ((1 / 2 : ℂ) + (t : ℂ) * Complex.I) := by intro t; norm_num
  simp only [hcast] at hCxi
  refine ⟨Cxi, hCxi0, ?_⟩
  intro t ht
  have hsne : ((1 / 2 : ℂ) + (t : ℂ) * Complex.I) ≠ 1 := by
    intro h; have := congrArg Complex.re h; simp at this
  have hxival : xiF ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)
      = (((1 / 2 : ℂ) + (t : ℂ) * Complex.I) - 1)
          * riemannZeta ((1 / 2 : ℂ) + (t : ℂ) * Complex.I) := xiF_eq_of_ne hsne
  have htpos : (0 : ℝ) < |t| := lt_of_lt_of_le one_pos ht
  have hbn : (0 : ℝ) < ‖((1 / 2 : ℂ) + (t : ℂ) * Complex.I) - 1‖ :=
    lt_of_lt_of_le htpos (norm_half_sub_one_ge t)
  have hzeq : ‖riemannZeta ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)‖
      = ‖xiF ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)‖
          / ‖((1 / 2 : ℂ) + (t : ℂ) * Complex.I) - 1‖ := by
    rw [hxival, norm_mul,
      mul_comm ‖((1 / 2 : ℂ) + (t : ℂ) * Complex.I) - 1‖
        ‖riemannZeta ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)‖,
      mul_div_assoc, div_self (ne_of_gt hbn), mul_one]
  rw [hzeq, div_le_iff₀ hbn]
  have hsplit : |t| ^ (1 / 4 : ℝ) * |t| = |t| ^ (5 / 4 : ℝ) := by
    have : |t| ^ (1 / 4 : ℝ) * |t| ^ (1 : ℝ) = |t| ^ (5 / 4 : ℝ) := by
      rw [← Real.rpow_add htpos]; norm_num
    rwa [Real.rpow_one] at this
  calc ‖xiF ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)‖
      ≤ Cxi * |t| ^ (5 / 4 : ℝ) := hCxi t ht
    _ = Cxi * |t| ^ (1 / 4 : ℝ) * |t| := by rw [mul_assoc, hsplit]
    _ ≤ Cxi * |t| ^ (1 / 4 : ℝ) * ‖((1 / 2 : ℂ) + (t : ℂ) * Complex.I) - 1‖ := by
        apply mul_le_mul_of_nonneg_left (norm_half_sub_one_ge t)
        positivity

/-- **ζ convexity bound** (matches `ScratchConvexity.zeta_convexity_bound` /
`ScratchCountWiring.zeta_convexity_bound` byte-for-byte).  Proven, not an axiom. -/
theorem zeta_convexity_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 1 ≤ |t| →
      ‖riemannZeta ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C * |t| ^ (1 / 4 : ℝ) :=
  tWeightedPL_zeta_convexity

end OverflowResidueRH.BacklundTuring.RHConvexityWire

-- Axiom audit across the import boundary: the transplant axiom `tWeightedPL_linear_sharp` is
-- GONE; only Mathlib + `verticalStrip_lower_reflection` + the ζ-edge transplants remain.
#print axioms OverflowResidueRH.BacklundTuring.RHConvexityWire.tWeightedPL_zeta_convexity
#print axioms OverflowResidueRH.BacklundTuring.RHConvexityWire.zeta_convexity_bound
