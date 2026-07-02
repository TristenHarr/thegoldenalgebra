import rh

/-!
# ScratchResidue: the atomic rectangle residue computation

This file proves the single missing analytic obligation behind the residue-free
argument principle in `rh.lean`:

  `R.principalKernelRectangleIntegral k a = 2πi · k`

for a singularity `a` strictly inside an axis-aligned rectangle `R`, and inhabits
the previously-assumed structure `PrincipalKernelUnnormalizedIntegralTheorem`.

The proof is a direct four-edge computation.  Each edge integral
`∫₀¹ (γ t - a)⁻¹ · γ'(t) dt` is evaluated by the Fundamental Theorem of Calculus
using the antiderivative `t ↦ Complex.log (γ t - a)` (or, on the left edge that
crosses the principal branch cut, `t ↦ Complex.log (a - γ t)`).  The four
log-differences telescope; the residual is the total argument increment `2πi`,
supplied by `Complex.arg_neg_eq_arg_sub_pi_of_im_pos` /
`arg_neg_eq_arg_add_pi_of_im_neg`.
-/

open Complex intervalIntegral
open scoped Real

namespace OverflowResidueRH
namespace BacklundTuring

/-! ## Generic affine-edge integral via FTC

For an affine edge `γ(t) = c + t·d` with `γ(t) - a ∈ slitPlane` for all `t ∈ [0,1]`
(via the `log` branch chosen by `sgn`), the integral telescopes to a log
difference. -/

/-- One edge integral of the unit kernel, evaluated by FTC with the principal-log
antiderivative.  Hypothesis: `γ t - a` stays in the slit plane on `[0,1]`. -/
theorem edge_integral_log
    (γ : ℝ → ℂ) (d a : ℂ)
    (hγ : ∀ t : ℝ, HasDerivAt γ d t)
    (hslit : ∀ t ∈ Set.uIcc (0:ℝ) 1, (γ t - a) ∈ slitPlane) :
    (∫ t in (0:ℝ)..1, (γ t - a)⁻¹ * d) =
      Complex.log (γ 1 - a) - Complex.log (γ 0 - a) := by
  have hF : ∀ t ∈ Set.uIcc (0:ℝ) 1,
      HasDerivAt (fun s => Complex.log (γ s - a)) ((γ t - a)⁻¹ * d) t := by
    intro t ht
    have hsub : HasDerivAt (fun s => γ s - a) d t := (hγ t).sub_const a
    have := hsub.clog_real (hslit t ht)
    simpa [div_eq_inv_mul] using this
  have hcont : ContinuousOn (fun t => (γ t - a)⁻¹ * d) (Set.uIcc (0:ℝ) 1) := by
    intro t ht
    have hne : γ t - a ≠ 0 := by
      have := hslit t ht
      rw [mem_slitPlane_iff] at this
      rcases this with h | h
      · intro hz; rw [hz] at h; simp at h
      · intro hz; rw [hz] at h; simp at h
    have hγc : ContinuousAt (fun s => γ s - a) t :=
      ((hγ t).continuousAt.sub continuousAt_const)
    have : ContinuousAt (fun s => (γ s - a)⁻¹ * d) t :=
      (hγc.inv₀ hne).mul continuousAt_const
    exact this.continuousWithinAt
  have hint : IntervalIntegrable (fun t => (γ t - a)⁻¹ * d) MeasureTheory.volume 0 1 :=
    hcont.intervalIntegrable
  exact integral_eq_sub_of_hasDerivAt hF hint

/-- Variant using the `log(a - γ)` branch (for the left edge). -/
theorem edge_integral_log_neg
    (γ : ℝ → ℂ) (d a : ℂ)
    (hγ : ∀ t : ℝ, HasDerivAt γ d t)
    (hslit : ∀ t ∈ Set.uIcc (0:ℝ) 1, (a - γ t) ∈ slitPlane) :
    (∫ t in (0:ℝ)..1, (γ t - a)⁻¹ * d) =
      Complex.log (a - γ 1) - Complex.log (a - γ 0) := by
  have hF : ∀ t ∈ Set.uIcc (0:ℝ) 1,
      HasDerivAt (fun s => Complex.log (a - γ s)) ((γ t - a)⁻¹ * d) t := by
    intro t ht
    have hsub : HasDerivAt (fun s => a - γ s) (-d) t := ((hγ t).const_sub a)
    have hlog := hsub.clog_real (hslit t ht)
    -- derivative is `(-d) / (a - γ t) = (γ t - a)⁻¹ * d`
    have heq : (-d) / (a - γ t) = (γ t - a)⁻¹ * d := by
      have hrw : a - γ t = -(γ t - a) := by ring
      rw [hrw, div_neg, neg_div, neg_neg, div_eq_inv_mul]
    rw [heq] at hlog
    exact hlog
  have hcont : ContinuousOn (fun t => (γ t - a)⁻¹ * d) (Set.uIcc (0:ℝ) 1) := by
    intro t ht
    have hne : a - γ t ≠ 0 := by
      have := hslit t ht
      rw [mem_slitPlane_iff] at this
      rcases this with h | h
      · intro hz; rw [hz] at h; simp at h
      · intro hz; rw [hz] at h; simp at h
    have hne' : γ t - a ≠ 0 := by
      intro hz; apply hne; rw [← neg_sub, hz, neg_zero]
    have hγc : ContinuousAt (fun s => γ s - a) t :=
      ((hγ t).continuousAt.sub continuousAt_const)
    have : ContinuousAt (fun s => (γ s - a)⁻¹ * d) t :=
      (hγc.inv₀ hne').mul continuousAt_const
    exact this.continuousWithinAt
  have hint : IntervalIntegrable (fun t => (γ t - a)⁻¹ * d) MeasureTheory.volume 0 1 :=
    hcont.intervalIntegrable
  exact integral_eq_sub_of_hasDerivAt hF hint

/-! ## Branch-jump helpers: `log w - log (-w)` -/

/-- For `w` strictly in the second quadrant (`re < 0`, `im > 0`),
`log w - log (-w) = π·I`. -/
theorem log_sub_log_neg_im_pos {w : ℂ} (him : 0 < w.im) :
    Complex.log w - Complex.log (-w) = (Real.pi : ℂ) * Complex.I := by
  have hnorm : ‖-w‖ = ‖w‖ := by rw [norm_neg]
  rw [Complex.log, Complex.log, hnorm]
  rw [Complex.arg_neg_eq_arg_sub_pi_of_im_pos him]
  push_cast
  ring

/-- For `w` strictly in the third quadrant (`re < 0`, `im < 0`),
`log w - log (-w) = -π·I`. -/
theorem log_sub_log_neg_im_neg {w : ℂ} (him : w.im < 0) :
    Complex.log w - Complex.log (-w) = -((Real.pi : ℂ) * Complex.I) := by
  have hnorm : ‖-w‖ = ‖w‖ := by rw [norm_neg]
  rw [Complex.log, Complex.log, hnorm]
  rw [Complex.arg_neg_eq_arg_add_pi_of_im_neg him]
  push_cast
  ring

/-! ## The four concrete edge integrals -/

/-- Bottom edge integral.  On the bottom edge `im = bottom < a.im`, so
`edge t - a` has negative imaginary part ⇒ in slitPlane. -/
theorem bottom_edge_eq (R : ZetaRectangle) (a : ℂ) (ha : R.ContainsOpen a) :
    (∫ t in (0:ℝ)..1, (R.bottomEdge t - a)⁻¹ * deriv R.bottomEdge t) =
      Complex.log ((⟨R.right, R.bottom⟩ : ℂ) - a)
        - Complex.log ((⟨R.left, R.bottom⟩ : ℂ) - a) := by
  rw [show (fun t => (R.bottomEdge t - a)⁻¹ * deriv R.bottomEdge t)
        = fun t => (R.bottomEdge t - a)⁻¹ * ((R.right - R.left : ℝ) : ℂ) by
        funext t; rw [R.deriv_bottomEdge t]]
  have hslit : ∀ t ∈ Set.uIcc (0:ℝ) 1, (R.bottomEdge t - a) ∈ slitPlane := by
    intro t _
    rw [mem_slitPlane_iff]
    right
    have him : (R.bottomEdge t - a).im = R.bottom - a.im := by
      simp [ZetaRectangle.bottomEdge]
    rw [him]
    have := ha.2.2.1
    intro h; linarith [sub_eq_zero.mp h]
  have key := edge_integral_log R.bottomEdge ((R.right - R.left : ℝ) : ℂ) a
    (fun t => R.hasDerivAt_bottomEdge t) hslit
  rw [key, R.bottomEdge_one, R.bottomEdge_zero]

/-- Right edge integral.  On the right edge `re = right > a.re`, so
`edge t - a` has positive real part ⇒ in slitPlane. -/
theorem right_edge_eq (R : ZetaRectangle) (a : ℂ) (ha : R.ContainsOpen a) :
    (∫ t in (0:ℝ)..1, (R.rightEdge t - a)⁻¹ * deriv R.rightEdge t) =
      Complex.log ((⟨R.right, R.top⟩ : ℂ) - a)
        - Complex.log ((⟨R.right, R.bottom⟩ : ℂ) - a) := by
  rw [show (fun t => (R.rightEdge t - a)⁻¹ * deriv R.rightEdge t)
        = fun t => (R.rightEdge t - a)⁻¹ * (((R.top - R.bottom : ℝ) : ℂ) * Complex.I) by
        funext t; rw [R.deriv_rightEdge t]]
  have hslit : ∀ t ∈ Set.uIcc (0:ℝ) 1, (R.rightEdge t - a) ∈ slitPlane := by
    intro t _
    rw [mem_slitPlane_iff]
    left
    have hre : (R.rightEdge t - a).re = R.right - a.re := by
      simp [ZetaRectangle.rightEdge]
    rw [hre]
    have := ha.2.1
    linarith
  have key := edge_integral_log R.rightEdge (((R.top - R.bottom : ℝ) : ℂ) * Complex.I) a
    (fun t => R.hasDerivAt_rightEdge t) hslit
  rw [key, R.rightEdge_one, R.rightEdge_zero]

/-- Top edge integral.  On the top edge `im = top > a.im`, so
`edge t - a` has positive imaginary part ⇒ in slitPlane. -/
theorem top_edge_eq (R : ZetaRectangle) (a : ℂ) (ha : R.ContainsOpen a) :
    (∫ t in (0:ℝ)..1, (R.topEdge t - a)⁻¹ * deriv R.topEdge t) =
      Complex.log ((⟨R.left, R.top⟩ : ℂ) - a)
        - Complex.log ((⟨R.right, R.top⟩ : ℂ) - a) := by
  rw [show (fun t => (R.topEdge t - a)⁻¹ * deriv R.topEdge t)
        = fun t => (R.topEdge t - a)⁻¹ * (-((R.right - R.left : ℝ) : ℂ)) by
        funext t; rw [R.deriv_topEdge t]]
  have hslit : ∀ t ∈ Set.uIcc (0:ℝ) 1, (R.topEdge t - a) ∈ slitPlane := by
    intro t _
    rw [mem_slitPlane_iff]
    right
    have him : (R.topEdge t - a).im = R.top - a.im := by
      simp [ZetaRectangle.topEdge]
    rw [him]
    have := ha.2.2.2
    intro h; linarith [sub_eq_zero.mp h]
  have key := edge_integral_log R.topEdge (-((R.right - R.left : ℝ) : ℂ)) a
    (fun t => R.hasDerivAt_topEdge t) hslit
  rw [key, R.topEdge_one, R.topEdge_zero]

/-- Left edge integral.  On the left edge `re = left < a.re`, so
`edge t - a` has negative real part and crosses the principal branch cut.
We use the `log (a - edge)` antiderivative branch: `a - edge t` has positive
real part ⇒ in slitPlane. -/
theorem left_edge_eq (R : ZetaRectangle) (a : ℂ) (ha : R.ContainsOpen a) :
    (∫ t in (0:ℝ)..1, (R.leftEdge t - a)⁻¹ * deriv R.leftEdge t) =
      Complex.log (a - (⟨R.left, R.bottom⟩ : ℂ))
        - Complex.log (a - (⟨R.left, R.top⟩ : ℂ)) := by
  rw [show (fun t => (R.leftEdge t - a)⁻¹ * deriv R.leftEdge t)
        = fun t => (R.leftEdge t - a)⁻¹ * (-(((R.top - R.bottom : ℝ) : ℂ) * Complex.I)) by
        funext t; rw [R.deriv_leftEdge t]]
  have hslit : ∀ t ∈ Set.uIcc (0:ℝ) 1, (a - R.leftEdge t) ∈ slitPlane := by
    intro t _
    rw [mem_slitPlane_iff]
    left
    have hre : (a - R.leftEdge t).re = a.re - R.left := by
      simp [ZetaRectangle.leftEdge]
    rw [hre]
    have := ha.1
    linarith
  have key := edge_integral_log_neg R.leftEdge (-(((R.top - R.bottom : ℝ) : ℂ) * Complex.I)) a
    (fun t => R.hasDerivAt_leftEdge t) hslit
  rw [key, R.leftEdge_one, R.leftEdge_zero]

/-! ## Assembly: the unit-kernel rectangle integral equals `2πi` -/

/-- **Atomic residue computation.**  For `a` strictly inside the rectangle,
the unit principal-kernel rectangle contour integral equals `2πi`. -/
theorem unitPrincipalKernelRectangleIntegral_eq_twoPiI
    (R : ZetaRectangle) (a : ℂ) (ha : R.ContainsOpen a) :
    R.principalKernelRectangleIntegral 1 a = ZetaRectangle.twoPiI := by
  -- Rewrite each integrand `principalKernel 1 a (edge t) * deriv` to `(edge t - a)⁻¹ * deriv`.
  have hkernel : ∀ (edge : ℝ → ℂ),
      (∫ t in (0:ℝ)..1, ZetaRectangle.principalKernel 1 a (edge t) * deriv edge t)
        = ∫ t in (0:ℝ)..1, (edge t - a)⁻¹ * deriv edge t := by
    intro edge
    refine intervalIntegral.integral_congr (fun t _ => ?_)
    unfold ZetaRectangle.principalKernel
    rw [Int.cast_one, one_div]
  unfold ZetaRectangle.principalKernelRectangleIntegral
  rw [hkernel R.bottomEdge, hkernel R.rightEdge, hkernel R.topEdge, hkernel R.leftEdge]
  rw [bottom_edge_eq R a ha, right_edge_eq R a ha, top_edge_eq R a ha,
      left_edge_eq R a ha]
  -- Abbreviate the two left corners.
  set BL : ℂ := (⟨R.left, R.bottom⟩ : ℂ) with hBL
  set TL : ℂ := (⟨R.left, R.top⟩ : ℂ) with hTL
  -- All `BR`, `TR` logs cancel; reorganize using `a - X = -(X - a)`.
  have hBLneg : a - BL = -(BL - a) := by ring
  have hTLneg : a - TL = -(TL - a) := by ring
  rw [hBLneg, hTLneg]
  -- The remaining four logs: log(TL-a) - log(BL-a) + log(-(BL-a)) - log(-(TL-a)).
  have hTL_jump : Complex.log (TL - a) - Complex.log (-(TL - a))
      = (Real.pi : ℂ) * Complex.I := by
    apply log_sub_log_neg_im_pos
    have : (TL - a).im = R.top - a.im := by rw [hTL]; simp
    rw [this]; linarith [ha.2.2.2]
  have hBL_jump : Complex.log (BL - a) - Complex.log (-(BL - a))
      = -((Real.pi : ℂ) * Complex.I) := by
    apply log_sub_log_neg_im_neg
    have : (BL - a).im = R.bottom - a.im := by rw [hBL]; simp
    rw [this]; linarith [ha.2.2.1]
  -- Assemble: `BR`/`TR` logs cancel; the two left-corner jumps give `2π·I`.
  unfold ZetaRectangle.twoPiI
  linear_combination hTL_jump - hBL_jump

/-! ## Inhabiting the assumed structures in `rh.lean` -/

/-- **The unit-kernel Cauchy-index theorem**, now proved.  This inhabits the
previously-open `UnitPrincipalKernelIntegralTheorem`. -/
theorem unitPrincipalKernelIntegralTheorem
    (R : ZetaRectangle) (a : ℂ) (ha : R.ContainsOpen a) :
    R.UnitPrincipalKernelIntegralTheorem a where
  inside := ha
  boundary_avoids := by
    intro z hz heq
    subst heq
    exact hz.2 ha
  integral_eq := by
    unfold ZetaRectangle.unitPrincipalKernelRectangleIntegral
    exact unitPrincipalKernelRectangleIntegral_eq_twoPiI R a ha

/-- **The atomic residue computation**, now proved as a real theorem:
`∮_R k/(z-a) dz = 2πi · k` for `a` strictly inside the rectangle.  This inhabits
the previously-assumed structure field
`PrincipalKernelUnnormalizedIntegralTheorem.integral_eq`. -/
theorem principalKernelUnnormalizedIntegralTheorem
    (R : ZetaRectangle) (k : ℤ) (a : ℂ) (ha : R.ContainsOpen a) :
    R.PrincipalKernelUnnormalizedIntegralTheorem k a :=
  (unitPrincipalKernelIntegralTheorem R a ha).toUnnormalized k

/-- Standalone statement of the residue computation (the field that was assumed). -/
theorem principalKernelRectangleIntegral_eq_twoPiI_mul
    (R : ZetaRectangle) (k : ℤ) (a : ℂ) (ha : R.ContainsOpen a) :
    R.principalKernelRectangleIntegral k a = ZetaRectangle.twoPiI * (k : ℂ) :=
  (principalKernelUnnormalizedIntegralTheorem R k a ha).integral_eq

end BacklundTuring
end OverflowResidueRH

-- Axiom audit: must show only the three standard classical/quotient axioms,
-- with NO `sorryAx`.
#print axioms OverflowResidueRH.BacklundTuring.principalKernelUnnormalizedIntegralTheorem
#print axioms OverflowResidueRH.BacklundTuring.unitPrincipalKernelRectangleIntegral_eq_twoPiI
