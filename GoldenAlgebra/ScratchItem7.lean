import Mathlib
open Complex

open Filter Topology Metric

/-- The derivative of an entire function of linear growth is bounded by the growth constant. -/
theorem norm_deriv_le_of_linear_growth
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) {C : ℝ} (hC : 0 ≤ C)
    (hgrow : ∀ z : ℂ, ‖f z‖ ≤ C * (1 + ‖z‖)) :
    ∀ z : ℂ, ‖deriv f z‖ ≤ C := by
  intro z
  -- For each R > 0, Cauchy estimate gives ‖deriv f z‖ ≤ C * (1 + ‖z‖ + R) / R.
  have key : ∀ R : ℝ, 0 < R → ‖deriv f z‖ ≤ C * (1 + ‖z‖ + R) / R := by
    intro R hR
    have hsphere : ∀ w ∈ sphere z R, ‖f w‖ ≤ C * (1 + ‖z‖ + R) := by
      intro w hw
      rw [mem_sphere_iff_norm] at hw
      have hwnorm : ‖w‖ ≤ ‖z‖ + R := by
        have heq : w = (w - z) + z := by ring
        calc ‖w‖ = ‖(w - z) + z‖ := by rw [← heq]
          _ ≤ ‖w - z‖ + ‖z‖ := norm_add_le _ _
          _ = R + ‖z‖ := by rw [hw]
          _ = ‖z‖ + R := by ring
      calc ‖f w‖ ≤ C * (1 + ‖w‖) := hgrow w
        _ ≤ C * (1 + (‖z‖ + R)) := by
            apply mul_le_mul_of_nonneg_left _ hC
            linarith
        _ = C * (1 + ‖z‖ + R) := by ring
    have := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hR hf.diffContOnCl hsphere
    exact this
  -- Take R → ∞: C * (1 + ‖z‖ + R) / R → C.
  have htend : Tendsto (fun R : ℝ => C * (1 + ‖z‖ + R) / R) atTop (𝓝 C) := by
    have h1 : Tendsto (fun R : ℝ => (1 + ‖z‖ + R) / R) atTop (𝓝 1) := by
      have : (fun R : ℝ => (1 + ‖z‖ + R) / R) =ᶠ[atTop] (fun R : ℝ => (1 + ‖z‖) / R + 1) := by
        filter_upwards [eventually_gt_atTop 0] with R hR
        field_simp
      rw [tendsto_congr' this]
      have : Tendsto (fun R : ℝ => (1 + ‖z‖) / R) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop tendsto_id
      simpa using this.add tendsto_const_nhds
    have : Tendsto (fun R : ℝ => C * ((1 + ‖z‖ + R) / R)) atTop (𝓝 (C * 1)) :=
      tendsto_const_nhds.mul h1
    simp only [mul_one] at this
    convert this using 2 with R
    ring
  refine le_of_tendsto_of_tendsto tendsto_const_nhds htend ?_
  filter_upwards [eventually_gt_atTop 0] with R hR
  exact key R hR

-- (1) linear growth ⇒ the second derivative vanishes ⇒ affine
theorem affine_of_entire_of_linear_growth
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) (C : ℝ)
    (hgrow : ∀ z : ℂ, ‖f z‖ ≤ C * (1 + ‖z‖)) :
    ∃ a b : ℂ, ∀ z, f z = a * z + b := by
  -- WLOG C ≥ 0 (since ‖f 0‖ ≤ C * 1 forces C ≥ 0).
  have hC : 0 ≤ C := by
    have := hgrow 0
    simp only [norm_zero, add_zero, mul_one] at this
    exact le_trans (norm_nonneg _) this
  -- deriv f is bounded by C.
  have hbound := norm_deriv_le_of_linear_growth hf hC hgrow
  -- deriv f is entire.
  have hderiv_diff : Differentiable ℂ (deriv f) := by
    have := hf.differentiableOn.deriv isOpen_univ
    rw [differentiableOn_univ] at this
    exact this
  -- deriv f is bounded, hence constant by Liouville.
  have hconst : ∀ z, deriv f z = deriv f 0 := by
    intro z
    apply hderiv_diff.apply_eq_apply_of_bounded
    rw [isBounded_iff_forall_norm_le]
    exact ⟨C, by rintro x ⟨w, rfl⟩; exact hbound w⟩
  -- Set a := deriv f 0, b := f 0.  Show g z := f z - a * z is constant.
  set a := deriv f 0 with ha
  have hg_diff : Differentiable ℂ (fun z => f z - a * z) :=
    hf.sub ((differentiable_const a).mul differentiable_id)
  have hg_deriv : ∀ z, deriv (fun z => f z - a * z) z = 0 := by
    intro z
    have h1 : HasDerivAt f (deriv f z) z := (hf z).hasDerivAt
    have h2 : HasDerivAt (fun z => a * z) a z := by
      simpa using (hasDerivAt_id z).const_mul a
    have : HasDerivAt (fun z => f z - a * z) (deriv f z - a) z := h1.sub h2
    rw [this.deriv, hconst z, ha]
    ring
  have hg_const : ∀ z, (fun z => f z - a * z) z = (fun z => f z - a * z) 0 :=
    fun z => is_const_of_deriv_eq_zero hg_diff hg_deriv z 0
  refine ⟨a, f 0, fun z => ?_⟩
  have hz := hg_const z
  simp only [mul_zero, sub_zero] at hz
  -- hz : f z - a * z = f 0
  linear_combination hz

-- (2) zero-free entire ⇒ exp of an entire function (on all of ℂ, which is simply connected)
theorem exists_entire_exp_eq {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hne : ∀ z, f z ≠ 0) :
    ∃ g : ℂ → ℂ, Differentiable ℂ g ∧ ∀ z, f z = Complex.exp (g z) := by
  -- The logarithmic derivative deriv f / f is entire.
  have hlog_diff : Differentiable ℂ (fun z => deriv f z / f z) := by
    have hderiv_diff : Differentiable ℂ (deriv f) := by
      have := hf.differentiableOn.deriv isOpen_univ
      rw [differentiableOn_univ] at this
      exact this
    exact hderiv_diff.div hf (fun z => hne z)
  -- It has a primitive g₀ : HasDerivAt g₀ (deriv f z / f z) z for all z.
  obtain ⟨g₀, hg₀⟩ := hlog_diff.isExactOn_univ
  have hg₀' : ∀ z, HasDerivAt g₀ (deriv f z / f z) z := fun z => hg₀ z (Set.mem_univ z)
  have hg₀_diff : Differentiable ℂ g₀ := fun z => (hg₀' z).differentiableAt
  -- h z := f z * exp(- g₀ z) has derivative 0 everywhere.
  set h : ℂ → ℂ := fun z => f z * Complex.exp (- g₀ z) with hh
  have hderiv_h : ∀ z, HasDerivAt h 0 z := by
    intro z
    have hf' : HasDerivAt f (deriv f z) z := (hf z).hasDerivAt
    have hexp : HasDerivAt (fun z => Complex.exp (- g₀ z))
        (Complex.exp (- g₀ z) * (- (deriv f z / f z))) z :=
      ((hg₀' z).neg).cexp
    have hprod : HasDerivAt h
        (deriv f z * Complex.exp (- g₀ z)
          + f z * (Complex.exp (- g₀ z) * (- (deriv f z / f z)))) z :=
      hf'.mul hexp
    have heq : deriv f z * Complex.exp (- g₀ z)
        + f z * (Complex.exp (- g₀ z) * (- (deriv f z / f z))) = 0 := by
      have hfz : f z ≠ 0 := hne z
      field_simp
      ring
    rwa [heq] at hprod
  -- Hence h is constant.
  have hh_diff : Differentiable ℂ h := fun z => (hderiv_h z).differentiableAt
  have hh_deriv0 : ∀ z, deriv h z = 0 := fun z => (hderiv_h z).deriv
  have hh_const : ∀ z, h z = h 0 :=
    fun z => is_const_of_deriv_eq_zero hh_diff hh_deriv0 z 0
  -- h 0 = f 0 * exp(- g₀ 0) ≠ 0.
  set c : ℂ := h 0 with hc
  have hc_ne : c ≠ 0 := by
    rw [hc, hh]
    exact mul_ne_zero (hne 0) (Complex.exp_ne_zero _)
  -- f z = c * exp (g₀ z) since f z * exp(-g₀ z) = c.
  set d : ℂ := Complex.log c with hd
  have hcd : Complex.exp d = c := Complex.exp_log hc_ne
  refine ⟨fun z => g₀ z + d, hg₀_diff.add_const d, fun z => ?_⟩
  have hz := hh_const z
  simp only [hh] at hz
  -- hz : f z * exp(- g₀ z) = c
  rw [Complex.exp_add, hcd]
  -- goal: f z = exp (g₀ z) * c
  have key : f z = c * Complex.exp (g₀ z) := by
    have hstep : f z * Complex.exp (- g₀ z) * Complex.exp (g₀ z) = c * Complex.exp (g₀ z) := by
      rw [hz]
    rw [mul_assoc, ← Complex.exp_add] at hstep
    simp only [neg_add_cancel, Complex.exp_zero, mul_one] at hstep
    exact hstep
  rw [key]; ring
