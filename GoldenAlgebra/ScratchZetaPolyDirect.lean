import Mathlib

open Complex MeasureTheory Set Filter Topology
open scoped Real

noncomputable section

/-- The "fractional part" integral appearing in the first-order Euler–Maclaurin
continuation of the Riemann zeta function. -/
def zetaFractIntegral (s : ℂ) : ℂ :=
  ∫ x in Ioi (1 : ℝ), ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)

/-- Pointwise norm bound on the integrand: `‖{x}·x^{-s-1}‖ ≤ x^{-σ-1}` for `x > 0`. -/
theorem norm_integrand_le {s : ℂ} {x : ℝ} (hx : 0 < x) :
    ‖((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)‖ ≤ x ^ (-s.re - 1) := by
  rw [norm_mul]
  have hfract : ‖((Int.fract x : ℝ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Int.fract_nonneg x)]
    exact (Int.fract_lt_one x).le
  have hcpow : ‖(x : ℂ) ^ (-s - 1)‖ = x ^ (-s.re - 1) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]
    congr 1
  rw [hcpow]
  calc ‖((Int.fract x : ℝ) : ℂ)‖ * x ^ (-s.re - 1)
      ≤ 1 * x ^ (-s.re - 1) :=
        mul_le_mul_of_nonneg_right hfract (Real.rpow_nonneg hx.le _)
    _ = x ^ (-s.re - 1) := one_mul _

/-- The integrand is a.e.-strongly-measurable on `Ioi 1`. -/
theorem aestronglyMeasurable_integrand (s : ℂ) :
    AEStronglyMeasurable
      (fun x : ℝ ↦ ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1))
      (volume.restrict (Ioi (1 : ℝ))) := by
  apply AEStronglyMeasurable.mul
  · exact (Complex.continuous_ofReal.comp_aestronglyMeasurable
      (measurable_fract.aestronglyMeasurable))
  · -- x ↦ (x:ℂ)^(-s-1) is continuous on Ioi 1 (since x > 0 there)
    apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioi
    intro x hx
    exact (Complex.continuousAt_ofReal_cpow_const _ _
      (Or.inr (by simpa using (lt_trans one_pos (by simpa using hx)).ne'))).continuousWithinAt

/-- Integrability of the integrand on `Ioi 1` when `Re s > 0`. -/
theorem integrableOn_integrand {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn
      (fun x : ℝ ↦ ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1))
      (Ioi (1 : ℝ)) := by
  have hmaj : IntegrableOn (fun x : ℝ ↦ x ^ (-s.re - 1)) (Ioi (1 : ℝ)) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) one_pos
  apply Integrable.mono' hmaj (aestronglyMeasurable_integrand s)
  filter_upwards [self_mem_ae_restrict (measurableSet_Ioi)] with x hx
  exact norm_integrand_le (lt_trans one_pos hx)

/-- `∫_{Ioi 1} x^{-σ-1} dx = 1/σ` for `σ > 0`. -/
theorem integral_majorant {σ : ℝ} (hσ : 0 < σ) :
    ∫ x in Ioi (1 : ℝ), x ^ (-σ - 1) = 1 / σ := by
  rw [integral_Ioi_rpow_of_lt (by linarith) one_pos]
  rw [Real.one_rpow]
  rw [show -σ - 1 + 1 = -σ by ring]
  field_simp

/-- The key estimate: `‖zetaFractIntegral s‖ ≤ 1/(Re s)` for `Re s > 0`. -/
theorem norm_zetaFractIntegral_le {s : ℂ} (hs : 0 < s.re) :
    ‖zetaFractIntegral s‖ ≤ 1 / s.re := by
  unfold zetaFractIntegral
  calc ‖∫ x in Ioi (1 : ℝ), ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)‖
      ≤ ∫ x in Ioi (1 : ℝ), ‖((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)‖ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ x in Ioi (1 : ℝ), x ^ (-s.re - 1) := by
        apply integral_mono_of_nonneg
        · filter_upwards with x using norm_nonneg _
        · exact integrableOn_Ioi_rpow_of_lt (by linarith) one_pos
        · filter_upwards [self_mem_ae_restrict (measurableSet_Ioi)] with x hx
          exact norm_integrand_le (lt_trans one_pos hx)
    _ = 1 / s.re := integral_majorant hs

/-! ### The Euler–Maclaurin representation for `Re s > 1` via Abel summation -/

/-- Coefficient sequence: `1` for `n ≥ 1`, and `0` at `n = 0`. -/
def coeffOne : ℕ → ℂ := fun n => if n = 0 then 0 else 1

theorem coeffOne_zero : coeffOne 0 = 0 := rfl

theorem sum_coeffOne (n : ℕ) : ∑ k ∈ Finset.Icc 0 n, coeffOne k = (n : ℂ) := by
  induction n with
  | zero => simp [coeffOne]
  | succ m ih =>
      rw [Finset.sum_Icc_succ_top (Nat.zero_le _), ih]
      simp only [coeffOne, Nat.succ_ne_zero, if_false]
      push_cast
      ring

/-- Partial sums of `(k:ℂ)^(-s) · coeffOne k` over `Icc 0 n` tend to `ζ(s)` for `Re s > 1`. -/
theorem tendsto_partial_zeta {s : ℂ} (hs : 1 < s.re) :
    Filter.Tendsto
      (fun n : ℕ => ∑ k ∈ Finset.Icc 0 n, ((k : ℂ) ^ (-s)) * coeffOne k)
      Filter.atTop (𝓝 (riemannZeta s)) := by
  have hs0 : s ≠ 0 := by intro h; rw [h] at hs; simp at hs; linarith
  -- the summand equals 1/(k:ℂ)^s
  have hsummand : ∀ k : ℕ, ((k : ℂ) ^ (-s)) * coeffOne k = 1 / (k : ℂ) ^ s := by
    intro k
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk
      simp [coeffOne, Complex.zero_cpow hs0, Complex.zero_cpow (neg_ne_zero.mpr hs0)]
    · have hkne0 : k ≠ 0 := hk.ne'
      simp only [coeffOne, hkne0, if_false, mul_one]
      rw [Complex.cpow_neg, one_div]
  have hsum : Summable (fun n : ℕ => 1 / (n : ℂ) ^ s) := by
    simpa using Complex.summable_one_div_nat_cpow.mpr hs
  have hz : HasSum (fun n : ℕ => 1 / (n : ℂ) ^ s) (riemannZeta s) := by
    rw [zeta_eq_tsum_one_div_nat_cpow hs]
    exact hsum.hasSum
  have htend := hz.tendsto_sum_nat
  -- convert range (n) form to Icc 0 n form
  rw [show (fun n : ℕ => ∑ k ∈ Finset.Icc 0 n, ((k : ℂ) ^ (-s)) * coeffOne k)
        = (fun n : ℕ => ∑ k ∈ Finset.range (n+1), 1 / (k : ℂ) ^ s) by
      funext n
      rw [Nat.range_succ_eq_Icc_zero]
      exact Finset.sum_congr rfl (fun k _ => hsummand k)]
  exact (htend.comp (Filter.tendsto_add_atTop_nat 1))

/-- For `Re s > 1`, the floor-integral representation
`ζ(s) = - ∫_{Ioi 1} (deriv (·^(-s))) t · ⌊t⌋ dt`. -/
theorem zeta_eq_neg_integral_floor {s : ℂ} (hs : 1 < s.re) :
    riemannZeta s =
      - ∫ t in Ioi (1 : ℝ),
          deriv (fun y : ℝ => (y : ℂ) ^ (-s)) t * (⌊t⌋₊ : ℂ) := by
  have hs0 : s ≠ 0 := by
    intro h; rw [h] at hs; simp at hs; linarith
  have hsne : (-s) ≠ 0 := by simpa using hs0
  -- differentiability of f on Ici 1
  have hf_diff : ∀ t ∈ Ici (1 : ℝ), DifferentiableAt ℝ (fun y : ℝ => (y : ℂ) ^ (-s)) t := by
    intro t ht
    have : (0:ℝ) < t := lt_of_lt_of_le one_pos ht
    exact (hasDerivAt_ofReal_cpow_const this.ne' hsne).differentiableAt
  -- deriv formula on Ioi 0
  have hderiv : ∀ t : ℝ, 0 < t →
      deriv (fun y : ℝ => (y : ℂ) ^ (-s)) t = (-s) * (t : ℂ) ^ (-s - 1) := by
    intro t ht
    exact (hasDerivAt_ofReal_cpow_const ht.ne' hsne).deriv
  set f : ℝ → ℂ := fun y : ℝ => (y : ℂ) ^ (-s) with hf
  -- deriv is continuous on Ici 1, hence locally integrable there
  have hcont_pow : ContinuousOn (fun t : ℝ => (-s) * (t : ℂ) ^ (-s - 1)) (Ici (1 : ℝ)) := by
    apply ContinuousOn.const_smul (c := -s) ?_ |>.congr (fun t ht => by rw [smul_eq_mul])
    intro t ht
    exact (Complex.continuousAt_ofReal_cpow_const _ _
      (Or.inr (lt_of_lt_of_le one_pos ht).ne')).continuousWithinAt
  have hderiv_cont : ContinuousOn (deriv f) (Ici (1 : ℝ)) :=
    hcont_pow.congr (fun t ht => (hderiv t (lt_of_lt_of_le one_pos ht)))
  have hf_int : LocallyIntegrableOn (deriv f) (Ici (1 : ℝ)) :=
    hderiv_cont.locallyIntegrableOn measurableSet_Ici
  -- the limit l = 0:  f n * (n : ℂ) → 0
  have h_lim : Tendsto (fun n : ℕ => f n * ∑ k ∈ Finset.Icc 0 n, coeffOne k) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    -- ‖f n * n‖ = n^(1-σ) eventually, and that → 0
    have hev : (fun n : ℕ => ‖f n * ∑ k ∈ Finset.Icc 0 n, coeffOne k‖)
        =ᶠ[atTop] (fun n : ℕ => (n : ℝ) ^ (1 - s.re)) := by
      filter_upwards [eventually_ge_atTop 1] with n hn
      have hn0 : (0:ℝ) < (n : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le one_pos hn
      rw [sum_coeffOne, hf, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hn0,
        Complex.norm_natCast]
      rw [Complex.neg_re, show (1 - s.re) = -s.re + 1 by ring, Real.rpow_add_one hn0.ne']
    rw [Filter.tendsto_congr' hev]
    have hrw : (1 - s.re) = -(s.re - 1) := by ring
    rw [hrw]
    have : Tendsto (fun x : ℝ => x ^ (-(s.re - 1))) atTop (𝓝 0) :=
      tendsto_rpow_neg_atTop (by linarith)
    exact this.comp tendsto_natCast_atTop_atTop
  -- big-O domination by g t = t^(-s.re)
  have hg_dom : (fun t : ℝ => deriv f t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, coeffOne k)
      =O[atTop] (fun t : ℝ => t ^ (-s.re)) := by
    rw [Asymptotics.isBigO_iff]
    refine ⟨‖s‖, ?_⟩
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
    have ht0 : (0:ℝ) < t := lt_of_lt_of_le one_pos ht
    rw [sum_coeffOne, hderiv t ht0, norm_mul, norm_mul]
    have h1 : ‖(-s : ℂ)‖ = ‖s‖ := norm_neg s
    have h2 : ‖(t : ℂ) ^ (-s - 1)‖ = t ^ (-s.re - 1) := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos ht0]; congr 1
    have h3 : ‖((⌊t⌋₊ : ℕ) : ℂ)‖ = (⌊t⌋₊ : ℝ) := by
      rw [Complex.norm_natCast]
    have hgnorm : ‖t ^ (-s.re)‖ = t ^ (-s.re) := by
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg ht0.le _)]
    rw [h1, h2, h3, hgnorm]
    have hfloor : (⌊t⌋₊ : ℝ) ≤ t := Nat.floor_le ht0.le
    calc ‖s‖ * t ^ (-s.re - 1) * (⌊t⌋₊ : ℝ)
        ≤ ‖s‖ * t ^ (-s.re - 1) * t := by
          apply mul_le_mul_of_nonneg_left hfloor
          positivity
      _ = ‖s‖ * t ^ (-s.re) := by
          rw [mul_assoc]
          congr 1
          rw [Real.rpow_sub_one ht0.ne', div_mul_cancel₀]
          exact ht0.ne'
  have hg_int : IntegrableAtFilter (fun t : ℝ => t ^ (-s.re)) atTop :=
    ⟨Ioi 1, Ioi_mem_atTop 1, integrableOn_Ioi_rpow_of_lt (by linarith) one_pos⟩
  have key := tendsto_sum_mul_atTop_nhds_one_sub_integral₀ coeffOne coeffOne_zero
    hf_diff hf_int h_lim hg_dom hg_int
  -- the partial sums also tend to ζ(s)
  have hpz := tendsto_partial_zeta hs
  -- identify the two limits
  have heq : riemannZeta s =
      0 - ∫ t in Ioi (1 : ℝ), deriv f t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, coeffOne k :=
    tendsto_nhds_unique hpz key
  rw [heq, zero_sub]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  simp only [sum_coeffOne]

/-- `∫_{Ioi 1} (x:ℂ)^(-s) dx = 1/(s-1)` for `Re s > 1`. -/
theorem integral_cpow_neg {s : ℂ} (hs : 1 < s.re) :
    ∫ x in Ioi (1 : ℝ), (x : ℂ) ^ (-s) = 1 / (s - 1) := by
  have hsm1 : (-s).re < -1 := by simp only [Complex.neg_re]; linarith
  have hsne1 : s ≠ 1 := by
    intro h; rw [h] at hs; simp at hs
  have hne : (-s + 1) ≠ 0 := by
    intro h
    apply hsne1
    have : s = 1 := by linear_combination -h
    exact this
  have hsm1ne : s - 1 ≠ 0 := sub_ne_zero.mpr hsne1
  rw [integral_Ioi_cpow_of_lt (a := -s) hsm1 one_pos, Complex.ofReal_one, Complex.one_cpow]
  rw [div_eq_div_iff hne hsm1ne]
  ring

/-- `(x:ℂ)^(-s-1) * x = (x:ℂ)^(-s)` for `x > 0`. -/
theorem cpow_aux {s : ℂ} {x : ℝ} (hx : 0 < x) :
    (x : ℂ) ^ (-s - 1) * (x : ℂ) = (x : ℂ) ^ (-s) := by
  have hxne : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  conv_rhs => rw [show (-s) = (-s - 1) + 1 by ring]
  rw [Complex.cpow_add _ _ hxne, Complex.cpow_one]

/-- The Euler–Maclaurin representation for `Re s > 1`. -/
theorem zeta_rep_of_one_lt {s : ℂ} (hs : 1 < s.re) :
    riemannZeta s = s / (s - 1) - s * zetaFractIntegral s := by
  rw [zeta_eq_neg_integral_floor hs]
  -- rewrite integrand: deriv f t * ⌊t⌋₊  on Ioi 1
  have hderiv : ∀ t : ℝ, 0 < t →
      deriv (fun y : ℝ => (y : ℂ) ^ (-s)) t = (-s) * (t : ℂ) ^ (-s - 1) :=
    fun t ht => (hasDerivAt_ofReal_cpow_const ht.ne' (by simpa using
      (show s ≠ 0 by intro h; rw [h] at hs; simp at hs; linarith))).deriv
  -- on Ioi 1, the integrand equals  s * (x:ℂ)^(-s) - s * ({x} * (x:ℂ)^(-s-1))
  have hpt : ∀ x ∈ Ioi (1:ℝ),
      deriv (fun y : ℝ => (y : ℂ) ^ (-s)) x * (⌊x⌋₊ : ℂ)
        = -(s * (x : ℂ) ^ (-s)) + s * (((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)) := by
    intro x hx
    have hx0 : (0:ℝ) < x := lt_trans one_pos hx
    rw [hderiv x hx0]
    -- (⌊x⌋₊ : ℂ) = (x:ℂ) - (Int.fract x : ℂ)
    have hfloor : ((⌊x⌋₊ : ℕ) : ℂ) = (x : ℂ) - ((Int.fract x : ℝ) : ℂ) := by
      have : (⌊x⌋₊ : ℝ) = x - Int.fract x := by
        rw [Int.fract]
        rw [natCast_floor_eq_intCast_floor hx0.le]
        ring
      exact_mod_cast congrArg (Complex.ofReal) this
    rw [hfloor]
    have hxcpow : (x : ℂ) ^ (-s - 1) * (x : ℂ) = (x : ℂ) ^ (-s) := cpow_aux hx0
    linear_combination (-s) * hxcpow
  -- integrability pieces
  have hμ : MeasurableSet (Ioi (1:ℝ)) := measurableSet_Ioi
  have hint_zeta : IntegrableOn (fun x : ℝ => (x : ℂ) ^ (-s)) (Ioi (1:ℝ)) :=
    integrableOn_Ioi_cpow_of_lt (a := -s) (by simp only [Complex.neg_re]; linarith) one_pos
  have hint_J : IntegrableOn
      (fun x : ℝ => ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)) (Ioi (1:ℝ)) :=
    integrableOn_integrand (by linarith)
  rw [setIntegral_congr_fun hμ hpt]
  rw [integral_add (by
        apply Integrable.neg
        exact (hint_zeta.const_mul s))
      (by exact (hint_J.const_mul s))]
  rw [integral_neg, MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  rw [integral_cpow_neg hs]
  show -(-(s * (1 / (s - 1))) + s * zetaFractIntegral s) = s / (s - 1) - s * zetaFractIntegral s
  ring

/-! ### Holomorphy of `zetaFractIntegral` via the Mellin transform -/

/-- The function whose Mellin transform (at `-s`) is `zetaFractIntegral s`. -/
def fracIndic : ℝ → ℂ := fun t => if 1 < t then ((Int.fract t : ℝ) : ℂ) else 0

theorem zetaFractIntegral_eq_mellin (s : ℂ) :
    zetaFractIntegral s = mellin fracIndic (-s) := by
  unfold zetaFractIntegral mellin
  -- reduce the mellin integral from Ioi 0 to Ioi 1
  rw [show (∫ t in Ioi (0:ℝ), (t : ℂ) ^ (-s - 1) • fracIndic t)
        = (∫ t in Ioi (1:ℝ), (t : ℂ) ^ (-s - 1) • fracIndic t) from
      setIntegral_eq_of_subset_of_forall_diff_eq_zero measurableSet_Ioi
        (Ioi_subset_Ioi (by norm_num)) (fun t ht => by
          obtain ⟨_, htns⟩ := ht
          have h1 : ¬ (1:ℝ) < t := htns
          simp only [fracIndic, h1, if_false, smul_zero])]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  have h1 : (1:ℝ) < t := ht
  simp only [fracIndic, h1, if_true, smul_eq_mul]
  rw [mul_comm]

theorem fracIndic_norm_le (t : ℝ) : ‖fracIndic t‖ ≤ 1 := by
  unfold fracIndic
  by_cases h : 1 < t
  · simp only [h, if_true]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Int.fract_nonneg t)]
    exact (Int.fract_lt_one t).le
  · simp only [h, if_false, norm_zero]; norm_num

theorem fracIndic_eq_indicator :
    fracIndic = (Ioi (1:ℝ)).indicator (fun t => ((Int.fract t : ℝ) : ℂ)) := by
  funext t
  unfold fracIndic
  rw [Set.indicator_apply]
  by_cases h : 1 < t
  · rw [if_pos h, if_pos (Set.mem_Ioi.mpr h)]
  · rw [if_neg h, if_neg (by simpa using h)]

theorem measurable_fracIndic : Measurable fracIndic := by
  rw [fracIndic_eq_indicator]
  apply Measurable.indicator _ measurableSet_Ioi
  exact Complex.measurable_ofReal.comp measurable_fract

theorem locallyIntegrable_fracIndic : MeasureTheory.LocallyIntegrable fracIndic volume := by
  apply MeasureTheory.LocallyIntegrable.mono (g := fracIndic) (f := fun _ : ℝ => (1:ℝ))
    (locallyIntegrable_const _)
  · exact measurable_fracIndic.aestronglyMeasurable
  · filter_upwards with t
    rw [Real.norm_eq_abs, abs_one]
    exact fracIndic_norm_le t

/-- `zetaFractIntegral` is differentiable on `Re s > 0`. -/
theorem differentiableAt_zetaFractIntegral {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ zetaFractIntegral s := by
  have hmellin : DifferentiableAt ℂ (mellin fracIndic) (-s) := by
    apply mellin_differentiableAt_of_isBigO_rpow (a := 0) (b := -s.re - 1)
    · -- LocallyIntegrableOn fracIndic (Ioi 0)
      exact locallyIntegrable_fracIndic.locallyIntegrableOn _
    · -- fracIndic =O[atTop] (·^(-0))
      rw [neg_zero]
      apply Asymptotics.IsBigO.of_bound 1
      filter_upwards [eventually_gt_atTop (0:ℝ)] with t ht
      rw [Real.rpow_zero, norm_one, mul_one]
      exact fracIndic_norm_le t
    · -- (-s).re < 0
      simp only [Complex.neg_re]; linarith
    · -- fracIndic =O[𝓝[>] 0] (·^(-b)) ; fracIndic = 0 near 0
      apply Asymptotics.IsBigO.of_bound 1
      filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0:ℝ) < 1)] with t ht
      have h1 : ¬ (1:ℝ) < t := by
        obtain ⟨_, h⟩ := ht; linarith
      simp only [fracIndic, h1, if_false, norm_zero]
      positivity
    · -- b < (-s).re
      simp only [Complex.neg_re]; linarith
  have hcomp : zetaFractIntegral = (mellin fracIndic) ∘ (fun s : ℂ => -s) := by
    funext s; exact zetaFractIntegral_eq_mellin s
  rw [hcomp]
  exact hmellin.comp s (differentiableAt_id.neg)

/-- The RHS of the Euler–Maclaurin representation. -/
def zetaRHS (s : ℂ) : ℂ := s / (s - 1) - s * zetaFractIntegral s

/-- `zetaRHS` is analytic on any open set contained in `{0 < re}` and avoiding `s = 1`. -/
theorem analyticOnNhd_zetaRHS {U : Set ℂ} (hUopen : IsOpen U)
    (hUre : ∀ z ∈ U, 0 < z.re) (hU1 : (1 : ℂ) ∉ U) :
    AnalyticOnNhd ℂ zetaRHS U := by
  apply DifferentiableOn.analyticOnNhd _ hUopen
  intro s hs
  have hre : 0 < s.re := hUre s hs
  have hsne1 : s ≠ 1 := fun h => hU1 (h ▸ hs)
  apply DifferentiableAt.differentiableWithinAt
  apply DifferentiableAt.sub
  · exact DifferentiableAt.div differentiableAt_id
      (differentiableAt_id.sub (differentiableAt_const 1)) (sub_ne_zero.mpr hsne1)
  · exact differentiableAt_id.mul (differentiableAt_zetaFractIntegral hre)

/-- The representation `ζ(s) = s/(s-1) - s·J(s)` for `0 < re s` and `im s ≠ 0`. -/
theorem zeta_rep_of_im_ne_zero {s : ℂ} (hre : 0 < s.re) (him : s.im ≠ 0) :
    riemannZeta s = s / (s - 1) - s * zetaFractIntegral s := by
  -- choose the quadrant containing s
  set Q : Set ℂ := {z : ℂ | 0 < z.re ∧ (if 0 < s.im then 0 < z.im else z.im < 0)} with hQ
  have hsQ : s ∈ Q := by
    rw [hQ]; refine ⟨hre, ?_⟩
    by_cases h : 0 < s.im
    · simp [h]
    · simp only [h, if_false]
      exact lt_of_le_of_ne (not_lt.mp h) him
  have hQopen : IsOpen Q := by
    rw [hQ]
    by_cases h : 0 < s.im
    · simp only [h, if_true]
      exact (isOpen_lt continuous_const Complex.continuous_re).inter
        (isOpen_lt continuous_const Complex.continuous_im)
    · simp only [h, if_false]
      exact (isOpen_lt continuous_const Complex.continuous_re).inter
        (isOpen_lt Complex.continuous_im continuous_const)
  have hQconv : Convex ℝ Q := by
    rw [hQ]
    by_cases h : 0 < s.im
    · simp only [h, if_true]
      exact (convex_halfSpace_re_gt 0).inter (convex_halfSpace_im_gt 0)
    · simp only [h, if_false]
      exact (convex_halfSpace_re_gt 0).inter (convex_halfSpace_im_lt 0)
  have hQpre : IsPreconnected Q := (hQconv.isPathConnected ⟨s, hsQ⟩).isConnected.isPreconnected
  -- ζ analytic on Q
  have hζ : AnalyticOnNhd ℂ riemannZeta Q := by
    apply analyticOn_riemannZeta.mono
    intro z hz hz1
    rw [Set.mem_singleton_iff] at hz1
    rw [hQ] at hz; obtain ⟨_, hzim⟩ := hz
    rw [hz1] at hzim
    by_cases h : 0 < s.im <;> simp [h] at hzim
  -- g analytic on Q
  have hg : AnalyticOnNhd ℂ zetaRHS Q := by
    apply analyticOnNhd_zetaRHS hQopen
    · intro z hz; rw [hQ] at hz; exact hz.1
    · rw [hQ]; intro h1
      obtain ⟨_, h1im⟩ := h1
      by_cases h : 0 < s.im <;> simp [h] at h1im
  -- pick a point in Q ∩ {Re > 1}
  set w : ℂ := if 0 < s.im then ⟨2, 1⟩ else ⟨2, -1⟩ with hw
  have hwQ : w ∈ Q := by
    rw [hQ, hw]
    by_cases h : 0 < s.im <;> simp [h]
  have hwre : 1 < w.re := by rw [hw]; by_cases h : 0 < s.im <;> simp [h]
  -- ζ and g agree near w (they agree on the open set {Re > 1})
  have hagree : riemannZeta =ᶠ[𝓝 w] zetaRHS := by
    have hopen : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
    have hmem : w ∈ {z : ℂ | 1 < z.re} := hwre
    filter_upwards [hopen.mem_nhds hmem] with z hz
    rw [zetaRHS]
    exact zeta_rep_of_one_lt hz
  have := AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq hζ hg hQpre hwQ hagree hsQ
  simpa only [zetaRHS] using this

/-- A polynomial bound for `ζ` on the vertical strip `1/2 ≤ Re s ≤ 5/2`, `|Im s| ≥ 1`,
obtained from the first-order Euler–Maclaurin representation. -/
theorem norm_riemannZeta_poly_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, (1:ℝ)/2 ≤ s.re → s.re ≤ 5/2 → 1 ≤ |s.im| →
      ‖riemannZeta s‖ ≤ C * (1 + |s.im|) := by
  refine ⟨6, by norm_num, ?_⟩
  intro s hlo hhi ht
  have hσpos : 0 < s.re := lt_of_lt_of_le (by norm_num) hlo
  have him0 : s.im ≠ 0 := by
    intro h; rw [h] at ht; norm_num at ht
  have rep : riemannZeta s = s / (s - 1) - s * zetaFractIntegral s :=
    zeta_rep_of_im_ne_zero hσpos him0
  have hsne1 : s ≠ 1 := by
    intro h
    rw [h] at ht
    norm_num at ht
  -- bound ‖s‖ ≤ σ + |t| ≤ 5/2 + |t|
  have hnorms : ‖s‖ ≤ 5/2 + |s.im| := by
    calc ‖s‖ ≤ |s.re| + |s.im| := Complex.norm_le_abs_re_add_abs_im s
      _ ≤ 5/2 + |s.im| := by
            have : |s.re| ≤ 5/2 := abs_le.mpr ⟨by linarith, hhi⟩
            linarith
  -- bound ‖s - 1‖ ≥ |s.im| ≥ 1
  have hsm1 : 1 ≤ ‖s - 1‖ := by
    calc (1 : ℝ) ≤ |s.im| := ht
      _ = |(s - 1).im| := by simp
      _ ≤ ‖s - 1‖ := Complex.abs_im_le_norm _
  have hsm1pos : 0 < ‖s - 1‖ := lt_of_lt_of_le one_pos hsm1
  -- the representation
  rw [rep]
  -- ‖s/(s-1)‖ ≤ ‖s‖  (since ‖s-1‖ ≥ 1)
  have hterm1 : ‖s / (s - 1)‖ ≤ 5/2 + |s.im| := by
    rw [norm_div]
    calc ‖s‖ / ‖s - 1‖ ≤ ‖s‖ / 1 := by
            apply div_le_div_of_nonneg_left (norm_nonneg _) one_pos hsm1
      _ = ‖s‖ := by rw [div_one]
      _ ≤ 5/2 + |s.im| := hnorms
  -- ‖s * J‖ = ‖s‖ * ‖J‖ ≤ ‖s‖ * (1/σ) ≤ ‖s‖ * 2 ≤ (5/2+|t|)*2
  have hJ : ‖zetaFractIntegral s‖ ≤ 1 / s.re := norm_zetaFractIntegral_le hσpos
  have hinvσ : (1 : ℝ) / s.re ≤ 2 := by
    rw [div_le_iff₀ hσpos]
    have : (1:ℝ)/2 ≤ s.re := hlo
    linarith
  have hterm2 : ‖s * zetaFractIntegral s‖ ≤ (5/2 + |s.im|) * 2 := by
    rw [norm_mul]
    calc ‖s‖ * ‖zetaFractIntegral s‖
        ≤ (5/2 + |s.im|) * (1 / s.re) := by
          apply mul_le_mul hnorms hJ (norm_nonneg _)
          linarith [abs_nonneg s.im]
      _ ≤ (5/2 + |s.im|) * 2 := by
          apply mul_le_mul_of_nonneg_left hinvσ
          linarith [abs_nonneg s.im]
  calc ‖s / (s - 1) - s * zetaFractIntegral s‖
      ≤ ‖s / (s - 1)‖ + ‖s * zetaFractIntegral s‖ := norm_sub_le _ _
    _ ≤ (5/2 + |s.im|) + (5/2 + |s.im|) * 2 := by linarith
    _ ≤ 6 * (1 + |s.im|) := by nlinarith [abs_nonneg s.im, ht]

end

