import Mathlib
open Complex Filter Topology

noncomputable def genus1Factor (ρ s : ℂ) : ℂ := (1 - s / ρ) * Complex.exp (s / ρ)

theorem norm_genus1_sub_one_le {w : ℂ} (hw : ‖w‖ ≤ 1) :
    ‖(1 - w) * Complex.exp w - 1‖ ≤ 3 * ‖w‖ ^ 2 := by
  have hkey : (1 - w) * Complex.exp w - 1
      = (Complex.exp w - 1 - w) - w * (Complex.exp w - 1) := by ring
  have hp1 : ‖Complex.exp w - 1 - w‖ ≤ ‖w‖ ^ 2 := by
    have h := Complex.exp_bound (x := w) hw (n := 2) (by norm_num)
    have hsum : ∑ i ∈ Finset.range 2, w ^ i / (Nat.factorial i : ℂ) = 1 + w := by
      simp [Finset.sum_range_succ, Nat.factorial]
    rw [hsum] at h
    have heq : ‖Complex.exp w - (1 + w)‖ = ‖Complex.exp w - 1 - w‖ := by congr 1; ring
    rw [heq] at h
    refine h.trans (mul_le_of_le_one_right (sq_nonneg _) ?_)
    norm_num [Nat.factorial]
  have hp2 : ‖w * (Complex.exp w - 1)‖ ≤ 2 * ‖w‖ ^ 2 := by
    have h := Complex.exp_bound (x := w) hw (n := 1) (by norm_num)
    have hsum : ∑ i ∈ Finset.range 1, w ^ i / (Nat.factorial i : ℂ) = 1 := by simp
    rw [hsum] at h
    have hle : ‖Complex.exp w - 1‖ ≤ 2 * ‖w‖ := by
      refine h.trans (le_of_eq ?_); simp only [Nat.factorial_one, Nat.cast_one, mul_one, pow_one]; ring
    rw [norm_mul]
    calc ‖w‖ * ‖Complex.exp w - 1‖ ≤ ‖w‖ * (2 * ‖w‖) := mul_le_mul_of_nonneg_left hle (norm_nonneg w)
      _ = 2 * ‖w‖ ^ 2 := by ring
  rw [hkey]
  calc ‖(Complex.exp w - 1 - w) - w * (Complex.exp w - 1)‖
      ≤ ‖Complex.exp w - 1 - w‖ + ‖w * (Complex.exp w - 1)‖ := norm_sub_le _ _
    _ ≤ ‖w‖ ^ 2 + 2 * ‖w‖ ^ 2 := add_le_add hp1 hp2
    _ = 3 * ‖w‖ ^ 2 := by ring

/-- Pointwise: `genus1Factor (loc i) s - 1 = (1 - s/loc i)·exp(s/loc i) - 1`,
so the norm bound applies with `w = s / loc i`. -/
theorem norm_genus1Factor_sub_one_le {ρ s : ℂ} (h : ‖s / ρ‖ ≤ 1) :
    ‖genus1Factor ρ s - 1‖ ≤ 3 * ‖s / ρ‖ ^ 2 := by
  unfold genus1Factor
  exact norm_genus1_sub_one_le h

theorem genus1Product_multipliableLocallyUniformlyOn
    {ι : Type*} (loc : ι → ℂ)
    (_hne : ∀ i, loc i ≠ 0)
    (hsumm : Summable (fun i => 1 / ‖loc i‖ ^ 2))
    (hcofin : Tendsto (fun i => ‖loc i‖) cofinite atTop) :
    MultipliableLocallyUniformlyOn (fun i s => genus1Factor (loc i) s) Set.univ := by
  -- Each factor is continuous (entire).
  have hcts : ∀ i, Continuous (fun s : ℂ => genus1Factor (loc i) s) := by
    intro i
    unfold genus1Factor
    fun_prop
  -- Continuity of `s ↦ genus1Factor (loc i) s - 1`.
  have hcts' : ∀ i, Continuous (fun s : ℂ => genus1Factor (loc i) s - 1) := by
    intro i; exact (hcts i).sub continuous_const
  -- Reduce to the `1 + f` shape and use the congr lemma.
  apply MultipliableLocallyUniformlyOn_congr
    (f := fun i s => 1 + (genus1Factor (loc i) s - 1))
    (f' := fun i s => genus1Factor (loc i) s)
  · intro i s _hs; ring
  -- Now prove the `1 + f` version converges locally uniformly on `univ`.
  apply multipliableLocallyUniformlyOn_of_of_forall_exists_nhds
  intro x _hx
  -- Pick R big enough so that the closed ball of radius R is a nbhd of x.
  set R : ℝ := ‖x‖ + 1 with hR
  have hRpos : 0 < R := by positivity
  refine ⟨Metric.closedBall (0 : ℂ) R, ?_, ?_⟩
  · -- closedBall 0 R ∈ 𝓝[univ] x
    rw [nhdsWithin_univ]
    refine Metric.closedBall_mem_nhds_of_mem ?_
    simp only [Metric.mem_ball, dist_zero_right]
    rw [hR]; linarith [norm_nonneg x]
  · -- MultipliableUniformlyOn on the compact closed ball.
    have hK : IsCompact (Metric.closedBall (0 : ℂ) R) := isCompact_closedBall _ _
    -- summable majorant u i = 3 R^2 * (1 / ‖loc i‖^2)
    have hu : Summable (fun i => 3 * R ^ 2 * (1 / ‖loc i‖ ^ 2)) := hsumm.mul_left _
    -- the M-test bound: cofinitely many i with ‖loc i‖ ≥ R
    have hge : ∀ᶠ i in cofinite, R ≤ ‖loc i‖ := hcofin.eventually_ge_atTop R
    have hbound : ∀ᶠ i in cofinite,
        ∀ s ∈ Metric.closedBall (0 : ℂ) R, ‖genus1Factor (loc i) s - 1‖
          ≤ 3 * R ^ 2 * (1 / ‖loc i‖ ^ 2) := by
      filter_upwards [hge] with i hi s hs
      have hsR : ‖s‖ ≤ R := by simpa [dist_zero_right] using hs
      have hlocpos : 0 < ‖loc i‖ := by linarith
      -- ‖s / loc i‖ ≤ 1
      have hdiv : ‖s / loc i‖ ≤ 1 := by
        rw [norm_div]
        rw [div_le_one hlocpos]
        exact le_trans hsR hi
      have hb := norm_genus1Factor_sub_one_le (ρ := loc i) (s := s) hdiv
      refine hb.trans ?_
      -- 3 * ‖s/loc i‖^2 ≤ 3 * R^2 * (1/‖loc i‖^2)
      have hsq : ‖s‖ ^ 2 ≤ R ^ 2 := by
        apply pow_le_pow_left₀ (norm_nonneg s) hsR
      have hlsq : 0 < ‖loc i‖ ^ 2 := by positivity
      rw [norm_div, div_pow]
      calc 3 * (‖s‖ ^ 2 / ‖loc i‖ ^ 2)
          ≤ 3 * (R ^ 2 / ‖loc i‖ ^ 2) := by
            gcongr
        _ = 3 * R ^ 2 * (1 / ‖loc i‖ ^ 2) := by ring
    -- assemble via multipliableUniformlyOn_one_add
    have := Summable.multipliableUniformlyOn_one_add (f := fun i s => genus1Factor (loc i) s - 1)
      (K := Metric.closedBall (0 : ℂ) R) (u := fun i => 3 * R ^ 2 * (1 / ‖loc i‖ ^ 2))
      hK hu hbound (fun i => (hcts' i).continuousOn)
    exact this
