import Mathlib

open Complex

/-- The real Basel sum: `∑' n, 1/(n+1)^2 = π²/6`. -/
theorem basel_sum : (∑' n : ℕ, (1 : ℝ) / ((n:ℝ) + 1) ^ 2) = Real.pi ^ 2 / 6 := by
  have h2 : riemannZeta 2 = ∑' n : ℕ, 1 / ((n:ℂ) + 1) ^ (2:ℂ) := by
    have hre : (1:ℝ) < (2:ℂ).re := by norm_num
    exact zeta_eq_tsum_one_div_nat_add_one_cpow hre
  rw [riemannZeta_two] at h2
  have hterm : ∀ n : ℕ, (1 : ℂ) / ((n:ℂ) + 1) ^ (2:ℂ)
      = ((((1 : ℝ) / ((n:ℝ) + 1) ^ 2) : ℝ) : ℂ) := by
    intro n
    rw [show (2:ℂ) = ((2:ℕ):ℂ) by norm_num, cpow_natCast]
    push_cast
    ring
  rw [tsum_congr hterm] at h2
  rw [← Complex.ofReal_tsum] at h2
  have hh := congrArg Complex.re h2
  simp only [Complex.ofReal_re] at hh
  rw [← hh]
  rw [← Complex.ofReal_pow, show (6:ℂ) = ((6:ℝ):ℂ) by norm_num,
    ← Complex.ofReal_div, Complex.ofReal_re]

/-- The real Basel series is summable. -/
theorem basel_summable : Summable (fun n : ℕ => (1 : ℝ) / ((n:ℝ) + 1) ^ 2) := by
  have hbase : Summable (fun n : ℕ => (1 : ℝ) / (n:ℝ) ^ 2) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2)
  have := (summable_nat_add_iff 1).mpr hbase
  simpa [Nat.cast_add, Nat.cast_one] using this

/-- Tail Basel sum starting at `n+2`: `∑' n, 1/(n+2)^2 = π²/6 - 1`. -/
theorem basel_tail : (∑' n : ℕ, (1 : ℝ) / ((n:ℝ) + 2) ^ 2) = Real.pi ^ 2 / 6 - 1 := by
  have hsplit := basel_summable.tsum_eq_zero_add
  rw [basel_sum] at hsplit
  -- hsplit : π²/6 = (1/(0+1)^2) + ∑' n, 1/((n+1)+1)^2
  have h0 : (1 : ℝ) / (((0:ℕ):ℝ) + 1) ^ 2 = 1 := by norm_num
  rw [h0] at hsplit
  have hcong : (∑' n : ℕ, (1 : ℝ) / ((((n+1):ℕ):ℝ) + 1) ^ 2)
      = ∑' n : ℕ, (1 : ℝ) / ((n:ℝ) + 2) ^ 2 := by
    apply tsum_congr; intro n; push_cast; ring_nf
  rw [hcong] at hsplit
  linarith

/-- The tail Basel series `∑' n, 1/(n+2)^2` is summable. -/
theorem basel_tail_summable : Summable (fun n : ℕ => (1 : ℝ) / ((n:ℝ) + 2) ^ 2) := by
  have := (summable_nat_add_iff 1).mpr basel_summable
  apply this.congr; intro n; push_cast; ring_nf

/-- Uniform positive lower bound on `Re ζ` along the vertical line `σ = 2`.
The constant is `c₀ = 2 - π²/6 > 0`. -/
theorem re_riemannZeta_two_add_I_ge :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ t : ℝ, c₀ ≤ (riemannZeta (2 + t*Complex.I)).re := by
  refine ⟨2 - Real.pi ^ 2 / 6, ?_, ?_⟩
  · have hpi : Real.pi < 3.15 := Real.pi_lt_d2
    have hpi0 : (0:ℝ) < Real.pi := Real.pi_pos
    nlinarith [hpi, hpi0]
  · intro t
    set s : ℂ := 2 + t * Complex.I with hs
    have hsre : s.re = 2 := by rw [hs]; simp
    have hre : (1 : ℝ) < s.re := by rw [hsre]; norm_num
    -- ζ(s) = ∑' n, 1/(n+1)^s  (shifted form, avoids 0^s)
    have hzeta : riemannZeta s = ∑' n : ℕ, 1 / ((n:ℂ) + 1) ^ s :=
      zeta_eq_tsum_one_div_nat_add_one_cpow hre
    have hsum : Summable (fun n : ℕ => 1 / ((n:ℂ) + 1) ^ s) := by
      have hs0 : Summable (fun n : ℕ => 1 / (n:ℂ) ^ s) :=
        Complex.summable_one_div_nat_cpow.mpr hre
      have := (summable_nat_add_iff 1).mpr hs0
      simpa [Nat.cast_add, Nat.cast_one] using this
    -- take real parts through the tsum
    have hre_eq : (riemannZeta s).re = ∑' n : ℕ, (1 / ((n:ℂ) + 1) ^ s).re := by
      rw [hzeta]; exact Complex.reCLM.map_tsum hsum
    have hsumRe : Summable (fun n : ℕ => (1 / ((n:ℂ) + 1) ^ s).re) := by
      have h := hsum.map Complex.reCLM Complex.reCLM.continuous
      exact h.congr (fun n => rfl)
    rw [hre_eq, hsumRe.tsum_eq_zero_add]
    -- n=0 term = (1/1^s).re = 1
    have h0 : (1 / (((0:ℕ):ℂ) + 1) ^ s).re = 1 := by norm_num
    rw [h0]
    -- align the goal's tail (indexed by ↑(b+1)) with the ↑n+1 form
    rw [show (∑' b : ℕ, (1 / (((((b+1):ℕ)):ℂ) + 1) ^ s).re)
          = ∑' n : ℕ, (1 / (((((n:ℕ)+1):ℂ)) + 1) ^ s).re from
        tsum_congr (fun n => by push_cast; ring_nf)]
    -- tail T = ∑' n, (1/((n+1)+1)^s).re
    set T : ℝ := ∑' n : ℕ, (1 / (((((n:ℕ)+1):ℂ)) + 1) ^ s).re with hT
    have hTsum : Summable (fun n : ℕ => (1 / (((((n:ℕ)+1):ℂ)) + 1) ^ s).re) := by
      have h := (summable_nat_add_iff 1).mpr hsumRe
      apply h.congr; intro n; push_cast; ring_nf
    -- each norm: ‖1/((n+1)+1)^s‖ = 1/((n:ℝ)+2)^2
    have htermnorm : ∀ n : ℕ,
        ‖1 / (((((n:ℕ)+1):ℂ)) + 1) ^ s‖ = (1 : ℝ) / ((n:ℝ) + 2) ^ 2 := by
      intro n
      have hcast : ((((n:ℕ)+1):ℂ) + 1) = (((n + 2 : ℕ)) : ℂ) := by push_cast; ring
      rw [hcast, one_div, norm_inv, norm_natCast_cpow_of_pos (by positivity), hsre]
      rw [show ((n + 2 : ℕ) : ℝ) = ((n:ℝ) + 2) by push_cast; ring]
      rw [Real.rpow_ofNat, one_div]
    -- norm series summable
    have hnormsum : Summable (fun n : ℕ => ‖1 / (((((n:ℕ)+1):ℂ)) + 1) ^ s‖) := by
      apply Summable.congr basel_tail_summable
      intro n; exact (htermnorm n).symm
    -- T ≥ - ∑' ‖·‖
    have hTge : - (∑' n : ℕ, ‖1 / (((((n:ℕ)+1):ℂ)) + 1) ^ s‖) ≤ T := by
      rw [hT, ← tsum_neg]
      apply Summable.tsum_mono hnormsum.neg hTsum
      · intro n
        have := Complex.abs_re_le_norm (1 / (((((n:ℕ)+1):ℂ)) + 1) ^ s)
        have h2 := (abs_le.1 this).1
        simpa using h2
    -- ∑' ‖·‖ = π²/6 - 1
    have hnormtsum : (∑' n : ℕ, ‖1 / (((((n:ℕ)+1):ℂ)) + 1) ^ s‖)
        = Real.pi ^ 2 / 6 - 1 := by
      rw [tsum_congr htermnorm, basel_tail]
    rw [hnormtsum] at hTge
    linarith
