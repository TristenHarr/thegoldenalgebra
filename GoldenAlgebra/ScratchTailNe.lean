import Mathlib

open Complex Filter Topology

/-!
# Closing the two derivable gaps of the local split (Task #1 → unconditional)

The local-split theorem was proved conditional on two facts the abstract agent couldn't get from
`MultipliableLocallyUniformlyOn` alone. BUT in the real ξ setting we ALSO have inverse-square
summability `Summable (1/‖loc i‖²)`, which makes BOTH derivable. Prove them here.

`genus1Factor ρ s = (1 - s/ρ)·exp(s/ρ)`; the proven quadratic bound (paste it):
`‖genus1Factor ρ s - 1‖ ≤ 3‖s/ρ‖²` when `‖s/ρ‖ ≤ 1`.
-/

noncomputable def genus1Factor (ρ s : ℂ) : ℂ := (1 - s / ρ) * Complex.exp (s / ρ)

/-- The proven quadratic bound (pasted from `ScratchItem5.lean`'s `norm_genus1_sub_one_le`). -/
theorem norm_genus1Factor_sub_one_le {ρ s : ℂ} (h : ‖s / ρ‖ ≤ 1) :
    ‖genus1Factor ρ s - 1‖ ≤ 3 * ‖s / ρ‖ ^ 2 := by
  set w := s / ρ with hw
  show ‖(1 - w) * Complex.exp w - 1‖ ≤ 3 * ‖w‖ ^ 2
  have hkey : (1 - w) * Complex.exp w - 1
      = (Complex.exp w - 1 - w) - w * (Complex.exp w - 1) := by ring
  have hp1 : ‖Complex.exp w - 1 - w‖ ≤ ‖w‖ ^ 2 := by
    have hb := Complex.exp_bound (x := w) h (n := 2) (by norm_num)
    have hsum : ∑ i ∈ Finset.range 2, w ^ i / (Nat.factorial i : ℂ) = 1 + w := by
      simp [Finset.sum_range_succ, Nat.factorial]
    rw [hsum] at hb
    have heq : ‖Complex.exp w - (1 + w)‖ = ‖Complex.exp w - 1 - w‖ := by congr 1; ring
    rw [heq] at hb
    refine hb.trans (mul_le_of_le_one_right (sq_nonneg _) ?_)
    norm_num [Nat.factorial]
  have hp2 : ‖w * (Complex.exp w - 1)‖ ≤ 2 * ‖w‖ ^ 2 := by
    have hb := Complex.exp_bound (x := w) h (n := 1) (by norm_num)
    have hsum : ∑ i ∈ Finset.range 1, w ^ i / (Nat.factorial i : ℂ) = 1 := by simp
    rw [hsum] at hb
    have hle : ‖Complex.exp w - 1‖ ≤ 2 * ‖w‖ := by
      refine hb.trans (le_of_eq ?_)
      simp only [Nat.factorial_one, Nat.cast_one, mul_one, pow_one]; ring
    rw [norm_mul]
    calc ‖w‖ * ‖Complex.exp w - 1‖ ≤ ‖w‖ * (2 * ‖w‖) := mul_le_mul_of_nonneg_left hle (norm_nonneg w)
      _ = 2 * ‖w‖ ^ 2 := by ring
  rw [hkey]
  calc ‖(Complex.exp w - 1 - w) - w * (Complex.exp w - 1)‖
      ≤ ‖Complex.exp w - 1 - w‖ + ‖w * (Complex.exp w - 1)‖ := norm_sub_le _ _
    _ ≤ ‖w‖ ^ 2 + 2 * ‖w‖ ^ 2 := add_le_add hp1 hp2
    _ = 3 * ‖w‖ ^ 2 := by ring

/-- GAP 2 (`htail_ne`): the genus-1 product over a family with all `loc i ≠ z` and inverse-square
summable moduli is NONZERO at `z`. Route: at fixed `z`, `aᵢ := genus1Factor (loc i) z − 1` satisfies
`Σ ‖aᵢ‖ ≤ Σ 3‖z‖²/‖loc i‖² < ∞` EVENTUALLY (split off the finitely-many indices with `‖z/loc i‖>1`),
and each factor `1 + aᵢ = genus1Factor (loc i) z ≠ 0` (from `loc i ≠ z`); then
`tprod_one_add_ne_zero_of_summable` gives `∏(1 + aᵢ) ≠ 0`. -/
theorem genus1Product_ne_zero_of_summable
    {ι : Type*} (loc : ι → ℂ) (z : ℂ)
    (hsumm : Summable (fun i => 1 / ‖loc i‖ ^ 2))
    (hne : ∀ i, loc i ≠ 0)
    (hzne : ∀ i, loc i ≠ z) :
    (∏' i, genus1Factor (loc i) z) ≠ 0 := by
  -- Set aᵢ := genus1Factor (loc i) z − 1 ; then genus1Factor (loc i) z = 1 + aᵢ.
  set a : ι → ℂ := fun i => genus1Factor (loc i) z - 1 with ha
  have hfac : ∀ i, genus1Factor (loc i) z = 1 + a i := by
    intro i; simp [ha]
  -- Each factor is nonzero: genus1Factor (loc i) z = (1 - z/loc i)·exp(z/loc i),
  -- the exponential is nonzero, and (1 - z/loc i) ≠ 0 since loc i ≠ z.
  have hfne : ∀ i, (1 : ℂ) + a i ≠ 0 := by
    intro i
    rw [← hfac i]
    unfold genus1Factor
    apply mul_ne_zero
    · -- 1 - z / loc i ≠ 0
      intro hcontra
      have : z / loc i = 1 := by linear_combination -hcontra
      rw [div_eq_one_iff_eq (hne i)] at this
      exact (hzne i) this.symm
    · exact Complex.exp_ne_zero _
  -- Summability of ‖aᵢ‖ via eventual bound ‖aᵢ‖ ≤ 3‖z‖²·(1/‖loc i‖²).
  have hu : Summable (fun i => 3 * ‖z‖ ^ 2 * (1 / ‖loc i‖ ^ 2)) := hsumm.mul_left _
  -- ‖z / loc i‖ → 0 along cofinite would be nice, but we only have the bound EVENTUALLY where
  -- ‖z / loc i‖ ≤ 1. By summability, ‖loc i‖ → ∞ cofinitely, so ‖z/loc i‖ ≤ 1 cofinitely.
  -- From hsumm, 1/‖loc i‖² → 0 cofinitely, hence ‖loc i‖ ≥ ‖z‖ eventually.
  have htend : Tendsto (fun i => 1 / ‖loc i‖ ^ 2) cofinite (𝓝 0) := hsumm.tendsto_cofinite_zero
  have hzero_lt : (0:ℝ) < 1 / (max ‖z‖ 1) ^ 2 := by positivity
  have hev : ∀ᶠ i in cofinite, 1 / ‖loc i‖ ^ 2 < 1 / (max ‖z‖ 1) ^ 2 := by
    have := htend.eventually (eventually_lt_nhds hzero_lt)
    simpa using this
  have hbound : ∀ᶠ i in cofinite,
      ‖a i‖ ≤ 3 * ‖z‖ ^ 2 * (1 / ‖loc i‖ ^ 2) := by
    filter_upwards [hev] with i hi
    -- From hi: 1/‖loc i‖² < 1/(max ‖z‖ 1)², so ‖loc i‖ > max ‖z‖ 1 ≥ ‖z‖, and ‖loc i‖ > 0.
    have hmpos : (0:ℝ) < max ‖z‖ 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
    have hlocpos : 0 < ‖loc i‖ := by
      rw [norm_pos_iff]; exact hne i
    have hlt : (max ‖z‖ 1) ^ 2 < ‖loc i‖ ^ 2 := by
      have h1 : (0:ℝ) < (max ‖z‖ 1) ^ 2 := by positivity
      have h2 : (0:ℝ) < ‖loc i‖ ^ 2 := by positivity
      have := (div_lt_div_iff_of_pos_left (by norm_num) h2 h1).mp hi
      linarith [this]
    have hmlt : max ‖z‖ 1 < ‖loc i‖ := by
      have := (pow_lt_pow_iff_left₀ (le_of_lt hmpos) (le_of_lt hlocpos) (by norm_num : 2 ≠ 0)).mp hlt
      exact this
    have hzle : ‖z‖ < ‖loc i‖ := lt_of_le_of_lt (le_max_left _ _) hmlt
    have hdiv : ‖z / loc i‖ ≤ 1 := by
      rw [norm_div, div_le_one hlocpos]; exact le_of_lt hzle
    have hb : ‖a i‖ ≤ 3 * ‖z / loc i‖ ^ 2 := norm_genus1Factor_sub_one_le (ρ := loc i) (s := z) hdiv
    refine hb.trans (le_of_eq ?_)
    -- 3 * ‖z/loc i‖² = 3 * ‖z‖² * (1/‖loc i‖²)
    rw [norm_div, div_pow]; ring
  have hsummA : Summable (fun i => ‖a i‖) :=
    hu.of_norm_bounded_eventually (by simpa using hbound)
  -- Conclude via the nonvanishing product lemma.
  have hprod : (∏' i, (1 + a i)) ≠ 0 :=
    tprod_one_add_ne_zero_of_summable hfne hsummA
  have hcongr : (∏' i, genus1Factor (loc i) z) = ∏' i, (1 + a i) := by
    apply tprod_congr; intro i; exact hfac i
  rw [hcongr]; exact hprod

/-- GAP 1 (`hcompl`): the family restricted to the complement of a FINITE index set is still
locally-uniformly multipliable. The complement subtype `{i // i ∉ H}` is cofinite, so the
summable majorant `1/‖loc i‖²` and the `cofinite → atTop` divergence of `‖loc i‖` both restrict
via the injective inclusion `Subtype.val`; the M-test (`Summable.multipliableUniformlyOn_one_add`)
then applies exactly as in `ScratchItem5`'s loc-unif proof. -/
theorem genus1Product_compl_multipliableLocallyUniformlyOn
    {ι : Type*} (loc : ι → ℂ) (H : Finset ι)
    (hsumm : Summable (fun i => 1 / ‖loc i‖ ^ 2))
    (hne : ∀ i, loc i ≠ 0)
    (hcofin : Tendsto (fun i => ‖loc i‖) cofinite atTop) :
    MultipliableLocallyUniformlyOn
      (fun i : {i // i ∉ H} => fun s => genus1Factor (loc i) s) Set.univ := by
  -- Restrict hypotheses to the subtype via the injective inclusion `Subtype.val`.
  have hincl : Function.Injective (fun j : {i // i ∉ H} => (j : ι)) := Subtype.val_injective
  set loc' : {i // i ∉ H} → ℂ := fun j => loc (j : ι) with hloc'
  have hne' : ∀ j, loc' j ≠ 0 := fun j => hne _
  have hsumm' : Summable (fun j : {i // i ∉ H} => 1 / ‖loc' j‖ ^ 2) :=
    (hsumm.comp_injective hincl)
  have hcofin' : Tendsto (fun j : {i // i ∉ H} => ‖loc' j‖) cofinite atTop :=
    hcofin.comp hincl.tendsto_cofinite
  -- Now prove loc-unif multipliability for loc' (same structure as ScratchItem5).
  have hcts : ∀ j, Continuous (fun s : ℂ => genus1Factor (loc' j) s) := by
    intro j; unfold genus1Factor; fun_prop
  have hcts' : ∀ j, Continuous (fun s : ℂ => genus1Factor (loc' j) s - 1) := by
    intro j; exact (hcts j).sub continuous_const
  apply MultipliableLocallyUniformlyOn_congr
    (f := fun j s => 1 + (genus1Factor (loc' j) s - 1))
    (f' := fun j s => genus1Factor (loc' j) s)
  · intro j s _hs; ring
  apply multipliableLocallyUniformlyOn_of_of_forall_exists_nhds
  intro x _hx
  set R : ℝ := ‖x‖ + 1 with hR
  have hRpos : 0 < R := by positivity
  refine ⟨Metric.closedBall (0 : ℂ) R, ?_, ?_⟩
  · rw [nhdsWithin_univ]
    refine Metric.closedBall_mem_nhds_of_mem ?_
    simp only [Metric.mem_ball, dist_zero_right]
    rw [hR]; linarith [norm_nonneg x]
  · have hK : IsCompact (Metric.closedBall (0 : ℂ) R) := isCompact_closedBall _ _
    have hu : Summable (fun j => 3 * R ^ 2 * (1 / ‖loc' j‖ ^ 2)) := hsumm'.mul_left _
    have hge : ∀ᶠ j in cofinite, R ≤ ‖loc' j‖ := hcofin'.eventually_ge_atTop R
    have hbound : ∀ᶠ j in cofinite,
        ∀ s ∈ Metric.closedBall (0 : ℂ) R, ‖genus1Factor (loc' j) s - 1‖
          ≤ 3 * R ^ 2 * (1 / ‖loc' j‖ ^ 2) := by
      filter_upwards [hge] with j hj s hs
      have hsR : ‖s‖ ≤ R := by simpa [dist_zero_right] using hs
      have hlocpos : 0 < ‖loc' j‖ := by linarith
      have hdiv : ‖s / loc' j‖ ≤ 1 := by
        rw [norm_div, div_le_one hlocpos]; exact le_trans hsR hj
      have hb := norm_genus1Factor_sub_one_le (ρ := loc' j) (s := s) hdiv
      refine hb.trans ?_
      have hsq : ‖s‖ ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (norm_nonneg s) hsR _
      have hlsq : 0 < ‖loc' j‖ ^ 2 := by positivity
      rw [norm_div, div_pow]
      calc 3 * (‖s‖ ^ 2 / ‖loc' j‖ ^ 2)
          ≤ 3 * (R ^ 2 / ‖loc' j‖ ^ 2) := by gcongr
        _ = 3 * R ^ 2 * (1 / ‖loc' j‖ ^ 2) := by ring
    exact Summable.multipliableUniformlyOn_one_add
      (f := fun j s => genus1Factor (loc' j) s - 1)
      (K := Metric.closedBall (0 : ℂ) R) (u := fun j => 3 * R ^ 2 * (1 / ‖loc' j‖ ^ 2))
      hK hu hbound (fun j => (hcts' j).continuousOn)

#print axioms norm_genus1Factor_sub_one_le
#print axioms genus1Product_ne_zero_of_summable
#print axioms genus1Product_compl_multipliableLocallyUniformlyOn
