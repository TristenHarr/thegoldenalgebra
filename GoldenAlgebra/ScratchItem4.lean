import Mathlib
open Filter

theorem summable_inv_sq_of_shellCard
    {ι : Type*} (loc : ι → ℂ) (C : ℝ)
    (hlb : ∀ i, (1 : ℝ) ≤ ‖loc i‖)
    (hfin : ∀ k : ℕ, {i | ‖loc i‖ < 2 ^ (k+1)}.Finite)
    (hcard : ∀ k : ℕ,
      (Nat.card {i | (2:ℝ) ^ k ≤ ‖loc i‖ ∧ ‖loc i‖ < 2 ^ (k+1)} : ℝ) ≤ C * (k+1) * 2 ^ k) :
    Summable (fun i => 1 / ‖loc i‖ ^ 2) := by
  classical
  -- the shell index of point i
  set shell : ι → ℕ := fun i => ⌊Real.logb 2 ‖loc i‖⌋₊ with hshell
  -- membership: i lies in shell (shell i)
  have hmem : ∀ i, (2:ℝ) ^ (shell i) ≤ ‖loc i‖ ∧ ‖loc i‖ < 2 ^ (shell i + 1) := by
    intro i
    have hx : (1:ℝ) ≤ ‖loc i‖ := hlb i
    have hxpos : (0:ℝ) < ‖loc i‖ := lt_of_lt_of_le one_pos hx
    have hL0 : 0 ≤ Real.logb 2 ‖loc i‖ := Real.logb_nonneg (by norm_num) hx
    set L := Real.logb 2 ‖loc i‖ with hLdef
    constructor
    · -- 2^(shell i) ≤ ‖loc i‖
      have hk : ((shell i : ℝ)) ≤ L := by
        simpa [hshell] using Nat.floor_le hL0
      have : (2:ℝ) ^ ((shell i : ℝ)) ≤ ‖loc i‖ := by
        rw [← Real.le_logb_iff_rpow_le (by norm_num) hxpos]
        exact hk
      rwa [Real.rpow_natCast] at this
    · -- ‖loc i‖ < 2^(shell i + 1)
      have hk : L < (shell i : ℝ) + 1 := by
        simpa [hshell] using Nat.lt_floor_add_one L
      have : ‖loc i‖ < (2:ℝ) ^ ((shell i : ℝ) + 1) := by
        rw [← Real.logb_lt_iff_lt_rpow (by norm_num) hxpos]
        exact hk
      have hcast : ((shell i : ℝ) + 1) = ((shell i + 1 : ℕ) : ℝ) := by push_cast; ring
      rw [hcast, Real.rpow_natCast] at this
      exact this
  -- the fiber over shell index k is a subset of the (finite) ball, hence finite
  have hfiberfin : ∀ k : ℕ, {i | shell i = k}.Finite := by
    intro k
    apply Set.Finite.subset (hfin k)
    intro i hi
    simp only [Set.mem_setOf_eq] at hi ⊢
    have := (hmem i).2
    rw [hi] at this
    exact this
  -- abbreviate the summand
  set g : ι → ℝ := fun i => 1 / ‖loc i‖ ^ 2 with hg
  have hgnn : ∀ i, 0 ≤ g i := by
    intro i; positivity
  -- Use the sigma fiber equivalence to regroup the sum.
  rw [← (Equiv.sigmaFiberEquiv shell).summable_iff]
  -- Now summing g (e ⟨k, i⟩) over the sigma type.
  rw [summable_sigma_of_nonneg (by intro x; exact hgnn _)]
  refine ⟨?_, ?_⟩
  · -- each fiber summable (it is finite)
    intro k
    have : Finite {i // shell i = k} := (hfiberfin k).to_subtype
    exact summable_of_hasFiniteSupport (by exact Set.toFinite _)
  · -- the outer sum over k is summable, bounded by C*(k+1)/2^k
    -- give each fiber a Fintype instance
    have hfintype : ∀ k : ℕ, Fintype {i // shell i = k} := fun k => (hfiberfin k).fintype
    -- bound the per-fiber tsum by C*(k+1)/2^k
    have hbound : ∀ k : ℕ,
        (∑' (i : {i // shell i = k}), g (Equiv.sigmaFiberEquiv shell ⟨k, i⟩))
          ≤ C * (k+1) / 2 ^ k := by
      intro k
      have hft := hfintype k
      -- convert tsum to finset sum
      rw [tsum_fintype]
      -- each term ≤ 1/4^k
      have hterm : ∀ i : {i // shell i = k},
          g (Equiv.sigmaFiberEquiv shell ⟨k, i⟩) ≤ 1 / (4:ℝ) ^ k := by
        intro i
        have he : (Equiv.sigmaFiberEquiv shell ⟨k, i⟩) = (i : ι) := rfl
        rw [he, hg]
        simp only
        have hlow : (2:ℝ) ^ k ≤ ‖loc (i : ι)‖ := by
          have := (hmem (i : ι)).1
          rwa [i.2] at this
        have h2k : (0:ℝ) < (2:ℝ) ^ k := by positivity
        have hsq : ((2:ℝ) ^ k) ^ 2 ≤ ‖loc (i : ι)‖ ^ 2 := by
          apply pow_le_pow_left₀ (le_of_lt h2k) hlow
        have h4 : ((2:ℝ) ^ k) ^ 2 = (4:ℝ) ^ k := by
          rw [← pow_mul, mul_comm, pow_mul]; norm_num
        rw [h4] at hsq
        have h4pos : (0:ℝ) < (4:ℝ) ^ k := by positivity
        have hnpos : (0:ℝ) < ‖loc (i : ι)‖ ^ 2 := by
          have : (0:ℝ) < ‖loc (i : ι)‖ := lt_of_lt_of_le one_pos (hlb _)
          positivity
        rw [div_le_div_iff₀ hnpos h4pos]
        rw [one_mul, one_mul]
        exact hsq
      -- sum ≤ card • (1/4^k)
      have hsum_le : (∑ i : {i // shell i = k}, g (Equiv.sigmaFiberEquiv shell ⟨k, i⟩))
          ≤ (Finset.univ : Finset {i // shell i = k}).card • (1 / (4:ℝ) ^ k) := by
        apply Finset.sum_le_card_nsmul
        intro x _
        exact hterm x
      refine le_trans hsum_le ?_
      rw [nsmul_eq_mul]
      -- card = Nat.card fiber ≤ C(k+1)2^k
      have hcard_eq : ((Finset.univ : Finset {i // shell i = k}).card : ℝ)
          = (Nat.card {i // shell i = k} : ℝ) := by
        rw [Nat.card_eq_fintype_card]; rfl
      rw [hcard_eq]
      -- Nat.card fiber ≤ Nat.card shell-set
      have hsub : {i | shell i = k} ⊆
          {i | (2:ℝ) ^ k ≤ ‖loc i‖ ∧ ‖loc i‖ < 2 ^ (k+1)} := by
        intro i hi
        simp only [Set.mem_setOf_eq] at hi ⊢
        have h1 := (hmem i).1
        have h2 := (hmem i).2
        rw [hi] at h1 h2
        exact ⟨h1, h2⟩
      have hcardmono : (Nat.card {i // shell i = k} : ℝ) ≤
          (Nat.card {i | (2:ℝ) ^ k ≤ ‖loc i‖ ∧ ‖loc i‖ < 2 ^ (k+1)} : ℝ) := by
        have hfinbig : {i | (2:ℝ) ^ k ≤ ‖loc i‖ ∧ ‖loc i‖ < 2 ^ (k+1)}.Finite := by
          apply Set.Finite.subset (hfin k)
          intro i hi
          exact hi.2
        have : Nat.card {i // shell i = k} ≤
            Nat.card {i | (2:ℝ) ^ k ≤ ‖loc i‖ ∧ ‖loc i‖ < 2 ^ (k+1)} := by
          apply Nat.card_mono hfinbig hsub
        exact_mod_cast this
      -- chain: card * (1/4^k) ≤ C(k+1)2^k * (1/4^k) = C(k+1)/2^k
      have h4pos : (0:ℝ) < (4:ℝ) ^ k := by positivity
      have hstep1 : (Nat.card {i // shell i = k} : ℝ) * (1 / (4:ℝ) ^ k)
          ≤ (C * (k+1) * 2 ^ k) * (1 / (4:ℝ) ^ k) := by
        apply mul_le_mul_of_nonneg_right
        · exact le_trans hcardmono (hcard k)
        · positivity
      refine le_trans hstep1 ?_
      -- (C(k+1)2^k)/4^k = C(k+1)/2^k
      have h4eq : (4:ℝ) ^ k = (2:ℝ) ^ k * (2:ℝ) ^ k := by
        rw [← pow_add, ← two_mul, pow_mul]; norm_num
      rw [h4eq]
      have h2pos : (0:ℝ) < (2:ℝ) ^ k := by positivity
      have hne : (2:ℝ) ^ k ≠ 0 := ne_of_gt h2pos
      have hcompute : C * (↑k + 1) * 2 ^ k * (1 / (2 ^ k * 2 ^ k))
          = C * (↑k + 1) / 2 ^ k := by
        field_simp
      rw [hcompute]
    -- now: the outer sum is summable, since dominated by C*(k+1)/2^k which is summable
    apply Summable.of_nonneg_of_le _ hbound
    · -- summability of k ↦ C*(k+1)/2^k
      have hgeo : Summable (fun n : ℕ => (n:ℝ) ^ 1 * ((1:ℝ)/2) ^ n) :=
        summable_pow_mul_geometric_of_norm_lt_one 1 (by rw [Real.norm_eq_abs]; norm_num)
      have hgeo0 : Summable (fun n : ℕ => (n:ℝ) ^ 0 * ((1:ℝ)/2) ^ n) :=
        summable_pow_mul_geometric_of_norm_lt_one 0 (by rw [Real.norm_eq_abs]; norm_num)
      have hsum : Summable (fun k : ℕ => C * (k+1) / 2 ^ k) := by
        have heq : (fun k : ℕ => C * (k+1) / 2 ^ k)
            = (fun k : ℕ => C * ((k:ℝ) ^ 1 * ((1:ℝ)/2) ^ k) + C * ((k:ℝ) ^ 0 * ((1:ℝ)/2) ^ k)) := by
          funext k
          have h2pos : (0:ℝ) < (2:ℝ) ^ k := by positivity
          have hhalf : ((1:ℝ)/2) ^ k = 1 / (2:ℝ) ^ k := by
            rw [div_pow]; norm_num
          rw [hhalf]
          field_simp
        rw [heq]
        exact (hgeo.mul_left C).add (hgeo0.mul_left C)
      exact hsum
    · intro k
      apply tsum_nonneg
      intro i
      exact hgnn _
