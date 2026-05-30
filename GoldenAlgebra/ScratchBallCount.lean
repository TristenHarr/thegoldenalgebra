import Mathlib

open Filter

/-!
# Ball-count ⇒ inverse-square summability (G3 abstract engine)
-/

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

/-- Ball-count ⇒ inverse-square summability: the abstract G3 engine. -/
theorem summable_inv_sq_of_ballCount
    {ι : Type*} (loc : ι → ℂ) (A : ℝ) (_hA : 0 ≤ A)
    (hlb : ∀ i, (1 : ℝ) ≤ ‖loc i‖)
    (hfin : ∀ R : ℝ, {i | ‖loc i‖ ≤ R}.Finite)
    (hcount : ∀ R : ℝ, 2 ≤ R → (Nat.card {i | ‖loc i‖ ≤ R} : ℝ) ≤ A * R * Real.log R) :
    Summable (fun i => 1 / ‖loc i‖ ^ 2) := by
  -- Apply the dyadic-shell engine with C := 2 * A * Real.log 2.
  apply summable_inv_sq_of_shellCard loc (2 * A * Real.log 2) hlb
  · -- hfin (shell): {‖loc i‖ < 2^(k+1)} ⊆ {‖loc i‖ ≤ 2^(k+1)} which is finite.
    intro k
    apply Set.Finite.subset (hfin ((2:ℝ) ^ (k+1)))
    intro i hi
    simp only [Set.mem_setOf_eq] at hi ⊢
    exact le_of_lt hi
  · -- hcard: shell k ⊆ ball 2^(k+1), and count bound gives ≤ C*(k+1)*2^k.
    intro k
    -- R := 2^(k+1)
    set R : ℝ := (2:ℝ) ^ (k+1) with hR
    have hR2 : (2:ℝ) ≤ R := by
      rw [hR]
      calc (2:ℝ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (k+1) := by
              apply pow_le_pow_right₀ (by norm_num)
              omega
    -- shell ⊆ ball R
    have hsub : {i | (2:ℝ) ^ k ≤ ‖loc i‖ ∧ ‖loc i‖ < 2 ^ (k+1)} ⊆ {i | ‖loc i‖ ≤ R} := by
      intro i hi
      simp only [Set.mem_setOf_eq] at hi ⊢
      rw [hR]
      exact le_of_lt hi.2
    -- ball R is finite
    have hballfin : {i | ‖loc i‖ ≤ R}.Finite := hfin R
    -- Nat.card shell ≤ Nat.card ball
    have hcardmono : Nat.card {i | (2:ℝ) ^ k ≤ ‖loc i‖ ∧ ‖loc i‖ < 2 ^ (k+1)}
        ≤ Nat.card {i | ‖loc i‖ ≤ R} := Nat.card_mono hballfin hsub
    -- count bound for ball R
    have hcountR : (Nat.card {i | ‖loc i‖ ≤ R} : ℝ) ≤ A * R * Real.log R := hcount R hR2
    -- log R = (k+1) * log 2
    have hlogR : Real.log R = ((k:ℝ)+1) * Real.log 2 := by
      rw [hR, Real.log_pow]; push_cast; ring
    -- chain: card shell ≤ A*R*log R = A*2^(k+1)*(k+1)*log2 = (2*A*log2)*(k+1)*2^k
    have hchain : (Nat.card {i | (2:ℝ) ^ k ≤ ‖loc i‖ ∧ ‖loc i‖ < 2 ^ (k+1)} : ℝ)
        ≤ A * R * Real.log R := by
      refine le_trans ?_ hcountR
      exact_mod_cast hcardmono
    refine le_trans hchain (le_of_eq ?_)
    -- A * R * log R = (2*A*log2)*(k+1)*2^k
    rw [hlogR, hR]
    have hpow : (2:ℝ) ^ (k+1) = 2 ^ k * 2 := by rw [pow_succ]
    rw [hpow]
    ring

/-- Ball-count ⇒ inverse-square summability, WITHOUT the `1 ≤ ‖loc i‖` hypothesis.
Replaces it with `loc i ≠ 0` (so each summand is finite); the small-modulus points
`{i | ‖loc i‖ ≤ 1}` are finite, so summability is unaffected by them. -/
theorem summable_inv_sq_of_ballCount'
    {ι : Type*} (loc : ι → ℂ) (A : ℝ)
    (_hne : ∀ i, loc i ≠ 0)
    (hfin : ∀ R : ℝ, {i | ‖loc i‖ ≤ R}.Finite)
    (hcount : ∀ R : ℝ, 2 ≤ R → (Nat.card {i | ‖loc i‖ ≤ R} : ℝ) ≤ A * R * Real.log R) :
    Summable (fun i => 1 / ‖loc i‖ ^ 2) := by
  classical
  -- The small-modulus index set is finite.
  set S : Set ι := {i | ‖loc i‖ ≤ 1} with hS
  have hSfin : S.Finite := hfin 1
  -- Summability is unaffected by the finite set S: reduce to the complement subtype.
  rw [← hSfin.summable_compl_iff (f := fun i => 1 / ‖loc i‖ ^ 2)]
  -- `0 ≤ A` is forced by the count bound at R = 2 (the count is nonneg, log 2 > 0).
  have hA : 0 ≤ A := by
    have h2 := hcount 2 (le_refl 2)
    have hnn : (0:ℝ) ≤ (Nat.card {i | ‖loc i‖ ≤ (2:ℝ)} : ℝ) := by positivity
    have hle : (0:ℝ) ≤ A * 2 * Real.log 2 := le_trans hnn h2
    have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    nlinarith [hle, hlog2]
  -- On Sᶜ, restrict and apply the `1 ≤ ‖loc i‖` engine to `loc ∘ Subtype.val`.
  -- The summand `(fun i => 1/‖loc i‖^2) ∘ Subtype.val` equals
  -- `fun j => 1 / ‖loc ↑j‖ ^ 2` for j : ↥Sᶜ.
  apply summable_inv_sq_of_ballCount (fun j : (Sᶜ : Set ι) => loc (j : ι)) A hA
  · -- hlb on the complement: 1 ≤ ‖loc ↑j‖ since j ∉ S means ¬(‖loc ↑j‖ ≤ 1).
    intro j
    have hj : (j : ι) ∉ S := j.2
    simp only [hS, Set.mem_setOf_eq, not_le] at hj
    exact le_of_lt hj
  · -- hfin on the complement subtype.
    intro R
    -- inclusion of the subtype set into the ball, transported through Subtype.val.
    have : {j : (Sᶜ : Set ι) | ‖loc (j : ι)‖ ≤ R}
        = (Subtype.val : (Sᶜ : Set ι) → ι) ⁻¹' {i | ‖loc i‖ ≤ R} := by
      ext j; simp
    rw [this]
    apply Set.Finite.preimage _ (hfin R)
    exact (Subtype.val_injective).injOn
  · -- hcount on the complement subtype: card ≤ card of full ball.
    intro R hR
    refine le_trans ?_ (hcount R hR)
    -- Nat.card {j : ↥Sᶜ | ‖loc ↑j‖ ≤ R} ≤ Nat.card {i | ‖loc i‖ ≤ R}
    have hcardle : Nat.card {j : (Sᶜ : Set ι) | ‖loc (j : ι)‖ ≤ R}
        ≤ Nat.card {i | ‖loc i‖ ≤ R} := by
      -- image of the subtype set under Subtype.val sits inside the ball
      have himg : (Subtype.val : (Sᶜ : Set ι) → ι) '' {j | ‖loc (j : ι)‖ ≤ R}
          ⊆ {i | ‖loc i‖ ≤ R} := by
        rintro i ⟨j, hj, rfl⟩
        exact hj
      have hcard_img : Nat.card ((Subtype.val : (Sᶜ : Set ι) → ι) '' {j | ‖loc (j : ι)‖ ≤ R})
          = Nat.card {j : (Sᶜ : Set ι) | ‖loc (j : ι)‖ ≤ R} :=
        Nat.card_image_of_injective Subtype.val_injective _
      rw [← hcard_img]
      exact Nat.card_mono (hfin R) himg
    exact_mod_cast hcardle
