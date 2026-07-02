import Mathlib

open Complex Filter Topology MeromorphicOn Function

/-!
# TASK — `WithMultInvSqSummable` : the WITH-MULTIPLICITY refinement of B47

This file closes the `hMult` hypothesis of `ScratchMultIndex.lean`, namely

  `WithMultInvSqSummable :=
     Summable (fun ρ : {z // ξ z = 0} => (m_ρ : ℝ) · (1/‖ρ‖²))`,  `m_ρ = (analyticOrderAt ξ ρ).toNat`.

This is the *divisor-weighted* (each zero counted with multiplicity) version of B47
`xi_zero_invSq_summable`, which only sums over DISTINCT zeros (`Σ_ρ 1/‖ρ‖²`).

## The chain

The proof transplants the B47 architecture but feeds it the **multiplicity index**
`XiZeroIndexMult := Σ ρ : {ξ=0}, Fin m_ρ` and its location map `zeroLocMult ⟨ρ,k⟩ = (ρ : ℂ)`:

1. **Ball count over the mult index = the divisor finsum.**
   `Nat.card {i : XiZeroIndexMult | ‖zeroLocMult i‖ ≤ R}` equals `Σ_{ρ : ‖ρ‖≤R} m_ρ` (each
   distinct zero `ρ` in the ball contributes its `m_ρ` copies), and for the *analytic* ξ each
   `m_ρ = (analyticOrderNatAt ξ ρ)` equals `MeromorphicOn.divisor ξ (ball R) ρ`. Summing over the
   distinct zeros in the ball and dominating by the full divisor support gives
   `Σ_{ρ:‖ρ‖≤R} m_ρ ≤ ∑ᶠ_u divisor ξ (ball R) u`.  *(Proven here, `multBallCard_le_finsumDivisor`.)*

2. **Order-1 divisor growth.** `∑ᶠ_u divisor ξ (ball R) u ≤ A·(eR)·log(eR) − log‖ξ0‖` for `R ≥ 2`.
   This is the deep RvM/Jensen/Λ₀-Mellin count `xi_zero_count_bigO` of `Scratch.lean`; it counts
   WITH MULTIPLICITY (it is a divisor finsum, not a distinct-zero count), so it bounds the
   multiplicity ball count of step 1 directly. It is taken here as the single isolated hypothesis
   `XiDivisorCountBigO` (it cannot be re-proved without re-running the whole RvM chain).

3. **Arithmetic ⇒ `C·R·log R`.** The exact constant-chasing of B47, verbatim.

4. **Ball-count ⇒ Σ1/‖·‖² engine.** Feeding the multiplicity ball count into the dyadic-shell
   engine `summable_inv_sq_of_ballCount'` (copied here, fully proven) gives
   `Summable (fun i : XiZeroIndexMult => 1/‖zeroLocMult i‖²)`.

5. **Fiber regrouping.** By `summable_sigma_of_nonneg` the fiber-sum over `Fin m_ρ` is
   `m_ρ · (1/‖ρ‖²)`, so the sigma-summability of step 4 is exactly `WithMultInvSqSummable`.

The file is SELF-CONTAINED (`import Mathlib`): the short ξ-scaffolding and the abstract shell engine
are copied verbatim from `ScratchMultIndex.lean` / `ScratchBallCount.lean`. The ONE deep analytic
input is the isolated hypothesis `XiDivisorCountBigO` (= proven `xi_zero_count_bigO` of
`Scratch.lean`).
-/

set_option maxHeartbeats 4000000

namespace OverflowResidueRH.BacklundTuring.ScratchWithMultSummable

/-! ## 0. Self-contained ξ-scaffolding (copied verbatim from `ScratchMultIndex.lean`). -/

/-- The entire completion of ξ: `½·(s·(s−1)·Λ₀(s) + 1)` (manifestly entire). -/
noncomputable def entireRiemannXi (s : ℂ) : ℂ :=
  (1 / 2) * (s * (s - 1) * completedRiemannZeta₀ s + 1)

theorem differentiable_entireRiemannXi : Differentiable ℂ entireRiemannXi := by
  unfold entireRiemannXi
  exact (((differentiable_id.mul (differentiable_id.sub_const 1)).mul
    differentiable_completedZeta₀).add_const 1).const_mul _

theorem analyticOnNhd_entireRiemannXi :
    AnalyticOnNhd ℂ entireRiemannXi Set.univ :=
  differentiable_entireRiemannXi.differentiableOn.analyticOnNhd isOpen_univ

theorem entireRiemannXi_zero : entireRiemannXi 0 = 1 / 2 := by simp [entireRiemannXi]

theorem entireRiemannXi_zero_ne : entireRiemannXi 0 ≠ 0 := by
  rw [entireRiemannXi_zero]; norm_num

/-- ξ's zero set. -/
def riemannXiZeros : Set ℂ := entireRiemannXi ⁻¹' {0}

@[simp] lemma mem_riemannXiZeros {z : ℂ} :
    z ∈ riemannXiZeros ↔ entireRiemannXi z = 0 := Iff.rfl

lemma compl_riemannXiZeros_mem_codiscrete :
    riemannXiZerosᶜ ∈ codiscrete ℂ :=
  analyticOnNhd_entireRiemannXi.preimage_zero_mem_codiscrete entireRiemannXi_zero_ne

lemma isClosed_riemannXiZeros : IsClosed riemannXiZeros := by
  simpa using (mem_codiscrete'.mp compl_riemannXiZeros_mem_codiscrete).1

lemma isDiscrete_riemannXiZeros : IsDiscrete riemannXiZeros := by
  simpa using (mem_codiscrete'.mp compl_riemannXiZeros_mem_codiscrete).2

lemma isCompact_inter_riemannXiZeros_finite {S : Set ℂ} (hS : IsCompact S) :
    (S ∩ riemannXiZeros).Finite := by
  apply (hS.inter_right isClosed_riemannXiZeros).finite
  exact isDiscrete_riemannXiZeros.mono Set.inter_subset_right

/-- The single-index ξ-zero type (each zero appears ONCE). -/
abbrev XiZeroIndex : Type := riemannXiZeros

def xiZeroLoc (ρ : XiZeroIndex) : ℂ := (ρ : ℂ)

lemma entireRiemannXi_xiZeroLoc (ρ : XiZeroIndex) :
    entireRiemannXi (xiZeroLoc ρ) = 0 := ρ.2

lemma xiZeroLoc_ne_zero (ρ : XiZeroIndex) : xiZeroLoc ρ ≠ 0 := by
  intro h
  have hz := entireRiemannXi_xiZeroLoc ρ
  rw [h] at hz
  exact entireRiemannXi_zero_ne hz

/-! ## 1. ξ has finite order; the multiplicity index. -/

/-- ξ has finite analytic order at every point (it is not identically zero). -/
theorem analyticOrderAt_entireRiemannXi_ne_top (z : ℂ) :
    analyticOrderAt entireRiemannXi z ≠ ⊤ := by
  have h₀ : analyticOrderAt entireRiemannXi 0 ≠ ⊤ := by
    rw [(analyticOnNhd_entireRiemannXi 0 (Set.mem_univ _)).analyticOrderAt_eq_zero.2
      entireRiemannXi_zero_ne]
    exact (by simp : (0 : ℕ∞) ≠ ⊤)
  exact analyticOnNhd_entireRiemannXi.analyticOrderAt_ne_top_of_isPreconnected
    isPreconnected_univ (Set.mem_univ 0) (Set.mem_univ z) h₀

/-- **Multiplicity-aware ξ-zero index**: each zero `ρ` is repeated `m_ρ = analyticOrderNatAt ξ ρ`
times via the dependent sum over `Fin m_ρ`. (Defeq to `ScratchMultIndex.XiZeroIndexMult`.) -/
def XiZeroIndexMult : Type :=
  Σ ρ : XiZeroIndex, Fin (analyticOrderNatAt entireRiemannXi (xiZeroLoc ρ))

/-- Location map of the multiplicity index: every copy of `ρ` maps to `(ρ : ℂ)`. -/
def zeroLocMult (i : XiZeroIndexMult) : ℂ := xiZeroLoc i.1

lemma zeroLocMult_ne_zero (i : XiZeroIndexMult) : zeroLocMult i ≠ 0 :=
  xiZeroLoc_ne_zero i.1

lemma entireRiemannXi_zeroLocMult (i : XiZeroIndexMult) :
    entireRiemannXi (zeroLocMult i) = 0 :=
  entireRiemannXi_xiZeroLoc i.1

/-! ## 2. The abstract dyadic-shell ⇒ Σ1/‖·‖² engine (copied verbatim from `ScratchBallCount.lean`,
fully proven, no hypotheses). -/

theorem summable_inv_sq_of_shellCard
    {ι : Type*} (loc : ι → ℂ) (C : ℝ)
    (hlb : ∀ i, (1 : ℝ) ≤ ‖loc i‖)
    (hfin : ∀ k : ℕ, {i | ‖loc i‖ < 2 ^ (k+1)}.Finite)
    (hcard : ∀ k : ℕ,
      (Nat.card {i | (2:ℝ) ^ k ≤ ‖loc i‖ ∧ ‖loc i‖ < 2 ^ (k+1)} : ℝ) ≤ C * (k+1) * 2 ^ k) :
    Summable (fun i => 1 / ‖loc i‖ ^ 2) := by
  classical
  set shell : ι → ℕ := fun i => ⌊Real.logb 2 ‖loc i‖⌋₊ with hshell
  have hmem : ∀ i, (2:ℝ) ^ (shell i) ≤ ‖loc i‖ ∧ ‖loc i‖ < 2 ^ (shell i + 1) := by
    intro i
    have hx : (1:ℝ) ≤ ‖loc i‖ := hlb i
    have hxpos : (0:ℝ) < ‖loc i‖ := lt_of_lt_of_le one_pos hx
    have hL0 : 0 ≤ Real.logb 2 ‖loc i‖ := Real.logb_nonneg (by norm_num) hx
    set L := Real.logb 2 ‖loc i‖ with hLdef
    constructor
    · have hk : ((shell i : ℝ)) ≤ L := by
        simpa [hshell] using Nat.floor_le hL0
      have : (2:ℝ) ^ ((shell i : ℝ)) ≤ ‖loc i‖ := by
        rw [← Real.le_logb_iff_rpow_le (by norm_num) hxpos]
        exact hk
      rwa [Real.rpow_natCast] at this
    · have hk : L < (shell i : ℝ) + 1 := by
        simpa [hshell] using Nat.lt_floor_add_one L
      have : ‖loc i‖ < (2:ℝ) ^ ((shell i : ℝ) + 1) := by
        rw [← Real.logb_lt_iff_lt_rpow (by norm_num) hxpos]
        exact hk
      have hcast : ((shell i : ℝ) + 1) = ((shell i + 1 : ℕ) : ℝ) := by push_cast; ring
      rw [hcast, Real.rpow_natCast] at this
      exact this
  have hfiberfin : ∀ k : ℕ, {i | shell i = k}.Finite := by
    intro k
    apply Set.Finite.subset (hfin k)
    intro i hi
    simp only [Set.mem_setOf_eq] at hi ⊢
    have := (hmem i).2
    rw [hi] at this
    exact this
  set g : ι → ℝ := fun i => 1 / ‖loc i‖ ^ 2 with hg
  have hgnn : ∀ i, 0 ≤ g i := by
    intro i; positivity
  rw [← (Equiv.sigmaFiberEquiv shell).summable_iff]
  rw [summable_sigma_of_nonneg (by intro x; exact hgnn _)]
  refine ⟨?_, ?_⟩
  · intro k
    have : Finite {i // shell i = k} := (hfiberfin k).to_subtype
    exact summable_of_hasFiniteSupport (by exact Set.toFinite _)
  · have hfintype : ∀ k : ℕ, Fintype {i // shell i = k} := fun k => (hfiberfin k).fintype
    have hbound : ∀ k : ℕ,
        (∑' (i : {i // shell i = k}), g (Equiv.sigmaFiberEquiv shell ⟨k, i⟩))
          ≤ C * (k+1) / 2 ^ k := by
      intro k
      have hft := hfintype k
      rw [tsum_fintype]
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
      have hsum_le : (∑ i : {i // shell i = k}, g (Equiv.sigmaFiberEquiv shell ⟨k, i⟩))
          ≤ (Finset.univ : Finset {i // shell i = k}).card • (1 / (4:ℝ) ^ k) := by
        apply Finset.sum_le_card_nsmul
        intro x _
        exact hterm x
      refine le_trans hsum_le ?_
      rw [nsmul_eq_mul]
      have hcard_eq : ((Finset.univ : Finset {i // shell i = k}).card : ℝ)
          = (Nat.card {i // shell i = k} : ℝ) := by
        rw [Nat.card_eq_fintype_card]; rfl
      rw [hcard_eq]
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
      have h4pos : (0:ℝ) < (4:ℝ) ^ k := by positivity
      have hstep1 : (Nat.card {i // shell i = k} : ℝ) * (1 / (4:ℝ) ^ k)
          ≤ (C * (k+1) * 2 ^ k) * (1 / (4:ℝ) ^ k) := by
        apply mul_le_mul_of_nonneg_right
        · exact le_trans hcardmono (hcard k)
        · positivity
      refine le_trans hstep1 ?_
      have h4eq : (4:ℝ) ^ k = (2:ℝ) ^ k * (2:ℝ) ^ k := by
        rw [← pow_add, ← two_mul, pow_mul]; norm_num
      rw [h4eq]
      have h2pos : (0:ℝ) < (2:ℝ) ^ k := by positivity
      have hne : (2:ℝ) ^ k ≠ 0 := ne_of_gt h2pos
      have hcompute : C * (↑k + 1) * 2 ^ k * (1 / (2 ^ k * 2 ^ k))
          = C * (↑k + 1) / 2 ^ k := by
        field_simp
      rw [hcompute]
    apply Summable.of_nonneg_of_le _ hbound
    · have hgeo : Summable (fun n : ℕ => (n:ℝ) ^ 1 * ((1:ℝ)/2) ^ n) :=
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
  apply summable_inv_sq_of_shellCard loc (2 * A * Real.log 2) hlb
  · intro k
    apply Set.Finite.subset (hfin ((2:ℝ) ^ (k+1)))
    intro i hi
    simp only [Set.mem_setOf_eq] at hi ⊢
    exact le_of_lt hi
  · intro k
    set R : ℝ := (2:ℝ) ^ (k+1) with hR
    have hR2 : (2:ℝ) ≤ R := by
      rw [hR]
      calc (2:ℝ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (k+1) := by
              apply pow_le_pow_right₀ (by norm_num)
              omega
    have hsub : {i | (2:ℝ) ^ k ≤ ‖loc i‖ ∧ ‖loc i‖ < 2 ^ (k+1)} ⊆ {i | ‖loc i‖ ≤ R} := by
      intro i hi
      simp only [Set.mem_setOf_eq] at hi ⊢
      rw [hR]
      exact le_of_lt hi.2
    have hballfin : {i | ‖loc i‖ ≤ R}.Finite := hfin R
    have hcardmono : Nat.card {i | (2:ℝ) ^ k ≤ ‖loc i‖ ∧ ‖loc i‖ < 2 ^ (k+1)}
        ≤ Nat.card {i | ‖loc i‖ ≤ R} := Nat.card_mono hballfin hsub
    have hcountR : (Nat.card {i | ‖loc i‖ ≤ R} : ℝ) ≤ A * R * Real.log R := hcount R hR2
    have hlogR : Real.log R = ((k:ℝ)+1) * Real.log 2 := by
      rw [hR, Real.log_pow]; push_cast; ring
    have hchain : (Nat.card {i | (2:ℝ) ^ k ≤ ‖loc i‖ ∧ ‖loc i‖ < 2 ^ (k+1)} : ℝ)
        ≤ A * R * Real.log R := by
      refine le_trans ?_ hcountR
      exact_mod_cast hcardmono
    refine le_trans hchain (le_of_eq ?_)
    rw [hlogR, hR]
    have hpow : (2:ℝ) ^ (k+1) = 2 ^ k * 2 := by rw [pow_succ]
    rw [hpow]
    ring

/-- Ball-count ⇒ inverse-square summability, WITHOUT the `1 ≤ ‖loc i‖` hypothesis. -/
theorem summable_inv_sq_of_ballCount'
    {ι : Type*} (loc : ι → ℂ) (A : ℝ)
    (_hne : ∀ i, loc i ≠ 0)
    (hfin : ∀ R : ℝ, {i | ‖loc i‖ ≤ R}.Finite)
    (hcount : ∀ R : ℝ, 2 ≤ R → (Nat.card {i | ‖loc i‖ ≤ R} : ℝ) ≤ A * R * Real.log R) :
    Summable (fun i => 1 / ‖loc i‖ ^ 2) := by
  classical
  set S : Set ι := {i | ‖loc i‖ ≤ 1} with hS
  have hSfin : S.Finite := hfin 1
  rw [← hSfin.summable_compl_iff (f := fun i => 1 / ‖loc i‖ ^ 2)]
  have hA : 0 ≤ A := by
    have h2 := hcount 2 (le_refl 2)
    have hnn : (0:ℝ) ≤ (Nat.card {i | ‖loc i‖ ≤ (2:ℝ)} : ℝ) := by positivity
    have hle : (0:ℝ) ≤ A * 2 * Real.log 2 := le_trans hnn h2
    have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    nlinarith [hle, hlog2]
  apply summable_inv_sq_of_ballCount (fun j : (Sᶜ : Set ι) => loc (j : ι)) A hA
  · intro j
    have hj : (j : ι) ∉ S := j.2
    simp only [hS, Set.mem_setOf_eq, not_le] at hj
    exact le_of_lt hj
  · intro R
    have : {j : (Sᶜ : Set ι) | ‖loc (j : ι)‖ ≤ R}
        = (Subtype.val : (Sᶜ : Set ι) → ι) ⁻¹' {i | ‖loc i‖ ≤ R} := by
      ext j; simp
    rw [this]
    apply Set.Finite.preimage _ (hfin R)
    exact (Subtype.val_injective).injOn
  · intro R hR
    refine le_trans ?_ (hcount R hR)
    have hcardle : Nat.card {j : (Sᶜ : Set ι) | ‖loc (j : ι)‖ ≤ R}
        ≤ Nat.card {i | ‖loc i‖ ≤ R} := by
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

/-! ## 3. The single isolated DEEP input.

The order-1 divisor count of ξ: `∑ᶠ_u divisor ξ (ball R) u ≤ A·(eR)·log(eR) − log‖ξ0‖` for `R ≥ 2`.
This is *exactly* `xi_zero_count_bigO` of `Scratch.lean` (proven there via the Λ₀-Mellin strip /
Jensen / Riemann–von Mangoldt chain). It is a DIVISOR finsum, hence counts WITH MULTIPLICITY. It is
isolated here as the single honest hypothesis because reproving it needs the entire RvM machinery;
everything downstream of it (the with-multiplicity ball count and the summability) is proved
unconditionally in this file. -/

/-- The order-1 divisor-count datum (= proven `xi_zero_count_bigO`). -/
def XiDivisorCountBigO : Prop :=
  ∃ A : ℝ, 0 ≤ A ∧ ∀ r : ℝ, 2 ≤ r →
    ∑ᶠ u, MeromorphicOn.divisor entireRiemannXi (Metric.closedBall (0 : ℂ) r) u
      ≤ A * (Real.exp 1 * r) * Real.log (Real.exp 1 * r) - Real.log ‖entireRiemannXi 0‖

/-! ## 4. The with-multiplicity ball count = the divisor finsum.

`Nat.card {i : XiZeroIndexMult | ‖zeroLocMult i‖ ≤ R}` = `Σ_{ρ:‖ρ‖≤R} m_ρ` ≤ `∑ᶠ divisor`. -/

/-- The multiplicity-index ball is finite (each base zero in the ball contributes finitely many
copies, and the base zeros in the ball are finite). -/
theorem multBall_finite (R : ℝ) :
    {i : XiZeroIndexMult | ‖zeroLocMult i‖ ≤ R}.Finite := by
  classical
  -- The base zeros in the ball are finite.
  have hbasefin : {ρ : XiZeroIndex | ‖xiZeroLoc ρ‖ ≤ R}.Finite := by
    have hcpt : (Metric.closedBall (0 : ℂ) R ∩ riemannXiZeros).Finite :=
      isCompact_inter_riemannXiZeros_finite (isCompact_closedBall 0 R)
    apply Set.Finite.of_finite_image (f := (Subtype.val : XiZeroIndex → ℂ))
    · apply hcpt.subset
      rintro z ⟨ρ, hρ, rfl⟩
      exact ⟨by simpa [xiZeroLoc, Metric.mem_closedBall, dist_zero_right] using hρ, ρ.2⟩
    · exact Subtype.val_injective.injOn
  -- The mult-index ball injects into `Σ ρ : {base in ball}, Fin m_ρ` (finite).
  apply Set.Finite.ofFinset
    (s := (hbasefin.toFinset).sigma
      (fun ρ => (Finset.univ : Finset (Fin (analyticOrderNatAt entireRiemannXi (xiZeroLoc ρ))))) |>.image
      (fun p => (⟨p.1, p.2⟩ : XiZeroIndexMult)))
  intro i
  simp only [Finset.mem_image, Finset.mem_sigma, Set.Finite.mem_toFinset, Finset.mem_univ,
    and_true, Set.mem_setOf_eq]
  constructor
  · rintro ⟨⟨ρ, k⟩, hρ, rfl⟩
    show ‖zeroLocMult (⟨ρ, k⟩ : XiZeroIndexMult)‖ ≤ R
    simpa [zeroLocMult] using hρ
  · intro hi
    exact ⟨⟨i.1, i.2⟩, hi, rfl⟩

/-- **With-multiplicity ball count = the divisor finsum (upper bound).**
`Nat.card {i : XiZeroIndexMult | ‖zeroLocMult i‖ ≤ R} ≤ ∑ᶠ_u divisor ξ (ball R) u`. -/
theorem multBallCard_le_finsumDivisor (R : ℝ) :
    (Nat.card {i : XiZeroIndexMult | ‖zeroLocMult i‖ ≤ R} : ℝ)
      ≤ ∑ᶠ u, MeromorphicOn.divisor entireRiemannXi (Metric.closedBall (0 : ℂ) R) u := by
  classical
  -- Base zeros in the ball.
  have hbasefin : {ρ : XiZeroIndex | ‖xiZeroLoc ρ‖ ≤ R}.Finite := by
    have hcpt : (Metric.closedBall (0 : ℂ) R ∩ riemannXiZeros).Finite :=
      isCompact_inter_riemannXiZeros_finite (isCompact_closedBall 0 R)
    apply Set.Finite.of_finite_image (f := (Subtype.val : XiZeroIndex → ℂ))
    · apply hcpt.subset
      rintro z ⟨ρ, hρ, rfl⟩
      exact ⟨by simpa [xiZeroLoc, Metric.mem_closedBall, dist_zero_right] using hρ, ρ.2⟩
    · exact Subtype.val_injective.injOn
  -- Step A: Nat.card of the mult-ball = Σ_{ρ ∈ base ball} m_ρ.
  have hcardA : Nat.card {i : XiZeroIndexMult | ‖zeroLocMult i‖ ≤ R}
      = ∑ ρ ∈ hbasefin.toFinset, analyticOrderNatAt entireRiemannXi (xiZeroLoc ρ) := by
    -- equiv to Σ ρ : {base in ball}, Fin m_ρ
    have e : {i : XiZeroIndexMult | ‖zeroLocMult i‖ ≤ R}
        ≃ Σ ρ : {ρ : XiZeroIndex // ‖xiZeroLoc ρ‖ ≤ R},
            Fin (analyticOrderNatAt entireRiemannXi (xiZeroLoc ρ.1)) := by
      refine
        { toFun := fun i => ⟨⟨i.1.1, i.2⟩, i.1.2⟩
          invFun := fun j => ⟨⟨j.1.1, j.2⟩, j.1.2⟩
          left_inv := by rintro ⟨⟨ρ, k⟩, h⟩; rfl
          right_inv := by rintro ⟨⟨ρ, h⟩, k⟩; rfl }
    rw [Nat.card_congr e]
    haveI : Finite {ρ : XiZeroIndex // ‖xiZeroLoc ρ‖ ≤ R} := hbasefin
    haveI : Fintype {ρ : XiZeroIndex // ‖xiZeroLoc ρ‖ ≤ R} := Fintype.ofFinite _
    rw [Nat.card_sigma]
    simp only [Nat.card_eq_fintype_card, Fintype.card_fin]
    rw [← Finset.sum_coe_sort hbasefin.toFinset
      (fun ρ => analyticOrderNatAt entireRiemannXi (xiZeroLoc ρ))]
    apply Fintype.sum_equiv
      (Equiv.subtypeEquivRight (fun ρ => by simp [Set.Finite.mem_toFinset]))
    intro ρ; rfl
  -- Step B: Σ_{ρ ∈ base ball} m_ρ ≤ ∑ᶠ divisor.  Bridge via the ℂ-zeros-in-ball finset.
  set K : Set ℂ := Metric.closedBall (0:ℂ) R with hK
  have hf : AnalyticOnNhd ℂ entireRiemannXi Set.univ := analyticOnNhd_entireRiemannXi
  have hfK : AnalyticOnNhd ℂ entireRiemannXi K := hf.mono (Set.subset_univ _)
  have hmK : MeromorphicOn entireRiemannXi K := hfK.meromorphicOn
  have horder : ∀ z : ℂ, analyticOrderAt entireRiemannXi z ≠ ⊤ :=
    analyticOrderAt_entireRiemannXi_ne_top
  have hKcompact : IsCompact K := isCompact_closedBall _ _
  have hSfin : (MeromorphicOn.divisor entireRiemannXi K).support.Finite :=
    (MeromorphicOn.divisor entireRiemannXi K).finiteSupport hKcompact
  have hnonneg : ∀ z : ℂ, 0 ≤ MeromorphicOn.divisor entireRiemannXi K z := hfK.divisor_nonneg
  -- divisor at a zero ρ in the ball = m_ρ, and ≥ 1.
  have hdiv_eq : ∀ z, entireRiemannXi z = 0 → z ∈ K →
      MeromorphicOn.divisor entireRiemannXi K z = (analyticOrderNatAt entireRiemannXi z : ℤ) := by
    intro z hz0 hzK
    rw [hmK.divisor_apply hzK, (hfK z hzK).meromorphicOrderAt_eq]
    obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.1 (horder z)
    simp only [analyticOrderNatAt, ← hn]; rfl
  have hpos : ∀ z, entireRiemannXi z = 0 → z ∈ K →
      1 ≤ MeromorphicOn.divisor entireRiemannXi K z := by
    intro z hz0 hzK
    rw [hdiv_eq z hz0 hzK]
    have hne0 : analyticOrderAt entireRiemannXi z ≠ 0 :=
      (hfK z hzK).analyticOrderAt_ne_zero.2 hz0
    have hnat : analyticOrderNatAt entireRiemannXi z ≠ 0 := by
      rw [analyticOrderNatAt, Ne, ENat.toNat_eq_zero, not_or]
      exact ⟨hne0, horder z⟩
    omega
  -- The image of the base-ball finset (under val) as a ℂ-finset of zeros in the ball.
  set Zc : Finset ℂ := hbasefin.toFinset.image (fun ρ => xiZeroLoc ρ) with hZc
  have hZc_inj : Set.InjOn (fun ρ : XiZeroIndex => xiZeroLoc ρ) hbasefin.toFinset := by
    intro a _ b _ hab
    exact Subtype.ext hab
  -- Reindex the base sum to a sum over Zc.
  have hreindex : ∑ ρ ∈ hbasefin.toFinset, (analyticOrderNatAt entireRiemannXi (xiZeroLoc ρ) : ℤ)
      = ∑ z ∈ Zc, (analyticOrderNatAt entireRiemannXi z : ℤ) := by
    rw [hZc, Finset.sum_image (fun a ha b hb h => hZc_inj ha hb h)]
  -- Zc ⊆ divisor support, and on Zc divisor = m.
  have hZc_mem : ∀ z ∈ Zc, entireRiemannXi z = 0 ∧ z ∈ K := by
    intro z hz
    rw [hZc, Finset.mem_image] at hz
    obtain ⟨ρ, hρ, rfl⟩ := hz
    rw [Set.Finite.mem_toFinset] at hρ
    refine ⟨entireRiemannXi_xiZeroLoc ρ, ?_⟩
    simpa [hK, xiZeroLoc, Metric.mem_closedBall, dist_zero_right] using hρ
  have hZc_sub : Zc ⊆ hSfin.toFinset := by
    intro z hz
    obtain ⟨hz0, hzK⟩ := hZc_mem z hz
    rw [Set.Finite.mem_toFinset, Function.mem_support]
    have := hpos z hz0 hzK; omega
  have hZc_divisor : ∑ z ∈ Zc, (analyticOrderNatAt entireRiemannXi z : ℤ)
      = ∑ z ∈ Zc, MeromorphicOn.divisor entireRiemannXi K z := by
    apply Finset.sum_congr rfl
    intro z hz
    obtain ⟨hz0, hzK⟩ := hZc_mem z hz
    rw [hdiv_eq z hz0 hzK]
  -- Σ over Zc ≤ Σᶠ divisor.
  have hfinsum_int : (∑ z ∈ Zc, MeromorphicOn.divisor entireRiemannXi K z)
      ≤ ∑ᶠ u, MeromorphicOn.divisor entireRiemannXi K u := by
    rw [finsum_eq_finsetSum_of_support_subset (MeromorphicOn.divisor entireRiemannXi K)
        (s := hSfin.toFinset) (by rw [Set.Finite.coe_toFinset])]
    exact Finset.sum_le_sum_of_subset_of_nonneg hZc_sub (fun a _ _ => hnonneg a)
  -- Assemble (cast ℕ → ℤ → ℝ).
  have hcast : (Nat.card {i : XiZeroIndexMult | ‖zeroLocMult i‖ ≤ R} : ℤ)
      = ∑ z ∈ Zc, (analyticOrderNatAt entireRiemannXi z : ℤ) := by
    rw [hcardA, ← hreindex]; push_cast; ring
  calc (Nat.card {i : XiZeroIndexMult | ‖zeroLocMult i‖ ≤ R} : ℝ)
      = ((Nat.card {i : XiZeroIndexMult | ‖zeroLocMult i‖ ≤ R} : ℤ) : ℝ) := by push_cast; ring
    _ = ((∑ z ∈ Zc, (analyticOrderNatAt entireRiemannXi z : ℤ) : ℤ) : ℝ) := by rw [hcast]
    _ = ((∑ z ∈ Zc, MeromorphicOn.divisor entireRiemannXi K z : ℤ) : ℝ) := by rw [hZc_divisor]
    _ ≤ ((∑ᶠ u, MeromorphicOn.divisor entireRiemannXi K u : ℤ) : ℝ) := by exact_mod_cast hfinsum_int

/-! ## 5. The with-multiplicity ball-count bound `C·R·log R` (B47 arithmetic, verbatim) and the
final summability over the multiplicity index. -/

/-- **The with-multiplicity ball count is `O(R log R)`.** Combining `multBallCard_le_finsumDivisor`
with the deep order-1 divisor count `XiDivisorCountBigO` and the B47 constant-chasing. -/
theorem multBallCard_bigO (hCount : XiDivisorCountBigO) :
    ∃ C : ℝ, ∀ R : ℝ, 2 ≤ R →
      (Nat.card {i : XiZeroIndexMult | ‖zeroLocMult i‖ ≤ R} : ℝ) ≤ C * R * Real.log R := by
  obtain ⟨A, hA0, hA⟩ := hCount
  refine ⟨A * Real.exp 1 / Real.log 2 + A * Real.exp 1
      + |Real.log ‖entireRiemannXi 0‖| / Real.log 2 + 1, fun R hR => ?_⟩
  set C : ℝ := A * Real.exp 1 / Real.log 2 + A * Real.exp 1
      + |Real.log ‖entireRiemannXi 0‖| / Real.log 2 + 1 with hC
  have hrvm := hA R hR
  have hdiv := multBallCard_le_finsumDivisor R
  -- B47 arithmetic: A·(eR)·log(eR) − log‖ξ0‖ ≤ C·R·log R.
  have hlog : Real.log (Real.exp 1 * R) = 1 + Real.log R := by
    rw [Real.log_mul (Real.exp_pos 1).ne' (by linarith), Real.log_exp]
  have hRpos : (0 : ℝ) < R := by linarith
  have hlog2pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlogR : Real.log 2 ≤ Real.log R := Real.log_le_log (by norm_num) hR
  have hlogRpos : (0 : ℝ) < Real.log R := lt_of_lt_of_le hlog2pos hlogR
  have hRlogR : Real.log 2 ≤ R * Real.log R := by
    have : (1 : ℝ) * Real.log 2 ≤ R * Real.log R :=
      mul_le_mul (by linarith) hlogR hlog2pos.le hRpos.le
    linarith
  have hexp1pos : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have hcabs : -Real.log ‖entireRiemannXi 0‖ ≤ |Real.log ‖entireRiemannXi 0‖| :=
    neg_le_abs _
  have hterm1 : A * Real.exp 1 * R ≤ (A * Real.exp 1 / Real.log 2) * R * Real.log R := by
    have key : (A * Real.exp 1 / Real.log 2) * R * Real.log R
        = (A * Real.exp 1 * R) * (Real.log R / Real.log 2) := by
      field_simp
    rw [key]
    have hge1 : (1 : ℝ) ≤ Real.log R / Real.log 2 := by
      rw [le_div_iff₀ hlog2pos]; linarith
    nlinarith [hge1, mul_nonneg (mul_nonneg hA0 hexp1pos.le) hRpos.le]
  have hterm2 : |Real.log ‖entireRiemannXi 0‖|
      ≤ (|Real.log ‖entireRiemannXi 0‖| / Real.log 2) * R * Real.log R := by
    have key : (|Real.log ‖entireRiemannXi 0‖| / Real.log 2) * R * Real.log R
        = |Real.log ‖entireRiemannXi 0‖| * (R * Real.log R / Real.log 2) := by
      field_simp
    rw [key]
    have hge1 : (1 : ℝ) ≤ R * Real.log R / Real.log 2 := by
      rw [le_div_iff₀ hlog2pos]; linarith
    nlinarith [hge1, abs_nonneg (Real.log ‖entireRiemannXi 0‖)]
  calc (Nat.card {i : XiZeroIndexMult | ‖zeroLocMult i‖ ≤ R} : ℝ)
      ≤ A * (Real.exp 1 * R) * Real.log (Real.exp 1 * R)
          - Real.log ‖entireRiemannXi 0‖ := le_trans hdiv hrvm
    _ = A * Real.exp 1 * R * (1 + Real.log R) - Real.log ‖entireRiemannXi 0‖ := by
          rw [hlog]; ring
    _ ≤ C * R * Real.log R := by
          rw [hC]
          have hRlogRnn : 0 ≤ R * Real.log R := by positivity
          nlinarith [hterm1, hterm2, hcabs, hRlogRnn]

/-- **Inverse-square summability over the MULTIPLICITY index.**
`Summable (fun i : XiZeroIndexMult => 1/‖zeroLocMult i‖²)`. -/
theorem zeroLocMult_invSq_summable (hCount : XiDivisorCountBigO) :
    Summable (fun i : XiZeroIndexMult => 1 / ‖zeroLocMult i‖ ^ 2) := by
  obtain ⟨C, hC⟩ := multBallCard_bigO hCount
  exact summable_inv_sq_of_ballCount' zeroLocMult C zeroLocMult_ne_zero multBall_finite hC

/-! ## 6. THE DELIVERABLE: `WithMultInvSqSummable`.

By `summable_sigma_of_nonneg`, the sigma-summability of step 5 yields the fiber-summability, whose
fiber-sum over `Fin m_ρ` is `m_ρ · (1/‖ρ‖²)`. This is `WithMultInvSqSummable`. -/

/-- The with-multiplicity inverse-square summability (= `ScratchMultIndex.WithMultInvSqSummable`):
`Summable (fun ρ => m_ρ · (1/‖ρ‖²))`. -/
def WithMultInvSqSummable : Prop :=
  Summable (fun ρ : XiZeroIndex =>
    (analyticOrderNatAt entireRiemannXi (xiZeroLoc ρ) : ℝ) * (1 / ‖xiZeroLoc ρ‖ ^ 2))

/-- **THE DELIVERABLE.** The with-multiplicity inverse-square sum converges, given only the deep
order-1 divisor count `XiDivisorCountBigO` (= proven `xi_zero_count_bigO`). -/
theorem withMultInvSqSummable (hCount : XiDivisorCountBigO) : WithMultInvSqSummable := by
  -- The sigma-summability of `1/‖zeroLocMult ·‖²`, viewed on the explicit sigma type.
  have hsig : Summable (fun i : (Σ ρ : XiZeroIndex,
      Fin (analyticOrderNatAt entireRiemannXi (xiZeroLoc ρ))) =>
        1 / ‖zeroLocMult i‖ ^ 2) := zeroLocMult_invSq_summable hCount
  -- `summable_sigma_of_nonneg` ⇒ the fiber-sum function is summable.
  rw [summable_sigma_of_nonneg (fun i => by positivity)] at hsig
  obtain ⟨_, hfibersum⟩ := hsig
  -- The fiber-sum is exactly `m_ρ · (1/‖ρ‖²)`.
  have hfib : ∀ ρ : XiZeroIndex,
      (∑' k : Fin (analyticOrderNatAt entireRiemannXi (xiZeroLoc ρ)),
        1 / ‖zeroLocMult (⟨ρ, k⟩ : XiZeroIndexMult)‖ ^ 2)
        = (analyticOrderNatAt entireRiemannXi (xiZeroLoc ρ) : ℝ) * (1 / ‖xiZeroLoc ρ‖ ^ 2) := by
    intro ρ
    simp only [zeroLocMult]
    rw [tsum_fintype]
    simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  show Summable (fun ρ : XiZeroIndex =>
    (analyticOrderNatAt entireRiemannXi (xiZeroLoc ρ) : ℝ) * (1 / ‖xiZeroLoc ρ‖ ^ 2))
  rw [show (fun ρ : XiZeroIndex =>
      (analyticOrderNatAt entireRiemannXi (xiZeroLoc ρ) : ℝ) * (1 / ‖xiZeroLoc ρ‖ ^ 2))
      = (fun ρ : XiZeroIndex =>
        ∑' k : Fin (analyticOrderNatAt entireRiemannXi (xiZeroLoc ρ)),
          1 / ‖zeroLocMult (⟨ρ, k⟩ : XiZeroIndexMult)‖ ^ 2)
      from funext (fun ρ => (hfib ρ).symm)]
  exact hfibersum

#print axioms withMultInvSqSummable
#print axioms zeroLocMult_invSq_summable
#print axioms multBallCard_le_finsumDivisor
#print axioms multBallCard_bigO

end OverflowResidueRH.BacklundTuring.ScratchWithMultSummable
