import Mathlib

open MeromorphicOn

/-- The number of zeros of an entire (analytic on all of `ℂ`), not-identically-zero function `f`
in the closed ball of radius `r` is at most the weighted zero-count given by the divisor finsum
`∑ᶠ u, divisor f (closedBall 0 r) u`.  This is the elementary "cardinality ≤ counted-with-
multiplicity" step that lets a Jensen-style bound on the divisor finsum control the actual number
of zeros. -/
theorem natCard_zeros_le_finsum_divisor
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f Set.univ) (hf0 : ∃ z₀, f z₀ ≠ 0) {r : ℝ} (_hr : 0 ≤ r) :
    (Nat.card {z : ℂ // f z = 0 ∧ z ∈ Metric.closedBall (0:ℂ) r} : ℝ)
      ≤ ∑ᶠ u, MeromorphicOn.divisor f (Metric.closedBall (0:ℂ) r) u := by
  classical
  set K : Set ℂ := Metric.closedBall (0:ℂ) r with hK
  -- `f` is analytic on the ball, hence meromorphic there.
  have hfK : AnalyticOnNhd ℂ f K := hf.mono (Set.subset_univ _)
  have hmK : MeromorphicOn f K := hfK.meromorphicOn
  -- `f` has finite analytic order everywhere (it is not identically zero on the connected `univ`).
  obtain ⟨z₀, hz₀⟩ := hf0
  have horder : ∀ z : ℂ, analyticOrderAt f z ≠ ⊤ := by
    intro z
    have h₀ : analyticOrderAt f z₀ ≠ ⊤ := by
      rw [(hf z₀ (Set.mem_univ _)).analyticOrderAt_eq_zero.2 hz₀]
      exact (by simp : (0 : ℕ∞) ≠ ⊤)
    exact hf.analyticOrderAt_ne_top_of_isPreconnected isPreconnected_univ
      (Set.mem_univ z₀) (Set.mem_univ z) h₀
  -- The support of the divisor is finite (`K` is compact).
  have hKcompact : IsCompact K := isCompact_closedBall _ _
  have hSfin : (MeromorphicOn.divisor f K).support.Finite :=
    (MeromorphicOn.divisor f K).finiteSupport hKcompact
  set S : Finset ℂ := hSfin.toFinset with hSdef
  -- The divisor of an analytic function is everywhere nonnegative.
  have hnonneg : ∀ z : ℂ, 0 ≤ MeromorphicOn.divisor f K z := hfK.divisor_nonneg
  -- On `K`, the divisor is nonzero exactly at the zeros of `f`.
  have hdivne : ∀ z ∈ K, f z = 0 → MeromorphicOn.divisor f K z ≠ 0 := by
    intro z hz hfz
    rw [hfK.divisor_apply hz]
    have hne0 : analyticOrderAt f z ≠ 0 :=
      (hfK z hz).analyticOrderAt_ne_zero.2 hfz
    obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.1 (horder z)
    rw [← hn] at hne0 ⊢
    have hn1 : 1 ≤ n := by
      rcases Nat.eq_zero_or_pos n with h | h
      · rw [h] at hne0; exact absurd rfl hne0
      · exact h
    rw [Ne, WithTop.untop₀_eq_zero, not_or]
    refine ⟨?_, ?_⟩
    · rw [ENat.map_natCast_eq_zero]; exact hne0
    · exact ENat.map_coe (Nat.cast : ℕ → ℤ) n ▸ (by exact WithTop.coe_ne_top)
  -- Hence at each zero the divisor is `≥ 1`.
  have hpos : ∀ z ∈ K, f z = 0 → 1 ≤ MeromorphicOn.divisor f K z := by
    intro z hz hfz
    have h0 := hnonneg z
    have hne := hdivne z hz hfz
    omega
  -- Membership characterisation of the support.
  have hmem : ∀ z : ℂ, z ∈ S ↔ (f z = 0 ∧ z ∈ K) := by
    intro z
    rw [hSdef, Set.Finite.mem_toFinset, Function.mem_support]
    constructor
    · intro hz
      by_cases hzK : z ∈ K
      · refine ⟨?_, hzK⟩
        by_contra hfz
        have : analyticOrderAt f z = 0 := (hfK z hzK).analyticOrderAt_eq_zero.2 hfz
        apply hz
        rw [hfK.divisor_apply hzK, this]
        simp
      · exact absurd ((MeromorphicOn.divisor f K).apply_eq_zero_of_notMem hzK) hz
    · rintro ⟨hfz, hzK⟩
      have := hpos z hzK hfz
      omega
  -- The zero subtype has cardinality `S.card`.
  have hcard : Nat.card {z : ℂ // f z = 0 ∧ z ∈ K} = S.card := by
    have : {z : ℂ // f z = 0 ∧ z ∈ K} ≃ {z : ℂ // z ∈ S} := by
      apply Equiv.subtypeEquivRight
      intro z
      rw [hmem z]
    rw [Nat.card_congr this, Nat.card_eq_finsetCard]
  -- Rewrite the finsum as a finite sum over `S` (the support).
  have hfinsum : ∑ᶠ u, MeromorphicOn.divisor f K u = ∑ u ∈ S, MeromorphicOn.divisor f K u := by
    rw [finsum_eq_finsetSum_of_support_subset _ (s := S)]
    rw [hSdef, Set.Finite.coe_toFinset]
  -- Each term is `≥ 1`, so the sum dominates `S.card`.
  have hsum_ge : (S.card : ℤ) ≤ ∑ u ∈ S, MeromorphicOn.divisor f K u := by
    calc (S.card : ℤ) = ∑ _u ∈ S, (1 : ℤ) := by simp
      _ ≤ ∑ u ∈ S, MeromorphicOn.divisor f K u := by
          apply Finset.sum_le_sum
          intro u hu
          obtain ⟨hfu, huK⟩ := (hmem u).1 hu
          exact hpos u huK hfu
  -- Combine.
  rw [hcard]
  have : (∑ᶠ u, MeromorphicOn.divisor f K u : ℤ) = ∑ u ∈ S, MeromorphicOn.divisor f K u := hfinsum
  calc (S.card : ℝ) = ((S.card : ℤ) : ℝ) := by push_cast; ring
    _ ≤ ((∑ u ∈ S, MeromorphicOn.divisor f K u : ℤ) : ℝ) := by
        exact_mod_cast hsum_ge
    _ = ∑ᶠ u, MeromorphicOn.divisor f K u := by rw [← this]
