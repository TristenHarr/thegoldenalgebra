import Mathlib

open Complex Filter Topology

/-- Structural heart of Hadamard factorization: if two entire functions vanish to the
same order at every point, their quotient extends to a zero-free entire function. -/
theorem entire_quotient_of_analyticOrderAt_eq
    {f P : ℂ → ℂ} (hf : Differentiable ℂ f) (hP : Differentiable ℂ P)
    (hP0 : ∃ z₀, P z₀ ≠ 0)
    (horder : ∀ z, analyticOrderAt f z = analyticOrderAt P z) :
    ∃ Q : ℂ → ℂ, Differentiable ℂ Q ∧ (∀ z, Q z ≠ 0) ∧ ∀ z, f z = P z * Q z := by
  -- Analyticity of `f` and `P` at every point.
  have hfa : ∀ z, AnalyticAt ℂ f z := hf.analyticAt
  have hPa : ∀ z, AnalyticAt ℂ P z := hP.analyticAt
  -- The quotient `f / P` is meromorphic at every point.
  have hmero : ∀ z, MeromorphicAt (f / P) z := fun z =>
    (hfa z).meromorphicAt.div (hPa z).meromorphicAt
  -- `P` is not identically zero, so it never vanishes to infinite order (identity principle).
  have hPonNhd : AnalyticOnNhd ℂ P Set.univ := fun z _ => hPa z
  have hPnotTop : ∀ z, analyticOrderAt P z ≠ ⊤ := by
    intro z htop
    obtain ⟨z₀, hz₀⟩ := hP0
    have hev : P =ᶠ[𝓝 z] 0 := analyticOrderAt_eq_top.mp htop
    have : Set.EqOn P 0 Set.univ :=
      hPonNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero
        isPreconnected_univ (Set.mem_univ z) hev
    exact hz₀ (this (Set.mem_univ z₀))
  -- Its meromorphic order is `0` everywhere (orders cancel by `horder`).
  have horder0 : ∀ z, meromorphicOrderAt (f / P) z = 0 := by
    intro z
    rw [meromorphicOrderAt_div (hfa z).meromorphicAt (hPa z).meromorphicAt,
      (hfa z).meromorphicOrderAt_eq, (hPa z).meromorphicOrderAt_eq, horder z]
    exact LinearOrderedAddCommGroupWithTop.sub_self_eq_zero_of_ne_top
      (by rw [Ne, ENat.map_eq_top_iff]; exact hPnotTop z)
  -- Define `Q` as the meromorphic normal form of `f / P` on the whole plane.
  set Q : ℂ → ℂ := toMeromorphicNFOn (f / P) Set.univ with hQdef
  have hmeroOn : MeromorphicOn (f / P) Set.univ := fun z _ => hmero z
  -- `Q` agrees with `f / P` outside a discrete set; in particular its order is `0`.
  have hQorder : ∀ z, meromorphicOrderAt Q z = 0 := by
    intro z
    rw [hQdef, meromorphicOrderAt_toMeromorphicNFOn hmeroOn (Set.mem_univ z), horder0 z]
  -- `Q` is in normal form at every point, hence (order `0 ≥ 0`) analytic everywhere.
  have hQnf : ∀ z, MeromorphicNFAt Q z := fun z =>
    meromorphicNFOn_toMeromorphicNFOn (f / P) Set.univ (Set.mem_univ z)
  have hQa : ∀ z, AnalyticAt ℂ Q z := by
    intro z
    exact (hQnf z).meromorphicOrderAt_nonneg_iff_analyticAt.mp (by rw [hQorder z])
  -- `Q` is differentiable everywhere.
  have hQdiff : Differentiable ℂ Q := fun z => (hQa z).differentiableAt
  -- `Q` is zero-free: analytic with meromorphic order `0` means nonzero value.
  have hQne : ∀ z, Q z ≠ 0 := by
    intro z
    have hAorder : analyticOrderAt Q z = 0 := by
      have hmap := (hQa z).meromorphicOrderAt_eq
      rw [hQorder z] at hmap
      -- `0 = (analyticOrderAt Q z).map (↑)`, so the analytic order is `0`.
      rw [eq_comm, ENat.map_natCast_eq_zero] at hmap
      exact hmap
    exact ((hQa z).analyticOrderAt_eq_zero).mp hAorder
  refine ⟨Q, hQdiff, hQne, ?_⟩
  -- Pointwise identity `f z = P z * Q z`.
  intro z
  by_cases hPz : P z = 0
  · -- At a zero of `P`: matching order forces `f z = 0`, and `P z * Q z = 0`.
    have hPorderne : analyticOrderAt P z ≠ 0 := (hPa z).analyticOrderAt_ne_zero.mpr hPz
    have hforderne : analyticOrderAt f z ≠ 0 := by rw [horder z]; exact hPorderne
    have hfz : f z = 0 := apply_eq_zero_of_analyticOrderAt_ne_zero hforderne
    rw [hfz, hPz, zero_mul]
  · -- Away from zeros of `P`: `Q =ᶠ f/P` on a punctured nbhd, so `P*Q =ᶠ f`; conclude by continuity.
    have hQeq : Q =ᶠ[𝓝[≠] z] (f / P) :=
      hmeroOn.toMeromorphicNFOn_eq_self_on_nhdsNE (Set.mem_univ z)
    -- `P ≠ 0` on a neighborhood of `z`.
    have hPne_nhds : ∀ᶠ w in 𝓝 z, P w ≠ 0 :=
      (hPa z).continuousAt.eventually_ne hPz
    -- On the punctured nbhd, `P w * Q w = f w`.
    have hkey : (fun w => P w * Q w) =ᶠ[𝓝[≠] z] f := by
      filter_upwards [hQeq, hPne_nhds.filter_mono nhdsWithin_le_nhds] with w hw hPw
      rw [hw, Pi.div_apply, mul_div_cancel₀ _ hPw]
    -- `fun w => P w * Q w` is continuous at `z`, so it tends to its value there along `𝓝[≠] z`.
    have hcontPQ : ContinuousAt (fun w => P w * Q w) z :=
      ((hPa z).continuousAt).mul ((hQa z).continuousAt)
    have htends_val : Tendsto (fun w => P w * Q w) (𝓝[≠] z) (𝓝 (P z * Q z)) :=
      hcontPQ.continuousWithinAt.tendsto
    -- It also tends to `f z` (eventual equality with `f`, which is continuous at `z`).
    have htends_f : Tendsto (fun w => P w * Q w) (𝓝[≠] z) (𝓝 (f z)) :=
      ((hfa z).continuousAt.continuousWithinAt.tendsto).congr' hkey.symm
    -- `𝓝[≠] z` is nontrivial in `ℂ`, so the two limits coincide.
    exact (tendsto_nhds_unique htends_val htends_f).symm
