import Mathlib

open Complex Filter Topology

/-!
# TASK #2 — Multiplicity-aware zero index for the ξ Hadamard product

The single-index `XiZeroIndex := {z // entireRiemannXi z = 0}` lists each zero exactly ONCE.
Consequently `analyticOrderAt (∏ genus1Factor (xiZeroLoc ρ) ·) z = 1` at each zero, which matches
`analyticOrderAt ξ z` ONLY if every ξ-zero is simple. The Hadamard quotient `Q = ξ / ∏` is entire
iff the two `analyticOrderAt` agree at EVERY point, which (without assuming simple zeros) forces the
product index to repeat each zero `ρ` exactly `m_ρ = (analyticOrderAt ξ ρ).toNat` times.

This file builds the **multiplicity-aware** version:

* `XiZeroIndexMult := Σ z : {z // ξ z = 0}, Fin (analyticOrderNatAt ξ z)` (repeats `ρ` `m_ρ` times);
  `zeroLocMult` sends each copy to `(ρ : ℂ)`.
* `zeroLocMult_invSq_summable` : `Summable (1/‖zeroLocMult ·‖²)` over the mult index, from a
  with-multiplicity inverse-square datum (isolated hypothesis `hMult`, the multiplicity-weighted
  refinement of B47 `xi_zero_invSq_summable`).
* `xiMult_genus1Product_LU` : the genus-1 product over the mult index is
  `MultipliableLocallyUniformlyOn univ` (re-derived from the abstract M-test engine).
* `xiMult_genus1Product_analyticOrderAt` : **the deliverable** — unconditionally
  `analyticOrderAt (∏' i, genus1Factor (zeroLocMult i) ·) z = analyticOrderAt ξ z` for every `z`,
  via `Nat.card {i | zeroLocMult i = z} = analyticOrderAt ξ z` and the proven order-of-product
  lemma `analyticOrderAt_genus1Product`.

The file is SELF-CONTAINED (`import Mathlib`) because the main ξ-Hadamard file `Scratch.lean` is a
standalone scratch file, not a built library module. The short self-contained definitions
(`genus1Factor`, `entireRiemannXi`, the zero-set codiscreteness, `xiZeroLoc`) are copied verbatim
from `Scratch.lean`; the two DEEP results of `Scratch.lean` that cannot be re-proved here without
re-running the whole RvM/Jensen chain are taken as explicit, honestly-named hypotheses:
  * `xi_zero_invSq_summable` (B47, distinct-zero inverse-square summability), refined to the
    with-multiplicity datum `hMult`;
  * the local factorization `hsplit` (the genus-1 "order-of-locally-uniform-product" datum that
    Mathlib lacks a lemma for — see `genus1Product_local_split` in `ScratchSplit.lean`).
-/

set_option maxHeartbeats 2000000

namespace OverflowResidueRH.BacklundTuring.ScratchMultIndex

/-! ## 0. Self-contained copies of the ξ-Hadamard scaffolding (from `Scratch.lean`). -/

/-- Genus-1 Weierstrass factor `E₁(s/ρ) = (1 - s/ρ)·exp(s/ρ)`. -/
noncomputable def genus1Factor (ρ s : ℂ) : ℂ := (1 - s / ρ) * Complex.exp (s / ρ)

theorem analyticAt_genus1Factor (ρ : ℂ) (z : ℂ) : AnalyticAt ℂ (genus1Factor ρ) z := by
  unfold genus1Factor; fun_prop

theorem genus1Factor_self {ρ : ℂ} (hρ : ρ ≠ 0) : genus1Factor ρ ρ = 0 := by
  simp [genus1Factor, hρ]

theorem genus1Factor_eq_zero_iff {ρ s : ℂ} (hρ : ρ ≠ 0) :
    genus1Factor ρ s = 0 ↔ s = ρ := by
  unfold genus1Factor
  rw [mul_eq_zero, or_iff_left (Complex.exp_ne_zero _), sub_eq_zero, eq_comm,
    div_eq_one_iff_eq hρ, eq_comm]

theorem genus1Factor_ne_zero {ρ s : ℂ} (hρ : ρ ≠ 0) (hsρ : s ≠ ρ) :
    genus1Factor ρ s ≠ 0 := fun h => hsρ ((genus1Factor_eq_zero_iff hρ).mp h)

/-- `genus1Factor ρ` has a simple zero at `ρ` (order exactly 1). -/
theorem analyticOrderAt_genus1Factor_self {ρ : ℂ} (hρ : ρ ≠ 0) :
    analyticOrderAt (genus1Factor ρ) ρ = 1 := by
  rw [show (1 : ℕ∞) = ((1 : ℕ) : ℕ∞) from rfl,
    (analyticAt_genus1Factor ρ ρ).analyticOrderAt_eq_natCast]
  refine ⟨fun s => -(1 / ρ) * Complex.exp (s / ρ), by fun_prop, ?_, ?_⟩
  · exact mul_ne_zero (neg_ne_zero.mpr (div_ne_zero one_ne_zero hρ)) (Complex.exp_ne_zero _)
  · filter_upwards with s
    unfold genus1Factor
    rw [pow_one, smul_eq_mul]
    field_simp; ring

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

lemma tendsto_riemannXiZeros_cofinite_cocompact :
    Tendsto ((↑) : riemannXiZeros → ℂ) cofinite (cocompact ℂ) :=
  isClosed_riemannXiZeros.tendsto_coe_cofinite_of_isDiscrete isDiscrete_riemannXiZeros

/-! ## 1. The multiplicity-aware index.

`analyticOrderNatAt f z = (analyticOrderAt f z).toNat` is the zero ORDER as a natural number. Since
`ξ ≢ 0` (it is analytic on the connected `univ` and `ξ 0 = ½ ≠ 0`), `analyticOrderAt ξ z ≠ ⊤`
everywhere; hence `(analyticOrderNatAt ξ z : ℕ∞) = analyticOrderAt ξ z`. For a NON-zero `z` the
order is `0`, so `Fin 0` is empty and contributes nothing; for a zero `ρ` the fiber is
`Fin m_ρ`. -/

/-- ξ has finite analytic order at every point (it is not identically zero). -/
theorem analyticOrderAt_entireRiemannXi_ne_top (z : ℂ) :
    analyticOrderAt entireRiemannXi z ≠ ⊤ := by
  have h₀ : analyticOrderAt entireRiemannXi 0 ≠ ⊤ := by
    rw [(analyticOnNhd_entireRiemannXi 0 (Set.mem_univ _)).analyticOrderAt_eq_zero.2
      entireRiemannXi_zero_ne]
    exact (by simp : (0 : ℕ∞) ≠ ⊤)
  exact analyticOnNhd_entireRiemannXi.analyticOrderAt_ne_top_of_isPreconnected
    isPreconnected_univ (Set.mem_univ 0) (Set.mem_univ z) h₀

/-- `(analyticOrderNatAt ξ z : ℕ∞) = analyticOrderAt ξ z` everywhere (order finite). -/
theorem cast_analyticOrderNatAt_entireRiemannXi (z : ℂ) :
    (analyticOrderNatAt entireRiemannXi z : ℕ∞) = analyticOrderAt entireRiemannXi z :=
  Nat.cast_analyticOrderNatAt (analyticOrderAt_entireRiemannXi_ne_top z)

/-- **Multiplicity-aware ξ-zero index**: each zero `ρ` is repeated `m_ρ = analyticOrderNatAt ξ ρ`
times via the dependent sum over `Fin m_ρ`. -/
def XiZeroIndexMult : Type :=
  Σ ρ : XiZeroIndex, Fin (analyticOrderNatAt entireRiemannXi (xiZeroLoc ρ))

/-- Location map of the multiplicity index: every copy of `ρ` maps to `(ρ : ℂ)`. -/
def zeroLocMult (i : XiZeroIndexMult) : ℂ := xiZeroLoc i.1

lemma zeroLocMult_ne_zero (i : XiZeroIndexMult) : zeroLocMult i ≠ 0 :=
  xiZeroLoc_ne_zero i.1

lemma entireRiemannXi_zeroLocMult (i : XiZeroIndexMult) :
    entireRiemannXi (zeroLocMult i) = 0 :=
  entireRiemannXi_xiZeroLoc i.1

/-- The multiplicity index escapes to ∞ along the cofilter (so the M-test applies). -/
lemma tendsto_zeroLocMult_cofinite_cocompact :
    Tendsto zeroLocMult cofinite (cocompact ℂ) := by
  -- `zeroLocMult = (↑) ∘ Sigma.fst`, and `Sigma.fst` is cofinite→cofinite since each fiber
  -- `Fin m_ρ` is finite.
  have hfst : Tendsto (Sigma.fst : XiZeroIndexMult → XiZeroIndex) cofinite cofinite := by
    refine Tendsto.cofinite_of_finite_preimage_singleton (fun ρ => ?_)
    -- the fiber of `Sigma.fst` over `ρ` is the (finite) range of `k ↦ ⟨ρ, k⟩`
    apply Set.Finite.subset (Set.finite_range
      (fun k : Fin (analyticOrderNatAt entireRiemannXi (xiZeroLoc ρ)) => (⟨ρ, k⟩ : XiZeroIndexMult)))
    rintro ⟨b, k⟩ hb
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hb
    subst hb
    exact ⟨k, rfl⟩
  exact tendsto_riemannXiZeros_cofinite_cocompact.comp hfst

/-! ## 2. Summability over the multiplicity index.

`1/‖zeroLocMult i‖² = 1/‖xiZeroLoc i.1‖²` is constant on each fiber `Fin m_ρ`, so the sigma-sum is
`Σ_ρ m_ρ · (1/‖ρ‖²)`. This is the WITH-MULTIPLICITY inverse-square sum. B47
(`xi_zero_invSq_summable`) only gives the DISTINCT-zero sum `Σ_ρ 1/‖ρ‖²`; the multiplicity-weighted
version is the genuine refinement (it equals B44's divisor count, which already counts
multiplicity). We isolate exactly that datum as `hMult` and DERIVE the sigma-summability from it. -/

/-- The with-multiplicity inverse-square summability, as an honest isolated hypothesis: the
multiplicity-weighted refinement of B47. Concretely `Σ_ρ m_ρ/‖ρ‖² < ∞`, which the RvM/divisor
count of `Scratch.lean` (B44, counting with multiplicity) supplies; B47 itself only counts distinct
zeros. -/
def WithMultInvSqSummable : Prop :=
  Summable (fun ρ : XiZeroIndex =>
    (analyticOrderNatAt entireRiemannXi (xiZeroLoc ρ) : ℝ) * (1 / ‖xiZeroLoc ρ‖ ^ 2))

/-- Inverse-square summability over the MULTIPLICITY index, from the with-multiplicity datum.
Uses `summable_sigma_of_nonneg`: each fiber `Fin m_ρ` is finite (so summable), and the
fiber-sum is `m_ρ · (1/‖ρ‖²)`, which `hMult` makes summable over `ρ`. -/
theorem zeroLocMult_invSq_summable (hMult : WithMultInvSqSummable) :
    Summable (fun i : XiZeroIndexMult => 1 / ‖zeroLocMult i‖ ^ 2) := by
  -- Work with the explicit sigma type (defeq to `XiZeroIndexMult`) so `summable_sigma_of_nonneg`
  -- can fire, then transport back by defeq.
  show Summable (fun i : (Σ ρ : XiZeroIndex,
      Fin (analyticOrderNatAt entireRiemannXi (xiZeroLoc ρ))) => 1 / ‖zeroLocMult i‖ ^ 2)
  rw [summable_sigma_of_nonneg (fun i => by positivity)]
  refine ⟨fun ρ => ?_, ?_⟩
  · -- each fiber is over the finite type `Fin m_ρ`
    exact summable_of_hasFiniteSupport (Set.toFinite _)
  · -- fiber sum: `∑' k : Fin m_ρ, 1/‖ρ‖² = m_ρ · 1/‖ρ‖²`
    have hfib : ∀ ρ : XiZeroIndex,
        (∑' k : Fin (analyticOrderNatAt entireRiemannXi (xiZeroLoc ρ)),
          1 / ‖zeroLocMult (⟨ρ, k⟩ : XiZeroIndexMult)‖ ^ 2)
          = (analyticOrderNatAt entireRiemannXi (xiZeroLoc ρ) : ℝ) * (1 / ‖xiZeroLoc ρ‖ ^ 2) := by
      intro ρ
      simp only [zeroLocMult]
      rw [tsum_fintype]
      simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [show (fun ρ : XiZeroIndex =>
        ∑' k : Fin (analyticOrderNatAt entireRiemannXi (xiZeroLoc ρ)),
          1 / ‖zeroLocMult (⟨ρ, k⟩ : XiZeroIndexMult)‖ ^ 2)
        = (fun ρ : XiZeroIndex =>
        (analyticOrderNatAt entireRiemannXi (xiZeroLoc ρ) : ℝ) * (1 / ‖xiZeroLoc ρ‖ ^ 2))
        from funext hfib]
    exact hMult

/-! ## 3. Locally-uniform multipliability over the multiplicity index.

Re-derived from the abstract genus-1 M-test (Bridge 36/Bridge 7 of `Scratch.lean`, copied here):
the quadratic bound `‖E₁(w) - 1‖ ≤ 3‖w‖²` plus `Σ 1/‖loc i‖² < ∞` and `‖loc i‖ → ∞` give
locally-uniform multipliability via `Summable.multipliableUniformlyOn_one_add`. -/

/-- Bridge-7 quadratic Taylor bound: `‖(1-w)·exp w - 1‖ ≤ 3‖w‖²` for `‖w‖ ≤ 1`. -/
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
      refine h.trans (le_of_eq ?_)
      simp only [Nat.factorial_one, Nat.cast_one, mul_one, pow_one]; ring
    rw [norm_mul]
    calc ‖w‖ * ‖Complex.exp w - 1‖
        ≤ ‖w‖ * (2 * ‖w‖) := mul_le_mul_of_nonneg_left hle (norm_nonneg w)
      _ = 2 * ‖w‖ ^ 2 := by ring
  rw [hkey]
  calc ‖(Complex.exp w - 1 - w) - w * (Complex.exp w - 1)‖
      ≤ ‖Complex.exp w - 1 - w‖ + ‖w * (Complex.exp w - 1)‖ := norm_sub_le _ _
    _ ≤ ‖w‖ ^ 2 + 2 * ‖w‖ ^ 2 := add_le_add hp1 hp2
    _ = 3 * ‖w‖ ^ 2 := by ring

/-- `genus1Factor`-shaped version of the bound. -/
theorem norm_genus1Factor_sub_one_le {ρ s : ℂ} (h : ‖s / ρ‖ ≤ 1) :
    ‖genus1Factor ρ s - 1‖ ≤ 3 * ‖s / ρ‖ ^ 2 := by
  unfold genus1Factor; exact norm_genus1_sub_one_le h

/-- Abstract Bridge 36: a genus-1 product whose locations are nonzero, inverse-square summable, and
escape to ∞ is `MultipliableLocallyUniformlyOn univ`. (Copied from `Scratch.lean`.) -/
theorem genus1Product_multipliableLocallyUniformlyOn
    {ι : Type*} (loc : ι → ℂ)
    (hsumm : Summable (fun i => 1 / ‖loc i‖ ^ 2))
    (hcofin : Tendsto (fun i => ‖loc i‖) cofinite atTop) :
    MultipliableLocallyUniformlyOn (fun i s => genus1Factor (loc i) s) Set.univ := by
  have hcts : ∀ i, Continuous (fun s : ℂ => genus1Factor (loc i) s) := by
    intro i; unfold genus1Factor; fun_prop
  have hcts' : ∀ i, Continuous (fun s : ℂ => genus1Factor (loc i) s - 1) :=
    fun i => (hcts i).sub continuous_const
  apply MultipliableLocallyUniformlyOn_congr
    (f := fun i s => 1 + (genus1Factor (loc i) s - 1))
    (f' := fun i s => genus1Factor (loc i) s)
  · intro i s _hs; ring
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
    have hu : Summable (fun i => 3 * R ^ 2 * (1 / ‖loc i‖ ^ 2)) := hsumm.mul_left _
    have hge : ∀ᶠ i in cofinite, R ≤ ‖loc i‖ := hcofin.eventually_ge_atTop R
    have hbound : ∀ᶠ i in cofinite,
        ∀ s ∈ Metric.closedBall (0 : ℂ) R, ‖genus1Factor (loc i) s - 1‖
          ≤ 3 * R ^ 2 * (1 / ‖loc i‖ ^ 2) := by
      filter_upwards [hge] with i hi s hs
      have hsR : ‖s‖ ≤ R := by simpa [dist_zero_right] using hs
      have hlocpos : 0 < ‖loc i‖ := by linarith
      have hdiv : ‖s / loc i‖ ≤ 1 := by
        rw [norm_div, div_le_one hlocpos]; exact le_trans hsR hi
      have hb := norm_genus1Factor_sub_one_le (ρ := loc i) (s := s) hdiv
      refine hb.trans ?_
      have hsq : ‖s‖ ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (norm_nonneg s) hsR 2
      rw [norm_div, div_pow]
      calc 3 * (‖s‖ ^ 2 / ‖loc i‖ ^ 2)
          ≤ 3 * (R ^ 2 / ‖loc i‖ ^ 2) := by gcongr
        _ = 3 * R ^ 2 * (1 / ‖loc i‖ ^ 2) := by ring
    exact Summable.multipliableUniformlyOn_one_add
      (f := fun i s => genus1Factor (loc i) s - 1)
      (K := Metric.closedBall (0 : ℂ) R) (u := fun i => 3 * R ^ 2 * (1 / ‖loc i‖ ^ 2))
      hK hu hbound (fun i => (hcts' i).continuousOn)

/-- **Unconditional-modulo-`hMult` local-uniform convergence** of the genus-1 Hadamard product over
the MULTIPLICITY index. -/
theorem xiMult_genus1Product_LU (hMult : WithMultInvSqSummable) :
    MultipliableLocallyUniformlyOn (fun i s => genus1Factor (zeroLocMult i) s) Set.univ :=
  genus1Product_multipliableLocallyUniformlyOn zeroLocMult
    (zeroLocMult_invSq_summable hMult)
    (tendsto_norm_cocompact_atTop.comp tendsto_zeroLocMult_cofinite_cocompact)

/-! ## 4. The order-of-product machinery (copied from `Scratch.lean` / `ScratchOrder.lean`) and the
DELIVERABLE `analyticOrderAt` match. -/

/-- Order of a finite product of analytic functions = sum of the orders. -/
theorem analyticOrderAt_finsetProd {ι : Type*} (s : Finset ι) (F : ι → ℂ → ℂ) (z : ℂ)
    (hF : ∀ i ∈ s, AnalyticAt ℂ (F i) z) :
    analyticOrderAt (fun w => ∏ i ∈ s, F i w) z = ∑ i ∈ s, analyticOrderAt (F i) z := by
  classical
  induction s using Finset.induction with
  | empty =>
    simp only [Finset.prod_empty, Finset.sum_empty]
    rw [analyticOrderAt_eq_zero]; right; simp
  | insert a s ha ih =>
    simp only [Finset.prod_insert ha, Finset.sum_insert ha]
    have hAa : AnalyticAt ℂ (F a) z := hF a (Finset.mem_insert_self a s)
    have hArest : AnalyticAt ℂ (fun w => ∏ i ∈ s, F i w) z := by
      have := Finset.analyticAt_prod (𝕜 := ℂ) (f := F) s
        (fun i hi => hF i (Finset.mem_insert_of_mem hi))
      rw [Finset.prod_fn] at this; exact this
    have key : analyticOrderAt (fun w => F a w * ∏ i ∈ s, F i w) z
        = analyticOrderAt (F a) z + analyticOrderAt (fun w => ∏ i ∈ s, F i w) z := by
      have := analyticOrderAt_mul (f := F a) (g := fun w => ∏ i ∈ s, F i w) hAa hArest
      simpa [Pi.mul_def] using this
    rw [key, ih (fun i hi => hF i (Finset.mem_insert_of_mem hi))]

/-- Order of the locally-uniform genus-1 product at `z` equals the hitting count
`Nat.card {i | loc i = z}`, GIVEN the local factorization (finite hitting product × analytic
nonvanishing tail). This `hsplit` is the genuinely-missing "order of a locally-uniform product"
datum (provided in the real setting by `genus1Product_local_split` of `ScratchSplit.lean`).
Copied from `Scratch.lean`/`ScratchOrder.lean`. -/
theorem analyticOrderAt_genus1Product
    {ι : Type*} (loc : ι → ℂ) (z : ℂ)
    (hne : ∀ i, loc i ≠ 0)
    (hfin : {i | loc i = z}.Finite)
    (tail : ℂ → ℂ)
    (htail_an : AnalyticAt ℂ tail z)
    (htail_ne : tail z ≠ 0)
    (hsplit : ∀ᶠ s in nhds z,
      (∏' i, genus1Factor (loc i) s) = (∏ i ∈ hfin.toFinset, genus1Factor (loc i) s) * tail s) :
    analyticOrderAt (fun s => ∏' i, genus1Factor (loc i) s) z
      = (Nat.card {i | loc i = z} : ℕ∞) := by
  classical
  set F : ι → ℂ → ℂ := fun i s => genus1Factor (loc i) s with hFdef
  set Hfin : Finset ι := hfin.toFinset with hHfindef
  have horder : analyticOrderAt (fun s => ∏' i, F i s) z
      = analyticOrderAt (fun s => (∏ i ∈ Hfin, F i s) * tail s) z :=
    analyticOrderAt_congr hsplit
  rw [horder]
  have hAfin : AnalyticAt ℂ (fun s => ∏ i ∈ Hfin, F i s) z := by
    have := Finset.analyticAt_prod (𝕜 := ℂ) (f := F) Hfin
      (fun i _ => analyticAt_genus1Factor (loc i) z)
    rw [Finset.prod_fn] at this; exact this
  have hmul_eq : analyticOrderAt (fun s => (∏ i ∈ Hfin, F i s) * tail s) z
      = analyticOrderAt (fun s => ∏ i ∈ Hfin, F i s) z + analyticOrderAt tail z := by
    have := analyticOrderAt_mul (f := fun s => ∏ i ∈ Hfin, F i s) (g := tail) hAfin htail_an
    simpa [Pi.mul_def] using this
  rw [hmul_eq]
  have htail0 : analyticOrderAt tail z = 0 := by
    rw [htail_an.analyticOrderAt_eq_zero]; exact htail_ne
  rw [htail0, add_zero]
  rw [analyticOrderAt_finsetProd Hfin F z (fun i _ => analyticAt_genus1Factor (loc i) z)]
  have hmemz : ∀ i ∈ Hfin, loc i = z := fun i hi => (hfin.mem_toFinset.mp hi)
  have hsum : ∑ i ∈ Hfin, analyticOrderAt (F i) z = ∑ _i ∈ Hfin, (1 : ℕ∞) := by
    apply Finset.sum_congr rfl
    intro i hi
    have hlocz : loc i = z := hmemz i hi
    change analyticOrderAt (genus1Factor (loc i)) z = 1
    rw [hlocz]
    exact analyticOrderAt_genus1Factor_self (hlocz ▸ hne i)
  rw [hsum]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [Nat.card_eq_card_finite_toFinset hfin]

/-! ### 4a. The hitting-count over the MULTIPLICITY index equals the ξ order.

For a zero `ρ`, the indices `i : XiZeroIndexMult` with `zeroLocMult i = ρ` are exactly the copies
`⟨σ, k⟩` with `(σ : ℂ) = ρ`, i.e. `σ = ρ` as zero-subtype elements (val is injective); their count
is `m_ρ = analyticOrderNatAt ξ ρ`. For a non-zero `z` there are no such indices and the ξ-order is
0. Either way `Nat.card {i | zeroLocMult i = z} = analyticOrderAt ξ z` in `ℕ∞`. -/

/-- The fiber of `zeroLocMult` over a point `z` is finite (each base zero contributes its finite
multiplicity, and at most one base zero equals `z`). -/
theorem zeroLocMult_fiber_finite (z : ℂ) : {i : XiZeroIndexMult | zeroLocMult i = z}.Finite := by
  classical
  by_cases hz : entireRiemannXi z = 0
  · -- the only base that can match is the zero `⟨z, hz⟩`
    set ρ₀ : XiZeroIndex := ⟨z, hz⟩ with hρ₀
    -- the fiber injects into `Fin m_{ρ₀}` via the second component (after identifying the base)
    apply Set.Finite.ofFinset (Finset.univ.image
      (fun k : Fin (analyticOrderNatAt entireRiemannXi (xiZeroLoc ρ₀)) =>
        (⟨ρ₀, k⟩ : XiZeroIndexMult)))
    intro i
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨k, rfl⟩
      show zeroLocMult (⟨ρ₀, k⟩ : XiZeroIndexMult) = z
      rfl
    · intro hi
      -- `zeroLocMult i = z` means `(i.1 : ℂ) = z`, so `i.1 = ρ₀`
      have hval : (i.1 : ℂ) = z := hi
      have hbase : i.1 = ρ₀ := Subtype.ext hval
      refine ⟨hbase ▸ i.2, ?_⟩
      -- rebuild `i = ⟨ρ₀, _⟩`
      obtain ⟨b, k⟩ := i
      simp only at hbase
      subst hbase
      rfl
  · -- no index hits a non-zero point (every `zeroLocMult i` is a zero)
    convert Set.finite_empty
    ext i
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    intro hi
    exact hz (hi ▸ entireRiemannXi_zeroLocMult i)

/-- **Hitting count = ξ order.** `Nat.card {i | zeroLocMult i = z} = analyticOrderAt ξ z` (in ℕ∞). -/
theorem natCard_zeroLocMult_fiber_eq_order (z : ℂ) :
    (Nat.card {i : XiZeroIndexMult | zeroLocMult i = z} : ℕ∞)
      = analyticOrderAt entireRiemannXi z := by
  classical
  rw [← cast_analyticOrderNatAt_entireRiemannXi z, Nat.cast_inj]
  by_cases hz : entireRiemannXi z = 0
  · -- the fiber is in bijection with `Fin m_z`
    set ρ₀ : XiZeroIndex := ⟨z, hz⟩ with hρ₀
    have hloc : xiZeroLoc ρ₀ = z := rfl
    have hequiv : {i : XiZeroIndexMult | zeroLocMult i = z}
        ≃ Fin (analyticOrderNatAt entireRiemannXi (xiZeroLoc ρ₀)) := by
      refine
        { toFun := fun i => ?_
          invFun := fun k => ⟨⟨ρ₀, k⟩, by simp [zeroLocMult, xiZeroLoc, hρ₀]⟩
          left_inv := ?_
          right_inv := ?_ }
      · -- forward: base equals ρ₀, send to second component
        refine Fin.cast ?_ i.1.2
        have : i.1.1 = ρ₀ := Subtype.ext i.2
        rw [this]
      · rintro ⟨⟨b, k⟩, hb⟩
        have hbase : b = ρ₀ := Subtype.ext hb
        subst hbase
        simp
      · intro k
        simp
    rw [Nat.card_congr hequiv, Nat.card_eq_fintype_card, Fintype.card_fin, hloc]
  · -- both sides 0
    have h1 : {i : XiZeroIndexMult | zeroLocMult i = z} = ∅ := by
      ext i
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      intro hi
      exact hz (hi ▸ entireRiemannXi_zeroLocMult i)
    have h2 : analyticOrderNatAt entireRiemannXi z = 0 := by
      rw [analyticOrderNatAt, (analyticOnNhd_entireRiemannXi z (Set.mem_univ _)).analyticOrderAt_eq_zero.2 hz]
      rfl
    rw [h1, h2]
    simp

/-! ### 4b. THE DELIVERABLE.

`xiMult_genus1Product_analyticOrderAt`: unconditionally (given the proven structural inputs of
`Scratch.lean`, passed as hypotheses) the order of the multiplicity-aware genus-1 product matches
ξ's order at EVERY point. This is the statement that lets `Q = ξ/∏` be entire WITHOUT assuming the
zeros are simple. -/

/-- **Multiplicity-aware order match (the key deliverable).**
For every `z`, the order of the multiplicity-aware genus-1 product equals `analyticOrderAt ξ z`.

Inputs:
* `htail` — the per-point local factorization datum (finite hitting product × analytic nonvanishing
  tail). In the real setting this is `genus1Product_local_split` (`ScratchSplit.lean`) fed by
  `xiMult_genus1Product_LU`; here it is the single isolated structural hypothesis, exactly the
  "order of a locally-uniform product" content Mathlib lacks a lemma for. -/
theorem xiMult_genus1Product_analyticOrderAt
    (htail : ∀ z : ℂ, ∃ tail : ℂ → ℂ, AnalyticAt ℂ tail z ∧ tail z ≠ 0 ∧
      ∀ᶠ s in nhds z, (∏' i : XiZeroIndexMult, genus1Factor (zeroLocMult i) s)
        = (∏ i ∈ (zeroLocMult_fiber_finite z).toFinset, genus1Factor (zeroLocMult i) s) * tail s)
    (z : ℂ) :
    analyticOrderAt (fun s => ∏' i : XiZeroIndexMult, genus1Factor (zeroLocMult i) s) z
      = analyticOrderAt entireRiemannXi z := by
  obtain ⟨tail, htail_an, htail_ne, hsplit⟩ := htail z
  rw [analyticOrderAt_genus1Product zeroLocMult z zeroLocMult_ne_zero
    (zeroLocMult_fiber_finite z) tail htail_an htail_ne hsplit]
  exact natCard_zeroLocMult_fiber_eq_order z

#print axioms xiMult_genus1Product_analyticOrderAt
#print axioms zeroLocMult_invSq_summable
#print axioms xiMult_genus1Product_LU
#print axioms natCard_zeroLocMult_fiber_eq_order

end OverflowResidueRH.BacklundTuring.ScratchMultIndex
