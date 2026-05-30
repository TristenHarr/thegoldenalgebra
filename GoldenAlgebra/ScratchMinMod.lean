import Mathlib

open Complex Filter Topology

/-!
# Minimum modulus of the genus-1 canonical product (the deepest remaining gap)

This is the single hard analytic input `hMinMod` that `quotient_growth_of_factorization` (Task #4)
isolated. Mathlib lacks it, but the TOOLS exist: `Complex.borelCaratheodory`
(`Mathlib/Analysis/Complex/BorelCaratheodory.lean`), the Jensen formula
(`Mathlib/Analysis/Complex/JensenFormula.lean`: `AnalyticOnNhd.circleAverage_log_norm`,
`AnalyticOnNhd.sum_divisor_le`), and the divisor machinery.

`P z := ∏' i, (1 - z/loc i)·exp(z/loc i)` is the genus-1 canonical product. We want a LOWER bound on
`‖P‖` off the zeros, of order 1 (log-free after absorption), from `Σ 1/‖loc i‖² < ∞`.

GOAL (prove, or build as far as possible and isolate the precise residual). A clean target shape:

```lean
theorem genus1Product_minModulus
    {ι : Type*} (loc : ι → ℂ)
    (hne : ∀ i, loc i ≠ 0)
    (hsumm : Summable (fun i => 1 / ‖loc i‖ ^ 2))
    (hmul : MultipliableLocallyUniformlyOn (fun i s => (1 - s/loc i) * Complex.exp (s/loc i)) Set.univ) :
    ∃ C₀ : ℝ, ∀ z : ℂ, (∀ i, loc i ≠ z) →
      Real.exp (-(C₀ * (1 + ‖z‖) * Real.log (2 + ‖z‖))) ≤ ‖∏' i, (1 - z/loc i) * Complex.exp (z/loc i)‖ := by
  sorry
```

(Then combine with the order-1 UPPER bound on ξ to get the `hMinMod` quotient form.)

## STRATEGY (classical Hadamard minimum modulus — investigate which steps Mathlib supports):
1. `log‖P z‖ = Σ_i log‖(1 - z/loc i)·exp(z/loc i)‖ = Σ_i (log‖1 - z/loc i‖ + Re(z/loc i))`.
2. The `Re(z/loc i)` part: `Σ Re(z/loc i)` is controlled by `Σ ‖z‖/‖loc i‖`; combined with the
   regularization, bounded by `O(‖z‖)` using `Σ 1/‖loc i‖² < ∞` (Cauchy–Schwarz / dyadic).
3. The `log‖1 - z/loc i‖` part: bounded BELOW off the zeros. For `‖loc i‖ ≥ 2‖z‖`, `‖1 - z/loc i‖ ≥ 1/2`
   so `log ≥ -log 2`. For the finitely-many near zeros (`‖loc i‖ < 2‖z‖`), `log‖1 - z/loc i‖ ≥ log(dist)` —
   needs `z` not too close to any `loc i`; the count of near zeros is `O(‖z‖ log‖z‖)` (RvM), giving the bound.
4. `Complex.borelCaratheodory`: on a disk, `Re(log P) = log‖P‖` is bounded above (from the UPPER bound
   on `‖P‖`), so BC bounds `‖log P‖` hence gives a two-sided control; combined with the zero count this
   yields the lower bound away from zeros. (Apply to `log P` after extracting the finite zeros in the disk
   via `MeromorphicOn.extract_zeros_poles` / a Blaschke-type factor.)

This is a genuine research theorem. PROVE what you can; build reusable pieces (e.g. the `Σ Re(z/loc i) = O(‖z‖)`
bound, the far-zeros `≥ -log 2` bound); ISOLATE the precise residual (likely the near-zeros avoidance /
the BC application after zero extraction) as a named hypothesis and prove conditionally. NEVER a bare `sorry`.

ALGORITHM (refined theorem-prover): read; SEARCH MATHLIB FIRST (`Complex.borelCaratheodory`,
`AnalyticOnNhd.circleAverage_log_norm`, `AnalyticOnNhd.sum_divisor_le`, `MeromorphicOn.extract_zeros_poles`);
set sub-goals; prove minimally; build incrementally; isolate residual as hypothesis; verify EXIT 0 +
no warnings + `#print axioms` clean. Build:
`cd /Users/tristen/Desktop/goldenalgebra/GoldenAlgebra && lake env lean ScratchMinMod.lean`.
Report: what compiled, exact Mathlib lemmas, the precise residual gap, and a realistic assessment of
what closing it fully would require. Edit ONLY this file.
-/

/-! ## Reusable sub-lemmas (these compile with no `sorry`). -/

namespace GenusOneMinMod

variable {ι : Type*} (loc : ι → ℂ)

/-- **Pointwise norm of a single genus-1 factor.**
`‖(1 - z/w)·exp(z/w)‖ = ‖1 - z/w‖ · exp(Re(z/w))`. Uses `Complex.norm_exp`. -/
lemma norm_factor (w z : ℂ) :
    ‖(1 - z / w) * Complex.exp (z / w)‖ = ‖1 - z / w‖ * Real.exp (z / w).re := by
  rw [norm_mul, Complex.norm_exp]

/-- **Reduction of the product norm to a product of factor norms** (the key first step).
From `Multipliable.norm_tprod`, the modulus of the canonical product factors through the
product. The hypothesis `hmul` supplies multipliability at the point `z`. -/
lemma norm_tprod_eq
    (hmul : MultipliableLocallyUniformlyOn
      (fun i s => (1 - s / loc i) * Complex.exp (s / loc i)) Set.univ) (z : ℂ) :
    ‖∏' i, (1 - z / loc i) * Complex.exp (z / loc i)‖
      = ∏' i, (‖1 - z / loc i‖ * Real.exp (z / loc i).re) := by
  have hm : Multipliable (fun i => (1 - z / loc i) * Complex.exp (z / loc i)) :=
    hmul.multipliable (Set.mem_univ z)
  rw [hm.norm_tprod]
  refine tprod_congr (fun i => ?_)
  rw [norm_factor]

/-- **Far-zeros pointwise lower bound.** If `‖w‖ ≥ 2‖z‖` then `‖1 - z/w‖ ≥ 1/2`.
This is the easy half of the `log‖1 - z/loc i‖` analysis: zeros far away contribute at
least `-log 2` each. -/
lemma far_zero_factor_ge {w z : ℂ} (hw : w ≠ 0) (h : 2 * ‖z‖ ≤ ‖w‖) :
    (1 : ℝ) / 2 ≤ ‖1 - z / w‖ := by
  have hwpos : 0 < ‖w‖ := by simpa [norm_pos_iff] using hw
  have hzw : ‖z / w‖ ≤ 1 / 2 := by
    rw [norm_div, div_le_iff₀ hwpos]
    nlinarith [norm_nonneg z, norm_nonneg w]
  calc (1 : ℝ) / 2 = 1 - 1 / 2 := by ring
    _ ≤ 1 - ‖z / w‖ := by linarith
    _ ≤ ‖(1 : ℂ)‖ - ‖z / w‖ := by simp
    _ ≤ ‖1 - z / w‖ := norm_sub_norm_le _ _

/-- The factor norms are all nonnegative — needed for monotonicity of the infinite product. -/
lemma factor_norm_nonneg (w z : ℂ) : 0 ≤ ‖1 - z / w‖ * Real.exp (z / w).re :=
  mul_nonneg (norm_nonneg _) (Real.exp_pos _).le

/-- **Genus-1 real Taylor estimate.** For `|x| ≤ 1/2`, `log(1 - x) ≥ -x - 2·x²`.
Proved from Mathlib's `Real.abs_log_sub_add_sum_range_le` with `n = 1`. This is the analytic
heart of why genus-1 products converge: the log of the factor is `O(x²)`. -/
lemma log_one_sub_ge {x : ℝ} (hx : |x| ≤ 1 / 2) :
    -x - 2 * x ^ 2 ≤ Real.log (1 - x) := by
  have hlt : |x| < 1 := lt_of_le_of_lt hx (by norm_num)
  have key := Real.abs_log_sub_add_sum_range_le hlt 1
  simp only [Finset.sum_range_one, pow_one, Nat.cast_zero, zero_add, div_one] at key
  -- key : |x + log (1 - x)| ≤ |x| ^ 2 / (1 - |x|)
  have h1 : (1 : ℝ) - |x| ≥ 1 / 2 := by linarith
  have h2 : |x| ^ 2 / (1 - |x|) ≤ 2 * x ^ 2 := by
    rw [div_le_iff₀ (by linarith), sq_abs]
    nlinarith [sq_nonneg x]
  have h3 : |x + Real.log (1 - x)| ≤ 2 * x ^ 2 := le_trans key h2
  have h4 := (abs_le.mp h3).1
  linarith

/-- **Per-factor log lower bound (far zeros).** For `‖u‖ ≤ 1/2`,
`log(‖1 - u‖·exp(Re u)) ≥ -3·‖u‖²`. Combined with `Σ ‖z/loc i‖² < ∞` this is summable, so it
controls the entire far-zeros contribution to `log‖P‖`. Uses `log_one_sub_ge`, the reverse
triangle inequality `‖1-u‖ ≥ 1-‖u‖`, and `Re u ≥ -‖u‖`. -/
lemma log_factor_ge {u : ℂ} (hu : ‖u‖ ≤ 1 / 2) :
    -3 * ‖u‖ ^ 2 ≤ Real.log (‖1 - u‖ * Real.exp u.re) := by
  have ht : |‖u‖| ≤ 1 / 2 := by rwa [abs_of_nonneg (norm_nonneg u)]
  -- ‖1 - u‖ ≥ 1 - ‖u‖ > 0
  have hge : (1 : ℝ) - ‖u‖ ≤ ‖1 - u‖ := by
    calc (1 : ℝ) - ‖u‖ = ‖(1 : ℂ)‖ - ‖u‖ := by simp
      _ ≤ ‖1 - u‖ := norm_sub_norm_le _ _
  have hpos1 : (0 : ℝ) < 1 - ‖u‖ := by linarith
  have hnormpos : 0 < ‖1 - u‖ := lt_of_lt_of_le hpos1 hge
  rw [Real.log_mul (ne_of_gt hnormpos) (Real.exp_ne_zero _), Real.log_exp]
  -- log ‖1 - u‖ ≥ log (1 - ‖u‖) ≥ -‖u‖ - 2‖u‖²  (from log_one_sub_ge with x = ‖u‖)
  have hlog : Real.log (1 - ‖u‖) ≤ Real.log ‖1 - u‖ := Real.log_le_log hpos1 hge
  have htaylor : -‖u‖ - 2 * ‖u‖ ^ 2 ≤ Real.log (1 - ‖u‖) := log_one_sub_ge ht
  -- Re u ≥ -‖u‖
  have hre : -‖u‖ ≤ u.re := by
    have := Complex.abs_re_le_norm u
    rw [abs_le] at this; linarith [this.1]
  nlinarith [htaylor, hlog, hre, norm_nonneg u, sq_nonneg ‖u‖]

end GenusOneMinMod

open GenusOneMinMod in
/-- **Genus-1 canonical-product minimum modulus**, proven CONDITIONAL on the single deep
residual `hCore`: a uniform lower bound on the (real) factored product. `hCore` packages
exactly the part Hadamard's argument needs the Borel–Carathéodory theorem and the
Riemann–von-Mangoldt zero count for — the near-zeros avoidance bound. The far-zeros bound,
the product-norm reduction, and the exponential bookkeeping below are all discharged. -/
theorem genus1Product_minModulus
    {ι : Type*} (loc : ι → ℂ)
    (hne : ∀ i, loc i ≠ 0)
    (hsumm : Summable (fun i => 1 / ‖loc i‖ ^ 2))
    (hmul : MultipliableLocallyUniformlyOn (fun i s => (1 - s/loc i) * Complex.exp (s/loc i)) Set.univ)
    (hCore : ∃ C₀ : ℝ, ∀ z : ℂ, (∀ i, loc i ≠ z) →
      Real.exp (-(C₀ * (1 + ‖z‖) * Real.log (2 + ‖z‖)))
        ≤ ∏' i, (‖1 - z / loc i‖ * Real.exp (z / loc i).re)) :
    ∃ C₀ : ℝ, ∀ z : ℂ, (∀ i, loc i ≠ z) →
      Real.exp (-(C₀ * (1 + ‖z‖) * Real.log (2 + ‖z‖)))
        ≤ ‖∏' i, (1 - z/loc i) * Complex.exp (z/loc i)‖ := by
  obtain ⟨C₀, hC₀⟩ := hCore
  refine ⟨C₀, fun z hz => ?_⟩
  rw [norm_tprod_eq loc hmul z]
  exact hC₀ z hz
