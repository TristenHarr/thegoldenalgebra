import Mathlib

/-!
# ScratchEulerMaclaurin — the Euler–Maclaurin Σ-vs-∫ remainder for the arctan phase sum

This file supplies **core (2)** of the Γ-phase remainder left open by `ScratchBinetSeries.lean`:
the Euler–Maclaurin / Abel-summation comparison of the partial sums

  `S_n(T) = Σ_{k=1}^n g(k)`,   `g(x) = arctan( (T/2) / (x + ¼) )`,

to the integral `∫₁^n g(x) dx`, with a remainder bounded **uniformly in `T` and `n`**.

`ScratchBinetSeries.lean` already PROVED (no integral theory):
* `arg(1+z/k) = arctan((T/2)/(k+¼))` (`arg_wTerm_eq`),
* `|arctan x − x| ≤ x³`, `arctan x ≤ x` on `[0,∞)` (`sub_arctan_le_cube`, `arctan_le_self_of_nonneg`),
* summability of the per-term Weierstrass defect series (`summable_argDefect`).

The missing `O(1)` piece is the `Σ`-vs-`∫` comparison.  The key tractable fact (run brief):
`g'(x) = −(T/2)/((x+¼)²+(T/2)²) ≤ 0`, and the total variation
`∫₁^n |g'| = g(1) − g(n) ≤ g(1) = arctan((T/2)/(5/4)) < π/2` is **BOUNDED UNIFORMLY IN `T`**.

## What is PROVEN here

* `gPhase`, `gPhaseDeriv` and `hasDerivAt_gPhase`: the closed form
  `HasDerivAt (gPhase T) (gPhaseDeriv T x) x`, `gPhaseDeriv T x = −(T/2)/((x+¼)²+(T/2)²)`,
  via `Real.hasDerivAt_arctan` + the quotient rule (chain rule).
* `gPhaseDeriv_nonpos` (for `T ≥ 0`): `g'(x) ≤ 0`, so `g` is antitone; `gPhase_nonneg`.
* `abs_gPhaseDeriv` : `|g'(x)| = −g'(x)` (for `T ≥ 0`, `x ≥ 1`).
* `integral_abs_gPhaseDeriv_eq` : `∫₁^b |g'| = g(1) − g(b)` (FTC-2 on the antitone `g`).
* `integral_abs_gPhaseDeriv_le_pi_div_two` : **`∫₁^b |g'| ≤ π/2`** uniformly in `T ≥ 0`, `b ≥ 1`
  — the key uniform Euler–Maclaurin total-variation bound.

* The **Abel-summation Euler–Maclaurin identity** (`c ≡ 1`,
  `Σ_{k∈Icc 0 t} 1 = ⌊t⌋₊+1`): from Mathlib's `sum_mul_eq_sub_sub_integral_mul'`,
  `Σ_{k∈Ioc n m} g(k) = g(m)(m+1) − g(n)(n+1) − ∫_{(n,m]} g'(t)·(⌊t⌋₊+1) dt`
  (`abel_sum_gPhase`).
* `euler_maclaurin_remainder_bound` : the **uniform remainder bound**
  `|Σ_{k∈Ioc n m} g(k) − (g(m)(m+1) − g(n)(n+1)) + ∫_{(n,m]} g'(t)(t−⌊t⌋₊−1) dt| ... |R| ≤ π/2`
  where the Euler–Maclaurin remainder `R = ∫_{(n,m]} g'(t)·((⌊t⌋₊+1) − t) dt` (weight in `[0,1]`)
  satisfies `|R| ≤ ∫|g'| ≤ π/2`.  This is the genuine Σ-vs-∫ core: the leading integral
  `∫ₙ^m g` differs from the boundary term `g(m)(m+1) − g(n)(n+1)` by exactly an integration
  by parts whose `t·g'` part recombines with the floor integral into the bounded-weight `R`.

## Honest residual

The full closed-form evaluation of `∫ₙ^m g(t) dt` to the `stirPrincipal` shape (an `arctan`/`log`
antiderivative, integration-by-parts), and its final constant-matching to `≤ ½`, is NOT done here;
it remains in `ScratchBinetSeries.binetRem_via_series_axiom`.  What this file delivers is the
**uniform `O(1)` Euler–Maclaurin remainder bound `≤ π/2`** with the `∫|g'| ≤ π/2` total-variation
fact PROVEN — the genuine tractable core of (2).  `#print axioms` at the end exhibits the
axiom footprint (only Mathlib's classical axioms; **no `sorryAx`**).
-/

open Complex Real MeasureTheory intervalIntegral

namespace OverflowResidueRH
namespace BacklundTuring
namespace ScratchEulerMaclaurin

/-! ## Part 1 — the phase function `g(x) = arctan((T/2)/(x+¼))` and its derivative -/

/-- The Euler–Maclaurin phase summand `g(x) = arctan( (T/2) / (x + ¼) )`. -/
noncomputable def gPhase (T : ℝ) (x : ℝ) : ℝ := Real.arctan ((T / 2) / (x + 1 / 4))

/-- The closed-form derivative `g'(x) = −(T/2) / ((x + ¼)² + (T/2)²)`. -/
noncomputable def gPhaseDeriv (T : ℝ) (x : ℝ) : ℝ :=
  -(T / 2) / ((x + 1 / 4) ^ 2 + (T / 2) ^ 2)

/-- **`HasDerivAt (gPhase T) (gPhaseDeriv T x) x`** for `x > −¼` (chain rule:
`arctan' = 1/(1+u²)` with `u = (T/2)/(x+¼)`, `u' = −(T/2)/(x+¼)²`). -/
theorem hasDerivAt_gPhase (T : ℝ) {x : ℝ} (hx : -(1/4) < x) :
    HasDerivAt (gPhase T) (gPhaseDeriv T x) x := by
  have hxpos : (0 : ℝ) < x + 1 / 4 := by linarith
  have hxne : (x + 1 / 4) ≠ 0 := ne_of_gt hxpos
  -- inner u(x) = (T/2)/(x+¼), with u'(x) = −(T/2)/(x+¼)²
  have hden : HasDerivAt (fun y : ℝ => y + 1 / 4) 1 x := by
    simpa using (hasDerivAt_id x).add_const (1 / 4)
  have hu : HasDerivAt (fun y : ℝ => (T / 2) / (y + 1 / 4))
      (-(T / 2) / (x + 1 / 4) ^ 2) x := by
    have h := (hasDerivAt_const x (T / 2)).div hden hxne
    convert h using 1
    rw [show (0 : ℝ) * (x + 1 / 4) - T / 2 * 1 = -(T / 2) by ring]
  -- arctan ∘ u
  have hcomp := (Real.hasDerivAt_arctan ((T / 2) / (x + 1 / 4))).comp x hu
  -- now simplify the derivative value to gPhaseDeriv
  have hsq : (0 : ℝ) < (x + 1 / 4) ^ 2 := by positivity
  have hd2 : (0 : ℝ) < (x + 1 / 4) ^ 2 + (T / 2) ^ 2 := by positivity
  have hu2 : (1 : ℝ) + ((T / 2) / (x + 1 / 4)) ^ 2
      = ((x + 1 / 4) ^ 2 + (T / 2) ^ 2) / (x + 1 / 4) ^ 2 := by
    rw [eq_div_iff (ne_of_gt hsq), add_mul, div_pow, div_mul_cancel₀ _ (ne_of_gt hsq), one_mul]
  have hgoal : (1 : ℝ) / (1 + ((T / 2) / (x + 1 / 4)) ^ 2) * (-(T / 2) / (x + 1 / 4) ^ 2)
      = gPhaseDeriv T x := by
    unfold gPhaseDeriv
    rw [hu2, one_div_div, div_mul_div_comm,
        mul_comm ((x + 1 / 4) ^ 2) (-(T / 2)),
        mul_div_mul_right _ _ (ne_of_gt hsq)]
  rw [← hgoal]
  exact hcomp

/-- For `T ≥ 0`, `g'(x) ≤ 0` (so `g` is antitone). -/
theorem gPhaseDeriv_nonpos (T : ℝ) (hT : 0 ≤ T) (x : ℝ) : gPhaseDeriv T x ≤ 0 := by
  unfold gPhaseDeriv
  have hden : (0 : ℝ) ≤ (x + 1 / 4) ^ 2 + (T / 2) ^ 2 := by positivity
  apply div_nonpos_of_nonpos_of_nonneg
  · linarith
  · exact hden

/-- For `T ≥ 0` and `x ≥ 0`, `g(x) ≥ 0`. -/
theorem gPhase_nonneg (T : ℝ) (hT : 0 ≤ T) {x : ℝ} (hx : 0 ≤ x) : 0 ≤ gPhase T x := by
  unfold gPhase
  apply Real.arctan_nonneg.mpr
  have hpos : (0 : ℝ) < x + 1 / 4 := by linarith
  apply div_nonneg (by linarith : (0:ℝ) ≤ T / 2) hpos.le

/-- `g(x) ≤ π/2` for all `x` (arctan range). -/
theorem gPhase_lt_pi_div_two (T x : ℝ) : gPhase T x < π / 2 :=
  Real.arctan_lt_pi_div_two _

/-! ## Part 2 — the key uniform total-variation bound `∫₁^b |g'| ≤ π/2`

`g' ≤ 0` (for `T ≥ 0`), so `|g'| = −g'`, and by FTC-2 `∫₁^b |g'| = ∫₁^b (−g') = g(1) − g(b)`.
Since `g(b) ≥ 0` (Part 1) and `g(1) = arctan((T/2)/(5/4)) < π/2`, we get `∫₁^b |g'| ≤ π/2`,
**uniformly in `T ≥ 0` and `b ≥ 1`.** -/

/-- `gPhaseDeriv T` is continuous (denominator `(x+¼)²+(T/2)²` is never `0` once `x ≥ 1`; in fact
it is continuous everywhere it is finite, and on `[1,b]` the denominator is `≥ (5/4)² > 0`). -/
theorem continuousOn_gPhaseDeriv (T : ℝ) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ContinuousOn (gPhaseDeriv T) (Set.uIcc a b) := by
  apply ContinuousOn.div continuousOn_const
  · fun_prop
  · intro x hx
    have hx0 : 0 ≤ x := by
      rcases le_total a b with h | h
      · rw [Set.uIcc_of_le h] at hx; linarith [hx.1]
      · rw [Set.uIcc_of_ge h] at hx; linarith [hx.1, hx.2]
    have : (0 : ℝ) < (x + 1 / 4) ^ 2 + (T / 2) ^ 2 := by
      have : (0 : ℝ) < x + 1 / 4 := by linarith
      positivity
    exact ne_of_gt this

/-- `−gPhaseDeriv = |gPhaseDeriv|` for `T ≥ 0`. -/
theorem abs_gPhaseDeriv (T : ℝ) (hT : 0 ≤ T) (x : ℝ) :
    |gPhaseDeriv T x| = -gPhaseDeriv T x :=
  abs_of_nonpos (gPhaseDeriv_nonpos T hT x)

/-- **FTC-2:** `∫₁^b gPhaseDeriv = g(b) − g(1)` (for `b ≥ 1`). -/
theorem integral_gPhaseDeriv_eq (T : ℝ) {b : ℝ} (hb : 1 ≤ b) :
    ∫ x in (1:ℝ)..b, gPhaseDeriv T x = gPhase T b - gPhase T 1 := by
  apply integral_eq_sub_of_hasDerivAt
  · intro x hx
    rw [Set.uIcc_of_le hb] at hx
    apply hasDerivAt_gPhase
    linarith [hx.1]
  · exact (continuousOn_gPhaseDeriv T (by norm_num : (0:ℝ) ≤ 1)
      (by linarith : (0:ℝ) ≤ b)).intervalIntegrable

/-- **`∫₁^b |g'| = g(1) − g(b)`** (for `T ≥ 0`, `b ≥ 1`). -/
theorem integral_abs_gPhaseDeriv_eq (T : ℝ) (hT : 0 ≤ T) {b : ℝ} (hb : 1 ≤ b) :
    ∫ x in (1:ℝ)..b, |gPhaseDeriv T x| = gPhase T 1 - gPhase T b := by
  have : ∀ x, |gPhaseDeriv T x| = -gPhaseDeriv T x := fun x => abs_gPhaseDeriv T hT x
  simp_rw [this]
  rw [intervalIntegral.integral_neg, integral_gPhaseDeriv_eq T hb]
  ring

/-- **THE KEY UNIFORM BOUND: `∫₁^b |g'| ≤ π/2`** for `T ≥ 0`, `b ≥ 1`.
`∫₁^b |g'| = g(1) − g(b) ≤ g(1) < π/2`, using `g(b) ≥ 0` and `g(1) < π/2`.  This is the
Euler–Maclaurin total-variation bound, uniform in both `T` and `b` — the genuine tractable
core of the `Σ`-vs-`∫` comparison. -/
theorem integral_abs_gPhaseDeriv_le_pi_div_two (T : ℝ) (hT : 0 ≤ T) {b : ℝ} (hb : 1 ≤ b) :
    ∫ x in (1:ℝ)..b, |gPhaseDeriv T x| ≤ π / 2 := by
  rw [integral_abs_gPhaseDeriv_eq T hT hb]
  have h1 : gPhase T 1 < π / 2 := gPhase_lt_pi_div_two T 1
  have h2 : 0 ≤ gPhase T b := gPhase_nonneg T hT (by linarith)
  linarith

/-- General lower endpoint: **`∫ₐ^b |g'| = g(a) − g(b)`** for `T ≥ 0`, `0 ≤ a ≤ b`. -/
theorem integral_abs_gPhaseDeriv_eq' (T : ℝ) (hT : 0 ≤ T) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) :
    ∫ x in a..b, |gPhaseDeriv T x| = gPhase T a - gPhase T b := by
  have hneg : ∀ x, |gPhaseDeriv T x| = -gPhaseDeriv T x := fun x => abs_gPhaseDeriv T hT x
  simp_rw [hneg]
  rw [intervalIntegral.integral_neg]
  have hftc : ∫ x in a..b, gPhaseDeriv T x = gPhase T b - gPhase T a := by
    apply integral_eq_sub_of_hasDerivAt
    · intro x hx
      rw [Set.uIcc_of_le hab] at hx
      exact hasDerivAt_gPhase T (by linarith [hx.1])
    · exact (continuousOn_gPhaseDeriv T ha (le_trans ha hab)).intervalIntegrable
  rw [hftc]; ring

/-- General lower endpoint: **`∫ₐ^b |g'| ≤ π/2`** for `T ≥ 0`, `0 ≤ a ≤ b`. -/
theorem integral_abs_gPhaseDeriv_le_pi_div_two' (T : ℝ) (hT : 0 ≤ T) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) :
    ∫ x in a..b, |gPhaseDeriv T x| ≤ π / 2 := by
  rw [integral_abs_gPhaseDeriv_eq' T hT ha hab]
  have h1 : gPhase T a < π / 2 := gPhase_lt_pi_div_two T a
  have h2 : 0 ≤ gPhase T b := gPhase_nonneg T hT (le_trans ha hab)
  linarith

/-! ## Part 3 — the Abel-summation Euler–Maclaurin identity and the uniform remainder bound

We apply Mathlib's `sum_mul_eq_sub_sub_integral_mul'` (Abel summation, Nat endpoints) with the
constant coefficient sequence `c ≡ 1`, for which `∑_{k∈Icc 0 t} c k = ⌊t⌋₊ + 1` and
`∑_{k∈Ioc n m} g(k)·c(k) = ∑_{k∈Ioc n m} g(k)`.  This gives, with `g = gPhase T`,

  `Σ_{k∈Ioc n m} g(k) = g(m)·(m+1) − g(n)·(n+1) − ∫_{(n,m]} g'(t)·(⌊t⌋₊+1) dt`.

Rearranged, the **Euler–Maclaurin remainder**

  `R := Σ_{k∈Ioc n m} g(k) − (g(m)·(m+1) − g(n)·(n+1)) = − ∫_{(n,m]} g'(t)·(⌊t⌋₊+1) dt`,

and a *bounded-weight* form: subtracting the smooth `∫ t·g'` (the integration-by-parts term that
turns the boundary `g(m)(m+1)−g(n)(n+1)` into `∫ g + (g(m)−g(n))`), the genuinely bounded piece is
`∫ g'(t)·((⌊t⌋₊+1) − t) dt` with weight `(⌊t⌋₊+1)−t = 1−{t} ∈ [0,1]`, hence
`|∫ g'(t)·(1−{t}) dt| ≤ ∫|g'| ≤ π/2` (Part 2).  We prove that bounded-weight bound below. -/

/-- The constant-`1` coefficient sequence `c k = 1`. -/
private def cOne : ℕ → ℝ := fun _ => 1

@[simp] private theorem sum_cOne_Icc (n : ℕ) : ∑ k ∈ Finset.Icc 0 n, cOne k = (n : ℝ) + 1 := by
  unfold cOne; rw [Finset.sum_const, Nat.card_Icc]; simp

/-- `deriv (gPhase T) = gPhaseDeriv T` on `[0,∞)` (from `hasDerivAt_gPhase`). -/
theorem deriv_gPhase (T : ℝ) {x : ℝ} (hx : 0 ≤ x) : deriv (gPhase T) x = gPhaseDeriv T x :=
  (hasDerivAt_gPhase T (by linarith)).deriv

/-- **Abel-summation Euler–Maclaurin identity** for `g = gPhase T`, `n ≤ m`:
`Σ_{k∈Ioc n m} g(k) = g(m)(m+1) − g(n)(n+1) − ∫_{(n,m]} g'(t)(⌊t⌋₊+1) dt`. -/
theorem abel_sum_gPhase (T : ℝ) {n m : ℕ} (h : n ≤ m) :
    ∑ k ∈ Finset.Ioc n m, gPhase T k
      = gPhase T m * ((m : ℝ) + 1) - gPhase T n * ((n : ℝ) + 1)
        - ∫ t in Set.Ioc (n : ℝ) m, gPhaseDeriv T t * ((⌊t⌋₊ : ℝ) + 1) := by
  -- differentiability + integrability of deriv on [n,m]
  have hdiff : ∀ t ∈ Set.Icc (n : ℝ) m, DifferentiableAt ℝ (gPhase T) t := by
    intro t ht
    exact (hasDerivAt_gPhase T (by linarith [ht.1, Nat.cast_nonneg (α := ℝ) n])).differentiableAt
  have hderiv_eq : ∀ t ∈ Set.Icc (n : ℝ) m, deriv (gPhase T) t = gPhaseDeriv T t := by
    intro t ht
    exact deriv_gPhase T (le_trans (Nat.cast_nonneg n) ht.1)
  have hint : IntegrableOn (deriv (gPhase T)) (Set.Icc (n : ℝ) m) := by
    have hcont : ContinuousOn (gPhaseDeriv T) (Set.Icc (n : ℝ) m) := by
      have := continuousOn_gPhaseDeriv T (Nat.cast_nonneg n) (Nat.cast_nonneg m)
      rwa [Set.uIcc_of_le (by exact_mod_cast h : (n:ℝ) ≤ m)] at this
    have hgd : IntegrableOn (gPhaseDeriv T) (Set.Icc (n : ℝ) m) :=
      hcont.integrableOn_compact isCompact_Icc
    exact hgd.congr_fun (fun t ht => (hderiv_eq t ht).symm) measurableSet_Icc
  have key := sum_mul_eq_sub_sub_integral_mul' cOne h hdiff hint
  -- simplify the coefficient sums and the products f k * c k
  have hsm : (∑ _k ∈ Finset.Icc 0 m, cOne _k) = (m : ℝ) + 1 := sum_cOne_Icc m
  have hsn : (∑ _k ∈ Finset.Icc 0 n, cOne _k) = (n : ℝ) + 1 := sum_cOne_Icc n
  have hintegrand : ∀ t ∈ Set.Ioc (n : ℝ) m,
      deriv (gPhase T) t * (∑ _k ∈ Finset.Icc 0 ⌊t⌋₊, cOne _k)
        = gPhaseDeriv T t * ((⌊t⌋₊ : ℝ) + 1) := by
    intro t ht
    rw [hderiv_eq t ⟨ht.1.le, ht.2⟩, sum_cOne_Icc]
  rw [hsm, hsn, setIntegral_congr_fun measurableSet_Ioc hintegrand] at key
  -- key has Σ_{Ioc} g(k)*cOne k ; align with our LHS
  simp only [cOne, mul_one] at key
  exact key

/-! ## Part 4 — the bounded-weight Euler–Maclaurin remainder bound `|R| ≤ π/2`

The floor weight `w(t) = (⌊t⌋₊ + 1) − t = 1 − {t}` lies in `[0,1]`.  We bound the
bounded-weight remainder integral
`R = ∫_{(n,m]} g'(t)·w(t) dt` by `|R| ≤ ∫_{(n,m]} |g'(t)| dt ≤ π/2` (Part 2'), using:
* integrability of `g'·(⌊·⌋₊+1)` (Mathlib `integrableOn_mul_sum_Icc`, `c ≡ 1`) and `g'·(·)`
  (continuous), hence of `g'·w` and `|g'·w|`;
* `|g'(t)·w(t)| ≤ |g'(t)|` from `0 ≤ w ≤ 1`. -/

/-- The floor weight `w(t) = (⌊t⌋₊ + 1) − t = 1 − {t}`. -/
noncomputable def wFloor (t : ℝ) : ℝ := (⌊t⌋₊ : ℝ) + 1 - t

/-- `0 ≤ w(t) ≤ 1` for `0 ≤ t`. -/
theorem wFloor_mem (t : ℝ) (ht : 0 ≤ t) : 0 ≤ wFloor t ∧ wFloor t ≤ 1 := by
  unfold wFloor
  constructor
  · have := Nat.lt_floor_add_one t
    linarith
  · have := Nat.floor_le ht
    linarith

/-- `|w(t)| ≤ 1` for `0 ≤ t`. -/
theorem abs_wFloor_le_one (t : ℝ) (ht : 0 ≤ t) : |wFloor t| ≤ 1 := by
  rcases wFloor_mem t ht with ⟨h0, h1⟩
  rw [abs_of_nonneg h0]; exact h1

/-- Integrability of `t ↦ g'(t)·(⌊t⌋₊+1)` on `[n,m]` (Mathlib `integrableOn_mul_sum_Icc`,
constant coefficients `c ≡ 1`). -/
theorem integrableOn_gPhaseDeriv_mul_floor (T : ℝ) {n m : ℕ} :
    IntegrableOn (fun t => gPhaseDeriv T t * ((⌊t⌋₊ : ℝ) + 1)) (Set.Icc (n : ℝ) m) := by
  have hcont : IntegrableOn (gPhaseDeriv T) (Set.Icc (n : ℝ) m) := by
    rcases le_or_gt (n : ℝ) m with hnm | hnm
    · have := continuousOn_gPhaseDeriv T (Nat.cast_nonneg n) (Nat.cast_nonneg m)
      rw [Set.uIcc_of_le hnm] at this
      exact this.integrableOn_compact isCompact_Icc
    · rw [Set.Icc_eq_empty_of_lt hnm]
      exact integrableOn_empty
  have hI := integrableOn_mul_sum_Icc cOne (m := 0) (Nat.cast_nonneg n) (b := (m : ℝ)) hcont
  -- ∑ k ∈ Icc 0 ⌊t⌋₊, cOne k = ⌊t⌋₊ + 1
  refine hI.congr_fun (fun t _ => ?_) measurableSet_Icc
  simp only [sum_cOne_Icc]

/-- Integrability of `t ↦ gPhaseDeriv T t * t` on `[n,m]` (continuous). -/
theorem integrableOn_gPhaseDeriv_mul_id (T : ℝ) {n m : ℕ} :
    IntegrableOn (fun t => gPhaseDeriv T t * t) (Set.Icc (n : ℝ) m) := by
  rcases le_or_gt (n : ℝ) m with hnm | hnm
  · have hc : ContinuousOn (fun t => gPhaseDeriv T t * t) (Set.Icc (n : ℝ) m) := by
      have := continuousOn_gPhaseDeriv T (Nat.cast_nonneg n) (Nat.cast_nonneg m)
      rw [Set.uIcc_of_le hnm] at this
      exact this.mul continuousOn_id
    exact hc.integrableOn_compact isCompact_Icc
  · rw [Set.Icc_eq_empty_of_lt hnm]; exact integrableOn_empty

/-- Integrability of the bounded-weight integrand `t ↦ gPhaseDeriv T t * wFloor t` on `[n,m]`
(difference of the two integrable pieces above, since `g'·w = g'·(⌊·⌋+1) − g'·(·)`). -/
theorem integrableOn_gPhaseDeriv_mul_wFloor (T : ℝ) {n m : ℕ} :
    IntegrableOn (fun t => gPhaseDeriv T t * wFloor t) (Set.Icc (n : ℝ) m) := by
  have hsub := (integrableOn_gPhaseDeriv_mul_floor T (n := n) (m := m)).sub
    (integrableOn_gPhaseDeriv_mul_id T (n := n) (m := m))
  refine hsub.congr_fun (fun t _ => ?_) measurableSet_Icc
  simp only [Pi.sub_apply, wFloor]; ring

/-- **THE UNIFORM EULER–MACLAURIN REMAINDER BOUND.**
The bounded-weight remainder `R = ∫_{(n,m]} g'(t)·w(t) dt`, `w(t) = (⌊t⌋₊+1)−t ∈ [0,1]`, satisfies
`|R| ≤ ∫_{(n,m]} |g'| ≤ π/2`, **uniformly in `T ≥ 0` and `n ≤ m`.**  This is the genuine `Σ`-vs-`∫`
Euler–Maclaurin core: `R` is exactly the remainder reconciling `Σ_{k∈Ioc n m} g(k)` with the
leading integral `∫ₙ^m g` (after the integration-by-parts that converts the Abel boundary term),
and its bound is the uniform total-variation estimate `∫|g'| ≤ π/2`. -/
theorem euler_maclaurin_remainder_bound (T : ℝ) (hT : 0 ≤ T) {n m : ℕ} (h : n ≤ m) :
    |∫ t in Set.Ioc (n : ℝ) m, gPhaseDeriv T t * wFloor t| ≤ π / 2 := by
  have hnm : (n : ℝ) ≤ m := by exact_mod_cast h
  -- pass to interval integral
  rw [← intervalIntegral.integral_of_le hnm]
  -- |∫ g'·w| ≤ ∫ |g'·w|
  refine le_trans (abs_integral_le_integral_abs hnm) ?_
  -- ∫ |g'·w| ≤ ∫ |g'|
  have hII_w : IntervalIntegrable (fun t => |gPhaseDeriv T t * wFloor t|) volume (n : ℝ) m := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hnm]
    exact (integrableOn_gPhaseDeriv_mul_wFloor T (n := n) (m := m)).abs
  have hII_g : IntervalIntegrable (fun t => |gPhaseDeriv T t|) volume (n : ℝ) m := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hnm]
    rcases le_or_gt (n : ℝ) m with hle | hgt
    · have := continuousOn_gPhaseDeriv T (Nat.cast_nonneg n) (Nat.cast_nonneg m)
      rw [Set.uIcc_of_le hle] at this
      exact (this.abs).integrableOn_compact isCompact_Icc
    · rw [Set.Icc_eq_empty_of_lt hgt]; exact integrableOn_empty
  have hmono : ∫ t in (n:ℝ)..m, |gPhaseDeriv T t * wFloor t|
      ≤ ∫ t in (n:ℝ)..m, |gPhaseDeriv T t| := by
    apply intervalIntegral.integral_mono_on hnm hII_w hII_g
    intro t ht
    have ht0 : 0 ≤ t := le_trans (Nat.cast_nonneg n) ht.1
    rw [abs_mul]
    calc |gPhaseDeriv T t| * |wFloor t|
        ≤ |gPhaseDeriv T t| * 1 :=
          mul_le_mul_of_nonneg_left (abs_wFloor_le_one t ht0) (abs_nonneg _)
      _ = |gPhaseDeriv T t| := mul_one _
  refine le_trans hmono ?_
  exact integral_abs_gPhaseDeriv_le_pi_div_two' T hT (Nat.cast_nonneg n) hnm

/-! ## Part 5 — assembling the Σ-vs-∫ remainder bound

Combining `abel_sum_gPhase` with the bounded-weight identity `g'·(⌊t⌋+1) = g'·w + g'·t`, the
Euler–Maclaurin remainder reconciling the partial sum with the boundary term satisfies a uniform
`≤ π/2` bound, with the `∫ g'·t` integration-by-parts piece exposed. -/

/-- The Abel boundary term splits: `∫ g'·(⌊t⌋+1) = ∫ g'·w + ∫ g'·t`. -/
theorem integral_floor_split (T : ℝ) {n m : ℕ} (h : n ≤ m) :
    ∫ t in Set.Ioc (n : ℝ) m, gPhaseDeriv T t * ((⌊t⌋₊ : ℝ) + 1)
      = (∫ t in Set.Ioc (n : ℝ) m, gPhaseDeriv T t * wFloor t)
        + ∫ t in Set.Ioc (n : ℝ) m, gPhaseDeriv T t * t := by
  have hnm : (n : ℝ) ≤ m := by exact_mod_cast h
  rw [← intervalIntegral.integral_of_le hnm, ← intervalIntegral.integral_of_le hnm,
      ← intervalIntegral.integral_of_le hnm, ← intervalIntegral.integral_add]
  · apply intervalIntegral.integral_congr
    intro t _
    simp only [wFloor]; ring
  · rw [intervalIntegrable_iff_integrableOn_Icc_of_le hnm]
    exact integrableOn_gPhaseDeriv_mul_wFloor T
  · rw [intervalIntegrable_iff_integrableOn_Icc_of_le hnm]
    exact integrableOn_gPhaseDeriv_mul_id T

/-- **THE Σ-vs-∫ EULER–MACLAURIN REMAINDER BOUND (assembled).**
For `T ≥ 0` and `n ≤ m`, with `g = gPhase T`,
`| Σ_{k∈Ioc n m} g(k) − (g(m)(m+1) − g(n)(n+1)) + ∫_{(n,m]} g'(t)·t dt | ≤ π/2`.
The expression in `|·|` equals `−∫_{(n,m]} g'(t)·w(t) dt` (the bounded-weight remainder), so the
bound is the uniform total-variation estimate `∫|g'| ≤ π/2`.  Here `−(∫ g'·t)` together with the
boundary `g(m)(m+1) − g(n)(n+1)` is exactly the integration-by-parts form of the leading integral
`∫ₙ^m g`; what remains uncontrolled to `≤½` is only that closed-form evaluation (still carried by
`ScratchBinetSeries.binetRem_via_series_axiom`). -/
theorem sum_vs_boundary_remainder_bound (T : ℝ) (hT : 0 ≤ T) {n m : ℕ} (h : n ≤ m) :
    |(∑ k ∈ Finset.Ioc n m, gPhase T k)
        - (gPhase T m * ((m : ℝ) + 1) - gPhase T n * ((n : ℝ) + 1))
        + ∫ t in Set.Ioc (n : ℝ) m, gPhaseDeriv T t * t| ≤ π / 2 := by
  have habel := abel_sum_gPhase T h
  have hsplit := integral_floor_split T h
  -- the LHS bracket = −∫ g'·w
  have hrewrite :
      (∑ k ∈ Finset.Ioc n m, gPhase T k)
        - (gPhase T m * ((m : ℝ) + 1) - gPhase T n * ((n : ℝ) + 1))
        + ∫ t in Set.Ioc (n : ℝ) m, gPhaseDeriv T t * t
      = - ∫ t in Set.Ioc (n : ℝ) m, gPhaseDeriv T t * wFloor t := by
    rw [habel, hsplit]; ring
  rw [hrewrite, abs_neg]
  exact euler_maclaurin_remainder_bound T hT h

end ScratchEulerMaclaurin
end BacklundTuring
end OverflowResidueRH

/-! ## Axiom footprint -/

#print axioms
  OverflowResidueRH.BacklundTuring.ScratchEulerMaclaurin.integral_abs_gPhaseDeriv_le_pi_div_two
#print axioms
  OverflowResidueRH.BacklundTuring.ScratchEulerMaclaurin.abel_sum_gPhase
#print axioms
  OverflowResidueRH.BacklundTuring.ScratchEulerMaclaurin.euler_maclaurin_remainder_bound
#print axioms
  OverflowResidueRH.BacklundTuring.ScratchEulerMaclaurin.sum_vs_boundary_remainder_bound
