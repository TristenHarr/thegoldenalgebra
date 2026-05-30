import Mathlib

open Complex Filter Topology

/-!
# Genus-1 product: zero orders (G5 multiplicity matching — the hard structural piece)

`genus1Factor ρ s := (1 - s/ρ) * exp(s/ρ)` has a SIMPLE zero at `ρ` and no other zeros.
The Hadamard factorization needs: the order of the infinite product at any `z` equals the number
of indices hitting `z` — so that `analyticOrderAt ξ z = analyticOrderAt (∏) z` and the quotient
`Q = ξ/∏` is entire (B45 `entire_quotient_of_analyticOrderAt_eq`).

Prove the pieces below, EASIEST FIRST. Build after each:
`cd /Users/tristen/Desktop/goldenalgebra/GoldenAlgebra && lake env lean ScratchOrder.lean`.
-/

noncomputable def genus1Factor (ρ s : ℂ) : ℂ := (1 - s / ρ) * Complex.exp (s / ρ)

/-! ## PART 1 (tractable): the order of a single genus-1 factor.
`genus1Factor ρ` is entire, vanishes only at `ρ`, to order exactly 1. -/

/-- `genus1Factor ρ` is analytic everywhere. -/
theorem analyticAt_genus1Factor (ρ : ℂ) (z : ℂ) : AnalyticAt ℂ (genus1Factor ρ) z := by
  unfold genus1Factor
  fun_prop

/-- The cofactor `g s = -(1/ρ) * exp (s/ρ)` extracted from `genus1Factor ρ`, so that
`genus1Factor ρ s = (s - ρ) ^ 1 • g s`. -/
theorem analyticOrderAt_genus1Factor_self {ρ : ℂ} (hρ : ρ ≠ 0) :
    analyticOrderAt (genus1Factor ρ) ρ = 1 := by
  rw [show (1 : ℕ∞) = ((1 : ℕ) : ℕ∞) from rfl,
    (analyticAt_genus1Factor ρ ρ).analyticOrderAt_eq_natCast]
  refine ⟨fun s => -(1 / ρ) * Complex.exp (s / ρ), by fun_prop, ?_, ?_⟩
  · exact mul_ne_zero (neg_ne_zero.mpr (div_ne_zero one_ne_zero hρ)) (Complex.exp_ne_zero _)
  · filter_upwards with s
    unfold genus1Factor
    rw [pow_one, smul_eq_mul]
    field_simp
    ring

theorem analyticOrderAt_genus1Factor_ne {ρ z : ℂ} (hρ : ρ ≠ 0) (hz : z ≠ ρ) :
    analyticOrderAt (genus1Factor ρ) z = 0 := by
  rw [(analyticAt_genus1Factor ρ z).analyticOrderAt_eq_zero]
  unfold genus1Factor
  refine mul_ne_zero ?_ (Complex.exp_ne_zero _)
  rw [sub_ne_zero, ne_comm, ne_eq, div_eq_one_iff_eq hρ]
  exact hz

/-! ## PART 2 (the hard one): order of the infinite product = sum of factor orders.
Investigate Mathlib for `analyticOrderAt` of a locally-uniform `tprod`. The order of a
locally-uniformly-convergent product at `z` should equal the (finite) sum of the factor orders
at `z` — because only finitely many factors vanish at `z` (the locations are discrete), and the
tail product is analytic and nonzero near `z`.

Target (state precisely; you MAY add hypotheses — discreteness of `loc`, `loc i ≠ 0`, the
loc-uniform multipliability, and `Summable (1/‖loc i‖²)` — whatever the proof needs): -/

/-- Order of a finite product of analytic functions is the sum of the orders. -/
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

theorem analyticOrderAt_genus1Product
    {ι : Type*} [DecidableEq ι] (loc : ι → ℂ) (z : ℂ)
    (hne : ∀ i, loc i ≠ 0)
    (hmul : MultipliableLocallyUniformlyOn (fun i s => genus1Factor (loc i) s) Set.univ)
    -- `z` is hit by only finitely many indices (from discreteness):
    (hfin : {i | loc i = z}.Finite)
    -- The tail (over indices that do NOT hit `z`) is analytic at `z` and does not vanish there.
    -- This is the genuine analytic-number-theory input (locally-uniform-product order theory):
    -- it is the precise piece Mathlib lacks an order-of-`tprod` lemma for.
    (htail_an : AnalyticAt ℂ
      (fun s => ∏' i : {i // i ∉ hfin.toFinset}, genus1Factor (loc i) s) z)
    (htail_ne :
      (∏' i : {i // i ∉ hfin.toFinset}, genus1Factor (loc i) z) ≠ 0) :
    analyticOrderAt (fun s => ∏' i, genus1Factor (loc i) s) z
      = (Nat.card {i | loc i = z} : ℕ∞) := by
  classical
  let F : ι → ℂ → ℂ := fun i s => genus1Factor (loc i) s
  let Hfin : Finset ι := hfin.toFinset
  let tail : ℂ → ℂ := fun s => ∏' i : {i // i ∉ Hfin}, F i s
  -- pointwise multipliability of the family
  have hmult : ∀ s : ℂ, Multipliable (fun i => F i s) := fun s =>
    hmul.multipliable (Set.mem_univ s)
  -- split the product as (finite hitting product) * (tail) at every point
  have hsplit : ∀ s : ℂ, (∏' i, F i s) = (∏ i ∈ Hfin, F i s) * tail s := fun s =>
    ((hmult s).prod_mul_tprod_subtype_compl Hfin).symm
  -- order of the product = order of finite product + order of tail
  have horder : analyticOrderAt (fun s => ∏' i, F i s) z
      = analyticOrderAt (fun s => (∏ i ∈ Hfin, F i s) * tail s) z :=
    analyticOrderAt_congr (Filter.Eventually.of_forall hsplit)
  rw [horder]
  have hAfin : AnalyticAt ℂ (fun s => ∏ i ∈ Hfin, F i s) z := by
    have := Finset.analyticAt_prod (𝕜 := ℂ) (f := F) Hfin
      (fun i _ => analyticAt_genus1Factor (loc i) z)
    rw [Finset.prod_fn] at this; exact this
  rw [analyticOrderAt_mul hAfin htail_an]
  -- tail order is 0 (nonvanishing at z)
  have htail0 : analyticOrderAt tail z = 0 := by
    rw [htail_an.analyticOrderAt_eq_zero]; exact htail_ne
  rw [htail0, add_zero]
  -- finite product order = sum of (order-1) factors = card
  rw [analyticOrderAt_finsetProd Hfin F z (fun i _ => analyticAt_genus1Factor (loc i) z)]
  have hmemz : ∀ i ∈ Hfin, loc i = z := fun i hi => (hfin.mem_toFinset.mp hi)
  have hsum : ∑ i ∈ Hfin, analyticOrderAt (F i) z = ∑ _i ∈ Hfin, (1 : ℕ∞) := by
    apply Finset.sum_congr rfl
    intro i hi
    have hlocz : loc i = z := hmemz i hi
    show analyticOrderAt (genus1Factor (loc i)) z = 1
    rw [hlocz]
    exact analyticOrderAt_genus1Factor_self (hlocz ▸ hne i)
  rw [hsum]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
  -- card of the finite set = card of the finset
  rw [Nat.card_eq_card_finite_toFinset hfin]

/-!
## INVESTIGATION POINTERS (search Mathlib HARD before declaring absent):
* `analyticOrderAt`, `AnalyticAt.analyticOrderAt_eq`, the local factorization
  `f =ᶠ (· - z₀)^n • g, g z₀ ≠ 0` (`Mathlib/Analysis/Analytic/Order.lean`).
* `analyticOrderAt_mul` / order of a product (`analyticOrderAt (f*g) = analyticOrderAt f + analyticOrderAt g`).
* Splitting `∏' i, F i = (∏ i ∈ finset of hitting indices, F i) * (∏' i ∈ rest, F i)`:
  `tprod_eq_prod_mul_tprod`/`Multipliable.tprod_eq_mulIndicator…`, `Finset.mul_prod_…`, and that the
  tail product is analytic and NONZERO at `z` (each tail factor nonzero at `z`, loc-unif ⇒ analytic).
* For Part 1: `genus1Factor ρ s - 0 = (1 - s/ρ)·exp(s/ρ)`; at `s = ρ`, `(1 - s/ρ)` has a simple
  zero and `exp ≠ 0`. Use `analyticOrderAt_eq_natCast`/the `(· - ρ)^1 • g` form with
  `g s = exp(s/ρ) * (-1/ρ)·((s-ρ)/(s-ρ))`… more cleanly: `genus1Factor ρ s = (-(1/ρ))·(s - ρ)·exp(s/ρ)`
  since `1 - s/ρ = -(1/ρ)(s - ρ)`. So `genus1Factor ρ = (· - ρ)^1 • g` with `g s = -(1/ρ)·exp(s/ρ)`,
  `g ρ = -(1/ρ)·exp 1 ≠ 0`. That directly gives order 1 via `AnalyticAt.analyticOrderAt_eq` /
  `analyticOrderAt_eq_natCast`-style lemmas.

## ALGORITHM (follow strictly):
0. (Branch already created by the orchestrator — work only in THIS file.)
1. Read this file and the pointers.
2. Search Mathlib for the order-of-product lemma BEFORE attempting Part 2 from scratch.
3. Prove Part 1 fully (it is self-contained and should close).
4. For Part 2: prove it, OR if a Mathlib "order of loc-unif product" lemma is genuinely absent,
   prove the FINITE-product analogue + the tail-nonvanishing, isolate the exact missing infinite-
   product-order lemma as a precise hypothesis, and prove Part 2 conditional on it (COMPILING, no sorry).
5. Verify: EXIT 0, no sorry/admit/axiom, no linter warnings; `#print axioms <thm>` shows only
   `[propext, Classical.choice, Quot.sound]`.
6. Report: final signatures, exact Mathlib lemmas used, hypotheses added, and any isolated gap.
Edit ONLY this file.
-/
