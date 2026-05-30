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

theorem analyticOrderAt_genus1Factor_self {ρ : ℂ} (hρ : ρ ≠ 0) :
    analyticOrderAt (genus1Factor ρ) ρ = 1 := by
  sorry

theorem analyticOrderAt_genus1Factor_ne {ρ z : ℂ} (hρ : ρ ≠ 0) (hz : z ≠ ρ) :
    analyticOrderAt (genus1Factor ρ) z = 0 := by
  sorry

/-! ## PART 2 (the hard one): order of the infinite product = sum of factor orders.
Investigate Mathlib for `analyticOrderAt` of a locally-uniform `tprod`. The order of a
locally-uniformly-convergent product at `z` should equal the (finite) sum of the factor orders
at `z` — because only finitely many factors vanish at `z` (the locations are discrete), and the
tail product is analytic and nonzero near `z`.

Target (state precisely; you MAY add hypotheses — discreteness of `loc`, `loc i ≠ 0`, the
loc-uniform multipliability, and `Summable (1/‖loc i‖²)` — whatever the proof needs): -/

theorem analyticOrderAt_genus1Product
    {ι : Type*} [DecidableEq ι] (loc : ι → ℂ) (z : ℂ)
    (hne : ∀ i, loc i ≠ 0)
    (hmul : MultipliableLocallyUniformlyOn (fun i s => genus1Factor (loc i) s) Set.univ)
    -- `z` is hit by only finitely many indices (from discreteness):
    (hfin : {i | loc i = z}.Finite) :
    analyticOrderAt (fun s => ∏' i, genus1Factor (loc i) s) z
      = (Nat.card {i | loc i = z} : ℕ∞) := by
  sorry

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
