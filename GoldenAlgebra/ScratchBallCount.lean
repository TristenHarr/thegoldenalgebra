import Mathlib

open Filter

/-!
# Ball-count ⇒ inverse-square summability (G3 abstract engine)

GOAL: a zero family `loc : ι → ℂ` with a Riemann–von Mangoldt ball-counting bound
`#{i : ‖loc i‖ ≤ R} ≤ A·R·log R` and all moduli `≥ 1` has summable inverse-squares.

This is the abstract engine that, specialized to ξ (via B44 `natCard_zeros_le_finsum_divisor`
and B47 `xi_zero_count_bigO`), discharges gap G3 (`Σ 1/‖ρ‖² < ∞`).

STRATEGY: the dyadic-shell lemma `summable_inv_sq_of_shellCard` is ALREADY PROVEN — READ
`/Users/tristen/Desktop/goldenalgebra/GoldenAlgebra/ScratchItem4.lean` and COPY the theorem
`summable_inv_sq_of_shellCard` (and only that theorem) verbatim into THIS file. Then prove the
target below by the ball→shell bridge:
  shell `k` ⊆ ball `2^(k+1)`, so `Nat.card (shell k) ≤ Nat.card {‖loc i‖ ≤ 2^(k+1)}`
  `≤ A·2^(k+1)·log(2^(k+1)) = A·2^(k+1)·(k+1)·log 2 ≤ (2·A·log 2)·(k+1)·2^k`,
giving the `hcard` hypothesis of `summable_inv_sq_of_shellCard` with `C := 2·A·log 2`; the `hfin`
hypothesis follows from `hfin` here (shell ⊆ ball). `Nat.card_mono` needs the bigger set finite.
Useful: `Real.log_rpow`/`Real.log_pow`, `Nat.card_mono`, `Set.Finite.subset`, `Real.rpow_natCast`.

GOAL (fill the sorry; keep the exact conclusion `Summable (fun i => 1 / ‖loc i‖ ^ 2)`):
-/

theorem summable_inv_sq_of_ballCount
    {ι : Type*} (loc : ι → ℂ) (A : ℝ) (hA : 0 ≤ A)
    (hlb : ∀ i, (1 : ℝ) ≤ ‖loc i‖)
    (hfin : ∀ R : ℝ, {i | ‖loc i‖ ≤ R}.Finite)
    (hcount : ∀ R : ℝ, 2 ≤ R → (Nat.card {i | ‖loc i‖ ≤ R} : ℝ) ≤ A * R * Real.log R) :
    Summable (fun i => 1 / ‖loc i‖ ^ 2) := by
  sorry

/-
Build: `cd /Users/tristen/Desktop/goldenalgebra/GoldenAlgebra && lake env lean ScratchBallCount.lean`.
Iterate to EXIT 0, no sorry/admit/axiom, no warnings. You MAY adjust the `hfin`/`hcount` hypothesis
spelling if needed for the proof to go through, as long as they remain derivable from "the number
of points with ‖loc i‖ ≤ R is ≤ A·R·log R" and the conclusion is unchanged. Report the final
signature + which hypotheses (if any) you adjusted. Edit ONLY this file.
-/
