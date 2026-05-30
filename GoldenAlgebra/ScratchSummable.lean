import Mathlib

open Complex Filter Topology

/-!
# ξ inverse-square summability (G3 closure) — proof against axiomatized upstream lemmas

GOAL: `xi_zero_invSq_summable` (bottom). The upstream facts it needs are ALREADY PROVEN in the
main development; here they are `axiom`s with the EXACT same names/signatures, so your finished
proof transplants verbatim into the main file (where they are real theorems). DO NOT prove the
axioms; USE them. Your only job: fill the final `sorry`.

ALGORITHM: read this file; search Mathlib for the subtype/`Nat.card`/`Set.Finite` glue you need
(`Nat.card_le_card_of_injective`, `Set.Finite.preimage`, `Set.Finite.subset`, `Set.Finite.to_subtype`,
`Metric.mem_closedBall`, `dist_zero_right`, `Real.log_mul`, `Real.log_exp`); prove the two
obligations (`hfin`, `hcount`) of `summable_inv_sq_of_ballCount'`, then close. NO `sorry` in the
final theorem; if blocked isolate the gap as a hypothesis. Verify EXIT 0 + no warnings +
`#print axioms` (it WILL list the axioms below — that's expected; just confirm no `sorryAx`).
-/

-- ## Real definitions (identical to the main file) --
noncomputable def entireRiemannXi (s : ℂ) : ℂ :=
  (1 / 2) * (s * (s - 1) * completedRiemannZeta₀ s + 1)

def riemannXiZeros : Set ℂ := entireRiemannXi ⁻¹' {0}

abbrev XiZeroIndex : Type := riemannXiZeros

def xiZeroLoc (ρ : XiZeroIndex) : ℂ := (ρ : ℂ)

-- ## Upstream lemmas (PROVEN elsewhere; axiomatized here with exact signatures) --
@[simp] axiom mem_riemannXiZeros {z : ℂ} : z ∈ riemannXiZeros ↔ entireRiemannXi z = 0
axiom xiZeroLoc_ne_zero (ρ : XiZeroIndex) : xiZeroLoc ρ ≠ 0
axiom analyticOnNhd_entireRiemannXi : AnalyticOnNhd ℂ entireRiemannXi Set.univ
axiom entireRiemannXi_zero_ne : entireRiemannXi 0 ≠ 0
axiom isCompact_inter_riemannXiZeros_finite {S : Set ℂ} (hS : IsCompact S) :
    (S ∩ riemannXiZeros).Finite

/-- B44: zero-count ≤ divisor finsum. -/
axiom natCard_zeros_le_finsum_divisor
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f Set.univ) (hf0 : ∃ z₀, f z₀ ≠ 0) {r : ℝ} (_hr : 0 ≤ r) :
    (Nat.card {z : ℂ // f z = 0 ∧ z ∈ Metric.closedBall (0 : ℂ) r} : ℝ)
      ≤ ∑ᶠ u, MeromorphicOn.divisor f (Metric.closedBall (0 : ℂ) r) u

/-- B47: unconditional RvM zero count. -/
axiom xi_zero_count_bigO :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ r : ℝ, 2 ≤ r →
      ∑ᶠ u, MeromorphicOn.divisor entireRiemannXi (Metric.closedBall (0 : ℂ) r) u
        ≤ A * (Real.exp 1 * r) * Real.log (Real.exp 1 * r) - Real.log ‖entireRiemannXi 0‖

/-- B48': ball-count ⇒ inverse-square summability (hlb-free). -/
axiom summable_inv_sq_of_ballCount'
    {ι : Type*} (loc : ι → ℂ) (A : ℝ)
    (_hne : ∀ i, loc i ≠ 0)
    (hfin : ∀ R : ℝ, {i | ‖loc i‖ ≤ R}.Finite)
    (hcount : ∀ R : ℝ, 2 ≤ R → (Nat.card {i | ‖loc i‖ ≤ R} : ℝ) ≤ A * R * Real.log R) :
    Summable (fun i => 1 / ‖loc i‖ ^ 2)

/-! ## GOAL: fill this `sorry`.
Apply `summable_inv_sq_of_ballCount' xiZeroLoc C xiZeroLoc_ne_zero hfin hcount`.
- `hfin R`: `{ρ : XiZeroIndex | ‖xiZeroLoc ρ‖ ≤ R}` is finite — it injects (via `Subtype.val`) into
  the finite set `Metric.closedBall 0 R ∩ riemannXiZeros` (`isCompact_inter_riemannXiZeros_finite`).
- `hcount R (hR : 2 ≤ R)`: `Nat.card {ρ | ‖xiZeroLoc ρ‖ ≤ R}` injects into
  `{z // ξ z = 0 ∧ z ∈ closedBall 0 R}` (so `Nat.card ≤` that, target finite via the same compact set),
  then `≤ ∑ᶠ divisor` (`natCard_zeros_le_finsum_divisor` with `analyticOnNhd_entireRiemannXi`,
  `⟨0, entireRiemannXi_zero_ne⟩`), then `≤ A·(e R)·log(e R) − log‖ξ0‖` (`xi_zero_count_bigO`).
  Finally dominate `A·(e R)·log(e R) − log‖ξ0‖ ≤ C·R·log R` for `R ≥ 2`: expand
  `log(e R) = 1 + log R` (`Real.log_mul (exp_pos) hR.pos`, `Real.log_exp`); then `e R = e R`,
  `e R ≤ (e/log2)·R·log R` and `−log‖ξ0‖ ≤ R·log R` (both since `log R ≥ log 2 > 0` for `R ≥ 2`),
  giving `C := A·e/Real.log 2 + A·e + 1` (or any explicit constant). Pick `C` and discharge with
  `nlinarith` + a few `have`s.
Choose the existential `A`/`C` from `xi_zero_count_bigO`. -/

theorem xi_zero_invSq_summable :
    Summable (fun ρ : XiZeroIndex => 1 / ‖xiZeroLoc ρ‖ ^ 2) := by
  sorry

/-
Build: `cd /Users/tristen/Desktop/goldenalgebra/GoldenAlgebra && lake env lean ScratchSummable.lean`.
Report the final compiling proof. Edit ONLY this file.
-/
