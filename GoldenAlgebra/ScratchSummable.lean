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
  -- Extract the growth constant `A` from the unconditional zero count.
  obtain ⟨A, hA0, hA⟩ := xi_zero_count_bigO
  -- Final dominating constant.
  set C : ℝ :=
    A * Real.exp 1 / Real.log 2 + A * Real.exp 1
      + |Real.log ‖entireRiemannXi 0‖| / Real.log 2 + 1 with hC
  -- Map a small-norm zero index into the compact-intersection finite set.
  -- (`closedBall 0 R ∩ riemannXiZeros`).
  have hfin : ∀ R : ℝ, {ρ : XiZeroIndex | ‖xiZeroLoc ρ‖ ≤ R}.Finite := by
    intro R
    -- The finite set we inject into.
    have hcpt : (Metric.closedBall (0 : ℂ) R ∩ riemannXiZeros).Finite :=
      isCompact_inter_riemannXiZeros_finite (isCompact_closedBall 0 R)
    -- The image of our set under `Subtype.val` lands in that finite set.
    apply Set.Finite.of_finite_image (f := (Subtype.val : XiZeroIndex → ℂ))
    · apply hcpt.subset
      rintro z ⟨ρ, hρ, rfl⟩
      refine ⟨?_, ?_⟩
      · -- z = ↑ρ ∈ closedBall 0 R
        simp only [Metric.mem_closedBall, dist_zero_right]
        simpa [xiZeroLoc] using hρ
      · exact ρ.2
    · -- `Subtype.val` is injective, hence injective on any set.
      exact Subtype.val_injective.injOn
  -- The counting bound.
  have hcount : ∀ R : ℝ, 2 ≤ R →
      (Nat.card {ρ : XiZeroIndex | ‖xiZeroLoc ρ‖ ≤ R} : ℝ) ≤ C * R * Real.log R := by
    intro R hR
    -- Target subtype of zeros in the ball; it is finite.
    have hballfin : (Metric.closedBall (0 : ℂ) R ∩ riemannXiZeros).Finite :=
      isCompact_inter_riemannXiZeros_finite (isCompact_closedBall 0 R)
    have : Finite {z : ℂ // entireRiemannXi z = 0 ∧ z ∈ Metric.closedBall (0 : ℂ) R} := by
      have hsub : {z : ℂ | entireRiemannXi z = 0 ∧ z ∈ Metric.closedBall (0 : ℂ) R}
          ⊆ Metric.closedBall (0 : ℂ) R ∩ riemannXiZeros := by
        rintro z ⟨hz0, hzb⟩
        exact ⟨hzb, by simpa [riemannXiZeros] using hz0⟩
      exact (hballfin.subset hsub).to_subtype
    -- Inject small-norm indices into the ball-zero subtype.
    have hcard_le :
        Nat.card {ρ : XiZeroIndex | ‖xiZeroLoc ρ‖ ≤ R}
          ≤ Nat.card {z : ℂ // entireRiemannXi z = 0 ∧ z ∈ Metric.closedBall (0 : ℂ) R} := by
      refine Nat.card_le_card_of_injective
        (fun ρ => ⟨(ρ.1 : ℂ), ?_, ?_⟩) ?_
      · -- ξ (↑ρ) = 0
        exact (mem_riemannXiZeros).1 ρ.1.2
      · -- ↑ρ ∈ closedBall 0 R
        have hρ2 : ‖xiZeroLoc ρ.1‖ ≤ R := ρ.2
        simp only [Metric.mem_closedBall, dist_zero_right]
        simpa [xiZeroLoc] using hρ2
      · -- injectivity
        rintro ⟨⟨ρ, hρmem⟩, hρ⟩ ⟨⟨σ, hσmem⟩, hσ⟩ h
        simp only [Subtype.mk.injEq] at h
        exact Subtype.ext (Subtype.ext h)
    -- Cast to ℝ and chain through divisor / RvM bounds.
    have hcard_leR :
        (Nat.card {ρ : XiZeroIndex | ‖xiZeroLoc ρ‖ ≤ R} : ℝ)
          ≤ (Nat.card {z : ℂ // entireRiemannXi z = 0 ∧ z ∈ Metric.closedBall (0 : ℂ) R} : ℝ) := by
      exact_mod_cast hcard_le
    have hdiv :
        (Nat.card {z : ℂ // entireRiemannXi z = 0 ∧ z ∈ Metric.closedBall (0 : ℂ) R} : ℝ)
          ≤ ∑ᶠ u, MeromorphicOn.divisor entireRiemannXi (Metric.closedBall (0 : ℂ) R) u :=
      natCard_zeros_le_finsum_divisor analyticOnNhd_entireRiemannXi
        ⟨0, entireRiemannXi_zero_ne⟩ (by linarith)
    have hrvm := hA R hR
    -- Now the arithmetic: A·(eR)·log(eR) − log‖ξ0‖ ≤ C·R·log R.
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
    -- `-log‖ξ0‖ ≤ |log‖ξ0‖|`
    have hcabs : -Real.log ‖entireRiemannXi 0‖ ≤ |Real.log ‖entireRiemannXi 0‖| :=
      neg_le_abs _
    -- `A·e·R ≤ (A·e/log2)·R·logR`  (since logR ≥ log2 > 0)
    have hterm1 : A * Real.exp 1 * R ≤ (A * Real.exp 1 / Real.log 2) * R * Real.log R := by
      have key : (A * Real.exp 1 / Real.log 2) * R * Real.log R
          = (A * Real.exp 1 * R) * (Real.log R / Real.log 2) := by
        field_simp
      rw [key]
      have hge1 : (1 : ℝ) ≤ Real.log R / Real.log 2 := by
        rw [le_div_iff₀ hlog2pos]; linarith
      nlinarith [hge1, mul_nonneg (mul_nonneg hA0 hexp1pos.le) hRpos.le]
    -- `|log‖ξ0‖| ≤ (|log‖ξ0‖|/log2)·R·logR`  (since R·logR ≥ log2)
    have hterm2 : |Real.log ‖entireRiemannXi 0‖|
        ≤ (|Real.log ‖entireRiemannXi 0‖| / Real.log 2) * R * Real.log R := by
      have key : (|Real.log ‖entireRiemannXi 0‖| / Real.log 2) * R * Real.log R
          = |Real.log ‖entireRiemannXi 0‖| * (R * Real.log R / Real.log 2) := by
        field_simp
      rw [key]
      have hge1 : (1 : ℝ) ≤ R * Real.log R / Real.log 2 := by
        rw [le_div_iff₀ hlog2pos]; linarith
      nlinarith [hge1, abs_nonneg (Real.log ‖entireRiemannXi 0‖)]
    -- Assemble.
    calc
      (Nat.card {ρ : XiZeroIndex | ‖xiZeroLoc ρ‖ ≤ R} : ℝ)
          ≤ A * (Real.exp 1 * R) * Real.log (Real.exp 1 * R)
              - Real.log ‖entireRiemannXi 0‖ :=
            le_trans hcard_leR (le_trans hdiv hrvm)
      _ = A * Real.exp 1 * R * (1 + Real.log R) - Real.log ‖entireRiemannXi 0‖ := by
            rw [hlog]; ring
      _ ≤ C * R * Real.log R := by
            rw [hC]
            have hRlogRnn : 0 ≤ R * Real.log R := by positivity
            nlinarith [hterm1, hterm2, hcabs, hRlogRnn]
  exact summable_inv_sq_of_ballCount' xiZeroLoc C xiZeroLoc_ne_zero hfin hcount

/-
Build: `cd /Users/tristen/Desktop/goldenalgebra/GoldenAlgebra && lake env lean ScratchSummable.lean`.
Report the final compiling proof. Edit ONLY this file.
-/
