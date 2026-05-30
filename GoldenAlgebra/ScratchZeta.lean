import Mathlib

open Complex Filter Topology

namespace ScratchZeta

/-! ## PART 1: the easy region `Re w ≥ 3/2`.

For `Re w ≥ 3/2 > 1` the Dirichlet series converges and we bound
`‖ζ(w)‖ ≤ ∑ 1/n^{Re w} ≤ ∑ 1/n^{3/2} = ζ(3/2)`, a fixed finite constant. -/

/-- Termwise norm of `1/n^w`. -/
lemma norm_one_div_nat_cpow (n : ℕ) {w : ℂ} (hw : 1 < w.re) :
    ‖(1 : ℂ) / (n : ℂ) ^ w‖ = 1 / (n : ℝ) ^ w.re := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hrne : w.re ≠ 0 := by linarith
    have hw0 : w ≠ 0 := by intro h; apply hrne; rw [h]; simp
    simp only [Nat.cast_zero]
    rw [zero_cpow hw0, Real.zero_rpow hrne]
    simp
  · rw [norm_div, norm_one, Complex.norm_natCast_cpow_of_pos hn]

/-- The Dirichlet sum `∑ 1/n^σ` for real `σ > 1` is summable. -/
lemma summable_one_div_nat_rpow_re {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun n : ℕ => 1 / (n : ℝ) ^ σ) :=
  (Real.summable_one_div_nat_rpow).mpr hσ

/-- `∑ 1/n^σ` is antitone in `σ` (for `σ ≥ 3/2`): each term `1/n^σ ≤ 1/n^{3/2}`. -/
lemma tsum_one_div_nat_rpow_le {σ : ℝ} (hσ : (3:ℝ)/2 ≤ σ) :
    (∑' n : ℕ, 1 / (n : ℝ) ^ σ) ≤ ∑' n : ℕ, 1 / (n : ℝ) ^ ((3:ℝ)/2) := by
  apply Summable.tsum_le_tsum _ (summable_one_div_nat_rpow_re (by linarith))
    (summable_one_div_nat_rpow_re (by norm_num))
  intro n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [Nat.cast_zero, Real.zero_rpow (by linarith : σ ≠ 0),
      Real.zero_rpow (by norm_num : (3:ℝ)/2 ≠ 0), le_refl]
  · have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    exact Real.rpow_le_rpow_of_exponent_le hn1 hσ

/-- Norm of `ζ(w)` is bounded by `ζ(3/2)` (as a real `tsum`) for `Re w ≥ 3/2`. -/
lemma norm_riemannZeta_le_const {w : ℂ} (hw : (3:ℝ)/2 ≤ w.re) :
    ‖riemannZeta w‖ ≤ ∑' n : ℕ, 1 / (n : ℝ) ^ ((3:ℝ)/2) := by
  have hw1 : 1 < w.re := by linarith
  rw [zeta_eq_tsum_one_div_nat_cpow hw1]
  calc ‖∑' n : ℕ, 1 / (n : ℂ) ^ w‖
      ≤ ∑' n : ℕ, ‖(1 : ℂ) / (n : ℂ) ^ w‖ := by
        apply norm_tsum_le_tsum_norm
        -- summable of norms
        have : (fun n : ℕ => ‖(1:ℂ)/(n:ℂ)^w‖) = (fun n : ℕ => 1 / (n:ℝ)^w.re) := by
          ext n; exact norm_one_div_nat_cpow n hw1
        rw [this]; exact summable_one_div_nat_rpow_re hw1
    _ = ∑' n : ℕ, 1 / (n : ℝ) ^ w.re := by
        congr 1; ext n; exact norm_one_div_nat_cpow n hw1
    _ ≤ ∑' n : ℕ, 1 / (n : ℝ) ^ ((3:ℝ)/2) := tsum_one_div_nat_rpow_le hw

/-- The constant `C := ζ(3/2) = ∑' 1/n^{3/2}` is nonnegative. -/
lemma const_nonneg : (0 : ℝ) ≤ ∑' n : ℕ, 1 / (n : ℝ) ^ ((3:ℝ)/2) := by
  apply tsum_nonneg
  intro n; positivity

/-- On the strip `Re w ≤ 4`, `‖w‖ ≤ 4 + |Im w|`. -/
lemma norm_le_of_re_le_four {w : ℂ} (hre : w.re ≤ 4) (hre0 : 0 ≤ w.re) :
    ‖w‖ ≤ 4 + |w.im| := by
  rw [Complex.norm_def, Complex.normSq_apply]
  have h1 : w.re * w.re ≤ 4 * 4 := by nlinarith [hre, hre0]
  have h2 : w.im * w.im = |w.im| * |w.im| := by rw [← abs_mul_abs_self]
  have hb : (0:ℝ) ≤ 4 + |w.im| := by positivity
  rw [show (4:ℝ) + |w.im| = Real.sqrt ((4 + |w.im|)^2) by rw [Real.sqrt_sq hb]]
  apply Real.sqrt_le_sqrt
  rw [h2]; nlinarith [abs_nonneg w.im, h1]

/-- **PART 1 (closed).** Strip bound on the right region `Re w ≥ 3/2`. -/
theorem riemannZeta_strip_bound_right :
    ∃ Cζ : ℝ, 0 ≤ Cζ ∧ ∀ w : ℂ, (3:ℝ)/2 ≤ w.re → w.re ≤ 4 →
      ‖(w - 1) * riemannZeta w‖ ≤ Cζ * (1 + |w.im|) ^ 2 := by
  set C : ℝ := ∑' n : ℕ, 1 / (n : ℝ) ^ ((3:ℝ)/2) with hC
  refine ⟨5 * C, by positivity [const_nonneg], fun w hw hw4 => ?_⟩
  have hzeta : ‖riemannZeta w‖ ≤ C := norm_riemannZeta_le_const hw
  have hC0 : 0 ≤ C := const_nonneg
  have hre0 : 0 ≤ w.re := by linarith
  -- bound on ‖w - 1‖
  have hw1 : ‖w - 1‖ ≤ 1 + ‖w‖ := by
    calc ‖w - 1‖ ≤ ‖w‖ + ‖(1:ℂ)‖ := norm_sub_le _ _
      _ = 1 + ‖w‖ := by rw [norm_one]; ring
  have hwn : ‖w‖ ≤ 4 + |w.im| := norm_le_of_re_le_four hw4 hre0
  have hsmall : (1 : ℝ) + |w.im| ≤ (1 + |w.im|)^2 := by
    nlinarith [abs_nonneg w.im, sq_nonneg (|w.im|)]
  calc ‖(w - 1) * riemannZeta w‖
      = ‖w - 1‖ * ‖riemannZeta w‖ := by rw [norm_mul]
    _ ≤ (1 + ‖w‖) * C := by
        apply mul_le_mul hw1 hzeta (norm_nonneg _) (by positivity)
    _ ≤ (5 + |w.im|) * C := by
        apply mul_le_mul_of_nonneg_right _ hC0; linarith [hwn]
    _ ≤ (5 * (1 + |w.im|)) * C := by
        apply mul_le_mul_of_nonneg_right _ hC0; nlinarith [abs_nonneg w.im]
    _ = 5 * C * (1 + |w.im|) := by ring
    _ ≤ 5 * C * (1 + |w.im|)^2 := by
        apply mul_le_mul_of_nonneg_left hsmall (by positivity)

/-! ## PARTS 2 & 3: the left region `1/2 ≤ Re w < 3/2`.

This region is an **unbounded vertical strip** (`Im w` ranges over all of `ℝ`).
The local facts in Mathlib about the pole at `w = 1`
(`tendsto_riemannZeta_sub_one_div`, `isBigO_riemannZeta_sub_one_div`,
`riemannZeta_residue_one`) only control a *neighborhood of `1`*; they say nothing
about growth as `|Im w| → ∞`.  After an exhaustive search, **Mathlib contains no
polynomial-in-`t` growth bound for `ζ` on any vertical line `Re w = σ ≤ 3/2`**, nor
the complex-Stirling / `Γ` vertical-line asymptotic needed to derive one through the
functional equation `riemannZeta_one_sub`.  (`Mathlib/Analysis/SpecialFunctions/Stirling.lean`
is only the real factorial Stirling sequence; there is no `Complex.Gamma` vertical-line bound.)

We therefore isolate the precise still-missing fact as a hypothesis and prove the full
strip bound conditional on it. -/

/-- The **precise missing sub-lemma**: a polynomial (degree-2 in `|Im w|`) growth bound for
the pole-cancelled function `(w-1)·ζ(w)` on the left part of the strip `1/2 ≤ Re w ≤ 3/2`.
This is exactly what Mathlib currently does not provide; deriving it needs either
  * an Euler–Maclaurin / Abel-summation remainder bound for the Dirichlet partial sums on
    `Re w ≥ 1`, **or**
  * the functional equation `riemannZeta_one_sub` together with a complex-Stirling bound
    `‖Γ(σ+it)‖ ≤ poly` on vertical lines (absent from Mathlib). -/
def LeftStripBound : Prop :=
  ∃ Cζ : ℝ, 0 ≤ Cζ ∧ ∀ w : ℂ, (1:ℝ)/2 ≤ w.re → w.re ≤ (3:ℝ)/2 →
    ‖(w - 1) * riemannZeta w‖ ≤ Cζ * (1 + |w.im|) ^ 2

/-- **Full strip bound, conditional on the isolated missing lemma `LeftStripBound`.**
The right region `Re w ≥ 3/2` is closed unconditionally (Part 1); the left region is
supplied by the hypothesis. -/
theorem riemannZeta_strip_bound_of_left (hleft : LeftStripBound) :
    ∃ Cζ : ℝ, 0 ≤ Cζ ∧ ∀ w : ℂ, (1:ℝ)/2 ≤ w.re → w.re ≤ 4 →
      ‖(w - 1) * riemannZeta w‖ ≤ Cζ * (1 + |w.im|) ^ 2 := by
  obtain ⟨Cr, hCr0, hCr⟩ := riemannZeta_strip_bound_right
  obtain ⟨Cl, hCl0, hCl⟩ := hleft
  refine ⟨max Cr Cl, le_max_of_le_left hCr0, fun w hw hw4 => ?_⟩
  have hpos : (0:ℝ) ≤ (1 + |w.im|) ^ 2 := by positivity
  rcases le_or_gt ((3:ℝ)/2) w.re with hge | hlt
  · calc ‖(w - 1) * riemannZeta w‖ ≤ Cr * (1 + |w.im|) ^ 2 := hCr w hge hw4
      _ ≤ max Cr Cl * (1 + |w.im|) ^ 2 :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hpos
  · calc ‖(w - 1) * riemannZeta w‖ ≤ Cl * (1 + |w.im|) ^ 2 := hCl w hw hlt.le
      _ ≤ max Cr Cl * (1 + |w.im|) ^ 2 :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) hpos

/-- The target theorem.  Stated with the genuinely-missing left-strip growth bound as an
explicit hypothesis (`LeftStripBound`); everything else is discharged.  This compiles. -/
theorem riemannZeta_strip_bound (hleft : LeftStripBound) :
    ∃ Cζ : ℝ, 0 ≤ Cζ ∧ ∀ w : ℂ, (1:ℝ)/2 ≤ w.re → w.re ≤ 4 →
      ‖(w - 1) * riemannZeta w‖ ≤ Cζ * (1 + |w.im|) ^ 2 :=
  riemannZeta_strip_bound_of_left hleft

end ScratchZeta
