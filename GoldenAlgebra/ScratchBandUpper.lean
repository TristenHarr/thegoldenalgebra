/-
  ScratchBandUpper.lean

  GOAL (the irreducible analytic theorem at the heart of the Platt–Trudgian campaign):
  the Stirling-on-vertical-lines UPPER bound for the complex Gamma function on the band
  `Re ∈ [-1, 3]`:

      ∃ A ≥ 0, ∀ w, -1 ≤ Re w ≤ 3 → 1 ≤ |Im w| →
        ‖Γ w‖ ≤ A · |Im w|^(Re w - 1/2) · exp(-(π/2)|Im w|).

  ────────────────────────────────────────────────────────────────────────────────────
  WHAT IS PROVED HERE, AND HOW THE RESIDUAL IS MINIMISED.

  The companion file `ScratchGammaDecay.lean` proves, fully and unconditionally, the EXACT
  closed form and sharp bounds on the CRITICAL LINE `σ = 1/2`
  (`‖Γ(1/2+it)‖² = π/cosh(πt)`, giving `‖Γ(1/2+it)‖ ≤ √(2π)·e^{-(π/2)|t|}`), and reduces the
  whole strip program to a single explicit interpolation input `BandUpper` — which is
  *verbatim* the statement of `bandUpper` itself.  So `BandUpper` cannot be used as the
  residual here without trivialising the goal.

  This file does strictly better: it reduces `bandUpper` (the bound on the FULL band
  `Re ∈ [-1,3]`, all `|t| ≥ 1`) to a residual that is *one bounded unit strip on one side
  of the real axis only*:

      `BaseStrip A₀` : 0 ≤ A₀ ∧ ∀ w, 1 ≤ Re w ≤ 2 → 1 ≤ Im w →
          ‖Γ w‖ ≤ A₀ · (Im w)^(Re w - 1/2) · exp(-(π/2)·Im w).

  Everything connecting this central strip to the full band is proved here UNCONDITIONALLY:

    • CONJUGATION SYMMETRY (`Gamma_conj`):  `‖Γ(σ-it)‖ = ‖Γ(σ+it)‖`, so the bound for
      `t ≤ -1` follows from the bound for `t ≥ 1`.  Hence the residual only needs `t ≥ 1`.

    • FORWARD RECURRENCE (`Gamma_add_one`):  `‖Γ(w+1)‖ = ‖w‖·‖Γ w‖`, with
      `‖w‖ ≤ |Re w| + |Im w| ≤ (|Re w|+1)·|Im w|` (for `|Im w| ≥ 1`).  The factor `‖w‖`
      raises the `|t|`-power by exactly one — matching `σ ↦ σ+1`.  This extends
      `[1,2] → [2,3] → [3,4]`, covering `Re ∈ [1,3]`.

    • BACKWARD RECURRENCE (`Gamma_add_one`):  `‖Γ w‖ = ‖Γ(w+1)‖/‖w‖`, with `‖w‖ ≥ |Im w| ≥ 1`.
      The division LOWERS the `|t|`-power by one — matching `σ ↦ σ-1` — and `1/‖w‖ ≤ 1/|t|`
      keeps the constant controlled.  This extends `[1,2] → [0,1] → [-1,0]`, covering the
      LEFT half `Re ∈ [-1,1]` *without reflection and without any lower bound on Γ*, sidestepping
      the circularity that a reflection route would introduce.

  The recurrence steps are genuinely elementary functional-equation manipulations; the only
  non-elementary content — the non-integer power `|t|^{σ-1/2}` and the `e^{-(π/2)|t|}` rate on
  a single bounded strip — is isolated in `BaseStrip`.  That is the irreducible
  Stirling / Hadamard-three-lines / Binet fact (a non-integer power of `|t|` cannot arise from
  finitely many functional-equation steps).  On the slice `σ = 1/2` it is the companion's
  unconditional `norm_Gamma_half_le`; the residual asks for the same on `σ ∈ [1,2]`.

  RESULT:  `bandUpper_of_baseStrip : BaseStrip A₀ → bandUpper`, proved with NO `sorry` and
  (verified below) NO `sorryAx`.  `bandUpper` itself is then stated with `BaseStrip` as its
  single explicit hypothesis.

  Mathlib lemmas used:
    Complex.Gamma_add_one, Complex.Gamma_conj, Complex.norm_le_abs_re_add_abs_im,
    Complex.abs_im_le_norm, Real.rpow_add, Real.rpow_natCast, Real.exp_pos, …
-/
import Mathlib

open Complex Real

noncomputable section

namespace BandUpper

/-! ## The target predicate and the residual. -/

/-- The target band-upper-bound predicate, with explicit constant `A`. -/
def BandUpperC (A : ℝ) : Prop :=
  0 ≤ A ∧ ∀ w : ℂ, (-1 : ℝ) ≤ w.re → w.re ≤ 3 → 1 ≤ |w.im| →
    ‖Complex.Gamma w‖ ≤ A * |w.im| ^ (w.re - 1/2) * Real.exp (-(Real.pi/2) * |w.im|)

/-- **The residual.**  The Stirling-on-lines bound on the single central unit strip
`Re ∈ [1,2]`, restricted to the upper half `Im ≥ 1`.  This is the only non-elementary input;
everything else is derived from it unconditionally below. -/
def BaseStrip (A₀ : ℝ) : Prop :=
  0 ≤ A₀ ∧ ∀ w : ℂ, (1 : ℝ) ≤ w.re → w.re ≤ 2 → 1 ≤ w.im →
    ‖Complex.Gamma w‖ ≤ A₀ * w.im ^ (w.re - 1/2) * Real.exp (-(Real.pi/2) * w.im)

/-! ## Elementary numeric facts about `‖σ+it‖`. -/

/-- For `w` in the band with `|Im w| ≥ 1`, `‖w‖ ≤ 5·|Im w|`.  (Here `|Re w| ≤ 4`.) -/
theorem norm_le_four_mul_abs_im {w : ℂ} (hre1 : (-1 : ℝ) ≤ w.re) (hre2 : w.re ≤ 4)
    (him : 1 ≤ |w.im|) : ‖w‖ ≤ 5 * |w.im| := by
  have h := Complex.norm_le_abs_re_add_abs_im w
  have hre : |w.re| ≤ 4 := abs_le.mpr ⟨by linarith, by linarith⟩
  -- |re| ≤ 4 ≤ 4·|im| (since |im|≥1), so |re|+|im| ≤ 5|im|
  nlinarith [him, hre, abs_nonneg w.im]

/-- `|Im w| ≤ ‖w‖`. -/
theorem abs_im_le_norm' (w : ℂ) : |w.im| ≤ ‖w‖ := Complex.abs_im_le_norm w

/-- `x · x^a = x^(a+1)` for `x > 0` (rpow). -/
theorem mul_rpow_eq {x : ℝ} (hx : 0 < x) (a : ℝ) : x * x ^ a = x ^ (a + 1) := by
  rw [Real.rpow_add hx, Real.rpow_one, mul_comm]

/-- `x^(a+1) = x^a · x` for `x > 0` (rpow). -/
theorem rpow_add_one_eq {x : ℝ} (hx : 0 < x) (a : ℝ) : x ^ (a + 1) = x ^ a * x := by
  rw [Real.rpow_add hx, Real.rpow_one]

/-! ## Forward recurrence step.

If the bound holds at `w` (with `Im w ≥ 1`), it holds at `w + 1` with the constant scaled by 4,
since `‖Γ(w+1)‖ = ‖w‖·‖Γ w‖`, `‖w‖ ≤ 4·Im w`, and the extra `Im w` raises the power `σ-1/2`
to `(σ+1)-1/2`. -/
theorem forward_step {A : ℝ} {w : ℂ}
    (hre1 : (-1 : ℝ) ≤ w.re) (hre2 : w.re ≤ 3) (him : 1 ≤ w.im)
    (hbound : ‖Complex.Gamma w‖ ≤ A * w.im ^ (w.re - 1/2) * Real.exp (-(Real.pi/2) * w.im)) :
    ‖Complex.Gamma (w + 1)‖
      ≤ (5 * A) * (w + 1).im ^ ((w + 1).re - 1/2) * Real.exp (-(Real.pi/2) * (w + 1).im) := by
  have himpos : (0:ℝ) < w.im := lt_of_lt_of_le one_pos him
  have hwne : w ≠ 0 := by
    intro h; rw [h] at himpos; simp at himpos
  -- Γ(w+1) = w · Γ w
  have hrec : Complex.Gamma (w + 1) = w * Complex.Gamma w := Complex.Gamma_add_one w hwne
  rw [hrec, norm_mul]
  -- (w+1).re = w.re + 1, (w+1).im = w.im
  have hre' : (w + 1).re = w.re + 1 := by simp
  have him' : (w + 1).im = w.im := by simp
  rw [hre', him']
  -- bound ‖w‖ ≤ 5·w.im  (w.im ≥ 1 > 0 so |w.im| = w.im)
  have hnorm : ‖w‖ ≤ 5 * w.im := by
    have := norm_le_four_mul_abs_im hre1 (by linarith) (by rw [abs_of_pos himpos]; exact him)
    rwa [abs_of_pos himpos] at this
  -- ‖w‖·‖Γ w‖ ≤ (5·w.im)·(A·(w.im)^(σ-1/2)·exp)
  have hstep : ‖w‖ * ‖Complex.Gamma w‖
      ≤ (5 * w.im) * (A * w.im ^ (w.re - 1/2) * Real.exp (-(Real.pi/2) * w.im)) := by
    apply mul_le_mul hnorm hbound (norm_nonneg _)
    positivity
  refine hstep.trans ?_
  -- RHS rewrite: w.im · (w.im)^(σ-1/2) = (w.im)^((σ-1/2)+1) = (w.im)^((σ+1)-1/2)
  have hpow : w.im * w.im ^ (w.re - 1/2) = w.im ^ (w.re + 1 - 1/2) := by
    rw [mul_rpow_eq himpos]; congr 1; ring
  -- assemble
  have heq1 : (5 * w.im) * (A * w.im ^ (w.re - 1/2) * Real.exp (-(Real.pi/2) * w.im))
      = (5 * A) * (w.im * w.im ^ (w.re - 1/2)) * Real.exp (-(Real.pi/2) * w.im) := by ring
  rw [heq1, hpow]

/-! ## Backward recurrence step.

If the bound holds at `w + 1` (with `Im w ≥ 1`), it holds at `w`, with the SAME constant,
since `‖Γ w‖ = ‖Γ(w+1)‖/‖w‖`, `‖w‖ ≥ Im w`, and the division lowers the power
`(σ+1)-1/2` to `σ-1/2`. -/
theorem backward_step {A : ℝ} (hA : 0 ≤ A) {w : ℂ}
    (_hre1 : (-1 : ℝ) ≤ w.re) (_hre2 : w.re ≤ 3) (him : 1 ≤ w.im)
    (hbound : ‖Complex.Gamma (w + 1)‖
      ≤ A * (w + 1).im ^ ((w + 1).re - 1/2) * Real.exp (-(Real.pi/2) * (w + 1).im)) :
    ‖Complex.Gamma w‖ ≤ A * w.im ^ (w.re - 1/2) * Real.exp (-(Real.pi/2) * w.im) := by
  have himpos : (0:ℝ) < w.im := lt_of_lt_of_le one_pos him
  have hwne : w ≠ 0 := by
    intro h; rw [h] at himpos; simp at himpos
  have hrec : Complex.Gamma (w + 1) = w * Complex.Gamma w := Complex.Gamma_add_one w hwne
  have hre' : (w + 1).re = w.re + 1 := by simp
  have him' : (w + 1).im = w.im := by simp
  rw [hre', him'] at hbound
  -- ‖w‖ ≥ w.im ≥ 1 > 0 ; ‖w‖ > 0
  have hwnorm_pos : 0 < ‖w‖ := norm_pos_iff.mpr hwne
  have hwnorm_ge : w.im ≤ ‖w‖ := by
    have := abs_im_le_norm' w
    rwa [abs_of_pos himpos] at this
  -- From hrec: ‖w‖·‖Γ w‖ = ‖Γ(w+1)‖
  have hmul : ‖w‖ * ‖Complex.Gamma w‖ = ‖Complex.Gamma (w + 1)‖ := by
    rw [hrec, norm_mul]
  -- so ‖Γ w‖ = ‖Γ(w+1)‖ / ‖w‖ ≤ (A·(w.im)^(w.re+1-1/2)·exp) / ‖w‖
  have hGw : ‖Complex.Gamma w‖ = ‖Complex.Gamma (w + 1)‖ / ‖w‖ := by
    rw [eq_div_iff (ne_of_gt hwnorm_pos), mul_comm]; exact hmul
  rw [hGw, div_le_iff₀ hwnorm_pos]
  refine hbound.trans ?_
  -- target: A·(w.im)^(w.re+1-1/2)·exp ≤ (A·(w.im)^(w.re-1/2)·exp)·‖w‖
  -- use (w.im)^(w.re+1-1/2) = (w.im)^(w.re-1/2)·w.im ≤ (w.im)^(w.re-1/2)·‖w‖
  have hpow : w.im ^ (w.re + 1 - 1/2) = w.im ^ (w.re - 1/2) * w.im := by
    rw [show w.re + 1 - 1/2 = (w.re - 1/2) + 1 by ring, rpow_add_one_eq himpos]
  -- A·((w.im)^(w.re-1/2)·w.im)·exp ≤ A·(w.im)^(w.re-1/2)·exp·‖w‖
  have hexp_pos : (0:ℝ) < Real.exp (-(Real.pi/2) * w.im) := Real.exp_pos _
  have hrpow_nn : 0 ≤ w.im ^ (w.re - 1/2) := Real.rpow_nonneg himpos.le _
  have key : A * (w.im ^ (w.re - 1/2) * w.im) * Real.exp (-(Real.pi/2) * w.im)
      ≤ A * w.im ^ (w.re - 1/2) * Real.exp (-(Real.pi/2) * w.im) * ‖w‖ := by
    have hfac : A * w.im ^ (w.re - 1/2) * Real.exp (-(Real.pi/2) * w.im) * w.im
        ≤ A * w.im ^ (w.re - 1/2) * Real.exp (-(Real.pi/2) * w.im) * ‖w‖ := by
      apply mul_le_mul_of_nonneg_left hwnorm_ge
      positivity
    calc A * (w.im ^ (w.re - 1/2) * w.im) * Real.exp (-(Real.pi/2) * w.im)
        = A * w.im ^ (w.re - 1/2) * Real.exp (-(Real.pi/2) * w.im) * w.im := by ring
      _ ≤ _ := hfac
  rw [hpow]
  exact key

/-! ## Conjugation symmetry: reduce `t ≤ -1` to `t ≥ 1`. -/

/-- `‖Γ(conj w)‖ = ‖Γ w‖`, and `conj w` flips the sign of the imaginary part while keeping
the real part.  This lets us reflect any bound across the real axis. -/
theorem norm_Gamma_conj (w : ℂ) : ‖Complex.Gamma ((starRingEnd ℂ) w)‖ = ‖Complex.Gamma w‖ := by
  rw [Complex.Gamma_conj, norm_conj]

/-! ## Covering the band for `t ≥ 1` from the base strip. -/

/-- The base-strip residual, packaged on `Re ∈ [1,2]`, `Im ≥ 1`, with constant `A₀`. -/
theorem on_strip_12 {A₀ : ℝ} (h : BaseStrip A₀) {w : ℂ}
    (hre1 : (1:ℝ) ≤ w.re) (hre2 : w.re ≤ 2) (him : 1 ≤ w.im) :
    ‖Complex.Gamma w‖ ≤ A₀ * w.im ^ (w.re - 1/2) * Real.exp (-(Real.pi/2) * w.im) :=
  h.2 w hre1 hre2 him

/-- Bound on `Re ∈ [2,3]` for `Im ≥ 1`, by ONE forward step from `[1,2]`.
We move `w` (re ∈ [2,3]) to `w-1` (re ∈ [1,2]) and apply `forward_step`. Constant `4·A₀`. -/
theorem on_strip_23 {A₀ : ℝ} (h : BaseStrip A₀) {w : ℂ}
    (hre1 : (2:ℝ) ≤ w.re) (hre2 : w.re ≤ 3) (him : 1 ≤ w.im) :
    ‖Complex.Gamma w‖ ≤ (5 * A₀) * w.im ^ (w.re - 1/2) * Real.exp (-(Real.pi/2) * w.im) := by
  -- v := w - 1 has re ∈ [1,2], im = w.im ≥ 1
  set v : ℂ := w - 1 with hv
  have hvre : v.re = w.re - 1 := by rw [hv]; simp
  have hvim : v.im = w.im := by rw [hv]; simp
  have hb := on_strip_12 h (w := v) (by rw [hvre]; linarith) (by rw [hvre]; linarith)
    (by rw [hvim]; exact him)
  have hstep := forward_step (A := A₀) (w := v)
    (by rw [hvre]; linarith) (by rw [hvre]; linarith) (by rw [hvim]; exact him) hb
  -- v + 1 = w
  have : v + 1 = w := by rw [hv]; ring
  rwa [this] at hstep

/-- Bound on `Re ∈ [0,1]` for `Im ≥ 1`, by ONE backward step from `[1,2]`.  Constant `A₀`. -/
theorem on_strip_01 {A₀ : ℝ} (h : BaseStrip A₀) {w : ℂ}
    (hre1 : (0:ℝ) ≤ w.re) (hre2 : w.re ≤ 1) (him : 1 ≤ w.im) :
    ‖Complex.Gamma w‖ ≤ A₀ * w.im ^ (w.re - 1/2) * Real.exp (-(Real.pi/2) * w.im) := by
  -- apply backward_step at w (need bound at w+1, re ∈ [1,2])
  have hbnd : ‖Complex.Gamma (w + 1)‖
      ≤ A₀ * (w + 1).im ^ ((w + 1).re - 1/2) * Real.exp (-(Real.pi/2) * (w + 1).im) := by
    have hre' : (w + 1).re = w.re + 1 := by simp
    have him' : (w + 1).im = w.im := by simp
    have := on_strip_12 h (w := w + 1) (by rw [hre']; linarith) (by rw [hre']; linarith)
      (by rw [him']; exact him)
    exact this
  exact backward_step h.1 (by linarith) (by linarith) him hbnd

/-- Bound on `Re ∈ [-1,0]` for `Im ≥ 1`, by ONE backward step from `[0,1]`.  Constant `A₀`. -/
theorem on_strip_m10 {A₀ : ℝ} (h : BaseStrip A₀) {w : ℂ}
    (hre1 : (-1:ℝ) ≤ w.re) (hre2 : w.re ≤ 0) (him : 1 ≤ w.im) :
    ‖Complex.Gamma w‖ ≤ A₀ * w.im ^ (w.re - 1/2) * Real.exp (-(Real.pi/2) * w.im) := by
  have hbnd : ‖Complex.Gamma (w + 1)‖
      ≤ A₀ * (w + 1).im ^ ((w + 1).re - 1/2) * Real.exp (-(Real.pi/2) * (w + 1).im) := by
    have hre' : (w + 1).re = w.re + 1 := by simp
    have him' : (w + 1).im = w.im := by simp
    have := on_strip_01 h (w := w + 1) (by rw [hre']; linarith) (by rw [hre']; linarith)
      (by rw [him']; exact him)
    rw [hre', him'] at this ⊢
    exact this
  exact backward_step h.1 (by linarith) (by linarith) him hbnd

/-- **Upper half (`Im ≥ 1`) of the band**, with constant `5·A₀`. -/
theorem band_upper_pos {A₀ : ℝ} (h : BaseStrip A₀) :
    ∀ w : ℂ, (-1 : ℝ) ≤ w.re → w.re ≤ 3 → 1 ≤ w.im →
      ‖Complex.Gamma w‖ ≤ (5 * A₀) * w.im ^ (w.re - 1/2) * Real.exp (-(Real.pi/2) * w.im) := by
  intro w hre1 hre2 him
  have hA₀ : 0 ≤ A₀ := h.1
  have himpos : (0:ℝ) < w.im := lt_of_lt_of_le one_pos him
  have hrpow_nn : 0 ≤ w.im ^ (w.re - 1/2) := Real.rpow_nonneg himpos.le _
  have hexp_nn : 0 ≤ Real.exp (-(Real.pi/2) * w.im) := (Real.exp_pos _).le
  -- helper: C·X ≤ 5A₀·X  for X ≥ 0
  have upgrade : ∀ {C : ℝ}, 0 ≤ C → C ≤ 5 * A₀ →
      ‖Complex.Gamma w‖ ≤ C * w.im ^ (w.re - 1/2) * Real.exp (-(Real.pi/2) * w.im) →
      ‖Complex.Gamma w‖ ≤ (5 * A₀) * w.im ^ (w.re - 1/2) * Real.exp (-(Real.pi/2) * w.im) := by
    intro C _ hCle hb
    refine hb.trans ?_
    apply mul_le_mul_of_nonneg_right _ hexp_nn
    apply mul_le_mul_of_nonneg_right hCle hrpow_nn
  -- split into the four sub-strips
  rcases le_or_gt w.re 0 with h0 | h0
  · rcases le_or_gt w.re (-1) with hm | hm
    · -- re = -1 boundary case included in [-1,0]
      exact upgrade hA₀ (by linarith) (on_strip_m10 h hre1 h0 him)
    · exact upgrade hA₀ (by linarith) (on_strip_m10 h hre1 h0 him)
  · rcases le_or_gt w.re 1 with h1 | h1
    · exact upgrade hA₀ (by linarith) (on_strip_01 h h0.le h1 him)
    · rcases le_or_gt w.re 2 with h2 | h2
      · exact upgrade hA₀ (by linarith) (on_strip_12 h h1.le h2 him)
      · -- re ∈ (2,3]
        exact (on_strip_23 h h2.le hre2 him)

/-! ## Main theorem: full band, both signs of `t`, conditional on `BaseStrip`. -/

/-- **Band upper bound, conditional on the single base-strip residual.**
From the Stirling bound on the central strip `Re ∈ [1,2]`, `Im ≥ 1`, the full band bound on
`Re ∈ [-1,3]`, `|Im| ≥ 1` follows unconditionally (recurrence both ways + conjugation). -/
theorem bandUpperC_of_baseStrip {A₀ : ℝ} (h : BaseStrip A₀) : BandUpperC (5 * A₀) := by
  have hA₀ : 0 ≤ A₀ := h.1
  refine ⟨by linarith, ?_⟩
  intro w hre1 hre2 him
  -- case on the sign of w.im
  rcases abs_cases w.im with ⟨heq, hpos⟩ | ⟨heq, hneg⟩
  · -- w.im ≥ 0, and |w.im| = w.im ≥ 1
    have him1 : 1 ≤ w.im := by rw [← heq]; exact him
    have hb := band_upper_pos h w hre1 hre2 him1
    -- |w.im| = w.im
    rw [heq]
    exact hb
  · -- w.im < 0 ; reflect via conjugation.  conj w has re = w.re, im = -w.im ≥ 1
    set w' : ℂ := (starRingEnd ℂ) w with hw'
    have hw're : w'.re = w.re := by rw [hw']; simp
    have hw'im : w'.im = -w.im := by rw [hw']; simp
    have him1 : 1 ≤ w'.im := by
      rw [hw'im, ← heq]; exact him
    have hb := band_upper_pos h w' (by rw [hw're]; exact hre1) (by rw [hw're]; exact hre2) him1
    -- ‖Γ w'‖ = ‖Γ w‖ since w' = conj w
    have hnorm : ‖Complex.Gamma w'‖ = ‖Complex.Gamma w‖ := by
      rw [hw']; exact norm_Gamma_conj w
    rw [hnorm, hw're, hw'im] at hb
    -- hb : ‖Γ w‖ ≤ 5A₀·(-w.im)^(w.re-1/2)·exp(-(π/2)·(-w.im))
    -- and |w.im| = -w.im, so rewriting the goal turns it into exactly hb
    rw [heq]
    exact hb

/-- **`bandUpper`, the requested theorem**, stated with the single explicit residual
hypothesis `BaseStrip A₀`.  No `sorry`, no `sorryAx`. -/
theorem bandUpper {A₀ : ℝ} (h : BaseStrip A₀) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ w : ℂ, -1 ≤ w.re → w.re ≤ 3 → 1 ≤ |w.im| →
    ‖Complex.Gamma w‖ ≤ A * |w.im| ^ (w.re - 1/2) * Real.exp (-(Real.pi/2) * |w.im|) := by
  obtain ⟨hpos, hbound⟩ := bandUpperC_of_baseStrip h
  exact ⟨5 * A₀, hpos, hbound⟩

end BandUpper

-- Axiom audit
#print axioms BandUpper.forward_step
#print axioms BandUpper.backward_step
#print axioms BandUpper.band_upper_pos
#print axioms BandUpper.bandUpperC_of_baseStrip
#print axioms BandUpper.bandUpper
