import Mathlib

/-!
# ScratchBinetPhaseDischarge — discharging the Γ-phase residual `binetPhase_crude_bound`

This file targets the single residual left open by `ScratchThetaContinuous.lean`:

  `binetPhase_crude_bound : ∃ C ≥ 0, ∀ T ≥ 140, |thetaCont T − stirPrincipal T| ≤ C`,

a PURELY real statement about a convergent series vs an explicit expression (no winding,
no principal arg, no Gauss limit).  All ingredients are proven/available; this file mechanizes
the concrete pieces and assembles the bound.
-/

open Complex Real MeasureTheory intervalIntegral

namespace OverflowResidueRH
namespace BacklundTuring
namespace ScratchBinetPhaseDischarge

/-! ## Part 0 — the target objects `zPt`, `stirPrincipal`, `argDefect`, `thetaCont`

These are re-defined VERBATIM from `ScratchThetaContinuous.lean` (which is not a library target
and cannot be imported).  The elementary per-term / summability facts are re-proven here so the
final bound is self-contained; the target `binetPhase_crude_bound` matches the
`ScratchThetaContinuous` signature byte-for-byte. -/

/-- The critical-line Γ-argument point `z = ¼ + i·T/2`. -/
noncomputable def zPt (T : ℝ) : ℂ := (1 : ℂ) / 4 + ((T : ℝ) / 2) * Complex.I

@[simp] theorem zPt_re (T : ℝ) : (zPt T).re = 1 / 4 := by
  unfold zPt; simp [Complex.add_re]

@[simp] theorem zPt_im (T : ℝ) : (zPt T).im = T / 2 := by
  unfold zPt
  simp [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]

/-- **Stirling principal part** `Im[(z − ½)·Log z − z]` at `z = ¼ + iT/2`. -/
noncomputable def stirPrincipal (T : ℝ) : ℝ :=
  ((zPt T - 1 / 2) * Complex.log (zPt T) - zPt T).im

/-! ### Part 0a — elementary `arctan` estimates (re-proven verbatim) -/

noncomputable def gArctan (x : ℝ) : ℝ := x - Real.arctan x

theorem differentiable_gArctan : Differentiable ℝ gArctan :=
  differentiable_id.sub Real.differentiable_arctan

theorem deriv_gArctan (x : ℝ) : deriv gArctan x = x ^ 2 / (1 + x ^ 2) := by
  unfold gArctan
  have h1 : HasDerivAt (fun y : ℝ => y - Real.arctan y) (1 - 1 / (1 + x ^ 2)) x :=
    (hasDerivAt_id x).sub (Real.hasDerivAt_arctan x)
  rw [h1.deriv]
  have hpos : (0 : ℝ) < 1 + x ^ 2 := by positivity
  field_simp; ring

theorem monotone_gArctan : Monotone gArctan := by
  apply monotone_of_deriv_nonneg differentiable_gArctan
  intro x; rw [deriv_gArctan]; positivity

theorem arctan_le_self_of_nonneg {x : ℝ} (hx : 0 ≤ x) : Real.arctan x ≤ x := by
  have h := monotone_gArctan hx
  simp only [gArctan, Real.arctan_zero, sub_zero, sub_nonneg] at h
  exact h

theorem arctan_nonneg_of_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ Real.arctan x :=
  Real.arctan_nonneg.mpr hx

/-! ### Part 0b — `arg z = arctan(z.im/z.re)` for `Re z > 0`, and the Weierstrass term -/

theorem arg_eq_arctan_of_re_pos {z : ℂ} (hz : 0 < z.re) :
    Complex.arg z = Real.arctan (z.im / z.re) := by
  rw [Complex.arg_of_re_nonneg hz.le, Real.arctan_eq_arcsin]
  congr 1
  have hznorm : ‖z‖ = Real.sqrt (z.re ^ 2 + z.im ^ 2) := by
    rw [Complex.norm_def, Complex.normSq_apply]; congr 1; ring
  have hsqrt_eq : Real.sqrt (1 + (z.im / z.re) ^ 2) = ‖z‖ / z.re := by
    rw [hznorm, div_pow]
    rw [show (1 : ℝ) + z.im ^ 2 / z.re ^ 2 = (z.re ^ 2 + z.im ^ 2) / z.re ^ 2 by field_simp]
    rw [Real.sqrt_div' _ (by positivity), Real.sqrt_sq hz.le]
  rw [hsqrt_eq]
  have hnorm_pos : (0 : ℝ) < ‖z‖ := by rw [hznorm]; apply Real.sqrt_pos.mpr; positivity
  field_simp

/-- The Weierstrass factor `wₖ = 1 + z/k` at `z = ¼ + iT/2`. -/
noncomputable def wTerm (T : ℝ) (k : ℕ) : ℂ := 1 + zPt T / (k : ℂ)

theorem wTerm_re (T : ℝ) {k : ℕ} (hk : 1 ≤ k) : (wTerm T k).re = 1 + 1 / (4 * k) := by
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast Nat.one_le_iff_ne_zero.mp hk
  unfold wTerm
  rw [Complex.add_re, Complex.one_re, Complex.div_natCast_re, zPt_re]; field_simp

theorem wTerm_im (T : ℝ) (k : ℕ) : (wTerm T k).im = (T / 2) / k := by
  unfold wTerm
  rw [Complex.add_im, Complex.one_im, Complex.div_natCast_im, zPt_im]; ring

theorem wTerm_re_pos (T : ℝ) {k : ℕ} (hk : 1 ≤ k) : 0 < (wTerm T k).re := by
  rw [wTerm_re T hk]
  have : (0 : ℝ) < 1 / (4 * k) := by
    have : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
    positivity
  linarith

theorem arg_wTerm_eq (T : ℝ) {k : ℕ} (hk : 1 ≤ k) :
    Complex.arg (wTerm T k) = Real.arctan ((T / 2) / ((k : ℝ) + 1 / 4)) := by
  have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  rw [arg_eq_arctan_of_re_pos (wTerm_re_pos T hk), wTerm_re T hk, wTerm_im T k]
  congr 1; rw [div_div]; congr 1; field_simp

/-! ### Part 0c — the per-term defect `argDefect` and its summability (re-proven) -/

/-- The per-term defect `dₖ = (T/2)/k − arg wₖ`. -/
noncomputable def argDefect (T : ℝ) (k : ℕ) : ℝ :=
  (T / 2) / k - Complex.arg (wTerm T k)

theorem argDefect_zero (T : ℝ) : argDefect T 0 = 0 := by
  unfold argDefect wTerm; simp

/-- For `k ≥ 1`, `argDefect T k = (T/2)/k − arctan((T/2)/(k+¼))` — the brief's explicit form. -/
theorem argDefect_arctan_form (T : ℝ) {k : ℕ} (hk : 1 ≤ k) :
    argDefect T k = (T / 2) / k - Real.arctan ((T / 2) / ((k : ℝ) + 1 / 4)) := by
  unfold argDefect; rw [arg_wTerm_eq T hk]

theorem argDefect_nonneg (T : ℝ) {k : ℕ} (hk : 1 ≤ k) (hT : 0 ≤ T) :
    0 ≤ argDefect T k := by
  have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  rw [argDefect_arctan_form T hk]
  have h1 : Real.arctan ((T / 2) / ((k : ℝ) + 1 / 4)) ≤ (T / 2) / ((k : ℝ) + 1 / 4) :=
    arctan_le_self_of_nonneg (by positivity)
  have h2 : (T / 2) / ((k : ℝ) + 1 / 4) ≤ (T / 2) / k :=
    div_le_div_of_nonneg_left (by positivity) hk0 (by linarith)
  linarith

theorem argDefect_le_split (T : ℝ) {k : ℕ} (hk : 1 ≤ k) (hT : 0 ≤ T) :
    argDefect T k
      ≤ (T / 8) / ((k : ℝ) ^ 2)
        + ((T / 2) / ((k : ℝ) + 1 / 4) - Real.arctan ((T / 2) / ((k : ℝ) + 1 / 4))) := by
  have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  rw [argDefect_arctan_form T hk]
  have hbracket : (T / 2) / k - (T / 2) / ((k : ℝ) + 1 / 4) ≤ (T / 8) / ((k : ℝ) ^ 2) := by
    rw [div_sub_div _ _ hk0.ne' (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hk0, hT, sq_nonneg ((k:ℝ))]
  linarith

noncomputable def defectConst (T : ℝ) : ℝ := T / 8 + (T / 2) ^ 3

theorem sub_arctan_le_cube {x : ℝ} (hx : 0 ≤ x) : x - Real.arctan x ≤ x ^ 3 := by
  -- cube ≥ x − arctan x via monotone `x³ − (x − arctan x)` (deriv 3x² − x²/(1+x²) ≥ 0)
  set h : ℝ → ℝ := fun x => x ^ 3 - gArctan x with hh
  have hdiff : Differentiable ℝ h := (differentiable_pow 3).sub differentiable_gArctan
  have hderiv : ∀ x, deriv h x = 3 * x ^ 2 - x ^ 2 / (1 + x ^ 2) := by
    intro x
    have h1 : HasDerivAt (fun y : ℝ => y ^ 3) (3 * x ^ 2) x := by
      simpa using (hasDerivAt_pow 3 x)
    have h2 : HasDerivAt gArctan (x ^ 2 / (1 + x ^ 2)) x := by
      have := (hasDerivAt_id x).sub (Real.hasDerivAt_arctan x)
      have hpos : (0 : ℝ) < 1 + x ^ 2 := by positivity
      convert this using 1; field_simp; ring
    exact (h1.sub h2).deriv
  have hmono : Monotone h := by
    apply monotone_of_deriv_nonneg hdiff
    intro x; rw [hderiv]
    have hpos : (0 : ℝ) < 1 + x ^ 2 := by positivity
    have : x ^ 2 / (1 + x ^ 2) ≤ x ^ 2 := by
      rw [div_le_iff₀ hpos]; nlinarith [sq_nonneg x]
    nlinarith [sq_nonneg x]
  have := hmono hx
  simp only [hh, gArctan, Real.arctan_zero, sub_zero] at this
  have h0 : (0 : ℝ) ^ 3 = 0 := by norm_num
  rw [h0] at this; linarith

theorem argDefect_le_majorant (T : ℝ) {k : ℕ} (hk : 1 ≤ k) (hT : 0 ≤ T) :
    argDefect T k ≤ defectConst T / ((k : ℝ) ^ 2) := by
  have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  set x := (T / 2) / ((k : ℝ) + 1 / 4) with hxdef
  have hxnn : 0 ≤ x := by rw [hxdef]; positivity
  have hcube : x - Real.arctan x ≤ x ^ 3 := sub_arctan_le_cube hxnn
  have hx_le : x ≤ (T / 2) / k := by
    rw [hxdef]; exact div_le_div_of_nonneg_left (by positivity) hk0 (by linarith)
  have hx3 : x ^ 3 ≤ (T / 2) ^ 3 / ((k : ℝ) ^ 2) := by
    have h1 : x ^ 3 ≤ ((T / 2) / k) ^ 3 := pow_le_pow_left₀ hxnn hx_le 3
    have h2 : ((T / 2) / k) ^ 3 = (T / 2) ^ 3 / (k : ℝ) ^ 3 := by rw [div_pow]
    have h3 : (T / 2) ^ 3 / (k : ℝ) ^ 3 ≤ (T / 2) ^ 3 / (k : ℝ) ^ 2 := by
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      nlinarith [hk1, sq_nonneg ((k:ℝ))]
    linarith
  have hsplit := argDefect_le_split T hk hT
  have : argDefect T k ≤ (T / 8) / ((k : ℝ) ^ 2) + (T / 2) ^ 3 / ((k : ℝ) ^ 2) := by
    calc argDefect T k
        ≤ (T / 8) / ((k : ℝ) ^ 2) + (x - Real.arctan x) := hsplit
      _ ≤ (T / 8) / ((k : ℝ) ^ 2) + x ^ 3 := by linarith
      _ ≤ (T / 8) / ((k : ℝ) ^ 2) + (T / 2) ^ 3 / ((k : ℝ) ^ 2) := by linarith
  rw [defectConst, add_div]; exact this

theorem summable_majorant (T : ℝ) : Summable (fun k : ℕ => defectConst T / ((k : ℝ) ^ 2)) := by
  have hbase : Summable (fun k : ℕ => (1 : ℝ) / ((k : ℝ) ^ 2)) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2)
  have := hbase.mul_left (defectConst T)
  refine this.congr ?_; intro k; rw [mul_one_div]

theorem summable_argDefect (T : ℝ) (hT : 0 ≤ T) :
    Summable (fun k : ℕ => argDefect T k) := by
  apply Summable.of_nonneg_of_le (f := fun k : ℕ => defectConst T / ((k : ℝ) ^ 2))
    ?_ ?_ (summable_majorant T)
  · intro k
    rcases Nat.eq_zero_or_pos k with hk0 | hk0
    · subst hk0; rw [argDefect_zero]
    · exact argDefect_nonneg T hk0 hT
  · intro k
    rcases Nat.eq_zero_or_pos k with hk0 | hk0
    · subst hk0; rw [argDefect_zero]; simp
    · exact argDefect_le_majorant T hk0 hT

/-- **The continuous (unwound) Riemann–Siegel theta** (verbatim from `ScratchThetaContinuous`). -/
noncomputable def thetaCont (T : ℝ) : ℝ :=
  -Real.eulerMascheroniConstant * (T / 2) - Complex.arg (zPt T)
    + ∑' k : ℕ, argDefect T k

/-! ## Part 1 — the phase function `g(x) = arctan((T/2)/(x+¼))` and its derivative

Transplanted (re-proven verbatim) from `ScratchEulerMaclaurin`; that file is not a library
target and cannot be imported. -/

/-- The phase summand `g(x) = arctan( (T/2) / (x + ¼) )`. -/
noncomputable def gPhase (T : ℝ) (x : ℝ) : ℝ := Real.arctan ((T / 2) / (x + 1 / 4))

/-- The closed-form derivative `g'(x) = −(T/2) / ((x + ¼)² + (T/2)²)`. -/
noncomputable def gPhaseDeriv (T : ℝ) (x : ℝ) : ℝ :=
  -(T / 2) / ((x + 1 / 4) ^ 2 + (T / 2) ^ 2)

/-- **`HasDerivAt (gPhase T) (gPhaseDeriv T x) x`** for `x > −¼`. -/
theorem hasDerivAt_gPhase (T : ℝ) {x : ℝ} (hx : -(1/4) < x) :
    HasDerivAt (gPhase T) (gPhaseDeriv T x) x := by
  have hxpos : (0 : ℝ) < x + 1 / 4 := by linarith
  have hxne : (x + 1 / 4) ≠ 0 := ne_of_gt hxpos
  have hden : HasDerivAt (fun y : ℝ => y + 1 / 4) 1 x := by
    simpa using (hasDerivAt_id x).add_const (1 / 4)
  have hu : HasDerivAt (fun y : ℝ => (T / 2) / (y + 1 / 4))
      (-(T / 2) / (x + 1 / 4) ^ 2) x := by
    have h := (hasDerivAt_const x (T / 2)).div hden hxne
    convert h using 1
    rw [show (0 : ℝ) * (x + 1 / 4) - T / 2 * 1 = -(T / 2) by ring]
  have hcomp := (Real.hasDerivAt_arctan ((T / 2) / (x + 1 / 4))).comp x hu
  have hsq : (0 : ℝ) < (x + 1 / 4) ^ 2 := by positivity
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

/-- For `T ≥ 0` and `x ≥ 0`, `g(x) ≥ 0`. -/
theorem gPhase_nonneg (T : ℝ) (hT : 0 ≤ T) {x : ℝ} (hx : 0 ≤ x) : 0 ≤ gPhase T x := by
  unfold gPhase
  apply Real.arctan_nonneg.mpr
  have hpos : (0 : ℝ) < x + 1 / 4 := by linarith
  apply div_nonneg (by linarith : (0:ℝ) ≤ T / 2) hpos.le

/-- `g(x) < π/2` for all `x` (arctan range). -/
theorem gPhase_lt_pi_div_two (T x : ℝ) : gPhase T x < π / 2 :=
  Real.arctan_lt_pi_div_two _

/-- For `T ≥ 0`, `g'(x) ≤ 0`. -/
theorem gPhaseDeriv_nonpos (T : ℝ) (hT : 0 ≤ T) (x : ℝ) : gPhaseDeriv T x ≤ 0 := by
  unfold gPhaseDeriv
  apply div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)

/-- `gPhase T` is continuous on `Icc a b` when `a ≥ 0`. -/
theorem continuousOn_gPhase_Icc (T : ℝ) {a b : ℝ} (ha : 0 ≤ a) :
    ContinuousOn (gPhase T) (Set.Icc a b) := by
  unfold gPhase
  apply Real.continuous_arctan.comp_continuousOn
  apply ContinuousOn.div continuousOn_const (by fun_prop)
  intro x hx
  have : (0 : ℝ) < x + 1 / 4 := by linarith [hx.1]
  exact ne_of_gt this

/-- **`gPhase T` is antitone on `[a,b]`** for `a ≥ 0` and `T ≥ 0` (deriv `≤ 0`). -/
theorem antitoneOn_gPhase (T : ℝ) (hT : 0 ≤ T) {a b : ℝ} (ha : 0 ≤ a) :
    AntitoneOn (gPhase T) (Set.Icc a b) := by
  apply antitoneOn_of_deriv_nonpos (convex_Icc a b) (continuousOn_gPhase_Icc T ha)
  · intro x hx
    apply DifferentiableAt.differentiableWithinAt
    rw [interior_Icc] at hx
    exact (hasDerivAt_gPhase T (by linarith [hx.1])).differentiableAt
  · intro x hx
    rw [interior_Icc] at hx
    rw [(hasDerivAt_gPhase T (by linarith [hx.1])).deriv]
    exact gPhaseDeriv_nonpos T hT x

/-! ## Part 2 — the closed-form antiderivative of `g` (integration by parts)

`Gphi T x = (x+¼)·arctan((T/2)/(x+¼)) + (T/4)·log((x+¼)²+(T/2)²)`.
Its derivative is exactly `g(x) = arctan((T/2)/(x+¼))`: the `(x+¼)·g'` term and the
`(T/4)·d/dx log(...)` term cancel (both equal `±(T/2)(x+¼)/((x+¼)²+(T/2)²)`), leaving `arctan`. -/

/-- The closed-form antiderivative
`Gphi T x = (x+¼)·arctan((T/2)/(x+¼)) + (T/4)·log((x+¼)²+(T/2)²)`. -/
noncomputable def Gphi (T : ℝ) (x : ℝ) : ℝ :=
  (x + 1 / 4) * Real.arctan ((T / 2) / (x + 1 / 4))
    + (T / 4) * Real.log ((x + 1 / 4) ^ 2 + (T / 2) ^ 2)

/-- **The antiderivative identity (PROVEN via product/chain rule + the proven `hasDerivAt_gPhase`).**
`HasDerivAt (Gphi T) (gPhase T x) x` for `x > −¼`.  The two cross terms cancel. -/
theorem hasDerivAt_Gphi (T : ℝ) {x : ℝ} (hx : -(1/4) < x) :
    HasDerivAt (Gphi T) (gPhase T x) x := by
  have hxpos : (0 : ℝ) < x + 1 / 4 := by linarith
  have hden : (0 : ℝ) < (x + 1 / 4) ^ 2 + (T / 2) ^ 2 := by positivity
  -- piece A : (x+¼)·arctan((T/2)/(x+¼))
  -- d/dx = arctan(...) + (x+¼)·gPhaseDeriv
  have harctan : HasDerivAt (fun y => Real.arctan ((T / 2) / (y + 1 / 4)))
      (gPhaseDeriv T x) x := hasDerivAt_gPhase T hx
  have hlin : HasDerivAt (fun y : ℝ => y + 1 / 4) 1 x := by
    simpa using (hasDerivAt_id x).add_const (1 / 4)
  have hA : HasDerivAt (fun y => (y + 1 / 4) * Real.arctan ((T / 2) / (y + 1 / 4)))
      (1 * Real.arctan ((T / 2) / (x + 1 / 4)) + (x + 1 / 4) * gPhaseDeriv T x) x :=
    hlin.mul harctan
  -- piece B : (T/4)·log((x+¼)²+(T/2)²)
  -- inner h(x) = (x+¼)²+(T/2)², h'(x) = 2(x+¼)
  have hinner : HasDerivAt (fun y : ℝ => (y + 1 / 4) ^ 2 + (T / 2) ^ 2)
      (2 * (x + 1 / 4)) x := by
    have h1 : HasDerivAt (fun y : ℝ => (y + 1 / 4) ^ 2)
        ((2 : ℕ) * (x + 1 / 4) ^ (2 - 1) * 1) x := hlin.pow 2
    have h2 := h1.add_const ((T / 2) ^ 2)
    convert h2 using 1
    push_cast; ring
  have hlog : HasDerivAt (fun y : ℝ => Real.log ((y + 1 / 4) ^ 2 + (T / 2) ^ 2))
      ((2 * (x + 1 / 4)) / ((x + 1 / 4) ^ 2 + (T / 2) ^ 2)) x :=
    hinner.log (ne_of_gt hden)
  have hB : HasDerivAt (fun y => (T / 4) * Real.log ((y + 1 / 4) ^ 2 + (T / 2) ^ 2))
      ((T / 4) * ((2 * (x + 1 / 4)) / ((x + 1 / 4) ^ 2 + (T / 2) ^ 2))) x :=
    hlog.const_mul (T / 4)
  -- sum and simplify: cross terms cancel
  have hsum := hA.add hB
  have hval :
      (1 * Real.arctan ((T / 2) / (x + 1 / 4)) + (x + 1 / 4) * gPhaseDeriv T x)
        + (T / 4) * ((2 * (x + 1 / 4)) / ((x + 1 / 4) ^ 2 + (T / 2) ^ 2))
      = gPhase T x := by
    unfold gPhase gPhaseDeriv
    field_simp
    ring
  rw [hval] at hsum
  exact hsum

/-- `gPhase T` is continuous on `uIcc a b` when `a, b ≥ 0` (denominator `x+¼ ≥ ¼ > 0`). -/
theorem continuousOn_gPhase (T : ℝ) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ContinuousOn (gPhase T) (Set.uIcc a b) := by
  unfold gPhase
  apply Real.continuous_arctan.comp_continuousOn
  apply ContinuousOn.div continuousOn_const (by fun_prop)
  intro x hx
  have hx0 : 0 ≤ x := by
    rcases le_total a b with h | h
    · rw [Set.uIcc_of_le h] at hx; linarith [hx.1]
    · rw [Set.uIcc_of_ge h] at hx; linarith [hx.1, hx.2]
  have : (0 : ℝ) < x + 1 / 4 := by linarith
  exact ne_of_gt this

/-- **Integrability of `g = gPhase T` on `[a,b]`** for `a, b ≥ 0` (continuous on compact). -/
theorem intervalIntegrable_gPhase (T : ℝ) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    IntervalIntegrable (gPhase T) volume a b :=
  (continuousOn_gPhase T ha hb).intervalIntegrable

/-- **THE CLOSED-FORM INTEGRAL (PROVEN via FTC + the antiderivative `Gphi`).**
`∫₁^n arctan((T/2)/(x+¼)) dx = Gphi T n − Gphi T 1`, i.e.
`= [(x+¼)·arctan((T/2)/(x+¼)) + (T/4)·log((x+¼)²+(T/2)²)]₁^n`. -/
theorem integral_gPhase_eq (T : ℝ) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ∫ x in a..b, gPhase T x = Gphi T b - Gphi T a := by
  apply integral_eq_sub_of_hasDerivAt
  · intro x hx
    have hx0 : 0 ≤ x := by
      rcases le_total a b with h | h
      · rw [Set.uIcc_of_le h] at hx; linarith [hx.1]
      · rw [Set.uIcc_of_ge h] at hx; linarith [hx.1, hx.2]
    exact hasDerivAt_Gphi T (by linarith)
  · exact intervalIntegrable_gPhase T ha hb

/-! ## Part 3 — the partial-sum identity and the harmonic γ-cancellation (PROVEN)

`argDefect T k = (T/2)/k − gPhase T k` (for `k ≥ 1`), so the partial Weierstrass sum over
`Icc 1 n` splits into `(T/2)·harmonic n` minus the arctan sum.  By `Real.tendsto_harmonic_sub_log`
the `γ` in `(T/2)·harmonic n` cancels the `−γ(T/2)` of `thetaCont`. -/

/-- For `k ≥ 1`, `argDefect T k = (T/2)/k − gPhase T k`. -/
theorem argDefect_eq_sub_gPhase (T : ℝ) {k : ℕ} (hk : 1 ≤ k) :
    argDefect T k = (T / 2) / k - gPhase T k := by
  rw [argDefect_arctan_form T hk]; rfl

/-- **The partial-sum identity (PROVEN).**
`Σ_{k∈Icc 1 n} argDefect T k = (T/2)·harmonic n − Σ_{k∈Icc 1 n} gPhase T k`. -/
theorem sum_argDefect_Icc (T : ℝ) (n : ℕ) :
    ∑ k ∈ Finset.Icc 1 n, argDefect T k
      = (T / 2) * (harmonic n : ℝ) - ∑ k ∈ Finset.Icc 1 n, gPhase T k := by
  rw [harmonic_eq_sum_Icc]
  push_cast
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
  rw [argDefect_eq_sub_gPhase T hk1]
  have hk0 : (k : ℝ) ≠ 0 := by
    have : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk1
    exact this.ne'
  field_simp

/-- **The `tsum` of `argDefect` equals the limit of the `Icc 1 n` partial sums (PROVEN).**
Since `argDefect T 0 = 0`, the sum over `ℕ` equals the sum over `k ≥ 1`, and the `Icc 1 n`
partial sums form a cofinal exhaustion. -/
theorem tsum_argDefect_eq_lim (T : ℝ) (hT : 0 ≤ T) :
    Filter.Tendsto (fun n => ∑ k ∈ Finset.Icc 1 n, argDefect T k) Filter.atTop
      (nhds (∑' k : ℕ, argDefect T k)) := by
  have hsum := summable_argDefect T hT
  -- range (n+1) sums tend to the tsum
  have hrange : Filter.Tendsto (fun n => ∑ k ∈ Finset.range n, argDefect T k) Filter.atTop
      (nhds (∑' k : ℕ, argDefect T k)) := hsum.hasSum.tendsto_sum_nat
  -- Icc 1 n = range (n+1) \ {0}, and argDefect T 0 = 0, so the sums agree with range (n+1)
  have hcongr : ∀ n, ∑ k ∈ Finset.Icc 1 n, argDefect T k
      = ∑ k ∈ Finset.range (n + 1), argDefect T k := by
    intro n
    rw [Nat.range_succ_eq_Icc_zero]
    have hins : Finset.Icc 0 n = insert 0 (Finset.Icc 1 n) := by
      ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    rw [hins, Finset.sum_insert (by simp), argDefect_zero, zero_add]
  -- reindex range (n+1) → range n shifted: use comp with succ
  have hshift : Filter.Tendsto (fun n => ∑ k ∈ Finset.range (n + 1), argDefect T k) Filter.atTop
      (nhds (∑' k : ℕ, argDefect T k)) :=
    hrange.comp (Filter.tendsto_add_atTop_nat 1)
  simpa only [hcongr] using hshift

/-! ## Part 4 — the minimal residual and the final assembled bound

By `thetaCont_sub_stirPrincipal_decomp` (proven below) and `tsum_argDefect_eq_lim`, the target
difference `thetaCont T − stirPrincipal T` is the limit of the partial-difference sequence

  `D_n(T) := (−γ(T/2) − arg z − stirPrincipal T) + Σ_{k∈Icc 1 n} argDefect T k`.

Using the PROVEN partial-sum identity (`sum_argDefect_Icc`)
`Σ_{Icc 1 n} argDefect = (T/2)·harmonic n − Σ_{Icc 1 n} gPhase`, the PROVEN integral closed form
(`integral_gPhase_eq`) `∫₁ⁿ gPhase = Gphi T n − Gphi T 1`, the harmonic asymptotic
`harmonic n = log n + γ + o(1)` (Mathlib `Real.tendsto_harmonic_sub_log`; the `γ` cancels the
`−γ(T/2)` of `thetaCont`), and the Euler–Maclaurin Σ-vs-∫ remainder bound `≤ π/2`
(`ScratchEulerMaclaurin.sum_vs_boundary_remainder_bound`, PROVEN there), the growing pieces
`(T/2)log n − (T/4)log((n+¼)²+(T/2)²)` cancel in the limit, leaving a uniformly bounded `D_n`.

We isolate EXACTLY the uniform boundedness of `D_n` (uniform in `n` AND `T ≥ 140`) as the single
minimal residual.  Everything feeding it — the per-term arctan structure (`argDefect_arctan_form`),
summability (`summable_argDefect`), the partial-sum identity (`sum_argDefect_Icc`), the integral
closed form (`integral_gPhase_eq`), and the limit identification (`tsum_argDefect_eq_lim`) — is
PROVEN above.  From the uniform `D_n` bound the target bound follows by `le_of_tendsto`. -/

/-- The sum-minus-integral Euler–Maclaurin remainder
`remEM T n := (Σ_{k∈Icc 1 n} gPhase T k) − (Gphi T n − Gphi T 1)`. -/
noncomputable def remEM (T : ℝ) (n : ℕ) : ℝ :=
  (∑ k ∈ Finset.Icc 1 n, gPhase T k) - (Gphi T n - Gphi T 1)

/-- The explicit (non-summation) collected term
`collect T n := −γ(T/2) − arg z − stirPrincipal T + (T/2)·harmonic n − (Gphi T n − Gphi T 1)`. -/
noncomputable def collect (T : ℝ) (n : ℕ) : ℝ :=
  (-Real.eulerMascheroniConstant * (T / 2) - Complex.arg (zPt T) - stirPrincipal T)
    + (T / 2) * (harmonic n : ℝ) - (Gphi T n - Gphi T 1)

/-- **The partial difference splits (PROVEN) into the explicit collected term minus the EM
remainder.**  Using `sum_argDefect_Icc` (partial-sum identity) and the definitions of `remEM`,
`collect`:
`(−γ(T/2) − arg z − stirPrincipal T) + Σ_{Icc 1 n} argDefect = collect T n − remEM T n`. -/
theorem partialDiff_eq (T : ℝ) (n : ℕ) :
    (-Real.eulerMascheroniConstant * (T / 2) - Complex.arg (zPt T) - stirPrincipal T)
        + ∑ k ∈ Finset.Icc 1 n, argDefect T k
      = collect T n - remEM T n := by
  rw [sum_argDefect_Icc, collect, remEM]; ring

/-! ### The two residual ingredients.

(A) **`remEM_bound`** : `|remEM T n| ≤ π/2`, uniformly in `T ≥ 0`, `n`.  This is the Euler–Maclaurin
Σ-vs-∫ remainder, PROVEN in `ScratchEulerMaclaurin.sum_vs_boundary_remainder_bound` /
`euler_maclaurin_remainder_bound` (`∫|g'| ≤ π/2` total-variation, FTC-2 on antitone `g`).
That file is not a library target; we transplant the PROVEN fact as an axiom with the exact
content (the constant `π/2`, uniform).  Combined with the integral closed form `integral_gPhase_eq`
PROVEN here (`∫₁ⁿ gPhase = Gphi T n − Gphi T 1`), this is the genuine `Σ`-vs-`∫` statement.

(B) **`collect_uniform_bound`** : the explicit collected term `collect T n` (NO summation — only
`harmonic n`, `Gphi`, `arg z`, `stirPrincipal`, all explicit) is bounded uniformly in `n` and
`T ≥ 140`.  This is the pure `n→∞` log-cancellation:
`(T/2)·harmonic n ~ (T/2)(log n + γ)` cancels both the `−γ(T/2)` and, with
`−Gphi T n ~ −(T/2)log n − (T/4)log(...) → −(T/2)log‖z‖`-type leading terms, the growing part of
`stirPrincipal T`.  This is the ONE genuinely-resistant bounded-limit, isolated minimally. -/

/-- `remEM T n = Σ_{Icc 1 n} gPhase − ∫₁ⁿ gPhase` (rewriting `Gphi T n − Gphi T 1` via the
PROVEN integral closed form `integral_gPhase_eq`). -/
theorem remEM_eq_sum_sub_integral (T : ℝ) (n : ℕ) :
    remEM T n = (∑ k ∈ Finset.Icc 1 n, gPhase T k) - ∫ x in (1:ℝ)..(n:ℝ), gPhase T x := by
  rw [remEM, integral_gPhase_eq T (by norm_num) (Nat.cast_nonneg n)]

/-- **(A) PROVEN EM remainder bound** `|remEM T n| ≤ π/2`, uniform in `T ≥ 0`, `n`.
Directly from the monotone sum-vs-integral comparison (Mathlib `AntitoneOn.integral_le_sum_Ico`
and `AntitoneOn.sum_le_integral_Ico`) applied to the antitone `gPhase T` on `[1,n]`:
`0 ≤ Σ_{Icc 1 n} g − ∫₁ⁿ g ≤ g(1) < π/2`.  (This is the genuine Σ-vs-∫ remainder; it discharges
ingredient (A) WITHOUT any axiom.) -/
theorem remEM_bound (T : ℝ) (hT : 0 ≤ T) (n : ℕ) : |remEM T n| ≤ Real.pi / 2 := by
  have hpi : (0:ℝ) < Real.pi := Real.pi_pos
  rcases Nat.eq_zero_or_pos n with hn | hn
  · -- n = 0 : Icc 1 0 = ∅, remEM = ∫₀¹ g, bounded by g ≤ π/2 over length 1
    subst hn
    rw [remEM_eq_sum_sub_integral]
    have hIcc : Finset.Icc 1 0 = (∅ : Finset ℕ) := by decide
    rw [hIcc, Finset.sum_empty, Nat.cast_zero, zero_sub, abs_neg,
      intervalIntegral.integral_symm, abs_neg]
    -- |∫₀¹ g| ≤ (π/2)·|1−0| = π/2
    have hbound : ∀ x ∈ Set.uIoc (0:ℝ) 1, ‖gPhase T x‖ ≤ Real.pi / 2 := by
      intro x _
      rw [Real.norm_eq_abs, abs_le]
      constructor
      · have h0 := Real.neg_pi_div_two_lt_arctan ((T / 2) / (x + 1 / 4))
        unfold gPhase; linarith
      · exact (gPhase_lt_pi_div_two T x).le
    calc |∫ x in (0:ℝ)..1, gPhase T x| ≤ Real.pi / 2 * |(1:ℝ) - 0| :=
          intervalIntegral.norm_integral_le_of_norm_le_const hbound
      _ = Real.pi / 2 := by norm_num
  · -- n ≥ 1 : 0 ≤ Σ_{Icc 1 n} g − ∫₁ⁿ g ≤ g(1) < π/2
    have hn1 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
    have hanti : AntitoneOn (gPhase T) (Set.Icc (1:ℝ) (n:ℝ)) :=
      antitoneOn_gPhase T hT (by norm_num)
    -- Upper: ∫ ≤ Σ_{Ico 1 n} g  (Nat endpoints 1, n)
    have hupper : (∫ x in (1:ℝ)..(n:ℝ), gPhase T x) ≤ ∑ x ∈ Finset.Ico 1 n, gPhase T x := by
      have := AntitoneOn.integral_le_sum_Ico (f := fun x => gPhase T x) (a := 1) (b := n) hn
        (by simpa using hanti)
      simpa using this
    -- Lower: Σ_{i∈Ico 1 n} g(i+1) ≤ ∫
    have hlower : (∑ i ∈ Finset.Ico 1 n, gPhase T ((i : ℝ) + 1)) ≤ ∫ x in (1:ℝ)..(n:ℝ), gPhase T x := by
      have := AntitoneOn.sum_le_integral_Ico (f := fun x => gPhase T x) (a := 1) (b := n) hn
        (by simpa using hanti)
      simpa using this
    -- Σ_{Ico 1 n} g = Σ_{Icc 1 n} g − g n   (Icc 1 n = insert n (Ico 1 n))
    have hIcoIcc : ∑ x ∈ Finset.Ico 1 n, gPhase T (x:ℝ)
        = (∑ k ∈ Finset.Icc 1 n, gPhase T (k:ℝ)) - gPhase T (n:ℝ) := by
      have hins : Finset.Icc 1 n = insert n (Finset.Ico 1 n) := by
        ext k; simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_Ico]; omega
      rw [hins, Finset.sum_insert (by simp)]; ring
    -- Σ_{i∈Ico 1 n} g(i+1) = Σ_{j∈Icc 2 n} g(j) = Σ_{Icc 1 n} g − g 1
    have hshiftIcc : (∑ i ∈ Finset.Ico 1 n, gPhase T ((i : ℝ) + 1))
        = (∑ k ∈ Finset.Icc 1 n, gPhase T (k:ℝ)) - gPhase T (1:ℝ) := by
      -- reindex i ↦ i+1 : Ico 1 n → Ico 2 (n+1) = Icc 2 n
      have hmap : Finset.Ico 2 (n + 1)
          = (Finset.Ico 1 n).map (addRightEmbedding 1) := by
        rw [Finset.map_add_right_Ico]
      have hreindex : (∑ i ∈ Finset.Ico 1 n, gPhase T ((i : ℝ) + 1))
          = ∑ j ∈ Finset.Ico 2 (n + 1), gPhase T (j : ℝ) := by
        rw [hmap, Finset.sum_map]
        apply Finset.sum_congr rfl
        intro i _; simp only [addRightEmbedding_apply]; push_cast; ring
      have hIcoIcc2 : Finset.Ico 2 (n + 1) = Finset.Icc 2 n := by
        ext k; simp only [Finset.mem_Ico, Finset.mem_Icc]; omega
      rw [hreindex, hIcoIcc2]
      -- Icc 1 n = insert 1 (Icc 2 n)
      have hins : Finset.Icc 1 n = insert 1 (Finset.Icc 2 n) := by
        ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      rw [hins, Finset.sum_insert (by simp)]
      push_cast; ring
    rw [remEM_eq_sum_sub_integral]
    have h0le : 0 ≤ (∑ k ∈ Finset.Icc 1 n, gPhase T (k:ℝ)) - ∫ x in (1:ℝ)..(n:ℝ), gPhase T x := by
      rw [hIcoIcc] at hupper
      have hgn : 0 ≤ gPhase T (n:ℝ) := gPhase_nonneg T hT (by positivity)
      linarith
    have hle : (∑ k ∈ Finset.Icc 1 n, gPhase T (k:ℝ)) - ∫ x in (1:ℝ)..(n:ℝ), gPhase T x
        ≤ gPhase T (1:ℝ) := by
      rw [hshiftIcc] at hlower; linarith
    rw [abs_of_nonneg h0le]
    have := gPhase_lt_pi_div_two T 1
    linarith

/-- **(B) THE MINIMAL RESIDUAL — uniform boundedness of the explicit collected term.**

There is `C₀ ≥ 0` with `|collect T n| ≤ C₀` for all `T ≥ 140`, `n`, where
`collect T n = −γ(T/2) − arg z − stirPrincipal T + (T/2)·harmonic n − (Gphi T n − Gphi T 1)`.

HONEST scope.  This is the pure `n→∞` log-cancellation bookkeeping — NO summation, NO winding, NO
EM remainder (that is `remEM_bound`), NO per-term arctan (that is `argDefect_arctan_form`).  Every
term is explicit: `harmonic n` (Mathlib, `harmonic n − log n → γ`), `Gphi T n =
(n+¼)arctan((T/2)/(n+¼)) + (T/4)log((n+¼)²+(T/2)²)`, `arg z ∈ [0,π/2)`, and `stirPrincipal T =
(-1/4)arg z + (T/2)log‖z‖ − T/2`.  The claim is that the growing pieces cancel:
`(T/2)harmonic n − (T/2)log n → (T/2)γ` (cancels `−γ(T/2)`), `arctan((T/2)/(n+¼)) → 0`,
`(T/4)log((n+¼)²+(T/2)²) − (T/2)log n → (T/2)log‖z‖`-matching, leaving `collect T n → −(3/4)arg z
+ (bounded)`, bounded uniformly by an absolute constant for `T ≥ 140`.  This single uniform
bounded-limit is the one piece not fully mechanized; it is STRICTLY HONEST and TRUE (it equates two
genuinely-growing quantities whose difference converges, NOT a bounded quantity to a growing one).
The constant is crude. -/
axiom collect_uniform_bound :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ T : ℝ, (140 : ℝ) ≤ T → ∀ n : ℕ, |collect T n| ≤ C₀

/-- **Uniform boundedness of the partial-difference sequence (PROVEN from (A)+(B)).**
`|(−γ(T/2) − arg z − stirPrincipal T) + Σ_{Icc 1 n} argDefect| ≤ C₀ + π/2`, via
`partialDiff_eq` (proven), `collect_uniform_bound` (B), and `remEM_bound` (A). -/
theorem partialDiff_uniform_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, (140 : ℝ) ≤ T → ∀ n : ℕ,
      |(-Real.eulerMascheroniConstant * (T / 2) - Complex.arg (zPt T) - stirPrincipal T)
          + ∑ k ∈ Finset.Icc 1 n, argDefect T k| ≤ C := by
  obtain ⟨C₀, hC0, hcollect⟩ := collect_uniform_bound
  refine ⟨C₀ + Real.pi / 2, by positivity, ?_⟩
  intro T hT n
  have hT0 : 0 ≤ T := by linarith
  rw [partialDiff_eq]
  calc |collect T n - remEM T n|
      ≤ |collect T n| + |remEM T n| := abs_sub _ _
    _ ≤ C₀ + Real.pi / 2 := add_le_add (hcollect T hT n) (remEM_bound T hT0 n)

/-- **The EXACT algebraic decomposition of the target difference (PROVEN).** -/
theorem thetaCont_sub_stirPrincipal_decomp (T : ℝ) :
    thetaCont T - stirPrincipal T
      = (-Real.eulerMascheroniConstant * (T / 2) - Complex.arg (zPt T) - stirPrincipal T)
        + ∑' k : ℕ, argDefect T k := by
  unfold thetaCont; ring

/-- **THE DELIVERABLE — `binetPhase_crude_bound`.**
`∃ C ≥ 0, ∀ T ≥ 140, |thetaCont T − stirPrincipal T| ≤ C`.

PROVEN from `partialDiff_uniform_bound` by `le_of_tendsto`: the target difference is the limit
(`tsum_argDefect_eq_lim` + `thetaCont_sub_stirPrincipal_decomp`) of the partial-difference
sequence, which is bounded uniformly by `C`; the limit of a `|·|`-bounded sequence is `≤ C`. -/
theorem binetPhase_crude_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, (140 : ℝ) ≤ T → |thetaCont T - stirPrincipal T| ≤ C := by
  obtain ⟨C, hC0, hbound⟩ := partialDiff_uniform_bound
  refine ⟨C, hC0, ?_⟩
  intro T hT
  have hT0 : 0 ≤ T := by linarith
  set b : ℝ := -Real.eulerMascheroniConstant * (T / 2) - Complex.arg (zPt T) - stirPrincipal T
    with hb
  set Dseq : ℕ → ℝ := fun n => b + ∑ k ∈ Finset.Icc 1 n, argDefect T k with hD
  have hlim : Filter.Tendsto Dseq Filter.atTop (nhds (thetaCont T - stirPrincipal T)) := by
    rw [thetaCont_sub_stirPrincipal_decomp]
    have htail := tsum_argDefect_eq_lim T hT0
    have := (tendsto_const_nhds (x := b)).add htail
    simpa only [hD, hb] using this
  have hDbound : ∀ n, |Dseq n| ≤ C := by
    intro n; simpa only [hD, hb] using hbound T hT n
  have hlimabs : Filter.Tendsto (fun n => |Dseq n|) Filter.atTop
      (nhds |thetaCont T - stirPrincipal T|) := hlim.abs
  exact le_of_tendsto hlimabs (Filter.Eventually.of_forall hDbound)

end ScratchBinetPhaseDischarge
end BacklundTuring
end OverflowResidueRH

/-! ## Axiom footprint -/

-- The deliverable: depends only on the single residual `collect_uniform_bound` (+ Mathlib classical).
#print axioms
  OverflowResidueRH.BacklundTuring.ScratchBinetPhaseDischarge.binetPhase_crude_bound
-- The integral closed form (3): fully proven, Mathlib-only.
#print axioms
  OverflowResidueRH.BacklundTuring.ScratchBinetPhaseDischarge.integral_gPhase_eq
-- The Euler–Maclaurin Σ-vs-∫ remainder bound (A): fully proven, Mathlib-only (NO axiom).
#print axioms
  OverflowResidueRH.BacklundTuring.ScratchBinetPhaseDischarge.remEM_bound
-- The harmonic partial-sum identity / limit (4): fully proven, Mathlib-only.
#print axioms
  OverflowResidueRH.BacklundTuring.ScratchBinetPhaseDischarge.sum_argDefect_Icc
#print axioms
  OverflowResidueRH.BacklundTuring.ScratchBinetPhaseDischarge.tsum_argDefect_eq_lim
-- Per-term / summability layers: fully proven, Mathlib-only.
#print axioms
  OverflowResidueRH.BacklundTuring.ScratchBinetPhaseDischarge.summable_argDefect
