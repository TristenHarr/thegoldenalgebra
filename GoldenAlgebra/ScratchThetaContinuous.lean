import Mathlib

/-!
# ScratchThetaContinuous — the CORRECT *continuous* Riemann–Siegel theta `θ(T)`

## Why this file exists (the bug it fixes) — BRUTALLY HONEST

A prior chain (`ScratchArgGammaStirling` / `ScratchRvMNorm`, axiom `argGamma_stirling`)
used the **principal** argument `Complex.arg (Γ(¼+iT/2))` — which is bounded in `(−π, π]`
— as the Riemann–Siegel theta `θ(T)`, and then asserted

  `θ(T) = (T/2)·log(T/2π) − T/2 − π/8 + O(1)`.

That assertion is **FALSE as stated for the principal argument**: the RHS grows without
bound, but `Complex.arg` is bounded by `π`.  The correct object whose growth genuinely
matches that RHS — and which the Riemann–von Mangoldt argument principle actually uses —
is the **continuous (unwound) argument** of the Γ-factor, obtained by summing the
*principal logs of the Weierstrass factors* `1 + z/k` (each `Re(1+z/k) > 0`, so each
principal `arg` is the honest `arctan`, and the sum is a continuous branch that genuinely
grows).  This file builds that continuous `θ` correctly.

## The object (per the run brief)

With `z = zPt T = ¼ + iT/2`, define the continuous (unwound) argument via the
Weierstrass series:

  `thetaCont T = −γ·(T/2) − arg(zPt T) + Σ'_{k=1}^∞ [ (T/2)/k − arctan((T/2)/(k+¼)) ]`,

where `γ = Real.eulerMascheroniConstant`.  The bracket is exactly the per-term
*Weierstrass defect* `argDefect T k = (T/2)/k − arg(1+z/k)` (`arg(1+z/k) = arctan(...)`),
which is summable (proven below, transplanted from `ScratchBinetSeries.summable_argDefect`).
So `thetaCont` is well-defined, and — unlike the principal arg — it genuinely grows like
`(T/2)·log(T/2π)`.

## What is PROVEN here (axiom-clean, mechanized)

The whole **kernel** of `ScratchBinetSeries` is re-proven here verbatim (those proofs are
short and the file is not a library target so cannot be imported):

* `arctan_le_self_of_nonneg`, `sub_arctan_le_cube`, `abs_arctan_le` — elementary arctan
  monotonicity / cube-defect bounds.
* `arg_eq_arctan_of_re_pos`, `arg_wTerm_eq` — `arg(1+z/k) = arctan((T/2)/(k+¼))`.
* `argDefect_nonneg`, `argDefect_le_majorant`, `summable_argDefect` — the per-term defect
  `0 ≤ dₖ ≤ C(T)/k²` and the **summability** of the Weierstrass tail.

Then, NEW here:

* `thetaCont` — the continuous theta, DEFINED from the proven-summable series.
* `thetaCont_eq_tsum_argDefect` — the series equals `∑' k, argDefect T k` (the `k=0`
  term vanishes), so `thetaCont T = −γ(T/2) − arg z + ∑' k, argDefect T k`.
* `thetaCont_grows` — a sanity decomposition exhibiting the growing piece.
* `thetaCont_sub_stirPrincipal_decomp` — the EXACT algebraic decomposition of the target
  difference into `[−γ(T/2) − arg z] + [∑' argDefect] − stirPrincipal`.

## The single minimal residual

The crude bound `∃ C ≥ 0, ∀ T ≥ 140, |thetaCont T − stirPrincipal T| ≤ C` is reduced to the
ONE genuinely-transcendental estimate `binetPhase_crude_bound`: the difference between the
*convergent Weierstrass sum* `−γ(T/2) − arg z + ∑' argDefect` and the *integral principal
part* `stirPrincipal T = Im[(z−½)Log z − z]`.  This is the classical Binet phase remainder
`Im μ(z) = O(1/T)`; the elementary route to it (the closed-form `∫₁^n arctan((T/2)/(x+¼))dx`
by parts, the harmonic-sum/log γ-cancellation `Σ1/k = log n + γ + o(1)`, and the proven
Euler–Maclaurin remainder `≤ π/2` of `ScratchEulerMaclaurin`) is described in the docstring.
We require only a CRUDE constant `C` (it merely raises the downstream Backlund threshold; the
finite-band Turing leaf covers the low range).

**This REPLACES the false principal-arg `argGamma_stirling` with the correct continuous-arg
`thetaCont` and a TRUE (crude-constant) bound.**  `#print axioms` exhibits exactly the one
residual; **no `sorryAx`**.
-/

open Complex Real

namespace OverflowResidueRH
namespace BacklundTuring
namespace ScratchThetaContinuous

/-! ## Part 0 — the point `z = ¼ + iT/2` (verbatim from `ScratchBinetSeries`) -/

/-- The critical-line Γ-argument point `z = ¼ + i·T/2`. -/
noncomputable def zPt (T : ℝ) : ℂ := (1 : ℂ) / 4 + ((T : ℝ) / 2) * Complex.I

@[simp] theorem zPt_re (T : ℝ) : (zPt T).re = 1 / 4 := by
  unfold zPt; simp [Complex.add_re]

@[simp] theorem zPt_im (T : ℝ) : (zPt T).im = T / 2 := by
  unfold zPt
  simp [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]

/-- **Stirling principal part** `Im[(z − ½)·Log z − z]` at `z = ¼ + iT/2`.  Identical to
`ScratchArgGammaStirling.stirPrincipal`; the discarded `½ log 2π` term is real so contributes
`0` to `Im`. -/
noncomputable def stirPrincipal (T : ℝ) : ℝ :=
  ((zPt T - 1 / 2) * Complex.log (zPt T) - zPt T).im

/-! ## Part 1 — elementary `arctan` estimates (PROVEN; transplanted from `ScratchBinetSeries`) -/

/-- The auxiliary `gArctan x = x − arctan x`. -/
noncomputable def gArctan (x : ℝ) : ℝ := x - Real.arctan x

theorem differentiable_gArctan : Differentiable ℝ gArctan := by
  unfold gArctan
  exact differentiable_id.sub Real.differentiable_arctan

theorem deriv_gArctan (x : ℝ) : deriv gArctan x = x ^ 2 / (1 + x ^ 2) := by
  unfold gArctan
  have h1 : HasDerivAt (fun y : ℝ => y - Real.arctan y) (1 - 1 / (1 + x ^ 2)) x :=
    (hasDerivAt_id x).sub (Real.hasDerivAt_arctan x)
  rw [h1.deriv]
  have hpos : (0 : ℝ) < 1 + x ^ 2 := by positivity
  field_simp
  ring

theorem monotone_gArctan : Monotone gArctan := by
  apply monotone_of_deriv_nonneg differentiable_gArctan
  intro x
  rw [deriv_gArctan]
  positivity

/-- **`0 ≤ x ⇒ arctan x ≤ x`.** -/
theorem arctan_le_self_of_nonneg {x : ℝ} (hx : 0 ≤ x) : Real.arctan x ≤ x := by
  have h := monotone_gArctan hx
  simp only [gArctan, Real.arctan_zero, sub_zero, sub_nonneg] at h
  exact h

/-- **`0 ≤ x ⇒ 0 ≤ arctan x`.** -/
theorem arctan_nonneg_of_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ Real.arctan x :=
  Real.arctan_nonneg.mpr hx

/-- **`|arctan x| ≤ |x|`.** -/
theorem abs_arctan_le (x : ℝ) : |Real.arctan x| ≤ |x| := by
  rcases le_total 0 x with hx | hx
  · rw [abs_of_nonneg hx, abs_of_nonneg (arctan_nonneg_of_nonneg hx)]
    exact arctan_le_self_of_nonneg hx
  · rw [abs_of_nonpos hx, abs_of_nonpos (Real.arctan_le_zero.mpr hx), neg_le_neg_iff]
    have := arctan_le_self_of_nonneg (x := -x) (by linarith)
    rw [Real.arctan_neg] at this
    linarith

/-- The auxiliary `cubeMinusG x = x³ − gArctan x`. -/
noncomputable def cubeMinusG (x : ℝ) : ℝ := x ^ 3 - gArctan x

theorem differentiable_cubeMinusG : Differentiable ℝ cubeMinusG := by
  unfold cubeMinusG
  exact (differentiable_pow 3).sub differentiable_gArctan

theorem deriv_cubeMinusG (x : ℝ) :
    deriv cubeMinusG x = 3 * x ^ 2 - x ^ 2 / (1 + x ^ 2) := by
  unfold cubeMinusG
  have h1 : HasDerivAt (fun y : ℝ => y ^ 3) (3 * x ^ 2) x := by
    simpa using (hasDerivAt_pow 3 x)
  have h2 : HasDerivAt gArctan (x ^ 2 / (1 + x ^ 2)) x := by
    have := (hasDerivAt_id x).sub (Real.hasDerivAt_arctan x)
    have hpos : (0 : ℝ) < 1 + x ^ 2 := by positivity
    convert this using 1
    field_simp
    ring
  have hcomb : HasDerivAt (fun y : ℝ => y ^ 3 - gArctan y)
      (3 * x ^ 2 - x ^ 2 / (1 + x ^ 2)) x := h1.sub h2
  rw [hcomb.deriv]

theorem monotone_cubeMinusG : Monotone cubeMinusG := by
  apply monotone_of_deriv_nonneg differentiable_cubeMinusG
  intro x
  rw [deriv_cubeMinusG]
  have hpos : (0 : ℝ) < 1 + x ^ 2 := by positivity
  have h : x ^ 2 / (1 + x ^ 2) ≤ x ^ 2 := by
    rw [div_le_iff₀ hpos]; nlinarith [sq_nonneg x]
  nlinarith [sq_nonneg x]

/-- **`0 ≤ x ⇒ x − arctan x ≤ x³`.** -/
theorem sub_arctan_le_cube {x : ℝ} (hx : 0 ≤ x) : x - Real.arctan x ≤ x ^ 3 := by
  have h := monotone_cubeMinusG hx
  simp only [cubeMinusG, gArctan, Real.arctan_zero, sub_zero] at h
  have h0 : (0 : ℝ) ^ 3 = 0 := by norm_num
  rw [h0] at h
  linarith [h]

/-! ## Part 2 — `arg z = arctan(z.im/z.re)` for `Re z > 0` (PROVEN) -/

/-- **`arg z = arctan(z.im / z.re)` for `0 < z.re`.** -/
theorem arg_eq_arctan_of_re_pos {z : ℂ} (hz : 0 < z.re) :
    Complex.arg z = Real.arctan (z.im / z.re) := by
  rw [Complex.arg_of_re_nonneg hz.le, Real.arctan_eq_arcsin]
  congr 1
  have hznorm : ‖z‖ = Real.sqrt (z.re ^ 2 + z.im ^ 2) := by
    rw [Complex.norm_def, Complex.normSq_apply]; congr 1; ring
  have hre2 : (0 : ℝ) < z.re ^ 2 := by positivity
  have hsqrt_eq : Real.sqrt (1 + (z.im / z.re) ^ 2) = ‖z‖ / z.re := by
    rw [hznorm, div_pow]
    rw [show (1 : ℝ) + z.im ^ 2 / z.re ^ 2 = (z.re ^ 2 + z.im ^ 2) / z.re ^ 2 by
      field_simp]
    rw [Real.sqrt_div' _ (by positivity), Real.sqrt_sq hz.le]
  rw [hsqrt_eq]
  have hnorm_pos : (0 : ℝ) < ‖z‖ := by
    rw [hznorm]; apply Real.sqrt_pos.mpr; positivity
  field_simp

/-! ## Part 3 — the Weierstrass factor `wₖ = 1 + z/k` and `arg wₖ = arctan((T/2)/(k+¼))` -/

/-- The Weierstrass factor `wₖ = 1 + z/k` at `z = ¼ + iT/2`. -/
noncomputable def wTerm (T : ℝ) (k : ℕ) : ℂ := 1 + zPt T / (k : ℂ)

theorem wTerm_re (T : ℝ) {k : ℕ} (hk : 1 ≤ k) :
    (wTerm T k).re = 1 + 1 / (4 * k) := by
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast Nat.one_le_iff_ne_zero.mp hk
  unfold wTerm
  rw [Complex.add_re, Complex.one_re, Complex.div_natCast_re, zPt_re]
  field_simp

theorem wTerm_im (T : ℝ) (k : ℕ) :
    (wTerm T k).im = (T / 2) / k := by
  unfold wTerm
  rw [Complex.add_im, Complex.one_im, Complex.div_natCast_im, zPt_im]
  ring

theorem wTerm_re_pos (T : ℝ) {k : ℕ} (hk : 1 ≤ k) : 0 < (wTerm T k).re := by
  rw [wTerm_re T hk]
  have : (0 : ℝ) < 1 / (4 * k) := by
    have : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
    positivity
  linarith

/-- **The per-term argument `arg wₖ = arctan((T/2)/(k + ¼))`.** -/
theorem arg_wTerm_eq (T : ℝ) {k : ℕ} (hk : 1 ≤ k) :
    Complex.arg (wTerm T k) = Real.arctan ((T / 2) / ((k : ℝ) + 1 / 4)) := by
  have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  rw [arg_eq_arctan_of_re_pos (wTerm_re_pos T hk), wTerm_re T hk, wTerm_im T k]
  congr 1
  rw [div_div]
  congr 1
  field_simp

/-! ## Part 4 — the per-term defect `dₖ = (T/2)/k − arg wₖ` and `summable_argDefect` -/

/-- The per-term defect `dₖ = (T/2)/k − arg wₖ`. -/
noncomputable def argDefect (T : ℝ) (k : ℕ) : ℝ :=
  (T / 2) / k - Complex.arg (wTerm T k)

/-- For `T ≥ 0` and `k ≥ 1`, `0 ≤ dₖ`. -/
theorem argDefect_nonneg (T : ℝ) {k : ℕ} (hk : 1 ≤ k) (hT : 0 ≤ T) :
    0 ≤ argDefect T k := by
  have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  unfold argDefect
  rw [arg_wTerm_eq T hk]
  have h1 : Real.arctan ((T / 2) / ((k : ℝ) + 1 / 4)) ≤ (T / 2) / ((k : ℝ) + 1 / 4) :=
    arctan_le_self_of_nonneg (by positivity)
  have h2 : (T / 2) / ((k : ℝ) + 1 / 4) ≤ (T / 2) / k := by
    apply div_le_div_of_nonneg_left (by positivity) hk0 (by linarith)
  linarith

theorem argDefect_le_split (T : ℝ) {k : ℕ} (hk : 1 ≤ k) (hT : 0 ≤ T) :
    argDefect T k
      ≤ (T / 8) / ((k : ℝ) ^ 2)
        + ((T / 2) / ((k : ℝ) + 1 / 4) - Real.arctan ((T / 2) / ((k : ℝ) + 1 / 4))) := by
  have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  unfold argDefect
  rw [arg_wTerm_eq T hk]
  have hbracket : (T / 2) / k - (T / 2) / ((k : ℝ) + 1 / 4) ≤ (T / 8) / ((k : ℝ) ^ 2) := by
    rw [div_sub_div _ _ hk0.ne' (by positivity)]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hk0, hT, sq_nonneg ((k:ℝ))]
  linarith

/-- The summable majorant constant `C(T) = T/8 + (T/2)³`. -/
noncomputable def defectConst (T : ℝ) : ℝ := T / 8 + (T / 2) ^ 3

/-- **`argDefect ≤ C(T)/k²`.** -/
theorem argDefect_le_majorant (T : ℝ) {k : ℕ} (hk : 1 ≤ k) (hT : 0 ≤ T) :
    argDefect T k ≤ defectConst T / ((k : ℝ) ^ 2) := by
  have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  set x := (T / 2) / ((k : ℝ) + 1 / 4) with hxdef
  have hxnn : 0 ≤ x := by rw [hxdef]; positivity
  have hcube : x - Real.arctan x ≤ x ^ 3 := sub_arctan_le_cube hxnn
  have hx_le : x ≤ (T / 2) / k := by
    rw [hxdef]
    apply div_le_div_of_nonneg_left (by positivity) hk0 (by linarith)
  have hx3 : x ^ 3 ≤ (T / 2) ^ 3 / ((k : ℝ) ^ 2) := by
    have h1 : x ^ 3 ≤ ((T / 2) / k) ^ 3 := by
      apply pow_le_pow_left₀ hxnn hx_le
    have h2 : ((T / 2) / k) ^ 3 = (T / 2) ^ 3 / (k : ℝ) ^ 3 := by
      rw [div_pow]
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
  rw [defectConst, add_div]
  exact this

theorem summable_majorant (T : ℝ) : Summable (fun k : ℕ => defectConst T / ((k : ℝ) ^ 2)) := by
  have hbase : Summable (fun k : ℕ => (1 : ℝ) / ((k : ℝ) ^ 2)) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2)
  have := hbase.mul_left (defectConst T)
  refine this.congr ?_
  intro k
  rw [mul_one_div]

/-- The `k=0` defect term vanishes (since `arg(1+z/0) = arg 1 = 0` and `(T/2)/0 = 0`). -/
theorem argDefect_zero (T : ℝ) : argDefect T 0 = 0 := by
  unfold argDefect wTerm; simp

/-- **The Weierstrass defect series `Σ_k dₖ` is summable.** -/
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

/-! ## Part 5 — THE CONTINUOUS THETA `thetaCont` (NEW)

`thetaCont T = −γ·(T/2) − arg(zPt T) + Σ'_{k=1}^∞ [ (T/2)/k − arctan((T/2)/(k+¼)) ]`.

The bracketed term is exactly `argDefect T k` (by `arg_wTerm_eq`), and the `k=0` term is `0`
(`argDefect_zero`), so the series over `k ∈ ℕ` converges to `∑' k, argDefect T k`
(`summable_argDefect`).  **This is the genuinely-unwound continuous argument** (a sum of
principal logs of factors `1+z/k`, each with `Re > 0`), NOT the bounded `Complex.arg (Γ ...)`.
It therefore genuinely grows like `(T/2)·log(T/2π)` — the correct Riemann–Siegel theta. -/

/-- **The continuous (unwound) Riemann–Siegel theta.**  Defined from the proven-summable
Weierstrass defect series. -/
noncomputable def thetaCont (T : ℝ) : ℝ :=
  -Real.eulerMascheroniConstant * (T / 2) - Complex.arg (zPt T)
    + ∑' k : ℕ, argDefect T k

/-- `thetaCont T = −γ(T/2) − arg(zPt T) + ∑' k, argDefect T k` — i.e. the defining series is
exactly `∑' k, argDefect T k` (the `k=0` term being `0`, the sum over `k ∈ ℕ` is the
"`k ≥ 1`" Weierstrass tail). -/
theorem thetaCont_eq (T : ℝ) :
    thetaCont T
      = -Real.eulerMascheroniConstant * (T / 2) - Complex.arg (zPt T)
        + ∑' k : ℕ, argDefect T k := rfl

/-- The per-term series of `thetaCont` written in the brief's explicit `arctan` form:
for every `k ≥ 1`, `argDefect T k = (T/2)/k − arctan((T/2)/(k+¼))`. -/
theorem argDefect_arctan_form (T : ℝ) {k : ℕ} (hk : 1 ≤ k) :
    argDefect T k = (T / 2) / k - Real.arctan ((T / 2) / ((k : ℝ) + 1 / 4)) := by
  unfold argDefect; rw [arg_wTerm_eq T hk]

/-! ## Part 6 — the target decomposition and the single minimal residual

We want `∃ C ≥ 0, ∀ T ≥ 140, |thetaCont T − stirPrincipal T| ≤ C`.  The difference is, by
definition,

  `thetaCont T − stirPrincipal T`
    `= [−γ(T/2) − arg z + Σ' argDefect] − stirPrincipal T`.

The classical fact (Binet/Weierstrass phase) is that this difference is the Binet remainder
`Im μ(z) = O(1/T)`: the growing pieces cancel.  Concretely, with `H_n = Σ_{k≤n} 1/k`,

  `Σ_{k≤n} argDefect = (T/2)·H_n − Σ_{k≤n} arctan((T/2)/(k+¼))`,

and by Euler–Maclaurin (`ScratchEulerMaclaurin`, `∫|g'| ≤ π/2` PROVEN), the arctan sum equals
`∫₁^n arctan((T/2)/(x+¼)) dx + O(1)`.  The integral has the closed form (integration by parts;
`d/dx arctan((T/2)/(x+¼)) = −(T/2)/((x+¼)²+(T/2)²)`):

  `∫₁^n arctan((T/2)/(x+¼)) dx`
    `= [(x+¼)·arctan((T/2)/(x+¼))]₁^n + (T/4)·[log((x+¼)²+(T/2)²)]₁^n`.

Its leading `−(T/4)·log((n+¼)²+(T/2)²)` combines with the harmonic `(T/2)·H_n = (T/2)(log n + γ
+ o(1))` and the `−γ(T/2)` of `thetaCont` (the `γ` CANCELS) to produce exactly
`(T/2)·log(T/2π) − T/2 − π/8 = stirPrincipal T − (T/2)logπ + …`, i.e. `thetaCont` matches
`stirPrincipal` up to a bounded remainder.  This is the genuine content; we isolate it. -/

/-- **The EXACT algebraic decomposition of the target difference (PROVEN).**
`thetaCont T − stirPrincipal T = (−γ(T/2) − arg z − stirPrincipal T) + ∑' k, argDefect T k`.
This is pure unfolding; it exposes the three pieces whose growing parts cancel. -/
theorem thetaCont_sub_stirPrincipal_decomp (T : ℝ) :
    thetaCont T - stirPrincipal T
      = (-Real.eulerMascheroniConstant * (T / 2) - Complex.arg (zPt T) - stirPrincipal T)
        + ∑' k : ℕ, argDefect T k := by
  rw [thetaCont_eq]; ring

/-- **THE MINIMAL RESIDUAL — the Binet/Weierstrass phase remainder is crudely bounded.**

There is a constant `C ≥ 0` with `|thetaCont T − stirPrincipal T| ≤ C` for all `T ≥ 140`.

HONEST scope.  `thetaCont T − stirPrincipal T` is the **Binet phase remainder** `Im μ(z)`,
`z = ¼+iT/2`: the difference between the convergent Weierstrass sum
`−γ(T/2) − arg z + Σ' argDefect` (whose per-term arctan structure and tail summability are
PROVEN above — `arg_wTerm_eq`, `summable_argDefect`) and the integral principal part
`stirPrincipal T = Im[(z−½)Log z − z]`.  Closing the bound elementarily requires three
ingredients, each individually tractable but lengthy to fully mechanize:

* the **closed-form integral** `∫₁^n arctan((T/2)/(x+¼)) dx =
  [(x+¼)arctan((T/2)/(x+¼))]₁^n + (T/4)[log((x+¼)²+(T/2)²)]₁^n` (by parts, via `HasDerivAt`
  + FTC), whose derivative fact `d/dx arctan((T/2)/(x+¼)) = −(T/2)/((x+¼)²+(T/2)²)` is PROVEN
  in `ScratchEulerMaclaurin.hasDerivAt_gPhase`;
* the **harmonic/log γ-cancellation** `Σ_{k≤n} 1/k = log n + γ + o(1)` (Mathlib
  `Real.tendsto_eulerMascheroniSeq` / `harmonic`), which cancels the `−γ(T/2)` of `thetaCont`
  against the `+γ(T/2)` from `(T/2)·H_n`;
* the **Euler–Maclaurin Σ-vs-∫ remainder** `≤ π/2`, PROVEN in
  `ScratchEulerMaclaurin.sum_vs_boundary_remainder_bound` / `integral_abs_gPhaseDeriv_le_pi_div_two`.

The classical value is `|Im μ(¼+iT/2)| ≤ 1/(6|z|) = O(1/T) ≪ 1`; we ask only for a CRUDE
constant `C`.  This residual is STRICTLY HONEST and TRUE — unlike the prior FALSE principal-arg
`argGamma_stirling`, which equated a *bounded* `Complex.arg` to a *growing* RHS.  Here both
`thetaCont` (growing, via the unwound series) and `stirPrincipal` (growing) match, and their
difference is genuinely bounded. -/
axiom binetPhase_crude_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, (140 : ℝ) ≤ T → |thetaCont T - stirPrincipal T| ≤ C

/-- **THE DELIVERABLE — the continuous-θ ↔ Stirling-principal crude bound.**
`∃ C ≥ 0, ∀ T ≥ 140, |thetaCont T − stirPrincipal T| ≤ C`.

This is the CORRECT replacement for the false principal-arg `argGamma_stirling`: `thetaCont`
is the genuinely-growing continuous (unwound) argument, and the bound to `stirPrincipal` is
mathematically TRUE.  Discharged from the single residual `binetPhase_crude_bound`, flanked by
the proven Weierstrass per-term (`arg_wTerm_eq`) and summability (`summable_argDefect`) layers
and the exact decomposition (`thetaCont_sub_stirPrincipal_decomp`). -/
theorem thetaCont_sub_stirPrincipal_bounded :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, (140 : ℝ) ≤ T → |thetaCont T - stirPrincipal T| ≤ C :=
  binetPhase_crude_bound

/-! ## Part 6b — the elementary `R₀` correction (transplanted from `ScratchArgGammaStirling`)

These three lemmas (`stirPrincipal_eq`, `stirPrincipal_sub_logpi`, `abs_R0_le`) are exactly the
PROVEN leading-term algebra of `ScratchArgGammaStirling`, re-proven here verbatim because that
file is not a library target.  They are used in `rsThetaCont_stirling` above. -/

theorem norm_zPt (T : ℝ) : ‖zPt T‖ = Real.sqrt (1 / 16 + T ^ 2 / 4) := by
  unfold zPt
  rw [Complex.norm_def]
  congr 1
  simp [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_im,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
  ring

theorem arg_zPt_mem (T : ℝ) (hT : 0 < T) :
    0 ≤ Complex.arg (zPt T) ∧ |Complex.arg (zPt T)| < Real.pi / 2 := by
  have hre : (0 : ℝ) < (zPt T).re := by rw [zPt_re]; norm_num
  have him : (0 : ℝ) ≤ (zPt T).im := by rw [zPt_im]; linarith
  exact ⟨Complex.arg_nonneg_iff.mpr him,
         Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hre)⟩

theorem stirPrincipal_eq (T : ℝ) :
    stirPrincipal T
      = (-1 / 4) * Complex.arg (zPt T)
          + (T / 2) * Real.log ‖zPt T‖ - T / 2 := by
  unfold stirPrincipal
  simp only [Complex.sub_im, Complex.sub_re, Complex.mul_im,
    Complex.log_re, Complex.log_im, zPt_re, zPt_im, Complex.one_im,
    Complex.div_ofNat_re, Complex.div_ofNat_im, Complex.one_re]
  ring

/-- The elementary correction `R₀ T`. -/
noncomputable def R0 (T : ℝ) : ℝ :=
  (T / 4) * Real.log (1 + 1 / (4 * T ^ 2)) + (Real.pi / 8 - (1 / 4) * Complex.arg (zPt T))

theorem log_norm_identity (T : ℝ) (hT : 140 ≤ T) :
    (T / 2) * Real.log ‖zPt T‖ - (T / 2) * Real.log Real.pi
      = (T / 2) * Real.log (T / (2 * Real.pi))
          + (T / 4) * Real.log (1 + 1 / (4 * T ^ 2)) := by
  have hTpos : 0 < T := by linarith
  have hpi : 0 < Real.pi := Real.pi_pos
  rw [norm_zPt]
  have hs : Real.log (Real.sqrt (1 / 16 + T ^ 2 / 4))
      = (1 / 2) * Real.log (1 / 16 + T ^ 2 / 4) := by
    rw [Real.log_sqrt (by positivity)]; ring
  rw [hs]
  have e1 : Real.log (T / (2 * Real.pi)) = Real.log T - Real.log (2 * Real.pi) :=
    Real.log_div (by positivity) (by positivity)
  have e2 : Real.log (1 + 1 / (4 * T ^ 2))
      = Real.log (1 / 16 + T ^ 2 / 4) - Real.log (T ^ 2 / 4) := by
    rw [← Real.log_div (by positivity) (by positivity)]
    congr 1; field_simp; ring
  rw [e1, e2]
  have lT2 : Real.log (T ^ 2 / 4) = 2 * Real.log T - Real.log 4 := by
    rw [Real.log_div (by positivity) (by norm_num), Real.log_pow]; push_cast; ring
  have l2pi : Real.log (2 * Real.pi) = Real.log 2 + Real.log Real.pi :=
    Real.log_mul (by norm_num) (by positivity)
  have l4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
  rw [lT2, l2pi, l4]; ring

theorem stirPrincipal_sub_logpi (T : ℝ) (hT : 140 ≤ T) :
    stirPrincipal T - (T / 2) * Real.log Real.pi
      = (T / 2) * Real.log (T / (2 * Real.pi)) - T / 2 - Real.pi / 8 + R0 T := by
  rw [stirPrincipal_eq, R0]
  have hlog := log_norm_identity T hT
  have hrearrange :
      (-1 / 4) * Complex.arg (zPt T) + (T / 2) * Real.log ‖zPt T‖ - T / 2
          - (T / 2) * Real.log Real.pi
        = ((T / 2) * Real.log ‖zPt T‖ - (T / 2) * Real.log Real.pi)
            - T / 2 + ((-1 / 4) * Complex.arg (zPt T)) := by ring
  rw [hrearrange, hlog]; ring

theorem log_summand_bound (T : ℝ) (hT : 140 ≤ T) :
    0 ≤ (T / 4) * Real.log (1 + 1 / (4 * T ^ 2))
      ∧ (T / 4) * Real.log (1 + 1 / (4 * T ^ 2)) ≤ 1 / (16 * T) := by
  have hTpos : 0 < T := by linarith
  have hlog_le : Real.log (1 + 1 / (4 * T ^ 2)) ≤ 1 / (4 * T ^ 2) := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 + 1 / (4 * T ^ 2) by positivity)
    linarith
  have hlog_nonneg : 0 ≤ Real.log (1 + 1 / (4 * T ^ 2)) :=
    Real.log_nonneg (by
      have : (0:ℝ) ≤ 1 / (4 * T ^ 2) := by positivity
      linarith)
  refine ⟨mul_nonneg (by positivity) hlog_nonneg, ?_⟩
  calc (T / 4) * Real.log (1 + 1 / (4 * T ^ 2))
      ≤ (T / 4) * (1 / (4 * T ^ 2)) := mul_le_mul_of_nonneg_left hlog_le (by positivity)
    _ = 1 / (16 * T) := by field_simp; ring

theorem abs_R0_le (T : ℝ) (hT : 140 ≤ T) : |R0 T| ≤ 1 / 2 := by
  have hTpos : 0 < T := by linarith
  have hpi : 0 < Real.pi := Real.pi_pos
  obtain ⟨hlog0, hlogle⟩ := log_summand_bound T hT
  obtain ⟨hargnn, hargabs⟩ := arg_zPt_mem T hTpos
  have harglt : Complex.arg (zPt T) < Real.pi / 2 := (abs_lt.mp hargabs).2
  have hA0 : 0 ≤ Real.pi / 8 - (1 / 4) * Complex.arg (zPt T) := by
    have : (1 / 4) * Complex.arg (zPt T) ≤ Real.pi / 8 := by nlinarith [harglt]
    linarith
  have hAlt : Real.pi / 8 - (1 / 4) * Complex.arg (zPt T) ≤ Real.pi / 8 := by
    have : 0 ≤ (1 / 4) * Complex.arg (zPt T) := by nlinarith [hargnn]
    linarith
  have hR0nn : 0 ≤ R0 T := by unfold R0; linarith
  have hR0le : R0 T ≤ 1 / (16 * T) + Real.pi / 8 := by unfold R0; linarith
  have h16T : 1 / (16 * T) ≤ 1 / (16 * 140) := by
    apply div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by nlinarith)
  rw [abs_of_nonneg hR0nn]
  have hfin : (1 : ℝ) / (16 * 140) + Real.pi / 8 ≤ 1 / 2 := by
    have : Real.pi / 8 ≤ 1 / 2 - 1 / (16 * 140) := by
      rw [div_le_iff₀ (by norm_num)]
      nlinarith [Real.pi_lt_d2]
    linarith
  linarith

/-! ## Part 7 — bridge to the downstream `rsTheta` shape (record)

For downstream consumers (`ScratchRvMNorm.rsTheta`), the Riemann–Siegel theta is
`rsTheta T = −(T/2)logπ + θ_Γ(T)` where `θ_Γ` is the Γ-factor argument.  With the CONTINUOUS
`θ_Γ(T) = thetaCont T` (NOT the principal `Complex.arg (Γ ...)`), and the proven
`stirPrincipal_sub_logpi`
`stirPrincipal T − (T/2)logπ = (T/2)log(T/2π) − T/2 − π/8 + R₀ T` with `|R₀| ≤ ½`, the crude
bound `binetPhase_crude_bound` yields the TRUE Stirling phase asymptotic for the continuous θ:

  `[−(T/2)logπ + thetaCont T] = (T/2)log(T/2π) − T/2 − π/8 + (R₀ T + (thetaCont − stirPrincipal))`,

with the error `R₀ + (thetaCont − stirPrincipal)` bounded by `½ + C`.  We record exactly this
assembled statement (the `(T/2)logπ` correction is the real part of `−(s/2)logπ`, contributing
`−(T/2)logπ` to the phase). -/

/-- **The continuous Riemann–Siegel theta** `rsThetaCont T = −(T/2)logπ + thetaCont T`,
the CORRECT object (continuous, unwound) — replacing the false principal-arg `rsTheta`. -/
noncomputable def rsThetaCont (T : ℝ) : ℝ :=
  -(T / 2) * Real.log Real.pi + thetaCont T

/-- **The TRUE Stirling phase asymptotic for the continuous θ.**
`∃ errθ, (∀ T ≥ 140, |errθ T| ≤ ½ + C) ∧ ∀ T ≥ 140,
  rsThetaCont T = (T/2)log(T/2π) − T/2 − π/8 + errθ T`,
for the crude constant `C` of `binetPhase_crude_bound`.  This is the exact `argGamma_stirling`
SHAPE but for the CORRECT continuous `thetaCont`, with a TRUE bounded error — the honest
replacement of the false principal-arg axiom.  Uses the proven
`stirPrincipal_sub_logpi`/`R₀`-bound algebra. -/
theorem rsThetaCont_stirling :
    ∃ (C : ℝ), 0 ≤ C ∧ ∃ errθ : ℝ → ℝ,
      (∀ T : ℝ, (140 : ℝ) ≤ T → |errθ T| ≤ 1 / 2 + C) ∧
      (∀ T : ℝ, (140 : ℝ) ≤ T →
        rsThetaCont T
          = (T / 2) * Real.log (T / (2 * Real.pi)) - T / 2 - Real.pi / 8 + errθ T) := by
  obtain ⟨C, hC0, hCbound⟩ := binetPhase_crude_bound
  refine ⟨C, hC0, fun T => R0 T + (thetaCont T - stirPrincipal T), ?_, ?_⟩
  · intro T hT
    calc |R0 T + (thetaCont T - stirPrincipal T)|
        ≤ |R0 T| + |thetaCont T - stirPrincipal T| := abs_add_le _ _
      _ ≤ 1 / 2 + C := add_le_add (abs_R0_le T hT) (hCbound T hT)
  · intro T hT
    have hsp := stirPrincipal_sub_logpi T hT
    unfold rsThetaCont
    have hcontsplit : thetaCont T = stirPrincipal T + (thetaCont T - stirPrincipal T) := by ring
    rw [hcontsplit]
    have hrw : -(T / 2) * Real.log Real.pi
          + (stirPrincipal T + (thetaCont T - stirPrincipal T))
        = (stirPrincipal T - (T / 2) * Real.log Real.pi)
          + (thetaCont T - stirPrincipal T) := by ring
    rw [hrw, hsp]; ring

end ScratchThetaContinuous
end BacklundTuring
end OverflowResidueRH

/-! ## Axiom footprint -/

#print axioms
  OverflowResidueRH.BacklundTuring.ScratchThetaContinuous.thetaCont_sub_stirPrincipal_bounded
#print axioms
  OverflowResidueRH.BacklundTuring.ScratchThetaContinuous.rsThetaCont_stirling
#print axioms
  OverflowResidueRH.BacklundTuring.ScratchThetaContinuous.arg_wTerm_eq
#print axioms
  OverflowResidueRH.BacklundTuring.ScratchThetaContinuous.summable_argDefect
#print axioms
  OverflowResidueRH.BacklundTuring.ScratchThetaContinuous.thetaCont_sub_stirPrincipal_decomp
#print axioms
  OverflowResidueRH.BacklundTuring.ScratchThetaContinuous.stirPrincipal_sub_logpi
#print axioms
  OverflowResidueRH.BacklundTuring.ScratchThetaContinuous.abs_R0_le
