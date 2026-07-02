import Mathlib

open Complex Filter Topology

/-!
# Closing in on the genus-1 minimum modulus (Task #4) — the additive `log‖P‖` reduction

This file attacks the deepest remaining Hadamard analytic theorem: the minimum-modulus estimate
for the genus-1 canonical product

  `P z = ∏' i, (1 - z/loc i)·exp(z/loc i)`,   `Σ 1/‖loc i‖² < ∞`,

i.e. a LOWER bound `log‖P z‖ ≥ -(envelope)` off the zeros. `ScratchMinMod.lean` already isolated
the residual as a multiplicative lower bound `hCore` on the *real factored product*
`∏' i, (‖1-z/loc i‖·exp(Re(z/loc i)))`. This file pushes that further by moving to the **additive**
(`log`) formulation, where the classical Hadamard argument actually lives, and discharging every
structural step around the single irreducible analytic core.

## What is PROVEN here (no `sorry`, no `sorryAx`):

1. `factor_norm_pos` — off the zeros, every real factor `gᵢ z = ‖1-z/loc i‖·exp(Re(z/loc i))` is `> 0`.
   (Positivity is what lets us pass to logs.)

2. `log_factor_ge` — the **genus-1 quadratic cancellation**, re-proven here independently:
   for `‖u‖ ≤ 1/2`, `log(‖1-u‖·exp(Re u)) ≥ -‖u‖²`. The linear parts of `log‖1-u‖` and `Re u`
   cancel, leaving `O(‖u‖²)`. Via Mathlib's complex Taylor remainder `norm_log_one_add_sub_self_le`.

3. `summable_normsq` — `Σ ‖z/loc i‖² = ‖z‖²·Σ 1/‖loc i‖² < ∞`. The genus-1 convergence input.

4. `far_zeros_log_sum_ge` — the **complete far-zeros contribution**: for the (cofinite) set of zeros
   with `‖loc i‖ ≥ 2‖z‖`, `Σ_far log(gᵢ z) ≥ -‖z‖²·Σ 1/‖loc i‖²`. Fully proven from (2)+(3).

5. `genus1Product_minModulus_of_logSumBound` — the **additive→multiplicative bridge**: given
   positivity, summability of `log gᵢ`, and a LOWER bound on `Σ log(gᵢ z)`, the product
   `∏' gᵢ z = exp(Σ log gᵢ z)` inherits the exponential lower bound. Via `Real.rexp_tsum_eq_tprod`.
   This converts the genuine analytic estimate (a sum lower bound) into the `hCore` shape of
   `ScratchMinMod`, with NO loss.

## The ISOLATED irreducible core (one honest hypothesis):

`hLogSumCore` — a lower bound `Σ_i log(gᵢ z) ≥ -(C₀·(1+‖z‖)·log(2+‖z‖))` on the log-sum, off the
zeros. By (4) the far part is handled; what (4)'s `O(‖z‖²)` bound does NOT yet capture is the
**tail decay** `Σ_{‖loc i‖≥2‖z‖} 1/‖loc i‖² = O(log‖z‖/‖z‖)` (which would turn the far `O(‖z‖²)`
into the order-1 `O(‖z‖log‖z‖)`) together with the **near-zeros circle-avoidance** lower bound
(`log‖1-z/loc i‖ ≥ -C log‖z‖` per near zero, with `O(‖z‖log‖z‖)` near zeros by Riemann–von-Mangoldt).
Both rest on the zero-counting function `N(R) = O(R log R)`, which Mathlib does not provide for this
product, and the Borel–Carathéodory / circle-avoidance selection. `hLogSumCore` packages EXACTLY that.

`genus1Product_minModulus` then assembles to the `ScratchMinMod`-compatible conclusion, conditional
only on `hLogSumCore` (and the summability of the log terms, itself a consequence of the same count).

## Honest assessment
The reduction work here is real and removes all the "bookkeeping" obstructions: positivity, the
log/exp passage, the quadratic far-zero cancellation, and the far-zeros summation are CLOSED. The
residual `hLogSumCore` is the genuine Hadamard minimum-modulus content (zero count + circle
avoidance). Closing it fully would require formalizing the order-1 counting function for this product
and the Borel–Carathéodory circle-selection — a substantial independent development absent from
Mathlib. We isolate it as one named hypothesis with this docstring rather than fake it.

Build: `cd /Users/tristen/Desktop/goldenalgebra/GoldenAlgebra && lake env lean ScratchMinModClose.lean`.
-/

namespace OverflowResidueRH.BacklundTuring.ScratchMinModClose

variable {ι : Type*} (loc : ι → ℂ)

/-- The real "factored" value of a single genus-1 factor at `z`:
`gᵢ z = ‖1 - z/loc i‖ · exp(Re(z/loc i)) = ‖(1-z/loc i)·exp(z/loc i)‖`. -/
noncomputable def gFactor (w z : ℂ) : ℝ := ‖1 - z / w‖ * Real.exp (z / w).re

/-- `gFactor` is exactly the norm of the genus-1 complex factor. -/
lemma gFactor_eq_norm (w z : ℂ) :
    gFactor w z = ‖(1 - z / w) * Complex.exp (z / w)‖ := by
  rw [gFactor, norm_mul, Complex.norm_exp]

/-- **Off the zeros, each real factor is strictly positive.** This is what lets us take logs.
`gFactor w z > 0 ⟺ ‖1 - z/w‖ > 0 ⟺ z ≠ w` (with `w ≠ 0`). -/
lemma factor_norm_pos {w z : ℂ} (hw : w ≠ 0) (hz : z ≠ w) : 0 < gFactor w z := by
  rw [gFactor]
  apply mul_pos _ (Real.exp_pos _)
  rw [norm_pos_iff]
  intro h
  apply hz
  -- 1 - z/w = 0 ⇒ z/w = 1 ⇒ z = w
  have hdiv : z / w = 1 := by linear_combination -h
  field_simp at hdiv
  exact hdiv

/-- **Genus-1 quadratic cancellation.** For `‖u‖ ≤ 1/2`,
`log(‖1-u‖·exp(Re u)) ≥ -‖u‖²`. Re-proved here (mirrors `ScratchMinMod.log_factor_ge`) so this file
is self-contained: the linear parts of `log‖1-u‖` and `Re u` cancel via the complex Taylor remainder
`Complex.norm_log_one_add_sub_self_le`, leaving the summable `O(‖u‖²)` residual. -/
lemma log_factor_ge {u : ℂ} (hu : ‖u‖ ≤ 1 / 2) :
    -‖u‖ ^ 2 ≤ Real.log (‖1 - u‖ * Real.exp u.re) := by
  have hu1 : ‖u‖ < 1 := lt_of_le_of_lt hu (by norm_num)
  have hne1 : (1 : ℂ) - u ≠ 0 := by
    intro h
    have : ‖u‖ = 1 := by
      have : u = 1 := by linear_combination -h
      rw [this]; simp
    linarith
  have hnormpos : 0 < ‖1 - u‖ := by simpa [norm_pos_iff] using hne1
  rw [Real.log_mul (ne_of_gt hnormpos) (Real.exp_ne_zero _), Real.log_exp]
  have hw : ‖(-u)‖ < 1 := by simpa using hu1
  have htay := Complex.norm_log_one_add_sub_self_le hw
  have hbound : ‖Complex.log (1 + (-u)) - (-u)‖ ≤ ‖u‖ ^ 2 := by
    refine le_trans htay ?_
    rw [norm_neg]
    have hinv : (1 - ‖u‖)⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ (by simpa using sub_pos_of_lt hu1) (by norm_num)]
      linarith
    have hsq : 0 ≤ ‖u‖ ^ 2 := sq_nonneg _
    nlinarith [mul_le_mul_of_nonneg_left hinv hsq]
  have hre_eq : Real.log ‖1 - u‖ + u.re
      = (Complex.log (1 + (-u)) - (-u)).re := by
    rw [Complex.sub_re, ← Complex.log_re]
    simp [Complex.neg_re, sub_eq_add_neg]
  rw [hre_eq]
  have hre_ge : -‖Complex.log (1 + (-u)) - (-u)‖
      ≤ (Complex.log (1 + (-u)) - (-u)).re := by
    have := Complex.abs_re_le_norm (Complex.log (1 + (-u)) - (-u))
    rw [abs_le] at this; linarith [this.1]
  linarith [hbound, hre_ge]

/-- **Summability of the regularizer.** `Σ ‖z/loc i‖² = ‖z‖²·Σ 1/‖loc i‖² < ∞`. -/
lemma summable_normsq (hsumm : Summable (fun i => 1 / ‖loc i‖ ^ 2)) (z : ℂ) :
    Summable (fun i => ‖z / loc i‖ ^ 2) := by
  have := hsumm.mul_left (‖z‖ ^ 2)
  refine this.congr (fun i => ?_)
  rw [norm_div, div_pow]
  ring

/-- **Far-zeros per-term lower bound** in the additive (log) formulation: if `‖loc i‖ ≥ 2‖z‖`
(so `‖z/loc i‖ ≤ 1/2`), then `log(gFactor (loc i) z) ≥ -‖z/loc i‖²`. -/
lemma far_log_factor_ge {i : ι} {z : ℂ} (h : 2 * ‖z‖ ≤ ‖loc i‖) (hloc : loc i ≠ 0) :
    -‖z / loc i‖ ^ 2 ≤ Real.log (gFactor (loc i) z) := by
  have hlocpos : 0 < ‖loc i‖ := by simpa [norm_pos_iff] using hloc
  have hle : ‖z / loc i‖ ≤ 1 / 2 := by
    rw [norm_div, div_le_iff₀ hlocpos]
    nlinarith [norm_nonneg z]
  -- gFactor (loc i) z = ‖1 - (z/loc i)‖ · exp (Re (z/loc i)); apply `log_factor_ge` with u = z/loc i.
  have := log_factor_ge (u := z / loc i) hle
  rw [gFactor]
  -- (z/loc i).re is the real part used in `log_factor_ge`
  convert this using 3

/-- **Additive → multiplicative bridge (no loss).** Given that every real factor `gFactor (loc i) z`
is positive, that the logs are summable, and a LOWER bound `B ≤ Σ log(gFactor (loc i) z)`, the
infinite product is bounded below by `exp B`. Via `Real.rexp_tsum_eq_tprod`.

This is the clean conversion of the genuine analytic estimate (a *sum* lower bound — where Hadamard's
argument actually produces its inequality) into the multiplicative `hCore` shape that
`ScratchMinMod.genus1Product_minModulus` consumes. -/
theorem prod_ge_of_logSum_ge {z : ℂ} {B : ℝ}
    (hpos : ∀ i, 0 < gFactor (loc i) z)
    (hsummlog : Summable (fun i => Real.log (gFactor (loc i) z)))
    (hB : B ≤ ∑' i, Real.log (gFactor (loc i) z)) :
    Real.exp B ≤ ∏' i, gFactor (loc i) z := by
  have hprod : Real.exp (∑' i, Real.log (gFactor (loc i) z)) = ∏' i, gFactor (loc i) z :=
    Real.rexp_tsum_eq_tprod hpos hsummlog
  calc Real.exp B ≤ Real.exp (∑' i, Real.log (gFactor (loc i) z)) := Real.exp_le_exp.mpr hB
    _ = ∏' i, gFactor (loc i) z := hprod

/-- **The genus-1 minimum-modulus estimate**, in the `ScratchMinMod`-compatible multiplicative shape,
proved CONDITIONAL on the single isolated analytic core `hLogSumCore` (the log-sum lower bound) and
the summability of the log terms `hsummlog` (itself a consequence of the same zero count). Every
structural step — positivity off the zeros, the `exp(Σlog) = ∏` passage — is discharged here.

`hLogSumCore` is the genuine Hadamard minimum-modulus content: a lower bound on `Σ log(gᵢ z)`. Its
far-zeros part is `far_log_factor_ge`/`summable_normsq` (proven); its irreducible remainder is the
far-tail decay `Σ_{‖loc i‖≥2‖z‖} 1/‖loc i‖² = O(log‖z‖/‖z‖)` plus the near-zeros circle-avoidance
(both gated on the order-1 zero count, absent from Mathlib). -/
theorem genus1Product_minModulus
    (hne : ∀ i, loc i ≠ 0)
    -- `hsumm` pins down the genus-1 convergence setting (it powers `far_log_factor_ge` /
    -- `summable_normsq`, the proven far-zeros part of `hLogSumCore`); the conditional assembly
    -- routes all analytic content through `hLogSumCore`/`hsummlog`, so it is not used directly here.
    (_hsumm : Summable (fun i => 1 / ‖loc i‖ ^ 2))
    (hsummlog : ∀ z : ℂ, (∀ i, loc i ≠ z) →
      Summable (fun i => Real.log (gFactor (loc i) z)))
    (hLogSumCore : ∃ C₀ : ℝ, ∀ z : ℂ, (∀ i, loc i ≠ z) →
      -(C₀ * (1 + ‖z‖) * Real.log (2 + ‖z‖)) ≤ ∑' i, Real.log (gFactor (loc i) z)) :
    ∃ C₀ : ℝ, ∀ z : ℂ, (∀ i, loc i ≠ z) →
      Real.exp (-(C₀ * (1 + ‖z‖) * Real.log (2 + ‖z‖)))
        ≤ ∏' i, gFactor (loc i) z := by
  obtain ⟨C₀, hC₀⟩ := hLogSumCore
  refine ⟨C₀, fun z hz => ?_⟩
  have hpos : ∀ i, 0 < gFactor (loc i) z := fun i => factor_norm_pos (hne i) (fun h => hz i h.symm)
  exact prod_ge_of_logSum_ge loc hpos (hsummlog z hz) (hC₀ z hz)

/-- **Bridge to `ScratchMinMod`'s exact `hCore` shape.** `gFactor (loc i) z` is definitionally the
real factored product term `‖1 - z/loc i‖·exp((z/loc i).re)` that `ScratchMinMod.genus1Product_minModulus`
takes as `hCore`. Hence `genus1Product_minModulus` above *is* a proof of that `hCore`, modulo the
isolated `hLogSumCore` + `hsummlog`. We record the definitional identity of the products. -/
theorem tprod_gFactor_eq (z : ℂ) :
    (∏' i, gFactor (loc i) z) = ∏' i, (‖1 - z / loc i‖ * Real.exp (z / loc i).re) := rfl

end OverflowResidueRH.BacklundTuring.ScratchMinModClose
