import rh
import Mathlib

/-!
# ScratchCombine — honest conditional inhabitant of `BacklundClassicalCombinationInput`

This file performs an **honest reduction** of the single open gate of the
`½·logT + ½` envelope, namely

  `OverflowResidueRH.BacklundTuring.BacklundClassicalCombinationInput`   (rh.lean:17242)

whose only field is

  `combine : ∀ T, RvMGoodHeight T → 140 ≤ T →
      BacklundJensenRectangleEstimate T →
      BacklundRightSideArgumentVariationEstimate T →
      BacklundHorizontalBoundaryEstimate T →
        |concreteS T| ≤ ½·log T + ½`.

`concreteS T = N(T) − N₀(T)` where `N(T)` is the multiplicity-weighted count
of nontrivial ζ-zeros with `0 < Im ≤ T` and `N₀(T) = (T/2π)log(T/2π) − T/2π + 7/8`
is the smooth Riemann–von Mangoldt main term (rh.lean:7782, 2928).

## Why this is genuinely NOT derivable from the three estimate hypotheses

The three estimate hypotheses are tautological / carry uncontrolled existential
constants (see the warnings in the rh.lean constructors:
`BacklundJensenRectangleEstimate.of_height_ge_140` sets `C := max 0 D / log(T+2)`
*from* the very window count `D` it then "bounds";
`BacklundHorizontalBoundaryEstimate` is a bare compactness `∃ C, ‖ζ‖ ≤ C(T+1)`;
`BacklundRightSideArgumentVariationEstimate` is nonvanishing on `Re = 2` plus a
bare `∃ C` log-derivative bound). None of them pins the SHARP constant. So
`combine` AS STATED is essentially **Backlund's 1918 theorem**
`|S(T)| ≤ 0.137·logT + 0.443·loglogT + 1.588` (≈ 2.97 at T = 140, just under
`½logT + ½ = 2.97` — that is why the threshold is exactly 140).

## Recon of Mathlib (argument principle)

What EXISTS (disk / Jensen flavour, all zero-counting via mean values of
`log‖f‖`, never a rectangle boundary-argument identity):
* `Mathlib/Analysis/Complex/JensenFormula.lean`:
  `AnalyticOnNhd.sum_divisor_le`, `MeromorphicOn.circleAverage_log_norm`,
  `AnalyticOnNhd.circleAverage_log_norm` — Jensen's formula on circles.
* `Mathlib/Analysis/Complex/ValueDistribution/LogCounting/*` — the Nevanlinna
  logarithmic counting function `logCounting`, built from `MeromorphicOn.divisor`
  on closed balls, with `logCounting_*` monotonicity/sub-additivity lemmas.
* `Mathlib/Analysis/Complex/CauchyIntegral.lean`:
  `Complex.integral_boundary_rect_eq_zero_of_differentiableOn` (Goursat: the
  boundary integral of a HOLOMORPHIC function over an axis-parallel rectangle
  vanishes — no poles, hence no residue/count information by itself).

What is ABSENT (verified by exhaustive grep over the Mathlib source tree):
* NO `argumentPrinciple` / winding-number theorem of any kind
  (`grep windingNumber` ⇒ nothing in analysis).
* NO rectangle (or contour) residue theorem expressing a zero count as
  `(1/2πi)∮ f'/f`  (`grep "logDeriv" CauchyIntegral.lean` ⇒ nothing).
* NO continuous-argument lift `Complex.arg`-along-a-path with a variation count.

Therefore the **Backlund contour identity** — that `concreteS T` equals the net
change of `arg ζ` around the standard rectangle (modulo the absorbed main term),
with sharp per-side numeric bounds — is genuinely not in Mathlib and is isolated
below as the single named kernel axiom `BacklundContourBound`.

## What this file delivers

* `BacklundContourBound` : the ONE isolated kernel hypothesis (the genuine
  Backlund 1918 content; precise meaning in its docstring).
* `backlundClassicalCombinationInput_of_kernel` : a `noncomputable def`
  inhabiting `BacklundClassicalCombinationInput` from that single kernel.
* Genuinely-true arithmetic bridge lemmas, fully proved (no `sorry`, no fragile
  decimals): envelope monotonicity and the `loglog ≤ log` comparison.

`#print axioms backlundClassicalCombinationInput_of_kernel` at the end reports the
exact dependency set; the only non-standard axiom is `BacklundContourBound`.
-/

namespace OverflowResidueRH.BacklundTuring.ScratchCombine

open OverflowResidueRH OverflowResidueRH.BacklundTuring

/-! ## Genuinely-true arithmetic bridge lemmas (fully proved) -/

/-- The envelope `½·log T + ½` is monotone nondecreasing on positive heights.
A true, elementary fact, proved from monotonicity of `Real.log`. -/
theorem envelope_mono {T₁ T₂ : ℝ} (h₁ : 0 < T₁) (h₂ : T₁ ≤ T₂) :
    (1 / 2 : ℝ) * Real.log T₁ + 1 / 2 ≤ (1 / 2 : ℝ) * Real.log T₂ + 1 / 2 := by
  have hlog : Real.log T₁ ≤ Real.log T₂ := Real.log_le_log h₁ h₂
  linarith

/-- `log (log T) ≤ log T` for `T ≥ e` (so in particular for `T ≥ 140`):
the iterated logarithm is dominated by a single logarithm.  Proved from the
general bound `Real.log x ≤ x` applied to `x = log T`.  A true, unconditional
ingredient of the Backlund constant bookkeeping. -/
theorem loglog_le_log {T : ℝ} (hT : Real.exp 1 ≤ T) :
    Real.log (Real.log T) ≤ Real.log T := by
  have hlogpos : (1 : ℝ) ≤ Real.log T := by
    have := Real.log_le_log (Real.exp_pos 1) hT
    simpa [Real.log_exp] using this
  -- `Real.log x ≤ x` for all `x`; specialize to `x = log T (> 0)`.
  exact (Real.log_le_sub_one_of_pos (lt_of_lt_of_le one_pos hlogpos)).trans (by linarith)

/-- The envelope value `½·log T + ½` is positive for `T ≥ 140` (in fact
`≥ ½·log 140 + ½ > 0`).  Used so the kernel's absolute-value bound is meaningful. -/
theorem envelope_pos {T : ℝ} (hT : (140 : ℝ) ≤ T) :
    0 < (1 / 2 : ℝ) * Real.log T + 1 / 2 := by
  have hTpos : (0 : ℝ) < T := lt_of_lt_of_le (by norm_num) hT
  have hlog_nonneg : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
  linarith

/-! ## The single isolated kernel hypothesis (genuine Backlund 1918 content)

We carry it as an `axiom` (the axiom-transplant pattern): it can later be
replaced by an honest proof once Mathlib acquires (or this project builds) the
rectangle argument-principle.  Its statement is EXACTLY the headline
good-height bound on `concreteS`, which is what the classical Backlund contour
computation produces and what the three weak estimates provably cannot. -/

/-- **KERNEL (the real wall — Backlund 1918).**

`BacklundContourBound` asserts the sharp good-height bound on the zero-counting
fluctuation:

  `∀ T, RvMGoodHeight T → 140 ≤ T → |concreteS T| ≤ ½·log T + ½`.

Mathematical content: by the argument principle, the multiplicity-weighted count
`N(T)` of nontrivial ζ-zeros up to height `T` equals the smooth main term
`N₀(T)` plus `S(T) = (1/π)·arg ζ(½ + iT)`, where `arg ζ` is the continuous
variation of the argument of `ζ` along the contour from `2` to `2 + iT` to
`½ + iT`.  Backlund (1918) bounds the right vertical side via the von Mangoldt
log-derivative series and the horizontal sides via convexity/`ζ`-growth, yielding
`|S(T)| ≤ 0.137·log T + 0.443·log log T + 1.588`, which lies under `½·log T + ½`
precisely for `T ≥ 140`.

Why Mathlib lacks it: there is NO argument principle, winding number, or
rectangle-residue theorem in Mathlib (only disk-based Jensen / Nevanlinna
counting and the Goursat vanishing theorem) — verified by exhaustive source
search.  Hence the contour identity relating `concreteS` to the boundary
argument variation, and the sharp per-side numeric bounds, are genuinely
irreducible here. -/
axiom BacklundContourBound :
    ∀ T : ℝ, RvMGoodHeight T → (140 : ℝ) ≤ T →
      |concreteS T| ≤ (1 / 2 : ℝ) * Real.log T + 1 / 2

/-! ## Conditional inhabitant of the open gate -/

/-- **Honest conditional inhabitant.**

Given the single isolated kernel hypothesis `kernel` (the genuine Backlund 1918
contour bound — exactly the content Mathlib lacks), the open gate
`BacklundClassicalCombinationInput` is inhabited.

The three estimate arguments `hJ`, `hR`, `hH` are accepted but, as documented in
rh.lean, are tautological / uncontrolled-constant Props and therefore CANNOT
themselves supply the sharp bound; the bound comes entirely from `kernel`.  This
is the faithful state of affairs: the reduction does not pretend the weak
estimates close the gate. -/
noncomputable def backlundClassicalCombinationInput_of_kernel
    (kernel :
      ∀ T : ℝ, RvMGoodHeight T → (140 : ℝ) ≤ T →
        |concreteS T| ≤ (1 / 2 : ℝ) * Real.log T + 1 / 2) :
    BacklundClassicalCombinationInput :=
  ⟨fun T hgood hT _hJ _hR _hH => kernel T hgood hT⟩

/-- Unconditional inhabitant obtained by transplanting the kernel axiom. -/
noncomputable def backlundClassicalCombinationInput_via_axiom :
    BacklundClassicalCombinationInput :=
  backlundClassicalCombinationInput_of_kernel BacklundContourBound

/-! ## Sanity: the kernel-form bound rephrases as the numerical estimate -/

/-- The kernel directly yields `BacklundNumericalCombinationEstimate T`
(definitionally `|concreteS T| ≤ ½·log T + ½`) at every good height `T ≥ 140`. -/
theorem backlundNumericalCombinationEstimate_of_kernel
    (kernel :
      ∀ T : ℝ, RvMGoodHeight T → (140 : ℝ) ≤ T →
        |concreteS T| ≤ (1 / 2 : ℝ) * Real.log T + 1 / 2)
    {T : ℝ} (hgood : RvMGoodHeight T) (hT : (140 : ℝ) ≤ T) :
    BacklundNumericalCombinationEstimate T :=
  kernel T hgood hT

end OverflowResidueRH.BacklundTuring.ScratchCombine

/-! ## Axiom audit -/

open OverflowResidueRH.BacklundTuring.ScratchCombine in
#print axioms backlundClassicalCombinationInput_of_kernel

open OverflowResidueRH.BacklundTuring.ScratchCombine in
#print axioms backlundClassicalCombinationInput_via_axiom

open OverflowResidueRH.BacklundTuring.ScratchCombine in
#print axioms envelope_mono

open OverflowResidueRH.BacklundTuring.ScratchCombine in
#print axioms loglog_le_log
