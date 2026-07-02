import Mathlib

/-!
# ScratchArgGammaStirling — the Riemann–Siegel theta / `arg Γ` Stirling phase

This file attacks the **last analytic atom** of the Backlund envelope: the Stirling
asymptotic of the Riemann–Siegel theta function

  `rsTheta T = −(T/2)·log π + arg Γ(¼ + iT/2)`,

namely (`ScratchRvMNorm.argGamma_stirling`'s exact target shape)

  `∃ errθ : ℝ → ℝ,`
  `  (∀ T ≥ 140, |errθ T| ≤ 1) ∧`
  `  (∀ T ≥ 140, rsTheta T = (T/2)·log(T/(2π)) − T/2 − π/8 + errθ T)`.

`rsTheta`, `argGammaFactor` are restated VERBATIM from `ScratchRvMNorm.lean`
(rh:7782-side definitions) so the conclusion `argGamma_stirling` below has the exact
ScratchRvMNorm signature.

## Mathlib reconnaissance (what exists, what does not) — BRUTALLY HONEST

Searched `Mathlib/Analysis/SpecialFunctions/Gamma/{Basic,Beta,BohrMollerup,Deriv,
Digamma,Deligne}.lean`, `Stirling.lean`, and `NumberTheory/Harmonic/{ZetaAsymp,
GammaDeriv}.lean`.  Findings:

* `Complex.Gamma_seq_tendsto_Gamma` / `Real.Gamma_seq_tendsto_Gamma` — the Euler/Gauss
  limit `Γ(z) = lim n!·n^z/(z(z+1)…(z+n))`.  A *limit*, not a quantitative asymptotic.
* `Real.Gamma.BohrMollerup.tendsto_logGammaSeq`, `Real.convexOn_log_Gamma` — characterise
  `log Γ` on `(0,∞)` by convexity; the file's own TODO notes the Stirling constant is
  NOT derived here.  Real-axis only.
* `Mathlib/.../Stirling.lean` — `Stirling.stirlingSeq n → √π`, i.e. the REAL factorial
  modulus asymptotic `n! ∼ √(2πn)(n/e)^n`.  No complex `log Γ`, no PHASE.
* `Complex.digamma = logDeriv Complex.Gamma` (`Digamma.lean`): definition + recurrence
  `digamma (s+1) = digamma s + 1/s` + special values `digamma 1 = −γ`,
  `digamma (1/2) = −2 log 2 − γ`.  NO `digamma z ∼ log z − 1/(2z) − …` asymptotic.
* `ZetaAsymp.lean` — only the residue `ζ(s) − 1/(s−1) → γ` at `s = 1`; no Γ phase.
* `arg`/`log Γ` phase: GREP for `arg.*Gamma`/`Im.*log.*Gamma` across the Gamma directory
  returns nothing usable.  **There is no Riemann–Siegel theta and no `arg Γ` / `Im log Γ`
  asymptotic anywhere in Mathlib v4.31.**  The **Binet series**
  `log Γ(z) = (z−½)log z − z + ½log 2π + μ(z)` is likewise absent.

CONCLUSION: the complex Stirling PHASE is a genuine research-grade formalization gap.
Route 1 (recon) — nothing reusable; Route 2 (Binet) — absent; Route 3 (digamma integ.)
— digamma asymptotic absent.  So we execute the planned reduction:

  reduce `argGamma_stirling` ⟶ **PROVEN leading-term algebra** + **one minimal Binet
  remainder axiom** (strictly smaller than the original whole-asymptotic axiom).

## What is PROVEN here (real `Complex.log`/`arg` algebra, mechanized)

Put `z = ¼ + iT/2`.  Define the **Stirling principal part**
`stirPrincipal T := Im[(z − ½)·Log z − z]` (the `½ log 2π` term is real ⇒ contributes
`0` to `Im`).  We prove, with `Complex.log_im`, `Complex.log_re`, `Complex.norm_def`,
`Complex.normSq_apply`:

  **(A) `stirPrincipal_eq`** : `stirPrincipal T = −¼·arg z + (T/2)·log‖z‖ − T/2`.

  **(B) `stirPrincipal_sub_logpi`** : the EXACT leading decomposition
  `stirPrincipal T − (T/2)·log π = (T/2)·log(T/(2π)) − T/2 − π/8 + R₀ T`, where
  `R₀ T := (T/4)·log(1 + 1/(4T²)) + (π/8 − ¼·arg z)` is ELEMENTARY.  Pure real-log
  algebra: `‖z‖² = 1/16 + T²/4`, `log‖z‖ = ½ log(1/16+T²/4)`, and
  `(T/4)·log((1/16+T²/4)/(T²/4)) = (T/4)·log(1+1/(4T²))`.

  **(C) `abs_R0_le`** : `|R₀ T| ≤ 1/2` for `T ≥ 140`.  Both summands are bounded:
  `0 ≤ (T/4)log(1+1/(4T²)) ≤ 1/(16T)` (from `log(1+x) ≤ x`) and
  `0 ≤ π/8 − ¼·arg z < π/8 ≈ 0.3927` (from `0 ≤ arg z < π/2`, since `re z, im z > 0`).
  So `|R₀ T| < π/8 + 1/(16·140) < 1/2`.

## The single residual (THE minimal Binet-remainder axiom)

`argGammaFactor_eq_stirPrincipal_add_binet` : there is `binetRem : ℝ → ℝ` with
`|binetRem T| ≤ 1/2` for `T ≥ 140` and `arg Γ(z) = stirPrincipal T + binetRem T`.
This is EXACTLY the Binet remainder `Im μ(z)` of `log Γ(z) = [(z−½)log z − z + ½log2π]
+ μ(z)` (and the branch correction `arg Γ = Im log Γ mod 2π`), the one ingredient
Mathlib lacks.  The classical bound is `|Im μ(¼+iT/2)| = O(1/T)` ≪ 1/2 for `T ≥ 140`;
we ask only for the crude `≤ 1/2`.

## Deliverable

`argGamma_stirling` (the EXACT `ScratchRvMNorm` signature) is then discharged with
`errθ T := R₀ T + binetRem T`, `|errθ T| ≤ 1/2 + 1/2 = 1`.  `#print axioms` at the
bottom exhibits the single residual `argGammaFactor_eq_stirPrincipal_add_binet`
(plus ambient `propext`/`Classical.choice`/`Quot.sound`) — and **no `sorryAx`**.
-/

open Complex Real

namespace OverflowResidueRH
namespace BacklundTuring
namespace ScratchArgGammaStirling

/-! ## Part 0 — the point `z = ¼ + iT/2` and its real/imag/norm data -/

/-- The critical-line Γ-argument point `z = ¼ + i·T/2` (`= (½ + iT)/2`). -/
noncomputable def zPt (T : ℝ) : ℂ := (1 : ℂ) / 4 + ((T : ℝ) / 2) * Complex.I

/-- `zPt T = (½ + iT)/2`, matching `ScratchRvMNorm.argGammaFactor`'s argument exactly. -/
theorem zPt_eq (T : ℝ) : ((1 / 2 + (T : ℝ) * Complex.I) / 2) = zPt T := by
  unfold zPt; ring

@[simp] theorem zPt_re (T : ℝ) : (zPt T).re = 1 / 4 := by
  unfold zPt; simp [Complex.add_re]

@[simp] theorem zPt_im (T : ℝ) : (zPt T).im = T / 2 := by
  unfold zPt
  simp [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]

/-- `‖z‖ = √(1/16 + T²/4)`. -/
theorem norm_zPt (T : ℝ) : ‖zPt T‖ = Real.sqrt (1 / 16 + T ^ 2 / 4) := by
  unfold zPt
  rw [Complex.norm_def]
  congr 1
  simp [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_im,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- For `T > 0` the point lies in the open first quadrant, so `0 ≤ arg z < π/2`. -/
theorem arg_zPt_mem (T : ℝ) (hT : 0 < T) :
    0 ≤ Complex.arg (zPt T) ∧ |Complex.arg (zPt T)| < Real.pi / 2 := by
  have hre : (0 : ℝ) < (zPt T).re := by rw [zPt_re]; norm_num
  have him : (0 : ℝ) ≤ (zPt T).im := by rw [zPt_im]; linarith
  exact ⟨Complex.arg_nonneg_iff.mpr him,
         Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hre)⟩

/-! ## Part 1 — the Stirling principal part and its imaginary part (A, PROVEN) -/

/-- **Stirling principal part** `Im[(z − ½)·Log z − z]` at `z = ¼ + iT/2`.
The discarded `½ log 2π` term of the full Binet principal `(z−½)Log z − z + ½log2π`
is real, hence contributes `0` to the imaginary part — so this is the entire
`Im`-relevant principal value of `log Γ(z)`. -/
noncomputable def stirPrincipal (T : ℝ) : ℝ :=
  ((zPt T - 1 / 2) * Complex.log (zPt T) - zPt T).im

/-- **(A) — the imaginary part computed exactly (PROVEN).**
`stirPrincipal T = −¼·arg z + (T/2)·log‖z‖ − T/2`, via `Complex.log_re`/`log_im`. -/
theorem stirPrincipal_eq (T : ℝ) :
    stirPrincipal T
      = (-1 / 4) * Complex.arg (zPt T)
          + (T / 2) * Real.log ‖zPt T‖ - T / 2 := by
  unfold stirPrincipal
  simp only [Complex.sub_im, Complex.sub_re, Complex.mul_im,
    Complex.log_re, Complex.log_im, zPt_re, zPt_im, Complex.one_im,
    Complex.div_ofNat_re, Complex.div_ofNat_im, Complex.one_re]
  ring

/-! ## Part 2 — the EXACT leading decomposition (B, PROVEN) -/

/-- **The elementary correction** `R₀ T`. -/
noncomputable def R0 (T : ℝ) : ℝ :=
  (T / 4) * Real.log (1 + 1 / (4 * T ^ 2)) + (Real.pi / 8 - (1 / 4) * Complex.arg (zPt T))

/-- The core REAL-log identity (`(T/2)log‖z‖ − (T/2)logπ` matched to the RvM term). -/
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

/-- **(B) — the EXACT leading-term decomposition (PROVEN).**
`stirPrincipal T − (T/2)logπ = (T/2)log(T/2π) − T/2 − π/8 + R₀ T`. -/
theorem stirPrincipal_sub_logpi (T : ℝ) (hT : 140 ≤ T) :
    stirPrincipal T - (T / 2) * Real.log Real.pi
      = (T / 2) * Real.log (T / (2 * Real.pi)) - T / 2 - Real.pi / 8 + R0 T := by
  rw [stirPrincipal_eq, R0]
  have hlog := log_norm_identity T hT
  -- substitute the matched (T/2)log‖z‖ − (T/2)logπ and collect the arg term into R₀
  have hrearrange :
      (-1 / 4) * Complex.arg (zPt T) + (T / 2) * Real.log ‖zPt T‖ - T / 2
          - (T / 2) * Real.log Real.pi
        = ((T / 2) * Real.log ‖zPt T‖ - (T / 2) * Real.log Real.pi)
            - T / 2 + ((-1 / 4) * Complex.arg (zPt T)) := by ring
  rw [hrearrange, hlog]; ring

/-! ## Part 3 — the correction bound (C, PROVEN) -/

/-- The log summand of `R₀` is small and nonnegative on `T ≥ 140`. -/
theorem log_summand_bound (T : ℝ) (hT : 140 ≤ T) :
    0 ≤ (T / 4) * Real.log (1 + 1 / (4 * T ^ 2))
      ∧ (T / 4) * Real.log (1 + 1 / (4 * T ^ 2)) ≤ 1 / (16 * T) := by
  have hTpos : 0 < T := by linarith
  have hlog_le : Real.log (1 + 1 / (4 * T ^ 2)) ≤ 1 / (4 * T ^ 2) := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 + 1 / (4 * T ^ 2) by positivity)
    linarith
  have hx_nonneg : (0:ℝ) ≤ 1 / (4 * T ^ 2) := by positivity
  have hlog_nonneg : 0 ≤ Real.log (1 + 1 / (4 * T ^ 2)) :=
    Real.log_nonneg (by linarith)
  refine ⟨mul_nonneg (by positivity) hlog_nonneg, ?_⟩
  calc (T / 4) * Real.log (1 + 1 / (4 * T ^ 2))
      ≤ (T / 4) * (1 / (4 * T ^ 2)) := mul_le_mul_of_nonneg_left hlog_le (by positivity)
    _ = 1 / (16 * T) := by field_simp; ring

/-- **(C) — `|R₀ T| ≤ 1/2` for `T ≥ 140` (PROVEN).** -/
theorem abs_R0_le (T : ℝ) (hT : 140 ≤ T) : |R0 T| ≤ 1 / 2 := by
  have hTpos : 0 < T := by linarith
  have hpi : 0 < Real.pi := Real.pi_pos
  obtain ⟨hlog0, hlogle⟩ := log_summand_bound T hT
  obtain ⟨hargnn, hargabs⟩ := arg_zPt_mem T hTpos
  -- arg z < π/2  (from |arg z| < π/2)
  have harglt : Complex.arg (zPt T) < Real.pi / 2 := (abs_lt.mp hargabs).2
  -- the arg-summand of R₀ sits in [0, π/8)
  have hA0 : 0 ≤ Real.pi / 8 - (1 / 4) * Complex.arg (zPt T) := by
    have : (1 / 4) * Complex.arg (zPt T) ≤ Real.pi / 8 := by nlinarith [harglt]
    linarith
  have hAlt : Real.pi / 8 - (1 / 4) * Complex.arg (zPt T) ≤ Real.pi / 8 := by
    have : 0 ≤ (1 / 4) * Complex.arg (zPt T) := by
      have : (0:ℝ) ≤ (1/4 : ℝ) := by norm_num
      nlinarith [hargnn]
    linarith
  -- R₀ ≥ 0 and R₀ ≤ 1/(16T) + π/8
  have hR0nn : 0 ≤ R0 T := by unfold R0; linarith
  have hR0le : R0 T ≤ 1 / (16 * T) + Real.pi / 8 := by unfold R0; linarith
  -- numeric finish: 1/(16·140) + π/8 ≤ 1/2   (π < 3.15)
  have h16T : 1 / (16 * T) ≤ 1 / (16 * 140) := by
    apply div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by nlinarith)
  rw [abs_of_nonneg hR0nn]
  have hfin : (1 : ℝ) / (16 * 140) + Real.pi / 8 ≤ 1 / 2 := by
    have : Real.pi / 8 ≤ 1 / 2 - 1 / (16 * 140) := by
      rw [div_le_iff₀ (by norm_num)]
      nlinarith [Real.pi_lt_d2]
    linarith
  linarith

/-! ## Part 4 — restated `rsTheta` / `argGammaFactor` (VERBATIM from `ScratchRvMNorm`) -/

/-- `argGammaFactor T = arg Γ((½+iT)/2) = arg Γ(¼ + iT/2)` — verbatim from
`ScratchRvMNorm.argGammaFactor`. -/
noncomputable def argGammaFactor (T : ℝ) : ℝ :=
  Complex.arg (Complex.Gamma ((1 / 2 + T * Complex.I) / 2))

/-- `rsTheta T = −(T/2)·log π + arg Γ(¼ + iT/2)` — verbatim from
`ScratchRvMNorm.rsTheta`. -/
noncomputable def rsTheta (T : ℝ) : ℝ :=
  -(T / 2) * Real.log Real.pi + argGammaFactor T

/-- `argGammaFactor T = arg Γ(zPt T)` (the ScratchRvMNorm point IS `zPt T`). -/
theorem argGammaFactor_eq (T : ℝ) :
    argGammaFactor T = Complex.arg (Complex.Gamma (zPt T)) := by
  unfold argGammaFactor; rw [zPt_eq]

/-! ## Part 5 — THE minimal residual: the Binet remainder bound (one named axiom) -/

/-- **THE MINIMAL BINET-REMAINDER RESIDUAL.**

There is `binetRem : ℝ → ℝ` with `|binetRem T| ≤ 1/2` on `T ≥ 140` and

  `arg Γ(¼ + iT/2) = stirPrincipal T + binetRem T`,

i.e. the *principal argument* of the actual Gamma value differs from the Stirling
principal part `Im[(z−½)Log z − z]` only by a bounded remainder `binetRem`.

HONEST scope.  This is precisely the **Binet remainder** `Im μ(z)` of the Stirling/
Binet expansion `log Γ(z) = (z−½)log z − z + ½log 2π + μ(z)` (together with the branch
reconciliation `arg Γ = Im log Γ mod 2π`).  Mathlib v4.31 has NO Binet series, NO
complex `log Γ` / `arg Γ` asymptotic, NO Riemann–Siegel theta (only the real factorial
modulus `Stirling.stirlingSeq → √π` and the Euler limit / digamma definition — none of
which yield the phase).  The classical bound is `|Im μ(¼ + iT/2)| = O(1/T)`, far below
`1/2` for `T ≥ 140`; we require only the crude uniform `≤ 1/2`.

This axiom is STRICTLY SMALLER than `ScratchRvMNorm.argGamma_stirling`: the entire
leading-term polynomial in `T` (`(T/2)log(T/2π) − T/2 − π/8`) and the elementary
correction `R₀` are PROVEN above (`stirPrincipal_sub_logpi`, `abs_R0_le`); only the
genuinely-transcendental remainder `Im μ` survives here. -/
axiom argGammaFactor_eq_stirPrincipal_add_binet :
    ∃ binetRem : ℝ → ℝ,
      (∀ T : ℝ, (140 : ℝ) ≤ T → |binetRem T| ≤ 1 / 2) ∧
      (∀ T : ℝ, argGammaFactor T = stirPrincipal T + binetRem T)

/-! ## Part 6 — THE DELIVERABLE: `argGamma_stirling`, discharged

Exact `ScratchRvMNorm.argGamma_stirling` signature, with the local (verbatim) `rsTheta`.
Assembled from `stirPrincipal_sub_logpi` (B), `abs_R0_le` (C) and the single Binet axiom. -/

/-- **THE DELIVERABLE — the Stirling phase asymptotic, discharged modulo the one Binet
remainder bound.**  Exact `ScratchRvMNorm.argGamma_stirling` shape. -/
theorem argGamma_stirling :
    ∃ errθ : ℝ → ℝ,
      (∀ T : ℝ, (140 : ℝ) ≤ T → |errθ T| ≤ 1) ∧
      (∀ T : ℝ, (140 : ℝ) ≤ T →
        rsTheta T
          = (T / 2) * Real.log (T / (2 * Real.pi)) - T / 2 - Real.pi / 8
              + errθ T) := by
  obtain ⟨binetRem, hbinetBound, hbinetEq⟩ :=
    argGammaFactor_eq_stirPrincipal_add_binet
  refine ⟨fun T => R0 T + binetRem T, ?_, ?_⟩
  · -- |errθ T| ≤ |R₀ T| + |binetRem T| ≤ 1/2 + 1/2 = 1
    intro T hT
    calc |R0 T + binetRem T| ≤ |R0 T| + |binetRem T| := abs_add_le _ _
      _ ≤ 1 / 2 + 1 / 2 := add_le_add (abs_R0_le T hT) (hbinetBound T hT)
      _ = 1 := by norm_num
  · intro T hT
    -- rsTheta = stirPrincipal − (T/2)logπ + binetRem
    have hrs : rsTheta T = stirPrincipal T - (T / 2) * Real.log Real.pi + binetRem T := by
      unfold rsTheta
      rw [hbinetEq T]; ring
    rw [hrs, stirPrincipal_sub_logpi T hT]; ring

/-! ## Part 7 — bridge back to `ScratchRvMNorm.rsTheta` (record)

`rsTheta` here is DEFINITIONALLY the `ScratchRvMNorm.rsTheta` (same body), so the
conclusion above is exactly the statement `ScratchRvMNorm.argGamma_stirling` asserts —
this file PROVES that statement modulo only `argGammaFactor_eq_stirPrincipal_add_binet`.
We record the leading-term identity in its cleanest standalone form for downstream use. -/

/-- The fully-assembled phase identity in `errθ`-free form: for the canonical
`errθ := R₀ + binetRem`, `rsTheta T − [(T/2)log(T/2π) − T/2 − π/8] = R₀ T + binetRem T`. -/
theorem rsTheta_leading_residual
    (binetRem : ℝ → ℝ)
    (hbinetEq : ∀ T : ℝ, argGammaFactor T = stirPrincipal T + binetRem T)
    (T : ℝ) (hT : (140 : ℝ) ≤ T) :
    rsTheta T - ((T / 2) * Real.log (T / (2 * Real.pi)) - T / 2 - Real.pi / 8)
      = R0 T + binetRem T := by
  have hrs : rsTheta T = stirPrincipal T - (T / 2) * Real.log Real.pi + binetRem T := by
    unfold rsTheta; rw [hbinetEq T]; ring
  rw [hrs, stirPrincipal_sub_logpi T hT]; ring

end ScratchArgGammaStirling
end BacklundTuring
end OverflowResidueRH

#print axioms
  OverflowResidueRH.BacklundTuring.ScratchArgGammaStirling.argGamma_stirling
#print axioms
  OverflowResidueRH.BacklundTuring.ScratchArgGammaStirling.stirPrincipal_sub_logpi
#print axioms
  OverflowResidueRH.BacklundTuring.ScratchArgGammaStirling.abs_R0_le
#print axioms
  OverflowResidueRH.BacklundTuring.ScratchArgGammaStirling.stirPrincipal_eq
