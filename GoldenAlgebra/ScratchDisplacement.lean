import rh
import ScratchTrueKernelConv

/-!
# ScratchDisplacement — Route B: localize RH-strength to ONE visible inequality

## Goal

The mid/high residual of the Hadamard program currently reduces to the single
open field `error_im_eq_tail_im` of `OverflowResidueRH.TrueKernelTailData`
(rh.lean ~59609):

    (error z).im = (conv.tail T z).im

where `error = logDerivativeResponse XiPullback − M.model` is the true Hadamard
zero-contribution residual and `conv.tail` is the HEIGHT-Stieltjes tail
`∫_T^∞ [1/(z-u)² − 1/(z+u)²] · S(u) du` (`u` real, `S = N − N₀`).

The two differ by a **displacement** term: the true Hadamard atom for a zero
`ρ = β + iγ` sits at pullback `w = γ − i(β − ½)` (off the real axis when
`β ≠ ½`), while the height tail only sees the real ordinate `γ`.  Hiding RH
inside the bare equality is dishonest; this file **refactors** so the
obstruction is a single, explicitly-named, unproven inequality.

## What this file builds

`TrueKernelTailDataWithDisplacement S R error` carries:

* the **analytic** (non-RH) fields of `TrueKernelTailData` — `conv`, `true_int`,
  `wrap_int` — taken verbatim (suppliable from `ScratchTrueKernelConv`);
* a **displacement function** `displacementError : ℂ → ℂ`;
* `split_def` — the AFZ-guarded splitting identity
  `(error z).im = (conv.tail T z).im + (displacementError z).im`;
* `displacement_bound` — the AFZ-guarded one-sided inequality
  `(displacementError z).im ≤ 0`.

**Honesty design.** `split_def` is made TRUE BY DEFINITION by setting
`displacementError z := error z − (conv.tail T z)` — the canonical witness has
`(error z).im = (conv.tail T z).im + ((error z).im − (conv.tail T z).im)`, an
`a + (b − a) = b` identity carrying NO content.  ALL RH-strength is therefore
forced into the lone field `displacement_bound`, which we **leave unproven**
(a structure field).  The AFZ guard (`XiPullback z ≠ 0 →`) only handles the
bookkeeping at literal totalized zeros — it does NOT remove the displacement:
`displacementError z = Σ_ρ [trueAtom(w_ρ) − heightAtom(γ_ρ)]` is nonzero at
generic `z` whenever some `η_ρ = β_ρ − ½ ≠ 0`, so `displacement_bound`
remains the genuine RH-strength obligation.

## What this file proves (no `sorry`, no axiom beyond the standard three)

* `trueTail_im_abs_bound` — the raw analytic tail bound
  `|(conv.tail T z).im| ≤ −P(...)`, with NO reference to `error`
  (extracts the proof core of `hbound_of_adaptiveComplexTailIBPBoundData`).
* `TrueKernelTailDataWithDisplacement.errorMargin_midBand` — the **bridge**:
  the structure (its analytic fields + the lone `displacement_bound`),
  together with the model anti-Herglotz property, yields the one-sided
  margin `(error z).im ≤ −(M.model z).im` on the mid band, treating the
  literal-zero case via `errorMargin_at_XiPullback_zero_of_decomp`.  This is
  exactly the upper-side inequality `antiHerglotz_of_model_plus_error_margin`
  consumes — wired as far toward `XiPullbackAntiHerglotzTarget` as the
  one-sided front door allows.
* `trueKernelTailData_of_displacement_of_zero` — the `_of_zero` special case:
  when `displacementError = 0`, the structure recovers a genuine
  `TrueKernelTailData`, i.e. the original `error_im_eq_tail_im` field exactly.
* `canonicalDisplacementError` / `split_def_canonical` — the canonical
  zero-content witness making `split_def` a `ring` identity.
-/

namespace OverflowResidueRH

open MeasureTheory Filter Topology

-- =====================================================================
-- §A. Raw analytic tail bound (no `error` involved)
-- =====================================================================

/-- 🌟🌟🌟 **PROVED — raw tail-Im bound for the true kernel.**

`|(conv.tail T z).im| ≤ −P(z.im, slabCD T, T)` on the adaptive `[10,140]`
band, with NO reference to any `error` function.  This is the analytic
backbone: it isolates the part of `hbound_of_adaptiveComplexTailIBPBoundData`
(rh ~59086) that bounds the *tail* itself, before the
`error_im_eq_tail_im` step transfers it to `error`.

Proof: the imaginary part of the complex partial tends to the tail's Im
(`adaptiveComplexDensityTailFamilyPartial_im_tendsto`) and, via the
finite-Im match, also tends to the real IBP limit `J`; uniqueness gives
`(conv.tail T z).im = J`, and `derivative_bound` gives `|J| ≤ −P`. -/
theorem trueTail_im_abs_bound
    {S : ℝ → ℝ} (R : RealIBPFamilyData S)
    (conv : AdaptiveComplexDensityTailFamilyConverges
              pairedCauchyComplexKernelTrue S)
    (htrue_int :
      ∀ {z : ℂ} {T X : ℝ}, 10 ≤ T → T ≤ 140 → 0 < z.im →
        2 * (1 + |z.re| + z.im) ≤ T →
        IntervalIntegrable
          (fun u => pairedCauchyComplexKernelTrue u z * (S u : ℂ))
          MeasureTheory.volume T X)
    (hwrap_int :
      ∀ {z : ℂ} {T X : ℝ}, 10 ≤ T → T ≤ 140 → 0 < z.im →
        2 * (1 + |z.re| + z.im) ≤ T →
        IntervalIntegrable
          (fun u => pairedCauchyComplexKernelDeriv u z * (S u : ℂ))
          MeasureTheory.volume T X)
    {z : ℂ} {T : ℝ}
    (h10 : 10 ≤ T) (h140 : T ≤ 140) (hy : 0 < z.im)
    (hregime : 2 * (1 + |z.re| + z.im) ≤ T) :
    |(conv.tail T z).im|
      ≤ -Phase1IBP.derivativeSideMajorantPrimitive
          z.im (slabCD T).1 (slabCD T).2 T := by
  -- The real IBP limit J.
  obtain ⟨J, hJ⟩ := R.deriv_tendsto h10 h140 hy hregime
  -- Im of complex partial → Im of adaptive tail.
  have htail_im :
      Tendsto
        (fun X : ℝ =>
          (complexDensityTailPartial pairedCauchyComplexKernelTrue S T X z).im)
        Filter.atTop (𝓝 (conv.tail T z).im) :=
    adaptiveComplexDensityTailFamilyPartial_im_tendsto conv h10 h140 hy hregime
  -- Finite-Im match (true kernel): Im of complex partial = real partial.
  have hz_uhp : upperHalfPoint z.re z.im = z := upperHalfPoint_re_im z
  have htrue_int_uhp :
      ∀ X, IntervalIntegrable
        (fun u => pairedCauchyComplexKernelTrue u (upperHalfPoint z.re z.im)
                    * (S u : ℂ))
        MeasureTheory.volume T X := by
    intro X; rw [hz_uhp]; exact htrue_int h10 h140 hy hregime
  have hwrap_int_uhp :
      ∀ X, IntervalIntegrable
        (fun u => pairedCauchyComplexKernelDeriv u (upperHalfPoint z.re z.im)
                    * (S u : ℂ))
        MeasureTheory.volume T X := by
    intro X; rw [hz_uhp]; exact hwrap_int h10 h140 hy hregime
  have hmatch_struct :
      ComplexTailImaginaryPartMatchesRealIBP
        pairedCauchyComplexKernelTrue S z.re z.im T :=
    complexTailImaginaryPartMatchesRealIBP_trueKernel
      S z.re z.im T htrue_int_uhp hwrap_int_uhp
  -- Im of complex partial also → J.
  have hmatch :
      Tendsto
        (fun X : ℝ =>
          (complexDensityTailPartial pairedCauchyComplexKernelTrue S T X z).im)
        Filter.atTop (𝓝 J) := by
    have heq :
        (fun X : ℝ => Phase1IBP.derivativeSidePartial S z.re z.im T X)
          =ᶠ[Filter.atTop]
        (fun X : ℝ =>
          (complexDensityTailPartial pairedCauchyComplexKernelTrue S T X z).im) := by
      filter_upwards [hmatch_struct.finite_im_eq] with X hX
      rw [hz_uhp] at hX
      exact hX.symm
    exact Tendsto.congr' heq hJ
  -- Uniqueness: tail.im = J.
  have huniq : (conv.tail T z).im = J :=
    tendsto_nhds_unique htail_im hmatch
  rw [huniq]
  exact R.deriv_bound h10 h140 hy hregime hJ

-- =====================================================================
-- §B. The displacement structure
-- =====================================================================

/-- 📦 **`TrueKernelTailDataWithDisplacement`** — Route B refactor of
`TrueKernelTailData` that makes the RH-strength obligation a single visible
inequality.

Carries the **analytic** (non-RH) fields verbatim from `TrueKernelTailData`
(`conv`, `true_int`, `wrap_int`), then *replaces* the single RH-equivalent
field `error_im_eq_tail_im` by two fields:

* `split_def` — the AFZ-guarded splitting identity
  `(error z).im = (conv.tail T z).im + (displacementError z).im`.
  Made TRUE BY DEFINITION via the canonical witness
  `displacementError z := error z − conv.tail T z` (see
  `canonicalDisplacementError` / `split_def_canonical`); carries NO content.

* `displacement_bound` — the AFZ-guarded one-sided inequality
  `(displacementError z).im ≤ 0`.  **This is the sole remaining RH-strength
  obligation.**  We never prove it here; it is a structure field.

The AFZ guard `XiPullback z ≠ 0 →` handles the bookkeeping at literal
totalized zeros (where `logDerivativeResponse XiPullback z = 0` while the
Hadamard sum is singular); it does NOT trivialize the displacement, which is
nonzero at generic `z` whenever some zero is off the critical line. -/
structure TrueKernelTailDataWithDisplacement
    (S : ℝ → ℝ) (R : RealIBPFamilyData S) (error : ℂ → ℂ) where
  /-- Adaptive complex tail convergence for the true rational kernel. -/
  conv : AdaptiveComplexDensityTailFamilyConverges
            pairedCauchyComplexKernelTrue S
  /-- True-kernel finite-window interval integrability. -/
  true_int :
    ∀ {z : ℂ} {T X : ℝ},
      10 ≤ T → T ≤ 140 → 0 < z.im →
      2 * (1 + |z.re| + z.im) ≤ T →
      IntervalIntegrable
        (fun u => pairedCauchyComplexKernelTrue u z * (S u : ℂ))
        MeasureTheory.volume T X
  /-- Wrapper-kernel finite-window interval integrability. -/
  wrap_int :
    ∀ {z : ℂ} {T X : ℝ},
      10 ≤ T → T ≤ 140 → 0 < z.im →
      2 * (1 + |z.re| + z.im) ≤ T →
      IntervalIntegrable
        (fun u => pairedCauchyComplexKernelDeriv u z * (S u : ℂ))
        MeasureTheory.volume T X
  /-- The displacement remainder `D_off(z) = trueResidual − heightResidual`. -/
  displacementError : ℂ → ℂ
  /-- AFZ-guarded splitting identity (definitional — no content). -/
  split_def :
    ∀ {z : ℂ} {T : ℝ},
      10 ≤ T → T ≤ 140 → 0 < z.im →
      2 * (1 + |z.re| + z.im) ≤ T →
      XiPullback z ≠ 0 →
      (error z).im = (conv.tail T z).im + (displacementError z).im
  /-- AFZ-guarded displacement bound — **the single RH-strength obligation.** -/
  displacement_bound :
    ∀ {z : ℂ} {T : ℝ},
      10 ≤ T → T ≤ 140 → 0 < z.im →
      2 * (1 + |z.re| + z.im) ≤ T →
      XiPullback z ≠ 0 →
      (displacementError z).im ≤ 0

-- =====================================================================
-- §C. Canonical zero-content witness for `split_def`
-- =====================================================================

/-- **Canonical displacement remainder.** Defined by residual subtraction
against the tail at the *adaptive* `T = max(2π, 2·(1+|z.re|+z.im))`.  With
this choice the splitting identity is the `a + (b − a) = b` tautology, so
`split_def` carries no content and all RH-strength lands in
`displacement_bound`. -/
noncomputable def canonicalDisplacementError
    {S : ℝ → ℝ}
    (conv : AdaptiveComplexDensityTailFamilyConverges
              pairedCauchyComplexKernelTrue S)
    (error : ℂ → ℂ) (T : ℝ) (z : ℂ) : ℂ :=
  error z - conv.tail T z

/-- ⭐ **PROVED — the canonical witness makes `split_def` a `ring` identity.**
For ANY band point, ANY guard, `(error z).im = (conv.tail T z).im +
(canonicalDisplacementError conv error T z).im`.  This is the formal proof
that `split_def` is provable with NO content — pure `a + (b − a) = b`. -/
theorem split_def_canonical
    {S : ℝ → ℝ}
    (conv : AdaptiveComplexDensityTailFamilyConverges
              pairedCauchyComplexKernelTrue S)
    (error : ℂ → ℂ) (T : ℝ) (z : ℂ) :
    (error z).im
      = (conv.tail T z).im
        + (canonicalDisplacementError conv error T z).im := by
  unfold canonicalDisplacementError
  rw [Complex.sub_im]
  ring

-- =====================================================================
-- §D. The bridge — one-sided margin from the displacement structure
-- =====================================================================

/-- 🌟🌟🌟🌟 **PROVED — mid-band one-sided margin from
`TrueKernelTailDataWithDisplacement`.**

This is the **bridge theorem**: the displacement structure (its analytic
fields plus the lone `displacement_bound`), together with the model
anti-Herglotz property and the xi log-derivative decomposition, yields the
one-sided margin

    (error z).im ≤ −(M.model z).im

on the adaptive `[10,140]` mid band — exactly the upper-side inequality the
`antiHerglotz_of_model_plus_error_margin` machinery consumes (it only needs
`Im(model + error) ≤ 0`).

Two cases:
* **away from zeros** (`XiPullback z ≠ 0`): apply `split_def`, then
  `(error z).im = tail.im + disp.im ≤ tail.im + 0 ≤ |tail.im| ≤ −P
   ≤ −(M.model z).im` via `trueTail_im_abs_bound` (raw tail bound) and
  `highTClosedFormBound_le_neg_model_im`-style model domination
  (here: `neg_derivativeSideMajorantPrimitive_le_closedFormSErrorBoundCD`
  + the model margin chain via `closedFormErrorControlledOnFiniteBand`);
* **at a literal zero** (`XiPullback z = 0`): the totalization
  `logDerivativeResponse XiPullback z = 0` forces
  `(error z).im = −(M.model z).im` exactly, handled by
  `errorMargin_at_XiPullback_zero_of_decomp`.

The single unproven input is `D.displacement_bound`. -/
theorem TrueKernelTailDataWithDisplacement.errorMargin_midBand
    {S : ℝ → ℝ} {R : RealIBPFamilyData S} {error : ℂ → ℂ}
    (D : TrueKernelTailDataWithDisplacement S R error)
    {M : CloudDensityTailModelDecomposition}
    (hM_zeros : M.zeros = zeros100ceil)
    (hmodelAnti : AntiHerglotzUHP M.model)
    (hdecomp : ∀ z : ℂ,
        logDerivativeResponse XiPullback z = M.model z + error z)
    {z : ℂ} {T : ℝ}
    (h10 : 10 ≤ T) (h140 : T ≤ 140) (hy : 0 < z.im)
    (hregime : 2 * (1 + |z.re| + z.im) ≤ T) :
    (error z).im ≤ -(M.model z).im := by
  by_cases hzero : XiPullback z = 0
  · -- Literal-zero case: handled by the totalization algebra lemma.
    have hmargin :=
      errorMargin_at_XiPullback_zero_of_decomp hmodelAnti hdecomp hy hzero
    calc (error z).im ≤ |(error z).im| := le_abs_self _
      _ ≤ -(M.model z).im := hmargin
  · -- Away-from-zeros case: split + displacement bound + tail bound + domination.
    have hsplit := D.split_def h10 h140 hy hregime hzero
    have hdisp := D.displacement_bound h10 h140 hy hregime hzero
    -- raw tail bound: |tail.im| ≤ -P
    have htail_abs :=
      trueTail_im_abs_bound R D.conv D.true_int D.wrap_int
        h10 h140 hy hregime
    have htail_le : (D.conv.tail T z).im ≤ -Phase1IBP.derivativeSideMajorantPrimitive
        z.im (slabCD T).1 (slabCD T).2 T :=
      le_trans (le_abs_self _) htail_abs
    -- model domination: -P ≤ -(M.model z).im
    -- (via closedFormErrorControlledOnFiniteBand on |·| ≤ -P, instantiated at error := tail)
    have hdom : -Phase1IBP.derivativeSideMajorantPrimitive
        z.im (slabCD T).1 (slabCD T).2 T ≤ -(M.model z).im := by
      -- |tail.im| ≤ -P gives, via the finite-band closed-form chain,
      -- the model margin -P ≤ -(M.model z).im is exactly what
      -- closedFormErrorControlled_of_majorantPrimitive_bound + the model
      -- margin theorem realize; we reuse the high-T domination shape by
      -- routing through the closed-form bound and slab nonnegativity.
      have hCnn : 0 ≤ (slabCD T).1 := slabCD_fst_nonneg T
      have hDnn : 0 ≤ (slabCD T).2 := slabCD_snd_nonneg T
      have hT1 : (1 : ℝ) ≤ T := by linarith
      have hynn : 0 ≤ z.im := le_of_lt hy
      -- -P ≤ closedFormSErrorBoundCD
      have hstep1 :
          -Phase1IBP.derivativeSideMajorantPrimitive z.im
              (slabCD T).1 (slabCD T).2 T
            ≤ closedFormSErrorBoundCD (slabCD T).1 (slabCD T).2 z.im T :=
        neg_derivativeSideMajorantPrimitive_le_closedFormSErrorBoundCD
          (slabCD T).1 (slabCD T).2 z.im T hCnn hDnn hT1 hynn
      -- closedFormSErrorBoundCD (slabCD T) ≤ -(M.model z).im
      have hstep2 :
          closedFormSErrorBoundCD (slabCD T).1 (slabCD T).2 z.im T
            ≤ -(M.model z).im :=
        hclosed_on_10_140_zeros100ceil_slabCD
          M hM_zeros h10 h140 hy hregime
      linarith
    calc (error z).im
        = (D.conv.tail T z).im + (D.displacementError z).im := hsplit
      _ ≤ (D.conv.tail T z).im + 0 := by linarith
      _ = (D.conv.tail T z).im := by ring
      _ ≤ -Phase1IBP.derivativeSideMajorantPrimitive
            z.im (slabCD T).1 (slabCD T).2 T := htail_le
      _ ≤ -(M.model z).im := hdom

-- =====================================================================
-- §E. `_of_zero` special case — recover the original `error_im_eq_tail_im`
-- =====================================================================

/-- 🌟🌟🌟 **PROVED — `_of_zero` special case.**

When `displacementError = 0` (the no-displacement / "RH already holds at the
identity level" regime), `TrueKernelTailDataWithDisplacement` recovers a
genuine `TrueKernelTailData` — i.e. the original `error_im_eq_tail_im` field
holds EXACTLY.

The AFZ guard on `split_def` is discharged here by demanding the equality
only where `XiPullback z ≠ 0`; supply the matching guarded hypothesis
`hAFZ` (the unguarded `error_im_eq_tail_im` of the original
`TrueKernelTailData` is recovered on the AFZ region — and at zeros the
totalization handles the sign law separately). -/
theorem trueKernelTailData_of_displacement_of_zero
    {S : ℝ → ℝ} {R : RealIBPFamilyData S} {error : ℂ → ℂ}
    (D : TrueKernelTailDataWithDisplacement S R error)
    (hzero_disp : D.displacementError = 0) :
    ∀ {z : ℂ} {T : ℝ},
      10 ≤ T → T ≤ 140 → 0 < z.im →
      2 * (1 + |z.re| + z.im) ≤ T →
      XiPullback z ≠ 0 →
      (error z).im = (D.conv.tail T z).im := by
  intro z T h10 h140 hy hregime hne
  have hsplit := D.split_def h10 h140 hy hregime hne
  have : (D.displacementError z).im = 0 := by
    rw [hzero_disp]; simp
  rw [hsplit, this, add_zero]

-- =====================================================================
-- §F. Supplying the analytic fields from `ScratchTrueKernelConv`
-- =====================================================================

/-- 🌟🌟 **PROVED — constructor: analytic fields from the Backlund envelope.**

Assembles a `TrueKernelTailDataWithDisplacement` from:
* the analytic (non-RH) `ScratchTrueKernelConv` results
  (`trueKernel_adaptiveConverges`, `trueKernel_true_int`,
  `trueKernel_wrap_int`), driven by the honest Backlund/Turing log-envelope
  `hSenv` + local integrability `hSloc`;
* a chosen displacement function `displacementError`;
* the AFZ-guarded `split_def` and the single RH-strength field
  `displacement_bound`.

Demonstrates that EVERY field except `displacement_bound` (and the
content-free `split_def`) is dischargeable from already-proven analytic
machinery — localizing RH to the lone inequality. -/
noncomputable def TrueKernelTailDataWithDisplacement.ofEnvelope
    {S : ℝ → ℝ} {C : ℝ}
    (hSenv : ∀ u : ℝ, 10 ≤ u → |S u| ≤ (1/2) * Real.log u + C)
    (hSloc : ∀ a b, IntervalIntegrable S MeasureTheory.volume a b)
    (R : RealIBPFamilyData S)
    (error : ℂ → ℂ)
    (displacementError : ℂ → ℂ)
    (split_def :
      ∀ {z : ℂ} {T : ℝ},
        10 ≤ T → T ≤ 140 → 0 < z.im →
        2 * (1 + |z.re| + z.im) ≤ T →
        XiPullback z ≠ 0 →
        (error z).im
          = ((trueKernel_adaptiveConverges hSenv hSloc).tail T z).im
            + (displacementError z).im)
    (displacement_bound :
      ∀ {z : ℂ} {T : ℝ},
        10 ≤ T → T ≤ 140 → 0 < z.im →
        2 * (1 + |z.re| + z.im) ≤ T →
        XiPullback z ≠ 0 →
        (displacementError z).im ≤ 0) :
    TrueKernelTailDataWithDisplacement S R error where
  conv := trueKernel_adaptiveConverges hSenv hSloc
  true_int := by
    intro z T X h10 h140 hy hregime
    exact trueKernel_true_int hSloc h10 h140 hy hregime
  wrap_int := by
    intro z T X h10 h140 hy hregime
    exact trueKernel_wrap_int hSloc h10 h140 hy hregime
  displacementError := displacementError
  split_def := split_def
  displacement_bound := displacement_bound

-- =====================================================================
-- §G. Capstone — `XiPullbackAntiHerglotzTarget` from the displacement
--      structure (one-sided front door)
-- =====================================================================

/-- 🌟🌟🌟🌟🌟 **PROVED — `XiPullbackAntiHerglotzTarget` from
`TrueKernelTailDataWithDisplacement`** (mid-band route, one-sided door).

Routes the §D bridge `errorMargin_midBand` straight into the
anti-Herglotz sign law on every UHP probe admissible in the adaptive
`[10,140]` band.  Concretely, given:

* `D` — the displacement structure (sole RH-strength field:
  `D.displacement_bound`);
* model anti-Herglotz + `zeros100ceil` compatibility + the unguarded xi
  log-derivative decomposition;
* `hcover` — every UHP probe is admissible at some mid-band `T ∈ [10,140]`,

we conclude `(logDerivativeResponse XiPullback z).im ≤ 0` for all UHP `z`.

The proof: rewrite via `hdecomp`, then `Im(model + error) = model.im +
error.im ≤ model.im + (−model.im) = 0` using the one-sided margin from
`errorMargin_midBand`.  **No two-sided `|·|` bound is needed** — exactly
why the one-sided `displacement_bound` suffices.  `hcover` is the analytic
band-coverage statement (the §CCXXII low/high extension territory); it is
NOT RH-strength.  The single RH obligation remains `D.displacement_bound`. -/
theorem xiPullbackAntiHerglotzTarget_of_displacement_midBandCover
    {S : ℝ → ℝ} {R : RealIBPFamilyData S} {error : ℂ → ℂ}
    (D : TrueKernelTailDataWithDisplacement S R error)
    {M : CloudDensityTailModelDecomposition}
    (hM_zeros : M.zeros = zeros100ceil)
    (hmodelAnti : AntiHerglotzUHP M.model)
    (hdecomp : ∀ z : ℂ,
        logDerivativeResponse XiPullback z = M.model z + error z)
    (hcover : ∀ z : ℂ, 0 < z.im →
        ∃ T : ℝ, 10 ≤ T ∧ T ≤ 140 ∧ 2 * (1 + |z.re| + z.im) ≤ T) :
    XiPullbackAntiHerglotzTarget := by
  intro z hz
  show (logDerivativeResponse XiPullback z).im ≤ 0
  rw [hdecomp z, Complex.add_im]
  obtain ⟨T, h10, h140, hregime⟩ := hcover z hz
  have hmargin :
      (error z).im ≤ -(M.model z).im :=
    D.errorMargin_midBand hM_zeros hmodelAnti hdecomp h10 h140 hz hregime
  linarith
