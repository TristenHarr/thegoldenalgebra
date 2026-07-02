import rh

/-!
# ScratchTrueKernelConv — analytic (non-RH) legs of `TrueKernelTailData`

This file proves, as standalone theorems, the two **analytic** fields of
`OverflowResidueRH.TrueKernelTailData` (rh.lean ~59609), taking the proven
Backlund / Turing envelope on the fluctuation `S` as a hypothesis:

  * `conv`    — `AdaptiveComplexDensityTailFamilyConverges pairedCauchyComplexKernelTrue S`
  * `true_int` / `wrap_int` — finite-window interval integrability of the two
                complex integrands on the adaptive band.

The RH-equivalent field `error_im_eq_tail_im` is intentionally *not* proved
here (it is the single remaining hypothesis of the program).

## Hypotheses used (all honest, all passed as arguments)

  * `S : ℝ → ℝ`
  * `hSenv : ∀ u, 10 ≤ u → |S u| ≤ (1/2) * Real.log u + C`  (the proven
    Backlund / Turing log-envelope P1, for some real constant `C`).
  * `hSloc : ∀ a b, IntervalIntegrable S volume a b`  (local interval
    integrability of `S`).  This is the minimal honest regularity needed to
    turn the *continuous* kernel into an integrable product; the kernel
    itself is bounded/continuous off the real axis, so all integrability
    flows from `hSloc` via `IntervalIntegrable.continuousOn_mul`.

## Kernel decay bound

The whole convergence rests on the rh-proven decay
  `‖pairedCauchyComplexKernelTrue u (upperHalfPoint x y)‖ ≤ 8 / u²`
for `0 < u` and `2|x| ≤ u`
(`norm_pairedCauchyComplexKernelTrue_le_eight_div_sq`), giving the
eventual norm-majorant `(8/u²)·((1/2)·log u + C)` whose improper integral
converges (`trueKernelLogMajorantConverges`).
-/

namespace OverflowResidueRH

open MeasureTheory Filter Topology

/-- **Finite-window integrability of `(S : ℂ)`.**  From local interval
integrability of the real `S`, the complex coercion `(S · : ℂ)` is interval
integrable on every window. -/
lemma scratch_ofReal_S_intervalIntegrable
    {S : ℝ → ℝ} (hSloc : ∀ a b, IntervalIntegrable S MeasureTheory.volume a b)
    (a b : ℝ) :
    IntervalIntegrable (fun u => ((S u : ℝ) : ℂ)) MeasureTheory.volume a b :=
  intervalIntegrable_ofReal (hSloc a b)

/-- **`true_int` (adaptive band).**  Finite-window interval integrability of
the *true* rational-kernel integrand `u ↦ pairedCauchyComplexKernelTrue u z · (S u : ℂ)`.

Derived purely from continuity of the kernel in `u` (off the real axis,
`continuous_pairedCauchyComplexKernelTrue_u`) times local interval
integrability of `S` (`hSloc`), via `IntervalIntegrable.continuousOn_mul`.
Holds for *every* `X` (no `T ≤ X` restriction), matching the
`TrueKernelTailData.true_int` field shape. -/
theorem trueKernel_true_int
    {S : ℝ → ℝ} (hSloc : ∀ a b, IntervalIntegrable S MeasureTheory.volume a b) :
    ∀ {z : ℂ} {T X : ℝ},
      10 ≤ T → T ≤ 140 → 0 < z.im →
      2 * (1 + |z.re| + z.im) ≤ T →
      IntervalIntegrable
        (fun u => pairedCauchyComplexKernelTrue u z * (S u : ℂ))
        MeasureTheory.volume T X := by
  intro z T X _h10 _h140 hy _hregime
  -- kernel continuous in u (z.im ≠ 0)
  have hk_cont : Continuous fun u : ℝ => pairedCauchyComplexKernelTrue u z := by
    have h := continuous_pairedCauchyComplexKernelTrue_u z.re z.im (ne_of_gt hy)
    simpa [upperHalfPoint_re_im] using h
  -- (S : ℂ) interval-integrable
  have hS_int : IntervalIntegrable (fun u => ((S u : ℝ) : ℂ))
      MeasureTheory.volume T X :=
    scratch_ofReal_S_intervalIntegrable hSloc T X
  -- product: integrable · continuous
  exact hS_int.continuousOn_mul hk_cont.continuousOn

/-- **`wrap_int` (adaptive band).**  Finite-window interval integrability of
the *wrapper* kernel integrand `u ↦ pairedCauchyComplexKernelDeriv u z · (S u : ℂ)`.

The wrapper kernel `pairedCauchyComplexKernelDeriv u z = (pairedCauchyImKernelDeriv z.re z.im u : ℂ)·I`
is continuous in `u` for `z.im > 0` (`pairedCauchyImKernelDeriv_continuous`),
so the same `continuousOn_mul` argument applies. -/
theorem trueKernel_wrap_int
    {S : ℝ → ℝ} (hSloc : ∀ a b, IntervalIntegrable S MeasureTheory.volume a b) :
    ∀ {z : ℂ} {T X : ℝ},
      10 ≤ T → T ≤ 140 → 0 < z.im →
      2 * (1 + |z.re| + z.im) ≤ T →
      IntervalIntegrable
        (fun u => pairedCauchyComplexKernelDeriv u z * (S u : ℂ))
        MeasureTheory.volume T X := by
  intro z T X _h10 _h140 hy _hregime
  -- wrapper kernel continuous in u via the real Im-kernel continuity
  have hk_cont : Continuous fun u : ℝ => pairedCauchyComplexKernelDeriv u z := by
    unfold pairedCauchyComplexKernelDeriv
    have hreal : Continuous fun u : ℝ => pairedCauchyImKernelDeriv z.re z.im u :=
      Phase1IBP.pairedCauchyImKernelDeriv_continuous hy z.re
    exact (Complex.continuous_ofReal.comp hreal).mul continuous_const
  have hS_int : IntervalIntegrable (fun u => ((S u : ℝ) : ℂ))
      MeasureTheory.volume T X :=
    scratch_ofReal_S_intervalIntegrable hSloc T X
  exact hS_int.continuousOn_mul hk_cont.continuousOn

/-- **Pointwise complex convergence at an adaptive `(z, T)`** for a generic
`S` carrying the Backlund log-envelope.  This is the per-point engine behind
the `conv` field; it mirrors rh's `trueKernelComplexTail_converges_at` but
uses the *generic* envelope `|S u| ≤ (1/2)·log u + C` (constants `1/2, C`)
instead of the finite-fluctuation `slabCD T` data, and gets finite-window
integrability from `hSloc` rather than the finite-fluctuation structure.

Routes through `improperComplexIntegralConverges_of_normMajorant` with the
log majorant `trueKernelLogMajorant (1/2) C` and the kernel decay
`‖kernel u (UHP x y)‖ ≤ 8/u²`. -/
theorem trueKernel_converges_at_of_envelope
    {S : ℝ → ℝ} {C : ℝ}
    (hSenv : ∀ u : ℝ, 10 ≤ u → |S u| ≤ (1/2) * Real.log u + C)
    (hSloc : ∀ a b, IntervalIntegrable S MeasureTheory.volume a b)
    {z : ℂ} {T : ℝ}
    (h10 : 10 ≤ T) (_h140 : T ≤ 140) (hy : 0 < z.im)
    (_hregime : 2 * (1 + |z.re| + z.im) ≤ T) :
    ∃ L : ℂ,
      Tendsto
        (fun X : ℝ =>
          complexDensityTailPartial pairedCauchyComplexKernelTrue S T X z)
        Filter.atTop (𝓝 L) := by
  have hTpos : 0 < T := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 10) h10
  -- majorant integral converges (constants 1/2, C)
  have hMconv :
      Tendsto (fun X : ℝ => ∫ u in T..X, trueKernelLogMajorant (1/2) C u)
        Filter.atTop
        (𝓝 (-trueKernelLogMajorantPrimitive (1/2) C T)) :=
    trueKernelLogMajorantConverges (1/2) C T hTpos
  -- eventual log envelope on |S| (the rh majorant lemma wants atTop form)
  have hS_eventual :
      ∀ᶠ u in Filter.atTop, |S u| ≤ (1/2) * Real.log u + C := by
    filter_upwards [Filter.eventually_ge_atTop (10 : ℝ)] with u hu
    exact hSenv u hu
  -- integrand norm majorant at the UHP point (x = z.re, y = z.im)
  have hbound_uhp :=
    trueKernel_integrand_norm_le_logMajorant_eventually
      (S := S) (C := (1/2)) (D := C) (x := z.re) (y := z.im) hS_eventual
  have hzUHP : upperHalfPoint z.re z.im = z := upperHalfPoint_re_im z
  have hbound :
      ∀ᶠ u in Filter.atTop,
        ‖pairedCauchyComplexKernelTrue u z * (S u : ℂ)‖
          ≤ trueKernelLogMajorant (1/2) C u := by
    filter_upwards [hbound_uhp] with u hu
    rw [hzUHP] at hu
    exact hu
  -- continuity of the true kernel in u (for finite-window integrability)
  have hk_cont : Continuous fun u : ℝ => pairedCauchyComplexKernelTrue u z := by
    have h := continuous_pairedCauchyComplexKernelTrue_u z.re z.im (ne_of_gt hy)
    simpa [upperHalfPoint_re_im] using h
  -- assemble via the Cauchy norm-majorant engine
  apply improperComplexIntegralConverges_of_normMajorant
    (f := fun u => pairedCauchyComplexKernelTrue u z * (S u : ℂ))
    (M := trueKernelLogMajorant (1/2) C)
    (T := T)
    (LM := -trueKernelLogMajorantPrimitive (1/2) C T)
  · -- finite-window integrability of the complex integrand
    intro X _hTX
    have hS_int : IntervalIntegrable (fun u => ((S u : ℝ) : ℂ))
        MeasureTheory.volume T X :=
      scratch_ofReal_S_intervalIntegrable hSloc T X
    exact hS_int.continuousOn_mul hk_cont.continuousOn
  · -- finite-window integrability of the real majorant
    intro X hTX
    exact trueKernelLogMajorant_intervalIntegrable (1/2) C T X hTpos hTX
  · exact hMconv
  · exact hbound

/-- **Adaptive tail value** for a generic `S` with the Backlund envelope.
Extracts the limit guaranteed by `trueKernel_converges_at_of_envelope`
inside the band; `0` outside. -/
noncomputable def trueKernelAdaptiveTailEnv
    {S : ℝ → ℝ} {C : ℝ}
    (hSenv : ∀ u : ℝ, 10 ≤ u → |S u| ≤ (1/2) * Real.log u + C)
    (hSloc : ∀ a b, IntervalIntegrable S MeasureTheory.volume a b)
    (T : ℝ) (z : ℂ) : ℂ :=
  if h : 10 ≤ T ∧ T ≤ 140 ∧ 0 < z.im ∧ 2 * (1 + |z.re| + z.im) ≤ T then
    Classical.choose
      (trueKernel_converges_at_of_envelope hSenv hSloc
        h.1 h.2.1 h.2.2.1 h.2.2.2)
  else
    0

/-- **`conv` field.**  Adaptive complex-tail convergence for the true rational
kernel, for any `S` satisfying the Backlund log-envelope and local interval
integrability.  Identifies the tail with the chosen limit via
`Classical.choose_spec` and transports through `dif_pos`. -/
noncomputable def trueKernel_adaptiveConverges
    {S : ℝ → ℝ} {C : ℝ}
    (hSenv : ∀ u : ℝ, 10 ≤ u → |S u| ≤ (1/2) * Real.log u + C)
    (hSloc : ∀ a b, IntervalIntegrable S MeasureTheory.volume a b) :
    AdaptiveComplexDensityTailFamilyConverges
      pairedCauchyComplexKernelTrue S where
  tail := trueKernelAdaptiveTailEnv hSenv hSloc
  tendsto := by
    intro T z h10 h140 hy hregime
    have hExists :=
      trueKernel_converges_at_of_envelope hSenv hSloc h10 h140 hy hregime
    have hregion :
        10 ≤ T ∧ T ≤ 140 ∧ 0 < z.im ∧ 2 * (1 + |z.re| + z.im) ≤ T :=
      ⟨h10, h140, hy, hregime⟩
    have htail_val :
        trueKernelAdaptiveTailEnv hSenv hSloc T z = Classical.choose hExists := by
      unfold trueKernelAdaptiveTailEnv
      rw [dif_pos hregion]
    rw [htail_val]
    exact Classical.choose_spec hExists

-- =====================================================================
-- AFZ-guarded `error_im_eq_tail_im` and the unguarded margin
-- =====================================================================
--
-- Background (mirrors rh.lean §CLXXXVd-bis, lines ~54507–54561).
-- `logDerivativeResponse XiPullback` totalizes to `0` at zeros of
-- `XiPullback` (Lean's `a / 0 = 0`), while the Hadamard / Stieltjes zero
-- sum is genuinely singular there.  The whole Stieltjes/Hadamard layer
-- therefore carries an `XiPullback z ≠ 0` (AFZ) guard.
--
-- CONSEQUENCE for the `error_im_eq_tail_im` field.  At a UHP zero `ρ`
-- the decomposition `Λ[Ξ] ρ = model ρ + error ρ` with `Λ[Ξ] ρ = 0`
-- forces `error ρ = -model ρ`, hence `(error ρ).im = -(model ρ).im`.
-- This is generally NOT equal to `(conv.tail T ρ).im` (the Cauchy-kernel
-- tail at `ρ`).  So the UNGUARDED *equality* `error_im_eq_tail_im`
-- cannot be proved at zeros without ruling them out (= RH).  What IS
-- unconditionally provable — and what the downstream margin chain
-- actually consumes (`hbound_of_adaptiveComplexTailIBPBoundData`,
-- rh:59086; `LocalXiCloudDensityErrorPackage.errorMargin`) — is the
-- *margin inequality* `|(error z).im| ≤ -(model z).im`, via a
-- `by_cases` on `XiPullback z = 0` exactly as rh's
-- `midLocalPackage_of_canonicalResidualFormulaAwayFromZeros` (rh:68883).
--
-- This section delivers:
--   * `error_im_eq_tail_im_AFZ`  — the honest on-line + AFZ equality;
--   * `errorMargin_unguarded`    — the unconditional margin, via by_cases.

/-- **AFZ-guarded `error_im_eq_tail_im`.**  Off the zero locus of
`XiPullback`, the residual error's imaginary part equals the true-kernel
adaptive tail's imaginary part.

The honest analytic input is `hAFZ`: away from zeros, the true-kernel
complex partials converge to `error z` itself (this is the Stieltjes
explicit-formula / canonical-tail identity — cf. rh's
`XiResidualCanonicalFormulaDataAwayFromZeros.residual_im_eq_canonical_tail`,
rh:68636, and its `of_complex_tendsto` constructor, rh:68696).  Since the
same partials converge to `(trueKernel_adaptiveConverges …).tail T z` by
construction (`conv.tendsto`), uniqueness of limits in `ℂ` gives the
imaginary-part equality.  No claim is made at zeros — the guard is
consumed precisely where `hAFZ` is applied. -/
theorem error_im_eq_tail_im_AFZ
    {S : ℝ → ℝ} {C : ℝ}
    (hSenv : ∀ u : ℝ, 10 ≤ u → |S u| ≤ (1/2) * Real.log u + C)
    (hSloc : ∀ a b, IntervalIntegrable S MeasureTheory.volume a b)
    {error : ℂ → ℂ}
    (hAFZ :
      ∀ {z : ℂ} {T : ℝ}, 10 ≤ T → T ≤ 140 → 0 < z.im →
        2 * (1 + |z.re| + z.im) ≤ T →
        XiPullback z ≠ 0 →
        Tendsto
          (fun X : ℝ =>
            complexDensityTailPartial pairedCauchyComplexKernelTrue S T X z)
          Filter.atTop (𝓝 (error z))) :
    ∀ {z : ℂ} {T : ℝ}, 10 ≤ T → T ≤ 140 → 0 < z.im →
      2 * (1 + |z.re| + z.im) ≤ T →
      XiPullback z ≠ 0 →
      (error z).im
        = ((trueKernel_adaptiveConverges hSenv hSloc).tail T z).im := by
  intro z T h10 h140 hy hregime hne
  -- The partials converge to `error z` (AFZ explicit formula) …
  have h_err :=
    (Complex.continuous_im.tendsto _).comp (hAFZ h10 h140 hy hregime hne)
  -- … and to the constructed tail (by `conv.tendsto`).
  have h_tail :=
    (Complex.continuous_im.tendsto _).comp
      ((trueKernel_adaptiveConverges hSenv hSloc).tendsto h10 h140 hy hregime)
  -- Uniqueness of the (real) limit of the imaginary parts.
  exact tendsto_nhds_unique h_err h_tail

/-- **Unguarded margin `|(error z).im| ≤ -(model z).im`.**  This is the
field actually consumed by the downstream package layer, and — unlike the
*equality* `error_im_eq_tail_im` — it IS provable unconditionally, by a
`by_cases` on `XiPullback z = 0`:

* **away from zeros**: the AFZ identity `error_im_eq_tail_im_AFZ` rewrites
  the goal to a bound on the tail's imaginary part, supplied by
  `htail_margin` (the IBP / anti-Herglotz tail bound — proved
  RH-independently elsewhere; passed here as a hypothesis, mirroring rh's
  `hclosed_on_10_140_zeros100ceil_slabCD` + `trueKernelAdaptiveTail_im_bound`
  chain inside `canonicalMidResidual_errorMargin_AwayFromZeros`, rh:68849);

* **at a zero**: rh's taint lemma `errorMargin_at_XiPullback_zero_of_decomp`
  (rh:54536) gives the bound directly from `hdecomp` + `hmodelAnti`
  (there `error z = -model z`, and anti-Herglotz makes `-(model z).im ≥ 0`).

The guard never leaks: `htail_margin` is only invoked off zeros, and the
zero case is closed purely by the taint lemma. -/
theorem errorMargin_unguarded
    {S : ℝ → ℝ} {C : ℝ}
    (hSenv : ∀ u : ℝ, 10 ≤ u → |S u| ≤ (1/2) * Real.log u + C)
    (hSloc : ∀ a b, IntervalIntegrable S MeasureTheory.volume a b)
    {M : CloudDensityTailModelDecomposition}
    {error : ℂ → ℂ}
    (hmodelAnti : AntiHerglotzUHP M.model)
    (hdecomp : ∀ z : ℂ,
      logDerivativeResponse XiPullback z = M.model z + error z)
    (hAFZ :
      ∀ {z : ℂ} {T : ℝ}, 10 ≤ T → T ≤ 140 → 0 < z.im →
        2 * (1 + |z.re| + z.im) ≤ T →
        XiPullback z ≠ 0 →
        Tendsto
          (fun X : ℝ =>
            complexDensityTailPartial pairedCauchyComplexKernelTrue S T X z)
          Filter.atTop (𝓝 (error z)))
    (htail_margin :
      ∀ {z : ℂ} {T : ℝ}, 10 ≤ T → T ≤ 140 → 0 < z.im →
        2 * (1 + |z.re| + z.im) ≤ T →
        |((trueKernel_adaptiveConverges hSenv hSloc).tail T z).im|
          ≤ -(M.model z).im) :
    ∀ {z : ℂ} {T : ℝ}, 10 ≤ T → T ≤ 140 → 0 < z.im →
      2 * (1 + |z.re| + z.im) ≤ T →
      |(error z).im| ≤ -(M.model z).im := by
  intro z T h10 h140 hy hregime
  by_cases hzero : XiPullback z = 0
  · -- Zero case: rh's totalization-taint lemma (pure algebra).
    exact errorMargin_at_XiPullback_zero_of_decomp hmodelAnti hdecomp hy hzero
  · -- AFZ case: rewrite via the guarded identity, then the tail margin.
    rw [error_im_eq_tail_im_AFZ hSenv hSloc hAFZ h10 h140 hy hregime hzero]
    exact htail_margin h10 h140 hy hregime

end OverflowResidueRH
