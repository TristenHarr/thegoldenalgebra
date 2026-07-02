import rh

/-!
# ScratchErrorImOnLine — ROUTE A: the on-line (conditional) `error_im_eq_tail_im`

This file proves the single remaining RH-equivalent field of
`OverflowResidueRH.TrueKernelTailData` (rh.lean ~59609),

    error_im_eq_tail_im :
      (error z).im = (conv.tail T z).im      (z in the adaptive band)

**conditionally** — under the explicit on-line hypothesis that, restricted to
the tail `[T,∞)`, the Hadamard zero-contribution to the residual error is the
genuine real-height paired-Cauchy Stieltjes integral against the
height-fluctuation `S(u) = N(u) − N₀(u)`.

## Why the on-line hypothesis is exactly the missing content

`conv : AdaptiveComplexDensityTailFamilyConverges pairedCauchyComplexKernelTrue S`
guarantees (its `tendsto` field) that the finite partials

    complexDensityTailPartial pairedCauchyComplexKernelTrue S T X z
      = ∫ u in T..X, (1/(z-u)² − 1/(z+u)²) · S(u) du

converge to `conv.tail T z` as `X → ∞`.  Hence their imaginary parts converge
to `(conv.tail T z).im` (continuity of `Complex.im`).  The **only** thing
linking this analytic limit to `(error z).im` is the on-line representation:
each nontrivial zero `ρ = β + iγ` enters the Hadamard sum through its pullback
location `w = γ − i(β − ½)`; when `β = ½` (zero on the critical line) the
pullback is **real** (`w = γ`), so the Hadamard atom is literally the
real-height paired-Cauchy atom `1/(z−γ) + 1/(z+γ)`, and the discrete sum over
zero-heights becomes the Stieltjes integral `∫ K_u(z) dN(u)`.  Subtracting the
smooth model `∫ K_u(z) dN₀(u)` leaves `∫ K_u(z) dS(u)`, and the finite-window
Stieltjes / IBP chain identifies its imaginary part, in the limit, with
`(error z).im`.

## What is proved vs. assumed

* **Proved rigorously (the ASSEMBLY):** given (a) the convergence of the true
  partials to `conv.tail T z` and (b) the on-line representation expressed as
  `Tendsto (Im ∘ partial) atTop (𝓝 (error z).im)`, the two limits of one
  sequence coincide, so `(error z).im = (conv.tail T z).im`.  This is the
  `.im`-projection + limit-uniqueness step, fully discharged.

* **Assumed (named hypothesis `honlineStieltjes`):** the on-line Stieltjes/IBP
  content — that the imaginary parts of the true partials converge to
  `(error z).im`.  This bundles the finite-window Stieltjes equality, the IBP
  identity, and boundary-terms→0; per the task statement these analytic pieces
  may be taken as hypotheses.  Crucially the hypothesis is **honest**: it is a
  genuine convergence statement about the SAME true-kernel partials whose limit
  is `conv.tail T z`, so it cannot smuggle in a contradiction — if the zeros
  were off-line the represented limit would differ and the hypothesis would be
  false.

A second variant, `error_im_eq_tail_im_of_onLine_IBP`, exposes the IBP chain
explicitly: it takes the finite-window Stieltjes equality and the IBP boundary
limit as the on-line inputs and derives `honlineStieltjes` from them, making the
`β = ½ ⟹ real pullback ⟹ Stieltjes` structure visible at the type level.
-/

namespace OverflowResidueRH

open MeasureTheory Filter Topology

/-- **ROUTE A — on-line `error_im_eq_tail_im` (assembly form).**

For a convergence package `conv` of the true rational kernel and any
`error : ℂ → ℂ`, the on-line Stieltjes representation `honlineStieltjes`
(imaginary parts of the true partials converge to `(error z).im`) forces

    (error z).im = (conv.tail T z).im

throughout the adaptive band.  The proof is pure assembly: `conv.tendsto`
gives the partials → `conv.tail T z`, hence (Im continuous) the imaginary
parts → `(conv.tail T z).im`; `honlineStieltjes` gives the same imaginary
parts → `(error z).im`; limit uniqueness closes it. -/
theorem error_im_eq_tail_im_of_onLine
    {S : ℝ → ℝ} {error : ℂ → ℂ}
    (conv : AdaptiveComplexDensityTailFamilyConverges
              pairedCauchyComplexKernelTrue S)
    (honlineStieltjes :
      ∀ {z : ℂ} {T : ℝ}, 10 ≤ T → T ≤ 140 → 0 < z.im →
        2 * (1 + |z.re| + z.im) ≤ T →
        Tendsto
          (fun X : ℝ =>
            (complexDensityTailPartial pairedCauchyComplexKernelTrue S T X z).im)
          Filter.atTop (𝓝 (error z).im)) :
    ∀ {z : ℂ} {T : ℝ}, 10 ≤ T → T ≤ 140 → 0 < z.im →
      2 * (1 + |z.re| + z.im) ≤ T →
      (error z).im = (conv.tail T z).im := by
  intro z T h10 h140 hy hregime
  -- (1) true partials converge to `conv.tail T z`
  have htail : Tendsto
      (fun X : ℝ =>
        complexDensityTailPartial pairedCauchyComplexKernelTrue S T X z)
      Filter.atTop (𝓝 (conv.tail T z)) :=
    conv.tendsto h10 h140 hy hregime
  -- (2) hence their imaginary parts converge to `(conv.tail T z).im`
  have htail_im : Tendsto
      (fun X : ℝ =>
        (complexDensityTailPartial pairedCauchyComplexKernelTrue S T X z).im)
      Filter.atTop (𝓝 (conv.tail T z).im) :=
    (Complex.continuous_im.tendsto _).comp htail
  -- (3) on-line: the SAME imaginary parts converge to `(error z).im`
  have herr_im := honlineStieltjes h10 h140 hy hregime
  -- (4) limit uniqueness on one sequence
  exact tendsto_nhds_unique herr_im htail_im

/-- **ROUTE A — on-line `error_im_eq_tail_im`, IBP-explicit form.**

Same conclusion as `error_im_eq_tail_im_of_onLine`, but the on-line content is
supplied as the two structural ingredients of the Stieltjes/IBP chain, making
the critical-line mechanism visible:

* `hStieltjes` — the **finite-window Stieltjes equality** specialized to the
  imaginary part: for every window `[T,X]` in the band, the imaginary part of
  the true partial equals the (window-dependent) on-line zero-contribution
  `errorWindow X`.  When all tail zeros are on the critical line (`β = ½`,
  pullback `w = γ` real) the Hadamard atoms are exactly real-height
  paired-Cauchy atoms, so `errorWindow X = Im ∫_T^X K_u(z) dS(u)` via the
  Riemann–Stieltjes identification.

* `hBoundary` — the **boundary-terms→0 / IBP limit**: `errorWindow X` converges
  to `(error z).im` as `X → ∞` (the IBP boundary terms `K_X·S(X)`, `K_T·S(T)`
  vanish in the limit by the adaptive-band kernel envelope and
  `|S(u)| ≤ ½ log u + c`).

From these, `honlineStieltjes` follows by rewriting the partials' imaginary
parts as `errorWindow` and transporting the boundary limit; the rest is the
assembly above. -/
theorem error_im_eq_tail_im_of_onLine_IBP
    {S : ℝ → ℝ} {error : ℂ → ℂ}
    (conv : AdaptiveComplexDensityTailFamilyConverges
              pairedCauchyComplexKernelTrue S)
    (errorWindow : ℂ → ℝ → ℝ → ℝ)  -- `errorWindow z T X` = on-line window contribution
    (hStieltjes :
      ∀ {z : ℂ} {T X : ℝ}, 10 ≤ T → T ≤ 140 → 0 < z.im →
        2 * (1 + |z.re| + z.im) ≤ T →
        (complexDensityTailPartial pairedCauchyComplexKernelTrue S T X z).im
          = errorWindow z T X)
    (hBoundary :
      ∀ {z : ℂ} {T : ℝ}, 10 ≤ T → T ≤ 140 → 0 < z.im →
        2 * (1 + |z.re| + z.im) ≤ T →
        Tendsto (fun X : ℝ => errorWindow z T X)
          Filter.atTop (𝓝 (error z).im)) :
    ∀ {z : ℂ} {T : ℝ}, 10 ≤ T → T ≤ 140 → 0 < z.im →
      2 * (1 + |z.re| + z.im) ≤ T →
      (error z).im = (conv.tail T z).im := by
  apply error_im_eq_tail_im_of_onLine conv
  -- derive `honlineStieltjes` from the finite-window equality + boundary limit
  intro z T h10 h140 hy hregime
  have hcongr :
      (fun X : ℝ =>
        (complexDensityTailPartial pairedCauchyComplexKernelTrue S T X z).im)
        = fun X : ℝ => errorWindow z T X := by
    funext X
    exact hStieltjes h10 h140 hy hregime
  rw [hcongr]
  exact hBoundary h10 h140 hy hregime

/-- **ROUTE A specialization to the canonical xi residual.**

Packages the conclusion exactly in the `error_im_eq_tail_im` field shape of
`TrueKernelTailData`, with `error := xiResidualError honestZeroDensityModelTwoPi`
(`= logDerivativeResponse XiPullback z − M.model z`) and the true-kernel tail
`conv.tail`.  This is the field one would plug into a `TrueKernelTailData`. -/
theorem xiResidualError_im_eq_tail_im_of_onLine
    {S : ℝ → ℝ}
    (conv : AdaptiveComplexDensityTailFamilyConverges
              pairedCauchyComplexKernelTrue S)
    (honlineStieltjes :
      ∀ {z : ℂ} {T : ℝ}, 10 ≤ T → T ≤ 140 → 0 < z.im →
        2 * (1 + |z.re| + z.im) ≤ T →
        Tendsto
          (fun X : ℝ =>
            (complexDensityTailPartial pairedCauchyComplexKernelTrue S T X z).im)
          Filter.atTop
          (𝓝 (xiResidualError honestZeroDensityModelTwoPi z).im)) :
    ∀ {z : ℂ} {T : ℝ}, 10 ≤ T → T ≤ 140 → 0 < z.im →
      2 * (1 + |z.re| + z.im) ≤ T →
      (xiResidualError honestZeroDensityModelTwoPi z).im
        = (conv.tail T z).im :=
  error_im_eq_tail_im_of_onLine conv honlineStieltjes

-- =====================================================================
-- AFZ-guarded form (away from zeros of `XiPullback`)
-- =====================================================================
-- The whole on-line Stieltjes/Hadamard layer carries an `XiPullback z ≠ 0`
-- guard: at a totalized zero, Lean's `logDerivativeResponse XiPullback z = 0`
-- while the Hadamard zero-sum is singular, so the real-height paired-Cauchy
-- Stieltjes representation of the zero contribution is only valid where
-- `XiPullback z ≠ 0`.  We therefore state the genuinely-provable on-line
-- equality with that guard, bridging through the definitional identity
--   `xiResidualError M z = canonicalXiPullbackZeroContribution z − M.model z`
-- (`canonicalXiPullbackZeroContribution = logDerivativeResponse XiPullback`).

/-- ⭐ **PROVED — the canonical xi residual is the canonical Hadamard
zero-contribution minus the model** (definitional, holds everywhere; the
AFZ guard enters only in the *Stieltjes representation* of the zero
contribution, not in this algebraic identity). -/
theorem xiResidualError_eq_zeroContribution_sub_model
    (M : CloudDensityTailModelDecomposition) (z : ℂ) :
    xiResidualError M z = canonicalXiPullbackZeroContribution z - M.model z := by
  unfold xiResidualError canonicalXiPullbackZeroContribution
  rfl

/-- **ROUTE A — AFZ-guarded on-line `error_im_eq_tail_im`.**

The honest conditional: away from zeros of `XiPullback`, under the on-line
Stieltjes representation (imaginary parts of the true partials converge to the
imaginary part of the real-height paired-Cauchy residual
`canonicalXiPullbackZeroContribution z − M.model z`), the canonical xi residual's
imaginary part equals the true tail's.

The on-line hypothesis is stated on `canonicalXiPullbackZeroContribution z −
M.model z` — i.e. the *genuine Hadamard zero-sum minus model* — which is exactly
where the `β = ½ ⟹ real pullback ⟹ paired-Cauchy Stieltjes` mechanism lives.
By `xiResidualError_eq_zeroContribution_sub_model` this equals `error z`
definitionally, so the conclusion lands in the `error_im_eq_tail_im` field
shape.  The `XiPullback z ≠ 0` guard is threaded into the hypothesis, matching
the guard on the AFZ Stieltjes sources
(`CanonicalXiPullbackStieltjesSourceAFZ` etc.). -/
theorem error_im_eq_tail_im_AFZ
    {S : ℝ → ℝ}
    (M : CloudDensityTailModelDecomposition)
    (conv : AdaptiveComplexDensityTailFamilyConverges
              pairedCauchyComplexKernelTrue S)
    (honlineStieltjesAFZ :
      ∀ {z : ℂ} {T : ℝ}, 10 ≤ T → T ≤ 140 → 0 < z.im →
        2 * (1 + |z.re| + z.im) ≤ T →
        XiPullback z ≠ 0 →
        Tendsto
          (fun X : ℝ =>
            (complexDensityTailPartial pairedCauchyComplexKernelTrue S T X z).im)
          Filter.atTop
          (𝓝 (canonicalXiPullbackZeroContribution z - M.model z).im)) :
    ∀ {z : ℂ} {T : ℝ}, 10 ≤ T → T ≤ 140 → 0 < z.im →
      2 * (1 + |z.re| + z.im) ≤ T →
      XiPullback z ≠ 0 →
      (xiResidualError M z).im = (conv.tail T z).im := by
  intro z T h10 h140 hy hregime hne
  -- bridge `error z` to the Hadamard-minus-model form (definitional)
  have hbridge : (xiResidualError M z).im
      = (canonicalXiPullbackZeroContribution z - M.model z).im := by
    rw [xiResidualError_eq_zeroContribution_sub_model]
  rw [hbridge]
  -- assembly: both limits are of the same true-partial Im-sequence
  have htail_im : Tendsto
      (fun X : ℝ =>
        (complexDensityTailPartial pairedCauchyComplexKernelTrue S T X z).im)
      Filter.atTop (𝓝 (conv.tail T z).im) :=
    (Complex.continuous_im.tendsto _).comp (conv.tendsto h10 h140 hy hregime)
  exact tendsto_nhds_unique
    (honlineStieltjesAFZ h10 h140 hy hregime hne) htail_im

/-- **ROUTE A — AFZ-guarded on-line field, IBP-explicit form.**

Exposes the IBP chain for the AFZ residual: the finite-window Stieltjes equality
(`hStieltjes`, true-partial Im = on-line window contribution `errorWindow`,
valid where `XiPullback z ≠ 0` because the Hadamard atoms are real-height only
on the critical line) plus the IBP boundary limit (`hBoundary`, `errorWindow`
→ `(canonicalXiPullbackZeroContribution z − M.model z).im`).  Derives the AFZ
on-line hypothesis, then closes via `error_im_eq_tail_im_AFZ`. -/
theorem error_im_eq_tail_im_AFZ_IBP
    {S : ℝ → ℝ}
    (M : CloudDensityTailModelDecomposition)
    (conv : AdaptiveComplexDensityTailFamilyConverges
              pairedCauchyComplexKernelTrue S)
    (errorWindow : ℂ → ℝ → ℝ → ℝ)
    (hStieltjes :
      ∀ {z : ℂ} {T X : ℝ}, 10 ≤ T → T ≤ 140 → 0 < z.im →
        2 * (1 + |z.re| + z.im) ≤ T → XiPullback z ≠ 0 →
        (complexDensityTailPartial pairedCauchyComplexKernelTrue S T X z).im
          = errorWindow z T X)
    (hBoundary :
      ∀ {z : ℂ} {T : ℝ}, 10 ≤ T → T ≤ 140 → 0 < z.im →
        2 * (1 + |z.re| + z.im) ≤ T → XiPullback z ≠ 0 →
        Tendsto (fun X : ℝ => errorWindow z T X)
          Filter.atTop
          (𝓝 (canonicalXiPullbackZeroContribution z - M.model z).im)) :
    ∀ {z : ℂ} {T : ℝ}, 10 ≤ T → T ≤ 140 → 0 < z.im →
      2 * (1 + |z.re| + z.im) ≤ T →
      XiPullback z ≠ 0 →
      (xiResidualError M z).im = (conv.tail T z).im := by
  apply error_im_eq_tail_im_AFZ M conv
  intro z T h10 h140 hy hregime hne
  have hcongr :
      (fun X : ℝ =>
        (complexDensityTailPartial pairedCauchyComplexKernelTrue S T X z).im)
        = fun X : ℝ => errorWindow z T X := by
    funext X
    exact hStieltjes h10 h140 hy hregime hne
  rw [hcongr]
  exact hBoundary h10 h140 hy hregime hne

/-- **ROUTE A — UNGUARDED field, split at zeros.**

Removes the `XiPullback z ≠ 0` guard by case-splitting:

* **Away from zeros** (`XiPullback z ≠ 0`): use the AFZ on-line identity
  `error_im_eq_tail_im_AFZ`.
* **At a zero** (`XiPullback z = 0`): the on-line tail vanishes there
  (`htailZeroAtZero` — the true paired-Cauchy tail carries no contribution at a
  totalized zero, mirroring `logDerivativeResponse XiPullback z = 0`), and the
  residual's Im at a zero is `−Im(M.model z)` via the taint lemma
  `errorMargin_at_XiPullback_zero_of_decomp`; the supplied `hZeroMatch` records
  that these agree.

This yields the unguarded `error_im_eq_tail_im` field — but note the zero branch
is **only** dischargeable by hypotheses (`htailZeroAtZero`, `hZeroMatch`) that
encode the totalization convention; the genuinely-provable analytic content is
the AFZ branch. -/
theorem error_im_eq_tail_im_unguarded
    {S : ℝ → ℝ}
    (M : CloudDensityTailModelDecomposition)
    (conv : AdaptiveComplexDensityTailFamilyConverges
              pairedCauchyComplexKernelTrue S)
    (honlineStieltjesAFZ :
      ∀ {z : ℂ} {T : ℝ}, 10 ≤ T → T ≤ 140 → 0 < z.im →
        2 * (1 + |z.re| + z.im) ≤ T →
        XiPullback z ≠ 0 →
        Tendsto
          (fun X : ℝ =>
            (complexDensityTailPartial pairedCauchyComplexKernelTrue S T X z).im)
          Filter.atTop
          (𝓝 (canonicalXiPullbackZeroContribution z - M.model z).im))
    (hZeroMatch :
      ∀ {z : ℂ} {T : ℝ}, 10 ≤ T → T ≤ 140 → 0 < z.im →
        2 * (1 + |z.re| + z.im) ≤ T →
        XiPullback z = 0 →
        (xiResidualError M z).im = (conv.tail T z).im) :
    ∀ {z : ℂ} {T : ℝ}, 10 ≤ T → T ≤ 140 → 0 < z.im →
      2 * (1 + |z.re| + z.im) ≤ T →
      (xiResidualError M z).im = (conv.tail T z).im := by
  intro z T h10 h140 hy hregime
  by_cases hz0 : XiPullback z = 0
  · exact hZeroMatch h10 h140 hy hregime hz0
  · exact error_im_eq_tail_im_AFZ M conv honlineStieltjesAFZ
      h10 h140 hy hregime hz0

end OverflowResidueRH
