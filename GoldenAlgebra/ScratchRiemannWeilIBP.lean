/-
================================================================================
# ScratchRiemannWeilIBP — the Riemann–Weil explicit-formula improper-IBP identity

This file pushes the genuine analytic heart of Path B: the improper
integration-by-parts (Stieltjes) identity behind the Riemann–Weil explicit
formula for the ξ pullback log derivative

      Λ[Ξ](z) = logDerivativeResponse XiPullback z
              = cloud(z) + smoothTail(z) + ∫_T^∞ kernel(u,z) · dS(u)

with the boundary term `[kernel·primitive]_T^∞ → 0`.

The kernel is the explicit true rational paired-Cauchy kernel
`pairedCauchyComplexKernelTrue u z = 1/(z−u)² − 1/(z+u)²` (≈ `8/u²` decay for
`z` in the upper-half plane, fixed); the primitive is
`finiteFluctuationPrimitive Dzero T0 u = N(u) − N₀(u)` (the discrete zero count
minus the smooth main-term count), i.e. the fluctuation `S(u)`.

--------------------------------------------------------------------------------
## STRUCTURE OF THE PROOF — four legs (per the task)
--------------------------------------------------------------------------------

The whole improper-IBP analytic engine (steps 1–3) is ALREADY proven
unconditionally inside `rh.lean`.  This file re-exposes those proofs in the
explicit-formula form and isolates the genuinely deep measure-theoretic core
(step 4) as ONE minimal named hypothesis.

* **STEP 1 — finite IBP on `[T,X]` (PROVED, unconditional).**
  `finiteIBP_on_window` re-exposes rh's
  `Phase1IBP.finiteFluctuationKernelPartial_true_ibp`:
      `F(T,X) = k(X)·S(X) − ∫_T^X S(u)·k'(u) du`
  the genuine finite-interval Stieltjes IBP (Mathlib FTC IBP +
  summation-by-parts), with NO analytic hypotheses.  The complex true kernel's
  imaginary part is identified with this real IBP integrand via
  `complexTail_im_eq_realDerivativePartial`
  (rh `complexDensityTailPartial_im_eq_derivativeSidePartial`).

* **STEP 2 — boundary term `k(X)·S(X) → 0` (PROVED, from the envelope).**
  `boundary_tendsto_zero` re-exposes rh's `boundary_atTop_of_log_envelope`:
  given the Turing/highLog envelope `|S(X)| ≤ C·log X + D`, the kernel's
  `~1/X²` decay kills `(C·log X + D)/X² → 0`.  This is the elementary squeeze
  the task calls for, driven by the carried envelope.

* **STEP 3 — improper convergence `∫_T^X → ∫_T^∞` (PROVED, from the envelope).**
  `tailValue_exists_mid` / `tailValue_exists_high` re-expose rh's
  `trueKernelComplexTail_converges_at`, producing an actual
  `XiFluctuationTailValue Dzero 10 T z L` (the `X→∞` limit of the complex
  true-kernel partials against `S`).  These ARE the converged tail integrals
  `L = ∫_T^∞ kernel·dS` — proved by the norm-majorant DCT with the log
  majorant `(8/u²)(C·log u + D)`.

* **STEP 4 — the measure decomposition `dN = dN₀ + dS` and the Stieltjes
  representation `Σ_ρ kernel(ρ) = ∫ kernel dN` (ISOLATED, one named hyp).**
  This is the genuinely deep Riemann–Weil content: that the Hadamard
  zero-sum `logDerivativeResponse XiPullback z` (= `Σ_ρ kernel(ρ)`, leg (a),
  discharged definitionally in rh) equals `cloud + smoothTail + L`, i.e. the
  zero-counting measure splits as smooth density `dN₀` (→ `cloud+smoothTail`)
  plus fluctuation `dS` (→ the Stieltjes tail `L`), and the zero sum is the
  integral against `dN`.  Steps 1–3 are exactly the machinery that TURNS this
  measure identity into the analytic explicit formula; the measure identity
  itself is the irreducible residual.  It is isolated as
  `ZeroSumStieltjesMeasureDecomposition` with an honest docstring.

--------------------------------------------------------------------------------
## DELIVERABLE
--------------------------------------------------------------------------------
* finite IBP, boundary→0, improper convergence: PROVED (re-exposed from rh,
  unconditional / envelope-driven), in the explicit-formula form.
* the measure-decomposition core: isolated as the SINGLE named hypothesis
  `ZeroSumStieltjesMeasureDecomposition`, with proof that it yields the full
  `CanonicalXiPullbackStieltjesSource` and hence `XiPullbackAntiHerglotzTarget`.

NO bare `sorry`/`admit`.  `#print axioms` at the bottom shows no `sorryAx`.
================================================================================
-/

import rh

open OverflowResidueRH
open OverflowResidueRH.Phase1IBP
open Complex Filter Topology

namespace OverflowResidueRH.BacklundTuring.ScratchRiemannWeilIBP

/-! ## STEP 1 — the finite-interval improper-IBP identity on `[T, X]`.

The finite Stieltjes IBP `∫_T^X k·dS = [k·S]_T^X − ∫_T^X S·k'` is rh's
`finiteFluctuationKernelPartial_true_ibp`, proved unconditionally from the
Mathlib FTC IBP and ordered summation-by-parts.  We re-expose it here, in the
clean `k(T)·S(T) = 0` (no-atom) form, as the explicit finite IBP the task
asks for, then provide the complex/real Im bridge that connects it to the
complex true-kernel partial used by `XiFluctuationTailValue`. -/

/-- 🌟🌟🌟 **STEP 1 — PROVED (re-exposed): FINITE-WINDOW STIELTJES IBP.**

For an ordered zero window on `[T, X]`, with the no-atom-at-`T` convention,
the finite kernel partial against the fluctuation measure satisfies the genuine
integration-by-parts identity

  `finiteFluctuationKernelPartial D x y T X
     = k(X)·S(X) − k(T)·S(T) − ∫_T^X S(u)·k'(u) du`

where `S = finiteFluctuationPrimitive D T`, `k = pairedCauchyImKernel x y`.
This is unconditional (no analytic Prop hypotheses): it is Mathlib's
finite-interval FTC integration-by-parts composed with ordered
summation-by-parts, packaged in rh as
`orderedWindowFiniteWindowKernelStieltjesIBP`. -/
theorem finiteIBP_on_window
    (D : Phase1IBP.OrderedFluctuationMeasureData)
    (x y T X : ℝ) {m : ℕ}
    (W : Phase1IBP.OrderedWindow D T X m)
    (hT : 0 < T) (hTX : T ≤ X) (hy : 0 < y)
    (hnoT : ∀ j ∈ Finset.range D.n, D.toFluctuationMeasureData.Z j ≠ T) :
    Phase1IBP.finiteFluctuationKernelPartial D x y T X
      =
    pairedCauchyImKernel x y X * Phase1IBP.finiteFluctuationPrimitive D T X
      - pairedCauchyImKernel x y T * Phase1IBP.finiteFluctuationPrimitive D T T
      - ∫ u in T..X,
          Phase1IBP.finiteFluctuationPrimitive D T u
            * pairedCauchyImKernelDeriv x y u :=
  (Phase1IBP.orderedWindowFiniteWindowKernelStieltjesIBP
    D x y T X W hT hTX hy hnoT).finite_ibp_at_X

/-- 🌟🌟 **STEP 1 (complex bridge) — PROVED (re-exposed): the imaginary part
of the COMPLEX derivative-side partial equals the REAL one.**

The true kernel's `Im`-derivative partial against `S` is exactly the real IBP
derivative-side integral `∫_T^X S·k'`.  This is the bridge that lets the
complex-tail `XiFluctuationTailValue` (whose `L` is a complex integral) be
controlled by the real IBP machinery of steps 1–2.  (rh
`complexDensityTailPartial_im_eq_derivativeSidePartial`, wrapper kernel.) -/
theorem complexTail_im_eq_realDerivativePartial
    (S : ℝ → ℝ) (x y T X : ℝ) :
    (complexDensityTailPartial
        pairedCauchyComplexKernelDeriv S T X (upperHalfPoint x y)).im
      = Phase1IBP.derivativeSidePartial S x y T X :=
  complexDensityTailPartial_im_eq_derivativeSidePartial S x y T X

/-- 🌟🌟🌟 **STEP 1 (eventual form) — PROVED (re-exposed): the finite IBP
holds for all sufficiently large `X`** under window-invariant ordered-tail
data.  This is the form actually consumed by the improper limit (step 3): the
boundary correction `k(X)·S(X)` and the derivative-side integral are taken to
`X → ∞`. -/
theorem finiteIBP_eventually
    (D : Phase1IBP.OrderedFluctuationMeasureData) (x y T : ℝ) {m : ℕ}
    (Wtail : Phase1IBP.OrderedTailWindowData D T m)
    (hT : 0 < T) (hy : 0 < y) :
    ∀ᶠ X in Filter.atTop,
      Phase1IBP.finiteFluctuationKernelPartial D x y T X =
        pairedCauchyImKernel x y X
            * Phase1IBP.finiteFluctuationPrimitive D T X
          - Phase1IBP.derivativeSidePartial
              (fun U => Phase1IBP.finiteFluctuationPrimitive D T U) x y T X :=
  Phase1IBP.finiteFluctuationKernelPartial_true_ibp_eventually D x y T Wtail hT hy

/-! ## STEP 2 — the IBP boundary term tends to zero.

`k(X)·S(X) → 0` as `X → ∞`.  This is exactly the elementary squeeze the task
describes: `|k(X)| ≤ C/X²` (the explicit `~1/X²` decay of the paired-Cauchy
kernel for fixed `z` with `Im z > 0`) times `|S(X)| ≤ ½ log X + c` (the
Turing/highLog log envelope, carried as the hypothesis `hS`), giving
`(½ log X + c)/X² → 0`.  rh proves this as `boundary_atTop_of_log_envelope`. -/

/-- 🌟🌟🌟 **STEP 2 — PROVED (re-exposed): BOUNDARY TERM → 0** under the log
envelope.  Given `|S(X)| ≤ C·log X + D` eventually (the Turing / high-log
envelope), the IBP boundary correction `k(X)·S(X)` tends to `0`.

This is the genuine boundary-vanishing leg.  Internally rh squeezes
`|k(X)·S(X)| ≤ 8·y·(C+|D|+1)/X → 0` from the kernel's `~y/X²` decay and the
`log X / X → 0` rate. -/
theorem boundary_tendsto_zero
    {S : ℝ → ℝ} {C D : ℝ} (x y : ℝ)
    (hy : 0 ≤ y) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hS : ∀ᶠ X in Filter.atTop, |S X| ≤ C * Real.log X + D) :
    Tendsto (fun X => pairedCauchyImKernel x y X * S X)
      Filter.atTop (𝓝 0) :=
  boundary_atTop_of_log_envelope x y hy hC hD hS

/-- 🌟🌟🌟 **STEP 2 (specialized) — PROVED: boundary → 0 for the actual
fluctuation primitive**, with the envelope supplied in the
`PathBTuringEnvelopeInputs` shape.  Concretely instantiates
`boundary_tendsto_zero` at `S = finiteFluctuationPrimitive Dzero 10` using the
high-log envelope `½·log u + 49/20` (any fixed `z` with `Im z > 0` and
`T ≥ 140` in the adaptive regime). -/
theorem boundary_tendsto_zero_pullback
    (Dzero : Phase1IBP.OrderedFluctuationMeasureData)
    {z : ℂ} {T : ℝ}
    (hT : 140 ≤ T) (hy : 0 < z.im)
    (hregime : 2 * (1 + |z.re| + z.im) ≤ T)
    (hHighLog :
      ∀ {z : ℂ} {T u : ℝ},
        140 ≤ T → 0 < z.im →
        2 * (1 + |z.re| + z.im) ≤ T →
        T ≤ u →
        |Phase1IBP.finiteFluctuationPrimitive Dzero 10 u|
          ≤ (1 / 2 : ℝ) * Real.log u + (49 / 20 : ℝ)) :
    Tendsto
      (fun X => pairedCauchyImKernel z.re z.im X
                  * Phase1IBP.finiteFluctuationPrimitive Dzero 10 X)
      Filter.atTop (𝓝 0) := by
  have hS : ∀ᶠ X in Filter.atTop,
      |Phase1IBP.finiteFluctuationPrimitive Dzero 10 X|
        ≤ (1 / 2 : ℝ) * Real.log X + (49 / 20 : ℝ) := by
    filter_upwards [Filter.eventually_ge_atTop T] with X hTX
    exact hHighLog hT hy hregime hTX
  exact boundary_tendsto_zero z.re z.im hy.le (by norm_num) (by norm_num) hS

/-! ## STEP 3 — improper convergence `∫_T^X → ∫_T^∞`.

The finite partials of the true complex kernel against `S` converge as
`X → ∞`; the limit `L` is the improper Stieltjes tail `∫_T^∞ kernel·dS`.  rh
proves this by a norm-majorant DCT (the integrand is dominated eventually by
the integrable log majorant `(8/u²)(C·log u + D)`), giving the converged tail
value `XiFluctuationTailValue`. -/

/-- 🌟🌟🌟 **STEP 3 (mid band) — PROVED (re-exposed): the improper tail
integral converges, producing a named `XiFluctuationTailValue`.**

For `z` in the mid band (some `T ∈ [10,140]` with `T ≥ 2(1+|x|+y)`), the
complex true-kernel partials against `S = finiteFluctuationPrimitive Dzero 10`
over `[canonicalAdaptiveT z, X]` converge to a limit `L` — the improper
Stieltjes tail `∫_{T}^∞ kernel·dS`.  Driven by the Turing envelope. -/
theorem tailValue_exists_mid
    (Dzero : Phase1IBP.OrderedFluctuationMeasureData)
    (hTuring :
      ∀ {z : ℂ} {T u : ℝ},
        10 ≤ T → T ≤ 140 → 0 < z.im →
        2 * (1 + |z.re| + z.im) ≤ T →
        T ≤ u →
        |Phase1IBP.finiteFluctuationPrimitive Dzero 10 u|
          ≤ (slabCD T).1 * Real.log u + (slabCD T).2)
    {z : ℂ}
    (hy : 0 < z.im)
    (hmid : ∃ T : ℝ, 10 ≤ T ∧ T ≤ 140 ∧ 2 * (1 + |z.re| + z.im) ≤ T) :
    ∃ L : ℂ, XiFluctuationTailValue Dzero 10 (canonicalAdaptiveT z) z L :=
  ⟨_, XiFluctuationTailValue.trueKernelAdaptiveTail_mid
        Dzero 10 (by norm_num) (by norm_num) hTuring hy hmid⟩

/-- 🌟🌟🌟 **STEP 3 (high band) — PROVED (re-exposed): the improper tail
integral converges in the high band `T ≥ 140`**, producing a named
`XiFluctuationTailValue`.  Same norm-majorant DCT, fixed cutoff `T`, driven by
the high-log envelope `½·log u + 49/20`.  Routes through the general-envelope
producer `trueKernelComplexTail_converges_at_of_logEnvelope`. -/
theorem tailValue_exists_high
    (Dzero : Phase1IBP.OrderedFluctuationMeasureData)
    (hHighLog :
      ∀ {z : ℂ} {T u : ℝ},
        140 ≤ T → 0 < z.im →
        2 * (1 + |z.re| + z.im) ≤ T →
        T ≤ u →
        |Phase1IBP.finiteFluctuationPrimitive Dzero 10 u|
          ≤ (1 / 2 : ℝ) * Real.log u + (49 / 20 : ℝ))
    {z : ℂ} {T : ℝ}
    (h140 : 140 ≤ T) (hy : 0 < z.im)
    (hregime : 2 * (1 + |z.re| + z.im) ≤ T) :
    ∃ L : ℂ, XiFluctuationTailValue Dzero 10 T z L := by
  have hTpos : 0 < T := lt_of_lt_of_le (by norm_num : (0:ℝ) < 140) h140
  have hT10 : (10 : ℝ) ≤ T := le_trans (by norm_num) h140
  have hSlogEnv :
      ∀ᶠ u in Filter.atTop,
        |Phase1IBP.finiteFluctuationPrimitive Dzero 10 u|
          ≤ (1 / 2 : ℝ) * Real.log u + (49 / 20 : ℝ) := by
    filter_upwards [Filter.eventually_ge_atTop T] with u hTu
    exact hHighLog h140 hy hregime hTu
  obtain ⟨L, hL⟩ :=
    trueKernelComplexTail_converges_at_of_logEnvelope
      Dzero 10 (by norm_num) hT10 hTpos hy hSlogEnv
  exact ⟨L, ⟨hL⟩⟩

/-- 🌟🌟🌟 **STEPS 2+3 bundled — PROVED: from the two raw log envelopes, both
mid- and high-band improper tails converge.**

This packages exactly the convergence facts the Stieltjes equality consumes,
discharged from the same envelopes that drive the boundary→0 leg.  It is the
analytic substance of the explicit formula, modulo the measure identity. -/
theorem tailConvergence_of_envelopes
    (Dzero : Phase1IBP.OrderedFluctuationMeasureData)
    (hTuring :
      ∀ {z : ℂ} {T u : ℝ},
        10 ≤ T → T ≤ 140 → 0 < z.im →
        2 * (1 + |z.re| + z.im) ≤ T →
        T ≤ u →
        |Phase1IBP.finiteFluctuationPrimitive Dzero 10 u|
          ≤ (slabCD T).1 * Real.log u + (slabCD T).2)
    (hHighLog :
      ∀ {z : ℂ} {T u : ℝ},
        140 ≤ T → 0 < z.im →
        2 * (1 + |z.re| + z.im) ≤ T →
        T ≤ u →
        |Phase1IBP.finiteFluctuationPrimitive Dzero 10 u|
          ≤ (1 / 2 : ℝ) * Real.log u + (49 / 20 : ℝ)) :
    (∀ {z : ℂ},
        0 < z.im →
        (∃ T : ℝ, 10 ≤ T ∧ T ≤ 140 ∧ 2 * (1 + |z.re| + z.im) ≤ T) →
        ∃ L : ℂ, XiFluctuationTailValue Dzero 10 (canonicalAdaptiveT z) z L)
    ∧
    (∀ {z : ℂ} {T : ℝ},
        140 ≤ T → 0 < z.im → 2 * (1 + |z.re| + z.im) ≤ T →
        ∃ L : ℂ, XiFluctuationTailValue Dzero 10 T z L) :=
  ⟨fun hy hmid => tailValue_exists_mid Dzero hTuring hy hmid,
   fun hT hy hregime => tailValue_exists_high Dzero hHighLog hT hy hregime⟩

/-! ## STEP 4 — the measure decomposition `dN = dN₀ + dS` and the Stieltjes
representation of the zero sum.  THE IRREDUCIBLE DEEP RESIDUAL.

Everything above (finite IBP, boundary→0, improper convergence) is the
machinery that converts a measure identity into the analytic explicit formula.
The remaining genuinely deep content is the measure identity itself:

  `Σ_ρ pairedCauchyKernel(ρ)  =  ∫_T^∞ kernel · dN₀  +  ∫_T^∞ kernel · dS`

i.e. the Hadamard regularized zero sum `logDerivativeResponse XiPullback z`
(= `Σ_ρ kernel(ρ)`, leg (a), discharged definitionally in rh as
`canonicalXiPullbackZeroContribution`) equals the smooth main term
`cloud(z) + smoothTail(z)` (the `dN₀` part) plus the converged fluctuation tail
`L` (the `dS` part `∫ kernel·dS`).

This is precisely the Riemann–von Mangoldt zero-counting-measure decomposition
plus the Stieltjes representation `Σ_ρ = ∫ dN` of the zero sum.  It is what an
analytic proof would establish by the argument principle / Stieltjes
representation of `ξ'/ξ`; here it is the one irreducible measure-theoretic
input, carried as `ZeroSumStieltjesMeasureDecomposition`. -/

/-- 📦 **THE SINGLE ISOLATED MEASURE-DECOMPOSITION RESIDUAL (step 4).**

`ZeroSumStieltjesMeasureDecomposition Dzero` asserts, for the actual ξ pullback
log derivative `canonicalXiPullbackZeroContribution = logDerivativeResponse
XiPullback` (= `Σ_ρ kernel(ρ)`), the Riemann–Weil measure identity in each
band:

* **mid / high** — with `L` the converged improper Stieltjes tail
  `∫_T^∞ kernel·dS` (a `XiFluctuationTailValue`):
        `Σ_ρ kernel(ρ) = cloud(z) + smoothTail(z) + L`,
  i.e. `dN = dN₀ + dS`, the smooth `dN₀` integral being the main term
  `cloud + smoothTail` and the `dS` integral being the tail `L`.

* **low** — on `lowCompactRegion`, under the first-zero gap on `[11,14]`, the
  imaginary part of `Σ_ρ kernel(ρ) − (cloud + smoothTail)` equals the finite
  boundary-plus-Stieltjes contribution `lowFiniteFluctuationContribution`.

HONEST GAP.  This is the genuine deep Riemann–Weil content and is NOT proved
here.  Steps 1–3 (finite IBP, boundary→0, improper convergence) are exactly the
machinery that turns this measure identity into the analytic explicit formula —
those ARE proved unconditionally / from the envelopes.  What remains is the
identification of the regularized zero sum with the integral against the
zero-counting measure and its smooth/fluctuation split — the argument-principle
/ Stieltjes-representation step beyond Mathlib.  It is definitionally exactly
rh's open `XiZeroContributionStieltjesEqualitySource Dzero 10
canonicalXiPullbackZeroContribution`. -/
def ZeroSumStieltjesMeasureDecomposition
    (Dzero : Phase1IBP.OrderedFluctuationMeasureData) : Prop :=
  XiZeroContributionStieltjesEqualitySource
    Dzero 10 canonicalXiPullbackZeroContribution

/-- 🌟 **PROVED — the measure residual is definitionally rh's canonical
Stieltjes source.**  Pure `rfl`: confirms we isolated EXACTLY rh's open object,
with no strengthening or weakening. -/
theorem measureDecomposition_eq_canonicalSource
    (Dzero : Phase1IBP.OrderedFluctuationMeasureData) :
    ZeroSumStieltjesMeasureDecomposition Dzero
      = CanonicalXiPullbackStieltjesSource Dzero :=
  rfl

/-- 🌟🌟 **PROVED — the mid/high half of the measure decomposition is exactly
the Stieltjes mid/high tail equality** (`Σ_ρ = cloud + smoothTail + L`), and
the low half is the low first-zero formula.  These are the two natural legs an
analytic proof attacks independently; the bundling is structural. -/
theorem measureDecomposition_iff_midHigh_low
    (Dzero : Phase1IBP.OrderedFluctuationMeasureData) :
    ZeroSumStieltjesMeasureDecomposition Dzero ↔
      (CanonicalXiPullbackMidHighStieltjesEquality Dzero
        ∧ CanonicalXiPullbackLowFirstZeroFormula Dzero) :=
  ⟨fun H => ⟨H.midHigh_eq, H.low_eq⟩, fun H => ⟨H.1, H.2⟩⟩

/-! ## ASSEMBLY — steps 1–3 (proved) + step 4 (the measure residual) ⟹ Path B.

The boundary→0 and improper-convergence legs are discharged from the Turing /
high-log envelopes (the `PathBTuringEnvelopeInputs`).  The finite IBP is
unconditional.  The ONLY remaining mathematical input is the measure
decomposition (step 4). -/

/-- 🌟🌟🌟🌟🌟 **PROVED — Path B from the measure-decomposition residual.**

```
ZeroSumStieltjesMeasureDecomposition Dzero    (THE deep measure identity, step 4)
+ PathBTuringEnvelopeInputs Dzero              (drives boundary→0 + convergence)
+ h_Z_ge_15                                    (trivial first-zero gap)
⟹ XiPullbackAntiHerglotzTarget
```

The finite IBP (step 1) is unconditional; the boundary→0 (step 2) and improper
convergence (step 3) are discharged inside rh's capstone from the carried
envelopes.  Leg (a) [Hadamard zero sum] is the definitional
`canonicalXiPullbackZeroContribution`; leg (c) [smooth main-term
cancellation] is the `rfl` model decomposition.  The sole open mathematics is
the measure decomposition residual. -/
theorem xiPullbackAntiHerglotzTarget_of_measureDecomposition
    (Dzero : Phase1IBP.OrderedFluctuationMeasureData)
    (h_Z_ge_15 : ∀ i : ℕ, (15 : ℝ) ≤ Dzero.toFluctuationMeasureData.Z i)
    (Hmeasure : ZeroSumStieltjesMeasureDecomposition Dzero)
    (Hturing : PathBTuringEnvelopeInputs Dzero) :
    XiPullbackAntiHerglotzTarget :=
  XiPullbackAntiHerglotzTarget_of_canonicalXiPullbackStieltjesSource_turingBundle
    Dzero h_Z_ge_15 Hmeasure Hturing

/-- 🌟🌟🌟🌟🌟 **PROVED — Path B from the measure decomposition with unbundled
envelopes.**  The two raw log envelopes — which simultaneously drive the
boundary→0 (step 2) and the improper convergence (step 3) — are supplied
directly. -/
theorem xiPullbackAntiHerglotzTarget_of_measureDecomposition_envelopes
    (Dzero : Phase1IBP.OrderedFluctuationMeasureData)
    (h_Z_ge_15 : ∀ i : ℕ, (15 : ℝ) ≤ Dzero.toFluctuationMeasureData.Z i)
    (Hmeasure : ZeroSumStieltjesMeasureDecomposition Dzero)
    (hTuring :
      ∀ {z : ℂ} {T u : ℝ},
        10 ≤ T → T ≤ 140 → 0 < z.im →
        2 * (1 + |z.re| + z.im) ≤ T →
        T ≤ u →
        |Phase1IBP.finiteFluctuationPrimitive Dzero 10 u|
          ≤ (slabCD T).1 * Real.log u + (slabCD T).2)
    (hHighLog :
      ∀ {z : ℂ} {T u : ℝ},
        140 ≤ T → 0 < z.im →
        2 * (1 + |z.re| + z.im) ≤ T →
        T ≤ u →
        |Phase1IBP.finiteFluctuationPrimitive Dzero 10 u|
          ≤ (1 / 2 : ℝ) * Real.log u + (49 / 20 : ℝ)) :
    XiPullbackAntiHerglotzTarget :=
  xiPullbackAntiHerglotzTarget_of_measureDecomposition
    Dzero h_Z_ge_15 Hmeasure
    (PathBTuringEnvelopeInputs.of_envelopes Dzero hTuring hHighLog)

/-- 🌟🌟🌟🌟🌟 **PROVED — Path B from the two split measure legs directly.**
Exposes the mid/high Stieltjes equality (`Σ_ρ = cloud + smoothTail + L`) and
the low first-zero formula as the two independent measure-decomposition inputs,
each the target of one independent analytic argument. -/
theorem xiPullbackAntiHerglotzTarget_of_midHigh_low_measure
    (Dzero : Phase1IBP.OrderedFluctuationMeasureData)
    (h_Z_ge_15 : ∀ i : ℕ, (15 : ℝ) ≤ Dzero.toFluctuationMeasureData.Z i)
    (HmidHigh : CanonicalXiPullbackMidHighStieltjesEquality Dzero)
    (Hlow : CanonicalXiPullbackLowFirstZeroFormula Dzero)
    (Hturing : PathBTuringEnvelopeInputs Dzero) :
    XiPullbackAntiHerglotzTarget :=
  xiPullbackAntiHerglotzTarget_of_measureDecomposition
    Dzero h_Z_ge_15
    ((measureDecomposition_iff_midHigh_low Dzero).mpr ⟨HmidHigh, Hlow⟩)
    Hturing

/-! ## Axiom check — the whole chain must be free of `sorryAx`. -/

#print axioms finiteIBP_on_window
#print axioms finiteIBP_eventually
#print axioms complexTail_im_eq_realDerivativePartial
#print axioms boundary_tendsto_zero
#print axioms boundary_tendsto_zero_pullback
#print axioms tailValue_exists_mid
#print axioms tailValue_exists_high
#print axioms tailConvergence_of_envelopes
#print axioms measureDecomposition_eq_canonicalSource
#print axioms measureDecomposition_iff_midHigh_low
#print axioms xiPullbackAntiHerglotzTarget_of_measureDecomposition
#print axioms xiPullbackAntiHerglotzTarget_of_midHigh_low_measure

end OverflowResidueRH.BacklundTuring.ScratchRiemannWeilIBP
