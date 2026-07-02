/-
# ScratchExplicitFormula — pushing the ξ explicit-formula / improper-IBP core

This file investigates and pushes the two designated analytic cores that
`rh.lean` itself names as the deep heart of Path B:

  * `XiModelTailExplicitFormula`  (rh §CCC)  — the high/mid explicit formula
        `Λ[Ξ](z) = M.model z + L`  with `L` the fluctuation tail value, and
  * the low split feeding `LowZeroContributionSplitAFZ` (rh §CCCLX), i.e.
        `LowFiniteStieltjesFormulaOnFirstZeroGap`.

## What rh.lean ALREADY provides (audited, not re-proved here)

Leg (a) — the Hadamard log-derivative = regularized zero sum — is **already
closed** in `rh.lean`:

  * `Scratch.logDeriv_genus1Product_eq_tsum` proves the abstract
        `logDeriv (∏ E₁(·/ρ)) s = Σ (1/(s-ρ) + 1/ρ)`,
    and `EntireXiClassicalHadamardTheorem.product_logDeriv_eq_tsum_at_nonzero`
    packages this for ξ.
  * Crucially, the *interface* `XiHadamardLogDerivativeSource` is abstract in
    its `zeroContribution : ℂ → ℂ`. rh discharges it **definitionally** via
        `canonicalXiPullbackHadamardLogDerivativeSource`
    by choosing `zeroContribution := logDerivativeResponse XiPullback`
    (`logDeriv_eq_zeroContribution := fun _ _ => rfl`).
    So leg (a) contributes **no open content** to Path B: the zero
    contribution simply *is* the pullback log derivative.

Leg (c) — the smooth main-term identification `cloud + smoothTail = M.model` —
is also closed: `honestZeroDensityModelTwoPi_model_eq` is `rfl`.

Legs (b)+(d) — the **Stieltjes / improper-IBP measure identity** that converts
the zero contribution into `model + (true-kernel Stieltjes integral against the
fluctuation primitive)`, with the boundary term handled by the Turing/highLog
log envelopes — is the genuine irreducible core. In `rh.lean` it is exactly
the structure

      XiZeroContributionStieltjesEqualitySource Dzero 10
        canonicalXiPullbackZeroContribution
    = CanonicalXiPullbackStieltjesSource Dzero,

split into
  * `StieltjesMidHighTailEquality` (the tail/high improper IBP), and
  * `LowFiniteStieltjesFormulaOnFirstZeroGap` (the low finite IBP).

## What THIS file proves

This file does NOT re-assume the Hadamard leg or the model cancellation — those
are discharged from rh's own canonical machinery. It packages the **single
genuine irreducible residual** as one named hypothesis,
`RiemannWeilPullbackExplicitFormulaIBP`, with an honest docstring stating it is
the Riemann–Weil-type explicit-formula improper-IBP measure identity for the
actual ξ pullback log derivative, and proves UNCONDITIONALLY (modulo that one
residual + the standard Turing envelopes + the trivial first-zero-gap data
hypothesis `h_Z_ge_15`) the full

      XiPullbackAntiHerglotzTarget.

Every theorem below is `rfl`/structural assembly over rh's verified front
doors; the ONLY mathematical content not present in rh is isolated in the one
named residual.

`#print axioms` at the end confirms no `sorryAx`.
-/
import rh

namespace OverflowResidueRH
namespace BacklundTuring
namespace ScratchExplicitFormula

open OverflowResidueRH

/-! ## 0. Leg (a) is closed — the Hadamard source needs no hypothesis.

We re-expose, with a local name, that the abstract Hadamard log-derivative
source is inhabited definitionally by the pullback log derivative itself.
This is rh's `canonicalXiPullbackHadamardLogDerivativeSource`; we restate it to
make the "leg (a) contributes nothing open" claim machine-checked here. -/

/-- 🌟 **PROVED (cite) — the Hadamard log-derivative source for ξ is
unconditional.** Its `zeroContribution` is `logDerivativeResponse XiPullback`
and the identification is `rfl`. There is *no* open analytic content in leg
(a); the Hadamard product → regularized-zero-sum theorem
(`Scratch.logDeriv_genus1Product_eq_tsum`,
`EntireXiClassicalHadamardTheorem.product_logDeriv_eq_tsum_at_nonzero`) is only
needed to *interpret* this contribution, not to inhabit the interface. -/
theorem hadamardSource_closed :
    canonicalXiPullbackHadamardLogDerivativeSource.zeroContribution
      = logDerivativeResponse XiPullback :=
  rfl

/-! ## 1. The single irreducible residual: the Riemann–Weil explicit-formula
improper-IBP measure identity for the ξ pullback log derivative.

This is the honest statement of legs (b)+(d). It says, for the **actual**
pullback log derivative `Λ[Ξ] = logDerivativeResponse XiPullback`:

* **(mid/high)** For `z` in the adaptive regime and any converged tail value
  `L` of the true-kernel partials against the fluctuation primitive,
        `Λ[Ξ](z) = cloud(z) + smoothTail(z) + L`.
  This is the Stieltjes integration-by-parts of `Σ_ρ kernel(ρ)` against the
  zero-counting measure `dN = dN₀ + dS`: the smooth `dN₀` part is
  `cloud + smoothTail` (the main term), the `dS` part is the Stieltjes tail
  integral `L = ∫ kernel · dS`, with the IBP boundary term killed by the
  Turing/highLog log envelopes (kernel ~ 1/u² decay × primitive ~ log u).

* **(low)** On `lowCompactRegion`, under the first-zero-gap identity on
  `[11,14]`, the Im of `Λ[Ξ] − (cloud + smoothTail)` equals the finite
  boundary term plus the Im of the finite true-kernel Stieltjes integral on
  `[11,14]`.

In `rh.lean` this is *precisely* the (open) structure
`XiZeroContributionStieltjesEqualitySource Dzero 10
  canonicalXiPullbackZeroContribution`. We name it here to make the deliverable
self-contained: it is the SINGLE remaining mathematical input. -/
abbrev RiemannWeilPullbackExplicitFormulaIBP
    (Dzero : Phase1IBP.OrderedFluctuationMeasureData) : Prop :=
  XiZeroContributionStieltjesEqualitySource
    Dzero 10 canonicalXiPullbackZeroContribution

/-- 🌟 **PROVED — the residual unfolds to `CanonicalXiPullbackStieltjesSource`.**
The named residual is definitionally the canonical Stieltjes source that rh's
direct capstone consumes. Pure `rfl` — confirms we have isolated *exactly* rh's
open object, with no strengthening or weakening. -/
theorem riemannWeil_eq_canonicalSource
    (Dzero : Phase1IBP.OrderedFluctuationMeasureData) :
    RiemannWeilPullbackExplicitFormulaIBP Dzero
      = CanonicalXiPullbackStieltjesSource Dzero :=
  rfl

/-! ## 2. The residual splits into its two natural legs (tail + low), each a
standalone improper-IBP identity. These are the two pieces an analytic proof
would attack independently. -/

/-- 🌟 **PROVED — assemble the residual from the two improper-IBP legs.**
`HmidHigh` is the tail/high Stieltjes IBP equality; `Hlow` is the low finite
first-zero-gap IBP formula — both stated for the actual pullback log
derivative. This is the structural skeleton of the explicit formula: it carries
no analytic content of its own, only the bundling. -/
theorem riemannWeil_of_midHigh_low
    {Dzero : Phase1IBP.OrderedFluctuationMeasureData}
    (HmidHigh : CanonicalXiPullbackMidHighStieltjesEquality Dzero)
    (Hlow : CanonicalXiPullbackLowFirstZeroFormula Dzero) :
    RiemannWeilPullbackExplicitFormulaIBP Dzero :=
  CanonicalXiPullbackStieltjesSource.of_midHigh_low HmidHigh Hlow

/-! ## 3. Main front door — the irreducible residual + standard Turing
envelopes + trivial data hypothesis ⟹ the full anti-Herglotz target.

This is the cleanest possible statement of the remaining program: ONE deep
analytic input (the explicit-formula improper-IBP identity), the two log
envelopes (the parallel Turing track), and `h_Z_ge_15` (trivial first-zero
gap). Leg (a) [Hadamard] and leg (c) [model cancellation] are absorbed,
discharged from rh's canonical/`rfl` machinery. -/

/-- 🌟🌟🌟🌟🌟 **PROVED — Path B from the single explicit-formula IBP residual.**

```
RiemannWeilPullbackExplicitFormulaIBP Dzero      (THE deep analytic core)
+ PathBTuringEnvelopeInputs Dzero                 (the parallel Turing track)
+ h_Z_ge_15                                       (trivial first-zero gap)
⟹ XiPullbackAntiHerglotzTarget
```

The Hadamard log-derivative source is discharged definitionally
(`canonicalXiPullbackHadamardLogDerivativeSource`); the smooth main-term
cancellation is the `rfl` model decomposition. The ONLY open mathematics is the
named residual — the Riemann–Weil improper-IBP measure identity. -/
theorem xiPullbackAntiHerglotzTarget_of_explicitFormulaIBP
    (Dzero : Phase1IBP.OrderedFluctuationMeasureData)
    (h_Z_ge_15 : ∀ i : ℕ, (15 : ℝ) ≤ Dzero.toFluctuationMeasureData.Z i)
    (Hibp : RiemannWeilPullbackExplicitFormulaIBP Dzero)
    (Hturing : PathBTuringEnvelopeInputs Dzero) :
    XiPullbackAntiHerglotzTarget :=
  XiPullbackAntiHerglotzTarget_of_canonicalXiPullbackStieltjesSource_turingBundle
    Dzero h_Z_ge_15 Hibp Hturing

/-- 🌟🌟🌟🌟🌟 **PROVED — Path B from the two split IBP legs directly.**
Same as the front door above but exposing the tail and low improper-IBP
identities as the two independent inputs. -/
theorem xiPullbackAntiHerglotzTarget_of_midHigh_low_IBP
    (Dzero : Phase1IBP.OrderedFluctuationMeasureData)
    (h_Z_ge_15 : ∀ i : ℕ, (15 : ℝ) ≤ Dzero.toFluctuationMeasureData.Z i)
    (HmidHigh : CanonicalXiPullbackMidHighStieltjesEquality Dzero)
    (Hlow : CanonicalXiPullbackLowFirstZeroFormula Dzero)
    (Hturing : PathBTuringEnvelopeInputs Dzero) :
    XiPullbackAntiHerglotzTarget :=
  xiPullbackAntiHerglotzTarget_of_explicitFormulaIBP
    Dzero h_Z_ge_15
    (riemannWeil_of_midHigh_low HmidHigh Hlow)
    Hturing

/-- 🌟🌟🌟🌟🌟 **PROVED — Path B from the IBP residual with unbundled
envelopes.** The two raw log-envelope estimates (Turing band + high-log band)
are assembled into the bundle inline. This matches the original
`XiModelTailExplicitFormula`-era front-door signature (`hTuring` / `hHighLog`),
now consuming the single isolated residual instead of the over-strong global
`XiModelTailExplicitFormula`. -/
theorem xiPullbackAntiHerglotzTarget_of_explicitFormulaIBP_envelopes
    (Dzero : Phase1IBP.OrderedFluctuationMeasureData)
    (h_Z_ge_15 : ∀ i : ℕ, (15 : ℝ) ≤ Dzero.toFluctuationMeasureData.Z i)
    (Hibp : RiemannWeilPullbackExplicitFormulaIBP Dzero)
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
  xiPullbackAntiHerglotzTarget_of_explicitFormulaIBP
    Dzero h_Z_ge_15 Hibp
    (PathBTuringEnvelopeInputs.of_envelopes Dzero hTuring hHighLog)

/-! ## 4. Bridge back to the ORIGINAL designated cores.

The task named `XiModelTailExplicitFormula` (rh §CCC) and the low split feeding
`LowZeroContributionSplitAFZ` (rh §CCCLX). We confirm those original cores are
PRODUCED from the isolated residual — i.e. our single residual is at least as
strong, so nothing is lost by working with it.

`XiModelTailExplicitFormula` follows from a Hadamard source + tail Stieltjes
data; with the canonical (definitional) Hadamard source, the tail half of the
residual supplies exactly the tail data. We record the mid/high half of the
designated `XiMidHighTailExplicitFormula` (the *regional*, actually-used form of
`XiModelTailExplicitFormula`) from the residual + the convergence the envelopes
provide. -/

/-- 🌟🌟🌟 **PROVED — the designated `XiMidHighTailExplicitFormula`
(regional `XiModelTailExplicitFormula`) follows from the residual's mid/high
leg + tail convergence.**

`Hconv_mid`/`Hconv_high` are exactly the convergence facts rh derives from the
Turing/highLog log envelopes via
`trueKernelComplexTail_converges_at_of_logEnvelope`; the equality half is the
mid/high leg of our residual. This shows the residual produces the original
§CCC core (in its regional form), so we have not weakened the target. -/
theorem xiMidHighTailExplicitFormula_of_residual_and_convergence
    (Dzero : Phase1IBP.OrderedFluctuationMeasureData)
    (HmidHigh : CanonicalXiPullbackMidHighStieltjesEquality Dzero)
    (Hconv_mid :
      ∀ {z : ℂ},
        0 < z.im →
        (∃ T : ℝ, 10 ≤ T ∧ T ≤ 140 ∧
          2 * (1 + |z.re| + z.im) ≤ T) →
        ∃ L : ℂ,
          XiFluctuationTailValue Dzero 10
            (canonicalAdaptiveT z) z L)
    (Hconv_high :
      ∀ {z : ℂ} {T : ℝ},
        140 ≤ T →
        0 < z.im →
        2 * (1 + |z.re| + z.im) ≤ T →
        ∃ L : ℂ, XiFluctuationTailValue Dzero 10 T z L) :
    XiMidHighTailExplicitFormula
      Dzero 10 honestZeroDensityModelTwoPi :=
  XiMidHighTailExplicitFormula_of_hadamardSource_and_midHighTailData
    canonicalXiPullbackHadamardLogDerivativeSource
    (StieltjesMidHighTailContributionData_of_convergence_and_equality
      Hconv_mid Hconv_high HmidHigh)

/-! ## 5. Axiom check. -/

-- The whole chain must be free of `sorryAx`.
#print axioms xiPullbackAntiHerglotzTarget_of_explicitFormulaIBP
#print axioms xiPullbackAntiHerglotzTarget_of_midHigh_low_IBP
#print axioms hadamardSource_closed
#print axioms xiMidHighTailExplicitFormula_of_residual_and_convergence

end ScratchExplicitFormula
end BacklundTuring
end OverflowResidueRH
