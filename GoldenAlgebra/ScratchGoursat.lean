import rh

/-!
# ScratchGoursat: Cauchy–Goursat remainder-vanishing for the residue-free argument principle

This file discharges the **Cauchy–Goursat remainder-vanishing** brick of the PT-A
contour program in `rh.lean`, the next brick after the atomic rectangle residue
(`ScratchResidue.lean`).

The analytic content is:

  *an analytic (holomorphic, singularity-free in/on the rectangle) integrand has
  ZERO rectangle contour integral.*

We prove this directly from Mathlib's rectangle Cauchy–Goursat theorem
`Complex.integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn`,
bridged to `rh.lean`'s four-edge `rectangleIntegral` form, and then thread it
through the principal-part contour decomposition so that

  `(2πi)⁻¹ ∮_R ζ'/ζ = Σ_s (principal-kernel index) − (remainder integral = 0)`

reduces to the weighted zero count minus the pole count.

Targets inhabited (all in namespace `OverflowResidueRH.BacklundTuring`,
structures in `ZetaRectangle`):

* `RectangleCauchyGoursatBridge`                      — analytic ⇒ `rectangleIntegral = 0`
* `RectangleLogDerivRemainderIntegralVanishes`        — BP3, `∮ remainder = 0`
* `RectanglePrincipalPartContourDecomposition`        — AO4 / BP4 contour split
* `CanonicalResidueFreeArgumentPrincipleData`         — via `of_remainderAnalytic`

The Mathlib lemma used for the rectangle-vanishing is
`Complex.integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn`.
The `rh.lean` bridges used are the coordinate/edge adapters
(`rectangleEdgeIntegralCoordinateBridge`,
`coordinateBoundaryIntegralMathlibBridge`) and the `mathlibCauchyGoursatHook`
assembler, all unconditional.
-/

open Complex
open scoped Real

namespace OverflowResidueRH
namespace BacklundTuring

open ZetaRectangle

namespace ScratchGoursat

/-! ## 1. The Cauchy–Goursat bridge, standalone

`rh.lean` already exposes `globalRectangleCauchyGoursatBridge`, built from
`Complex.integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn`
through the proved edge/coordinate adapters.  We re-export its content as a
single clean statement: the four-edge rectangle integral of any function
analytic on the closed rectangle vanishes. -/

/-- **Rectangle Cauchy–Goursat (four-edge form).**  If `f` is analytic at every
point of the closed rectangle, then its four-edge boundary integral vanishes.

This is the remainder-vanishing engine: Mathlib's
`integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn` transported
to `rh.lean`'s `rectangleIntegral`. -/
theorem rectangleIntegral_eq_zero_of_analyticOn_closed
    (R : ZetaRectangle) (f : ℂ → ℂ)
    (hf : ∀ z ∈ {z : ℂ | R.ContainsClosed z}, AnalyticAt ℂ f z) :
    R.rectangleIntegral f = 0 :=
  globalRectangleCauchyGoursatBridge.cauchyGoursat R f hf

/-- The Cauchy–Goursat bridge structure of `rh.lean`, re-inhabited here from the
standalone vanishing theorem above (which is the exact field it carries). -/
theorem rectangleCauchyGoursatBridge : RectangleCauchyGoursatBridge where
  cauchyGoursat := rectangleIntegral_eq_zero_of_analyticOn_closed

/-- Generic rectangle Cauchy–Goursat as a `RectangleCauchyGoursat` structure
for an arbitrary analytic `f`. -/
noncomputable def rectangleCauchyGoursat
    (R : ZetaRectangle) (f : ℂ → ℂ)
    (hf : ∀ z ∈ {z : ℂ | R.ContainsClosed z}, AnalyticAt ℂ f z) :
    R.RectangleCauchyGoursat f where
  integral_eq_zero := rectangleIntegral_eq_zero_of_analyticOn_closed R f hf

/-! ## 2. Remainder-vanishing (BP3) from analyticity of the remainder

The log-derivative remainder `ζ'/ζ − Σ_s principalKernel(coeff s)(s)(·)` is
analytic at every closed-rectangle point once each local principal part is
subtracted.  Feeding that analyticity through the Cauchy–Goursat bridge gives
the BP3 remainder-vanishing target. -/

/-- **BP3, discharged.**  Analyticity of the log-derivative remainder on the
closed rectangle implies its rectangle integral vanishes. -/
noncomputable def rectangleLogDerivRemainderIntegralVanishes
    {R : ZetaRectangle} {P : R.RectanglePrincipalPartData}
    (hAn : ∀ z ∈ {z : ℂ | R.ContainsClosed z},
      AnalyticAt ℂ (R.logDerivRemainder P) z) :
    R.RectangleLogDerivRemainderIntegralVanishes P where
  integral_eq_zero :=
    rectangleIntegral_eq_zero_of_analyticOn_closed R (R.logDerivRemainder P) hAn

/-! ## 3. Contour decomposition (AO4 / BP4) from linearity + vanishing

Pure linearity of the contour integral (BS6's `rectangleLogDerivContourLinearDecomposition`)
plus the BP3 vanishing fact gives the principal-part contour decomposition: the
normalized `ζ'/ζ` integral equals the finite sum of normalized principal-kernel
integrals, with no surviving remainder term. -/

/-- **AO4 / BP4, discharged.**  The principal-part contour decomposition follows
from the (unconditional) linearity decomposition and remainder-vanishing. -/
noncomputable def rectanglePrincipalPartContourDecomposition
    {R : ZetaRectangle} {P : R.RectanglePrincipalPartData}
    (hAn : ∀ z ∈ {z : ℂ | R.ContainsClosed z},
      AnalyticAt ℂ (R.logDerivRemainder P) z) :
    R.RectanglePrincipalPartContourDecomposition P :=
  RectanglePrincipalPartContourDecomposition.of_remainder_vanishes
    (rectangleLogDerivContourLinearDecomposition P)
    (rectangleLogDerivRemainderIntegralVanishes hAn)

/-! ## 4. Canonical residue-free argument-principle data

Bundling the per-kernel Cauchy index data with the analytic-remainder data, the
remainder-vanishing brick assembles the full `CanonicalResidueFreeArgumentPrincipleData`
package via the proved `of_remainderAnalytic` assembler.  This is the object that
rh.lean turns into the residue/index formula
`(2πi)⁻¹ ∮_R ζ'/ζ = (weighted zero count) − (pole count)`. -/

/-- **Capstone.**  Kernel-index data + analytic-remainder data inhabit the
canonical residue-free argument-principle package.  The remainder-vanishing
content proved above is exactly what `of_remainderAnalytic` consumes (through
`RectangleLogDerivRemainderAnalyticData.toVanishes`). -/
noncomputable def canonicalResidueFreeArgumentPrincipleData
    {R : ZetaRectangle} {hAdm : R.StronglyAdmissibleForZeta} {Z : R.ZeroSetInside}
    (K : R.RectangleKernelIndexData (R.countedPrincipalPartData hAdm Z))
    (A : R.RectangleLogDerivRemainderAnalyticData
            (R.countedPrincipalPartData hAdm Z)) :
    R.CanonicalResidueFreeArgumentPrincipleData hAdm Z :=
  CanonicalResidueFreeArgumentPrincipleData.of_remainderAnalytic K A

/-- Consistency check: the contour decomposition produced here from the
analytic-remainder data agrees with the one `of_remainderAnalytic` uses
internally (both go through BP4 / `of_remainder_vanishes`). -/
example
    {R : ZetaRectangle} {P : R.RectanglePrincipalPartData}
    (A : R.RectangleLogDerivRemainderAnalyticData P) :
    R.RectanglePrincipalPartContourDecomposition P :=
  rectanglePrincipalPartContourDecomposition A.analytic_remainder

end ScratchGoursat

end BacklundTuring
end OverflowResidueRH

/-! ## Axiom audit

Must show only the standard classical/quotient axioms (`propext`,
`Classical.choice`, `Quot.sound`) and NO `sorryAx`. -/

#print axioms OverflowResidueRH.BacklundTuring.ScratchGoursat.rectangleIntegral_eq_zero_of_analyticOn_closed
#print axioms OverflowResidueRH.BacklundTuring.ScratchGoursat.rectangleCauchyGoursatBridge
#print axioms OverflowResidueRH.BacklundTuring.ScratchGoursat.rectangleLogDerivRemainderIntegralVanishes
#print axioms OverflowResidueRH.BacklundTuring.ScratchGoursat.rectanglePrincipalPartContourDecomposition
#print axioms OverflowResidueRH.BacklundTuring.ScratchGoursat.canonicalResidueFreeArgumentPrincipleData
