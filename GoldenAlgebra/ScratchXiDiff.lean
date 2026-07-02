import rh

/-!
# Closing the `hdiff` residual of the energy / double-kernel route

This scratch file discharges the differentiability obligation `hdiff` that the
energy-route endpoint
`OverflowResidueRH.BacklundTuring.ScratchEnergyKernel.xiPullbackAntiHerglotzTarget_of_integratedPositivity`
threads through.  Reading that file, the exact shape of the residual is

```
hdiff : ∀ z : ℂ, 0 < z.im → DifferentiableAt ℂ XiPullback z
```

(the third explicit hypothesis of `xiPullbackAntiHerglotzTarget_of_integratedPositivity`,
inherited from the reused energy identity
`XiPullbackAntiHerglotzTarget_of_energyMonotone_and_diff`).

## The subtlety: which ξ?

`rh.lean` carries **two** completed-ξ pullbacks:

* `XiPullback z = completedXiFunction ((½ : ℂ) + I·z)` with
  `completedXiFunction s = ½·s·(s−1)·exp(−(s/2)·log π)·Γ(s/2)·ζ(s)`.
  This formula exposes the `Γ(s/2)` poles (which *cancel* the trivial zeros of
  `ζ` in the true ξ, but that cancellation is **not** built into the Lean
  definition).  Hence `XiPullback` is **not** unconditionally differentiable as
  written; `rh.lean` carries the cancellation as the named classical input
  `CompletedXiRegularity` (cf. the comment on
  `CompletedXiDifferentiableOnLeftHalfPlane`).  The genuine theorem is therefore
  `DifferentiableAt ℂ XiPullback z` **from** `CompletedXiRegularity`.

* `EntireXiPullback z = entireRiemannXi ((½ : ℂ) + I·z)` with
  `entireRiemannXi s = ½·s·(s−1)·completedRiemannZeta₀ s + ½`.
  This is **entire by construction** — `completedRiemannZeta₀` is Mathlib's
  entire `Λ₀`, with no poles — so `EntireXiPullback` is differentiable
  **everywhere, unconditionally** (`differentiable_completedZeta₀` + polynomial
  algebra).

So the honest `hdiff` deliverables are:

1. `entireXiPullback_hdiff` — the **unconditional** UHP-`hdiff` shape for the
   entire-by-construction `EntireXiPullback` (no hypotheses at all).
2. `xiPullback_hdiff_of_completedXiRegularity` — the UHP-`hdiff` shape for the
   actual `XiPullback` that `ScratchEnergyKernel` references, from the standard
   `CompletedXiRegularity` regularity input.

Both are reproved here from first principles (chain rule: entire/regular outer ξ
composed with the affine inner `z ↦ ½ + i·z`), so this file is self-contained.

We then *demonstrate* that the `hdiff` shape plugs into the reused energy-route
API `XiPullbackAntiHerglotzTarget_of_energyMonotone_and_diff` (the exact lemma
`ScratchEnergyKernel` calls for the second implication), confirming the shapes
line up exactly.  (We cannot reference `ScratchEnergyKernel` directly here — only
`import rh` is permitted — but `xiPullbackAntiHerglotzTarget_of_integratedPositivity`
literally forwards its `hdiff` argument to this `rh.lean` lemma, so discharging it
here discharges it there.)

## What is PROVED here (no `sorry`, no `admit`)

* `entireRiemannXi_differentiableAt'` / `entireXiPullback_differentiableAt'` —
  re-derivations of entire differentiability of `entireRiemannXi` and
  `EntireXiPullback` (independent of the `rh.lean` copies; ~3 lines each).
* `entireXiPullback_hdiff` — the unconditional `hdiff` shape for `EntireXiPullback`.
* `xiPullback_differentiableAt'` — `XiPullback` differentiable at every point
  from `CompletedXiRegularity` (re-derivation of
  `XiPullback_differentiableAt_of_completedXiRegularity`).
* `xiPullback_hdiff_of_completedXiRegularity` — the `hdiff` shape for `XiPullback`
  from `CompletedXiRegularity` (this is the object `ScratchEnergyKernel` uses).
* `xiPullbackAntiHerglotzTarget_of_energyMonotone_of_completedXiRegularity`
  — the reused endpoint with its `hdiff` hypothesis **discharged** by
  `xiPullback_hdiff_of_completedXiRegularity`, leaving only the genuine
  energy-monotonicity input.

`#print axioms` on the two `hdiff` lemmas and the discharged endpoint: only
`propext`, `Classical.choice`, `Quot.sound` (no `sorryAx`).
-/

namespace OverflowResidueRH
namespace BacklundTuring
namespace ScratchXiDiff

open Complex
open OverflowResidueRH

/-! ## §1. The affine inner map `z ↦ ½ + i·z` is differentiable everywhere -/

/-- **PROVED — the critical-shift inner map is differentiable at every point.**
`z ↦ (½ : ℂ) + I·z` is a constant plus (constant times identity), hence
differentiable everywhere. -/
theorem criticalShift_differentiableAt (z : ℂ) :
    DifferentiableAt ℂ (fun w : ℂ => (1 / 2 : ℂ) + Complex.I * w) z :=
  (differentiableAt_const _).add ((differentiableAt_const _).mul differentiableAt_fun_id)

/-! ## §2. Unconditional `hdiff` for the entire-by-construction `EntireXiPullback` -/

/-- **PROVED (unconditional) — `entireRiemannXi` is differentiable at every
point.**  Re-derivation: `entireRiemannXi s = (½·s·(s−1))·Λ₀(s) + ½` is a
polynomial times the *entire* Mathlib `completedRiemannZeta₀`
(`differentiable_completedZeta₀`) plus a constant. -/
theorem entireRiemannXi_differentiableAt' (s : ℂ) :
    DifferentiableAt ℂ entireRiemannXi s := by
  unfold entireRiemannXi
  have h_poly : DifferentiableAt ℂ
      (fun s : ℂ => (1 / 2 : ℂ) * s * (s - 1)) s :=
    (((differentiableAt_const _).mul differentiableAt_fun_id)).mul
      (differentiableAt_fun_id.sub (differentiableAt_const _))
  have h_zeta₀ : DifferentiableAt ℂ completedRiemannZeta₀ s :=
    differentiable_completedZeta₀ s
  exact (h_poly.mul h_zeta₀).add (differentiableAt_const _)

/-- **PROVED (unconditional) — `EntireXiPullback` is differentiable at every
point.**  Chain rule: the entire outer `entireRiemannXi` composed with the
affine inner `z ↦ ½ + i·z`.  Re-derivation of `EntireXiPullback_differentiable`. -/
theorem entireXiPullback_differentiableAt' (z : ℂ) :
    DifferentiableAt ℂ EntireXiPullback z := by
  unfold EntireXiPullback
  exact (entireRiemannXi_differentiableAt' _).comp z (criticalShift_differentiableAt z)

/-- ⭐ **PROVED (UNCONDITIONAL) — the `hdiff` shape for `EntireXiPullback`.**
This is exactly the `hdiff` hypothesis shape
`∀ z, 0 < z.im → DifferentiableAt ℂ · z` required by the energy-route endpoint,
discharged with **no hypotheses** for the entire-by-construction pullback. -/
theorem entireXiPullback_hdiff :
    ∀ z : ℂ, 0 < z.im → DifferentiableAt ℂ EntireXiPullback z :=
  fun z _ => entireXiPullback_differentiableAt' z

/-! ## §3. `hdiff` for the actual `XiPullback` from `CompletedXiRegularity`

`ScratchEnergyKernel.xiPullbackAntiHerglotzTarget_of_integratedPositivity` is
phrased on `rh.lean`'s `XiPullback` (the `completedXiFunction`-based pullback).
Because `completedXiFunction` exposes `Γ`/`ζ` singularities, its differentiability
is the named classical input `CompletedXiRegularity`.  Given that input, the
`hdiff` shape follows by the same chain rule. -/

/-- **PROVED — `XiPullback` differentiable at every point from
`CompletedXiRegularity`.**  Chain rule: the regular outer `completedXiFunction`
(differentiable everywhere by `CompletedXiRegularity.differentiable`) composed
with the affine inner.  Re-derivation of
`XiPullback_differentiableAt_of_completedXiRegularity`. -/
theorem xiPullback_differentiableAt' (H : CompletedXiRegularity) (z : ℂ) :
    DifferentiableAt ℂ XiPullback z := by
  unfold XiPullback
  exact (H.differentiable _).comp z (criticalShift_differentiableAt z)

/-- ⭐ **PROVED — the `hdiff` shape for `XiPullback` from `CompletedXiRegularity`.**
This is the *exact* hypothesis
`∀ z : ℂ, 0 < z.im → DifferentiableAt ℂ XiPullback z`
that `xiPullbackAntiHerglotzTarget_of_integratedPositivity` (and the reused
`XiPullbackAntiHerglotzTarget_of_energyMonotone_and_diff`) demands. -/
theorem xiPullback_hdiff_of_completedXiRegularity (H : CompletedXiRegularity) :
    ∀ z : ℂ, 0 < z.im → DifferentiableAt ℂ XiPullback z :=
  fun z _ => xiPullback_differentiableAt' H z

/-! ## §4. Plugging `hdiff` into the reused energy-route API

`ScratchEnergyKernel.xiPullbackAntiHerglotzTarget_of_integratedPositivity`
discharges the second implication by *forwarding its `hdiff` argument verbatim*
to `rh.lean`'s `XiPullbackAntiHerglotzTarget_of_energyMonotone_and_diff`.  We
cannot `import` that scratch file here, but we can show our `hdiff` slots into
the very lemma it forwards to — i.e. the shape is exactly right. -/

/-- ⭐ **PROVED — reused energy-route endpoint with `hdiff` discharged.**
`XiPullbackAntiHerglotzTarget` from the genuine analytic mountain
`XiPullbackEnergyMonotoneAwayFromZeros` **plus** `CompletedXiRegularity`, with
the differentiability obligation `hdiff` supplied internally by
`xiPullback_hdiff_of_completedXiRegularity`.  This is
`XiPullbackAntiHerglotzTarget_of_energyMonotone_and_diff` with its first
hypothesis discharged — and that is precisely the `hdiff` that
`ScratchEnergyKernel`'s endpoint forwards. -/
theorem xiPullbackAntiHerglotzTarget_of_energyMonotone_of_completedXiRegularity
    (H : CompletedXiRegularity)
    (hmono : XiPullbackEnergyMonotoneAwayFromZeros) :
    XiPullbackAntiHerglotzTarget :=
  XiPullbackAntiHerglotzTarget_of_energyMonotone_and_diff
    (xiPullback_hdiff_of_completedXiRegularity H) hmono

/-! ## §5. Axiom audit -/

#print axioms entireXiPullback_hdiff
#print axioms xiPullback_hdiff_of_completedXiRegularity
#print axioms xiPullbackAntiHerglotzTarget_of_energyMonotone_of_completedXiRegularity

end ScratchXiDiff
end BacklundTuring
end OverflowResidueRH
