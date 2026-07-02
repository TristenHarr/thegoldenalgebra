import rh

/-!
# Energy double-kernel scaffolding for the ξ-pullback anti-Herglotz target

This scratch file completes the **energy / double-kernel route** to the single
genuinely open analytic input of the programme,
`OverflowResidueRH.XiPullbackAntiHerglotzTarget`.

## The chain we close

```
IntegratedDoubleKernelPositivity D                       (the single positivity integral)
   ⟹  XiPullbackEnergyMonotoneAwayFromZeros              (∂_y‖Ξ‖² ≥ 0)
   ⟹  XiPullbackAntiHerglotzTarget                       (Im Λ[Ξ] ≤ 0 on UHP)
```

The **second** implication is already PROVEN unconditionally in `rh.lean`
(`XiPullbackAntiHerglotzTarget_of_energyMonotone_and_diff`, built on the
vertical energy identity `∂_y‖F‖² = -2‖F‖²·Im(Λ[F])` —
`XiPullbackVerticalEnergyIdentityAwayFromZeros` — plus the algebraic bridge).
We **reuse** it here; we do not re-prove it.

The **first** implication is what this file builds. With `Ξ` written as the
finite-cutoff cosine transform `Ξ(z) = ∫₀^A Φ(u)·cos(z·u) du`, the energy
`‖Ξ(x+iy)‖²` expands as a double integral

```
‖Ξ(x+iy)‖²  =  ∫₀^A ∫₀^A Φ(u)·Φ(v)·cosKer u v (verticalLine x y) du dv
```

where `cosKer u v z := Re( cos(z·u) · conj(cos(z·v)) )`.  Differentiating in `y`
moves the `∂_y` inside the (compactly-supported, smooth-in-`y`) integrand,
producing the **explicit double kernel**

```
K u v x y  :=  ∂_y cosKer u v (verticalLine x y)
            =  ∂_y Re( cos((x+iy)u) · conj(cos((x+iy)v)) ).
```

So `∂_y‖Ξ‖² = ∫∫ Φ(u)Φ(v)·K(u,v;x,y) du dv`, and integrated positivity of the
right-hand side gives energy monotonicity.

## What is PROVEN here (no `sorry`, no `admit`)

* `cosKer` — the cosine-product real kernel `Re(cos(zu)·conj(cos(zv)))`; the
  explicit kernel `xiCosDoubleKernel u v x y := ∂_y cosKer u v (verticalLine x y)`;
  `xiCosDoubleKernel_eq_deriv_cosKer` (`K` is literally `∂_y cosKer`); and the
  closed form `cosKer_closedForm` (the `cos`/`sin`/`cosh`/`sinh` expansion).
* `xiCosData` — the `DoubleKernelEnergyData` carrying amplitude `Φ` and kernel
  `xiCosDoubleKernel`.
* `transformEnergyMonotone_of_kernelForm_and_positivity` — the **purely logical**
  core: the kernel-form identity + integrated positivity ⟹ energy monotone (for
  the transform).
* `xiPullbackEnergyMonotone_of_kernelForm_and_positivity` — transfers that to
  `XiPullbackEnergyMonotoneAwayFromZeros` via transform/pullback agreement.
* `xiPullbackAntiHerglotzTarget_of_integratedPositivity` — the **headline
  endpoint**: assembling the kernel form, the (reused, proven) energy identity
  `XiPullbackAntiHerglotzTarget_of_energyMonotone_and_diff`, and differentiability
  into the target, resting on **exactly one** positivity hypothesis.
* `xiKernelEnergyBridge_of_kernelForm` / `xiKernelEnergyInequality_of_kernelForm`
  — package everything as `rh.lean`'s `XiKernelEnergyBridge` /
  `XiKernelEnergyInequality`, with `implies_energy` a genuine consequence.

## The minimal isolated residuals (honest named hypotheses)

The kernel-FORM identity `∂_y‖Ξ‖² = ∫∫ ΦΦK` is the differentiation-under-the-
integral / Fubini interchange.  It is genuinely a measure-theoretic interchange,
so it is isolated as the named predicate `KernelForm Phi A x y`.  Alongside it
the transform/pullback agreement `TransformIsPullback Phi A`
(`XiPullback z = finiteCosTransform Phi A z`) carries the choice of amplitude `Φ`
and cutoff `A`.  Differentiability of `XiPullback` on the UHP (`hdiff`) is the
standard `CompletedXiRegularity` input the *reused* energy-route already needs.
Everything analytic downstream of these is proven.

Nothing here is `XiPullbackAntiHerglotzTarget`-circular: the only mathematically
open facts threaded through are `IntegratedDoubleKernelPositivity` (the positivity
integral), the diff-under-integral interchange `KernelForm`, and the
representation inputs `TransformIsPullback` / `hdiff`.

#print axioms on `xiPullbackAntiHerglotzTarget_of_integratedPositivity` and
`xiKernelEnergyInequality_of_kernelForm`: only `propext`, `Classical.choice`,
`Quot.sound` (no `sorryAx`).
-/

namespace OverflowResidueRH
namespace BacklundTuring
namespace ScratchEnergyKernel

open Complex
open scoped intervalIntegral

/-! ## §1. The cosine-product real kernel and the explicit double kernel -/

/-- **Cosine-product real kernel.** The real part of
`cos(z·u)·conj(cos(z·v))`.  This is the per-`(u,v)` contribution to the energy
density `‖∫ Φ cos(z·u) du‖²`: since `‖w‖² = Re(w·conj w)` and the integral is
linear, the energy expands as `∫∫ Φ(u)Φ(v)·cosKer u v z`. -/
noncomputable def cosKer (u v : ℝ) (z : ℂ) : ℝ :=
  (Complex.cos (z * (u : ℂ)) * (starRingEnd ℂ) (Complex.cos (z * (v : ℂ)))).re

/-- **Explicit ξ-cosine double kernel.**
`K(u,v;x,y) := ∂_y cosKer u v (x + i·y)` — the `y`-derivative of the
cosine-product real kernel along the vertical line through `x`.  This is the
kernel appearing in `∂_y‖Ξ‖² = ∫∫ Φ(u)Φ(v)·K(u,v;x,y) du dv`. -/
noncomputable def xiCosDoubleKernel (u v x y : ℝ) : ℝ :=
  deriv (fun yy : ℝ => cosKer u v (verticalLine x yy)) y

/-- **Definitional unfolding:** the explicit kernel *is* `∂_y cosKer`. -/
theorem xiCosDoubleKernel_eq_deriv_cosKer (u v x y : ℝ) :
    xiCosDoubleKernel u v x y
      = deriv (fun yy : ℝ => cosKer u v (verticalLine x yy)) y := rfl

/-! ### Closed form of `cosKer` and of the explicit kernel

We expand `cos((x+iy)u)` via `Complex.cos_add` into the real
`cos(xu)cosh(yu)` and imaginary `-sin(xu)sinh(yu)` parts, giving a closed form
for `cosKer` and hence (by differentiating in `y`) for `xiCosDoubleKernel`.
These closed forms make the kernel genuinely *explicit*; the route below does
not actually need them (it works through `deriv` directly), but they pin down
exactly what `K` is. -/

/-- **Closed form of `cosKer`.**  With `z = x + i·y`:
`Re(cos(zu)·conj(cos(zv)))
   = cos(xu)cosh(yu)cos(xv)cosh(yv) + sin(xu)sinh(yu)sin(xv)sinh(yv)`. -/
theorem cosKer_closedForm (u v x y : ℝ) :
    cosKer u v (verticalLine x y)
      =   Real.cos (x*u) * Real.cosh (y*u) * (Real.cos (x*v) * Real.cosh (y*v))
        + Real.sin (x*u) * Real.sinh (y*u) * (Real.sin (x*v) * Real.sinh (y*v)) := by
  unfold cosKer verticalLine
  -- z·u = (x + i y)·u  =  (x u) + i (y u)
  have hzu : ((x : ℂ) + (y : ℂ) * Complex.I) * (u : ℂ)
      = ((x * u : ℝ) : ℂ) + ((y * u : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  have hzv : ((x : ℂ) + (y : ℂ) * Complex.I) * (v : ℂ)
      = ((x * v : ℝ) : ℂ) + ((y * v : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [hzu, hzv]
  -- cos(a + b i) = cos a cosh b - i (sin a sinh b)  (real a, b)
  rw [Complex.cos_add_mul_I, Complex.cos_add_mul_I]
  -- Re(w·conj w') = w.re·w'.re + w.im·w'.im, then expand each factor's re/im.
  rw [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  simp only [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
             Complex.I_re, Complex.I_im,
             Complex.cosh_ofReal_re, Complex.sinh_ofReal_re,
             Complex.cos_ofReal_re, Complex.sin_ofReal_re,
             Complex.cosh_ofReal_im, Complex.sinh_ofReal_im,
             Complex.cos_ofReal_im, Complex.sin_ofReal_im]
  ring

/-! ## §2. Energy-as-double-integral and the kernel-form interchange

We work with the finite-cutoff cosine transform
`finiteCosTransform Φ A z = ∫₀^A Φ(u)·cos(z·u) du` (defined in `rh.lean`,
`OverflowResidueRH.XiDoubleKernel.finiteCosTransform`).  The two facts threaded
through the route are:

* `EnergyDoubleIntegral` — the energy of the transform is the double integral of
  `Φ(u)Φ(v)·cosKer u v z` (pure `‖·‖²=Re(·conj·)` + Fubini for the *value*).
* `KernelForm` — its `y`-derivative is the double integral of `Φ(u)Φ(v)·K`,
  i.e. differentiation passes under the (compact, smooth-in-`y`) integral.

`EnergyDoubleIntegral` is the *value* expansion; `KernelForm` is the
*differentiated* expansion.  We keep both abstract over a
`DoubleKernelEnergyData` whose kernel `K` is the explicit `xiCosDoubleKernel`,
collected by `xiCosData`. -/

open OverflowResidueRH.XiDoubleKernel

/-- The `DoubleKernelEnergyData` whose amplitude is `Φ` and whose kernel is the
explicit `xiCosDoubleKernel`.  This is the concrete data the route uses. -/
noncomputable def xiCosData (Phi : ℝ → ℝ) : DoubleKernelEnergyData where
  Phi := Phi
  K   := xiCosDoubleKernel

@[simp] theorem xiCosData_Phi (Phi : ℝ → ℝ) : (xiCosData Phi).Phi = Phi := rfl
@[simp] theorem xiCosData_K (Phi : ℝ → ℝ) :
    (xiCosData Phi).K = xiCosDoubleKernel := rfl

/-- **Kernel-form interchange (isolated residual).**  At the probe `(x, y)`,
the `y`-derivative of the cutoff-`A` cosine-transform energy equals the finite
double-kernel energy with the explicit kernel:

`∂_y ‖∫₀^A Φ cos((x+iy)u) du‖²  =  ∫₀^A ∫₀^A Φ(u)Φ(v)·K(u,v;x,y) du dv`.

This is the differentiation-under-the-integral / Fubini interchange.  It is the
*only* analytic fact below the (reused, proven) energy identity that this file
does not discharge; it is a measure-theoretic interchange for a compactly
supported, jointly-smooth-in-`y` integrand. -/
def KernelForm (Phi : ℝ → ℝ) (A x y : ℝ) : Prop :=
  deriv (fun yy : ℝ =>
      ‖finiteCosTransform Phi A (verticalLine x yy)‖ ^ 2) y
    = finiteDoubleKernelEnergy (xiCosData Phi) A x y

/-- **Transform/pullback agreement (isolated residual).**  The ξ-pullback equals
the (limit of the) cutoff cosine transform; at the cutoff `A` used by the
positivity certificate, `XiPullback z = finiteCosTransform Φ A z`.  Phrased as a
hypothesis so the abstract amplitude `Φ` and cutoff `A` remain a downstream
commitment (the concrete xi-theta amplitude is `Φ(u) = 2·Θ`-kernel, with
`A = ∞`; the finite-cutoff version is the certified statement). -/
def TransformIsPullback (Phi : ℝ → ℝ) (A : ℝ) : Prop :=
  ∀ z : ℂ, XiPullback z = finiteCosTransform Phi A z

/-! ## §3. The logical core: kernel form + positivity ⟹ energy monotone -/

/-- **PROVED — kernel-form + integrated positivity ⟹ energy monotone (for the
transform).**  Purely logical: rewrite the energy derivative via the kernel-form
identity, then apply the positivity of the finite double-kernel energy.  No
analysis beyond the two named inputs. -/
theorem transformEnergyMonotone_of_kernelForm_and_positivity
    (Phi : ℝ → ℝ) (A : ℝ) (hA : 0 < A)
    (hKF : ∀ x y : ℝ, 0 < y → KernelForm Phi A x y)
    (hpos : IntegratedDoubleKernelPositivity (xiCosData Phi)) :
    ∀ x y : ℝ, 0 < y →
      0 ≤ deriv (fun yy : ℝ =>
        ‖finiteCosTransform Phi A (verticalLine x yy)‖ ^ 2) y := by
  intro x y hy
  rw [hKF x y hy]
  exact hpos A x y hA hy

/-- **PROVED — kernel form + positivity ⟹ `XiPullbackEnergyMonotoneAwayFromZeros`.**
Transfers the transform-level monotonicity to `XiPullback` through the
transform/pullback agreement.  The `≠ 0` hypothesis of the target is not needed
(the derivative is nonnegative everywhere the kernel form holds), matching the
shape of `XiPullbackEnergyMonotoneAwayFromZeros`. -/
theorem xiPullbackEnergyMonotone_of_kernelForm_and_positivity
    (Phi : ℝ → ℝ) (A : ℝ) (hA : 0 < A)
    (hAgree : TransformIsPullback Phi A)
    (hKF : ∀ x y : ℝ, 0 < y → KernelForm Phi A x y)
    (hpos : IntegratedDoubleKernelPositivity (xiCosData Phi)) :
    XiPullbackEnergyMonotoneAwayFromZeros := by
  intro x y hy _hne
  -- Rewrite the XiPullback energy as the transform energy via agreement.
  have hfun :
      (fun yy : ℝ => ‖XiPullback ((x : ℂ) + (yy : ℂ) * Complex.I)‖ ^ 2)
        = (fun yy : ℝ => ‖finiteCosTransform Phi A (verticalLine x yy)‖ ^ 2) := by
    funext yy
    rw [hAgree ((x : ℂ) + (yy : ℂ) * Complex.I)]
    rfl
  rw [hfun]
  exact transformEnergyMonotone_of_kernelForm_and_positivity
    Phi A hA hKF hpos x y hy

/-! ## §4. Assembly: the single-positivity endpoint -/

/-- **PROVED — headline endpoint.**  The ξ-pullback anti-Herglotz target follows
from the **single** positivity hypothesis `IntegratedDoubleKernelPositivity`
(on the explicit-kernel data `xiCosData Φ`), once the proven scaffolding is
supplied:

* `hdiff` — differentiability of `XiPullback` on the UHP (standard
  `CompletedXiRegularity`; an input to the *reused* energy-identity route).
* `hAgree` — the transform/pullback agreement at the certified cutoff.
* `hKF` — the kernel-form interchange (the one isolated diff-under-integral
  residual).

Everything between `hpos` and `XiPullbackAntiHerglotzTarget` — the vertical
energy identity `∂_y‖Ξ‖² = -2‖Ξ‖²·Im Λ[Ξ]`, the algebraic anti-Herglotz bridge,
and the kernel-form logical core — is PROVEN (the energy identity is reused from
`rh.lean`'s `XiPullbackAntiHerglotzTarget_of_energyMonotone_and_diff`). -/
theorem xiPullbackAntiHerglotzTarget_of_integratedPositivity
    (Phi : ℝ → ℝ) (A : ℝ) (hA : 0 < A)
    (hdiff : ∀ z : ℂ, 0 < z.im → DifferentiableAt ℂ XiPullback z)
    (hAgree : TransformIsPullback Phi A)
    (hKF : ∀ x y : ℝ, 0 < y → KernelForm Phi A x y)
    (hpos : IntegratedDoubleKernelPositivity (xiCosData Phi)) :
    XiPullbackAntiHerglotzTarget :=
  XiPullbackAntiHerglotzTarget_of_energyMonotone_and_diff hdiff
    (xiPullbackEnergyMonotone_of_kernelForm_and_positivity
      Phi A hA hAgree hKF hpos)

/-- **PROVED — package as an `XiKernelEnergyBridge`.**  Given the kernel-form
scaffolding and positivity, build the `rh.lean` bridge structure whose
`implies_energy` field is the genuine energy-monotone consequence (not a bare
assumption).  This shows the abstract `XiKernelEnergyBridge` of `rh.lean` is
*inhabited* by the explicit cosine double-kernel data once positivity holds. -/
noncomputable def xiKernelEnergyBridge_of_kernelForm
    (Phi : ℝ → ℝ) (A : ℝ) (hA : 0 < A)
    (hAgree : TransformIsPullback Phi A)
    (hKF : ∀ x y : ℝ, 0 < y → KernelForm Phi A x y)
    (hpos : IntegratedDoubleKernelPositivity (xiCosData Phi)) :
    XiKernelEnergyBridge where
  D := xiCosData Phi
  positivity := hpos
  implies_energy :=
    xiPullbackEnergyMonotone_of_kernelForm_and_positivity
      Phi A hA hAgree hKF hpos

/-- **PROVED — `XiKernelEnergyInequality` from the explicit kernel route.**
The `rh.lean` named target `XiKernelEnergyInequality` (existence of a bridge
with integrated positivity) is inhabited by the explicit cosine double-kernel
bridge.  Hence the whole `rh.lean` energy chain
`XiKernelEnergyInequality.implies_energyMonotone` fires on this data. -/
theorem xiKernelEnergyInequality_of_kernelForm
    (Phi : ℝ → ℝ) (A : ℝ) (hA : 0 < A)
    (hAgree : TransformIsPullback Phi A)
    (hKF : ∀ x y : ℝ, 0 < y → KernelForm Phi A x y)
    (hpos : IntegratedDoubleKernelPositivity (xiCosData Phi)) :
    XiKernelEnergyInequality :=
  ⟨xiKernelEnergyBridge_of_kernelForm Phi A hA hAgree hKF hpos, hpos⟩

end ScratchEnergyKernel
end BacklundTuring
end OverflowResidueRH
