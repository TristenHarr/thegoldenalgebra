import rh
import ScratchEnergyKernel

/-!
# `KernelForm` for a finite cutoff and continuous amplitude

This scratch file discharges the **value (Fubini) leg** of the `KernelForm`
interchange from `ScratchEnergyKernel.lean` and isolates the remaining
**differentiation-under-the-integral** leg as a single honest named hypothesis.

## Target

`KernelForm Phi A x y` (see `ScratchEnergyKernel`) is the identity

```
∂_y ‖∫₀^A Φ(u)·cos((x+iy)u) du‖²
  =  ∫₀^A ∫₀^A Φ(u)·Φ(v)·xiCosDoubleKernel u v x y du dv.
```

For a **finite** cutoff `A` and a **continuous** amplitude `Φ` this is standard
measure theory on the compact square `[0,A]²`.  We split it into the two
classical legs and close the first one outright.

## Leg 1 — the value/Fubini expansion (PROVEN: `energy_eq_doubleIntegral`)

For `0 ≤ A` and continuous `Φ`,

```
‖finiteCosTransform Φ A z‖²  =  ∫₀^A ∫₀^A Φ(u)·Φ(v)·cosKer u v z du dv.
```

Proof chain (all unconditional, no `sorry`):

* `‖w‖² = (w · conj w).re`        (`Complex.normSq_eq_norm_sq` + `Complex.mul_conj`),
* `conj (finiteCosTransform Φ A z) = ∫₀^A Φ(v)·conj(cos (z v)) dv`
  (`MeasureTheory.integral_conj`, `Φ` real so the conjugate only hits the cosine),
* the **product of two interval integrals is a double integral**
  (`MeasureTheory.setIntegral_prod_mul` / `setIntegral_prod`, the integrand being
  continuous on the compact square hence integrable),
* `(∫∫ …).re = ∫∫ (…).re` (`MeasureTheory.integral_re`, again by integrability),
* and pointwise `(Φ(u)·cos(z u) · Φ(v)·conj(cos (z v))).re = Φ(u)·Φ(v)·cosKer u v z`.

## Leg 2 — differentiation under the double integral (ISOLATED)

The only remaining fact is moving `∂_y` inside the (now established) double
integral:

```
∂_y ∫₀^A ∫₀^A Φ(u)·Φ(v)·cosKer u v (verticalLine x y) du dv
  =  ∫₀^A ∫₀^A Φ(u)·Φ(v)·∂_y cosKer u v (verticalLine x y) du dv.
```

Since `∂_y cosKer u v (verticalLine x y) = xiCosDoubleKernel u v x y` *definitionally*
(`xiCosDoubleKernel_eq_deriv_cosKer`), this is exactly the differentiation-under-
the-integral interchange — the standard `hasDerivAt_integral_of_dominated_…`
application on the compact square, with the `y`-derivative of the jointly-smooth
integrand dominated by a constant on `[0,A]²`.  It is isolated here as the single
named hypothesis `DiffUnderDoubleIntegral Phi A x y` with an honest docstring.

`KernelForm` then follows for continuous `Φ` and `0 ≤ A` by combining the proven
value expansion (rewritten as an equality of `y`-functions) with this one
interchange (`kernelForm_of_continuous`).

#print axioms on `energy_eq_doubleIntegral` and `kernelForm_of_continuous`:
only `propext`, `Classical.choice`, `Quot.sound` — no `sorryAx`.
-/

namespace OverflowResidueRH
namespace BacklundTuring
namespace ScratchKernelForm

open Complex MeasureTheory
open scoped ComplexConjugate

open OverflowResidueRH.XiDoubleKernel
open OverflowResidueRH.BacklundTuring.ScratchEnergyKernel

/-! ## §1. Pointwise rewriting of `cosKer` -/

/-- **`cosKer` as a real part of a complex product.**  Definitional unfolding of
`cosKer u v z = (cos (z u)·conj (cos (z v))).re`. -/
theorem cosKer_eq_re (u v : ℝ) (z : ℂ) :
    cosKer u v z = (Complex.cos (z * (u : ℂ)) * conj (Complex.cos (z * (v : ℂ)))).re :=
  rfl

/-- **Pointwise integrand identity.**  With `f u = Φ(u)·cos (z u)` and
`g v = Φ(v)·conj(cos (z v))`, the real part of `f u · g v` is the kernel weight
`Φ(u)·Φ(v)·cosKer u v z`. -/
theorem re_fg_eq (Phi : ℝ → ℝ) (z : ℂ) (u v : ℝ) :
    ((((Phi u : ℝ) : ℂ) * Complex.cos (z * (u : ℂ)))
        * (((Phi v : ℝ) : ℂ) * conj (Complex.cos (z * (v : ℂ))))).re
      = Phi u * Phi v * cosKer u v z := by
  rw [cosKer_eq_re]
  -- Reassociate so the two real scalars multiply the complex cos·conj-cos product.
  have hreorder :
      ((((Phi u : ℝ) : ℂ) * Complex.cos (z * (u : ℂ)))
          * (((Phi v : ℝ) : ℂ) * conj (Complex.cos (z * (v : ℂ)))))
        = (((Phi u * Phi v : ℝ) : ℂ))
            * (Complex.cos (z * (u : ℂ)) * conj (Complex.cos (z * (v : ℂ)))) := by
    push_cast; ring
  rw [hreorder, Complex.re_ofReal_mul]

/-! ## §2. Integrability of the factors and of the product on the square -/

/-- The `u`-factor `u ↦ Φ(u)·cos (z u)` is continuous when `Φ` is. -/
theorem continuous_uFactor {Phi : ℝ → ℝ} (hPhi : Continuous Phi) (z : ℂ) :
    Continuous (fun u : ℝ => ((Phi u : ℝ) : ℂ) * Complex.cos (z * (u : ℂ))) := by
  fun_prop

/-- The `v`-factor `v ↦ Φ(v)·conj(cos (z v))` is continuous when `Φ` is. -/
theorem continuous_vFactor {Phi : ℝ → ℝ} (hPhi : Continuous Phi) (z : ℂ) :
    Continuous (fun v : ℝ => ((Phi v : ℝ) : ℂ) * conj (Complex.cos (z * (v : ℂ)))) := by
  fun_prop

/-- The uncurried product `(u,v) ↦ f u · g v` is continuous on `ℝ²`. -/
theorem continuous_product {Phi : ℝ → ℝ} (hPhi : Continuous Phi) (z : ℂ) :
    Continuous (fun p : ℝ × ℝ =>
      (((Phi p.1 : ℝ) : ℂ) * Complex.cos (z * (p.1 : ℂ)))
        * (((Phi p.2 : ℝ) : ℂ) * conj (Complex.cos (z * (p.2 : ℂ))))) := by
  fun_prop

/-- The product is integrable on the compact square `Icc 0 A ×ˢ Icc 0 A`. -/
theorem integrableOn_product_Icc {Phi : ℝ → ℝ} (hPhi : Continuous Phi) (z : ℂ) (A : ℝ) :
    IntegrableOn
      (fun p : ℝ × ℝ =>
        (((Phi p.1 : ℝ) : ℂ) * Complex.cos (z * (p.1 : ℂ)))
          * (((Phi p.2 : ℝ) : ℂ) * conj (Complex.cos (z * (p.2 : ℂ)))))
      (Set.Icc 0 A ×ˢ Set.Icc 0 A) (volume.prod volume) :=
  (continuous_product hPhi z).continuousOn.integrableOn_compact
    (isCompact_Icc.prod isCompact_Icc)

/-- The product is integrable on the half-open square `Ioc 0 A ×ˢ Ioc 0 A`
(restrict the compact-square integrability to the subset). -/
theorem integrableOn_product_Ioc {Phi : ℝ → ℝ} (hPhi : Continuous Phi) (z : ℂ) (A : ℝ) :
    IntegrableOn
      (fun p : ℝ × ℝ =>
        (((Phi p.1 : ℝ) : ℂ) * Complex.cos (z * (p.1 : ℂ)))
          * (((Phi p.2 : ℝ) : ℂ) * conj (Complex.cos (z * (p.2 : ℂ)))))
      (Set.Ioc 0 A ×ˢ Set.Ioc 0 A) (volume.prod volume) :=
  (integrableOn_product_Icc hPhi z A).mono_set
    (Set.prod_mono Set.Ioc_subset_Icc_self Set.Ioc_subset_Icc_self)

/-! ## §3. Leg 1 — the value/Fubini expansion -/

/-- **PROVED — energy value expansion (Fubini leg).**  For `0 ≤ A` and continuous
`Φ`, the squared norm of the finite cosine transform is the double integral of the
cosine-product real kernel:

`‖finiteCosTransform Φ A z‖²  =  ∫₀^A ∫₀^A Φ(u)·Φ(v)·cosKer u v z du dv`.

This is the pure `‖·‖² = Re(·conj·)` + Fubini step (no differentiation). -/
theorem energy_eq_doubleIntegral {Phi : ℝ → ℝ} (hPhi : Continuous Phi)
    {A : ℝ} (hA : 0 ≤ A) (z : ℂ) :
    ‖finiteCosTransform Phi A z‖ ^ 2
      = ∫ u in (0 : ℝ)..A, ∫ v in (0 : ℝ)..A, Phi u * Phi v * cosKer u v z := by
  -- Abbreviations for the two factors.
  set f : ℝ → ℂ := fun u => ((Phi u : ℝ) : ℂ) * Complex.cos (z * (u : ℂ)) with hf
  set g : ℝ → ℂ := fun v => ((Phi v : ℝ) : ℂ) * conj (Complex.cos (z * (v : ℂ))) with hg
  -- `finiteCosTransform Φ A z = ∫ u in 0..A, f u`.
  have htrans : finiteCosTransform Phi A z = ∫ u in (0 : ℝ)..A, f u := rfl
  -- Step 0: `‖w‖² = (w · conj w).re`.
  rw [htrans]
  have hnorm : ∀ w : ℂ, ‖w‖ ^ 2 = (w * conj w).re := by
    intro w
    rw [← Complex.normSq_eq_norm_sq, Complex.mul_conj, Complex.ofReal_re]
  rw [hnorm]
  -- `conj (∫ f) = ∫ conj f = ∫ g` (Φ real, conj hits only the cosine).
  have hconj : conj (∫ u in (0 : ℝ)..A, f u) = ∫ v in (0 : ℝ)..A, g v := by
    rw [intervalIntegral.integral_of_le hA, intervalIntegral.integral_of_le hA]
    rw [← integral_conj]
    refine setIntegral_congr_fun measurableSet_Ioc ?_
    intro v _
    simp only [hf, hg, map_mul, Complex.conj_ofReal]
  rw [hconj]
  -- Convert ALL interval integrals (LHS factor `∫f`, `∫g`, and RHS doubles) to set
  -- integrals over `Ioc 0 A`.
  simp only [intervalIntegral.integral_of_le hA]
  -- Product of the two set integrals is the double set integral on the square.
  rw [← setIntegral_prod_mul f g (Set.Ioc 0 A) (Set.Ioc 0 A)]
  -- Integrability of the product over the *restricted product measure*.
  have hint_prod :
      Integrable
        (fun p : ℝ × ℝ =>
          (((Phi p.1 : ℝ) : ℂ) * Complex.cos (z * (p.1 : ℂ)))
            * (((Phi p.2 : ℝ) : ℂ) * conj (Complex.cos (z * (p.2 : ℂ)))))
        ((volume.restrict (Set.Ioc 0 A)).prod (volume.restrict (Set.Ioc 0 A))) := by
    rw [Measure.prod_restrict]
    exact integrableOn_product_Ioc hPhi z A
  -- Fubini: the prod integral equals the iterated set integral.
  rw [setIntegral_prod _ (integrableOn_product_Ioc hPhi z A)]
  -- Take real parts: push `.re` through the outer then inner integral.
  refine
    (integral_re (𝕜 := ℂ) ?_).symm.trans ?_
  · -- integrability of `u ↦ ∫ v in Ioc, f u * g v` on `Ioc 0 A`
    exact hint_prod.integral_prod_left
  · -- inner: rewrite each `(∫ v, f u * g v).re` and the pointwise integrand
    refine setIntegral_congr_fun measurableSet_Ioc ?_
    intro u _
    simp only []
    -- `Re (∫ v in Ioc, f u * g v) = ∫ v in Ioc, Re (f u * g v)`
    rw [← integral_re (𝕜 := ℂ)]
    · refine setIntegral_congr_fun measurableSet_Ioc ?_
      intro v _
      simpa [hf, hg] using re_fg_eq Phi z u v
    · -- integrability of `v ↦ f u * g v` on `Ioc 0 A` (continuous, compact subset)
      have : Continuous (fun v : ℝ => f u * g v) := by
        simp only [hf, hg]; fun_prop
      exact (this.integrableOn_Icc (a := 0) (b := A)).mono_set Set.Ioc_subset_Icc_self

/-! ## §4. Leg 2 — the isolated differentiation-under-the-integral residual -/

/-- **Differentiation under the double integral (isolated residual).**  At the
probe `(x, y)`, the `y`-derivative of the double integral of the cosine-product
real kernel along the vertical line equals the double integral of the `y`-derivative
of the kernel:

```
∂_y ∫₀^A ∫₀^A Φ(u)·Φ(v)·cosKer u v (verticalLine x y) du dv
  =  ∫₀^A ∫₀^A Φ(u)·Φ(v)·(∂_y cosKer u v (verticalLine x ·)) y du dv.
```

This is the *only* remaining analytic fact: the differentiation-under-the-integral
interchange on the compact square `[0,A]²`.  It is the standard
`hasDerivAt_integral_of_dominated_loc_of_deriv_le` application — the `y`-derivative
of the jointly-smooth integrand `(u,v) ↦ Φ(u)Φ(v)·cosKer u v (x+iy)` is dominated
by a constant on the compact square — applied once for the outer and once for the
inner interval integral.  It is isolated as a named hypothesis so the value
expansion above remains fully discharged.  Note the inner integrand on the RHS is
literally `Φ(u)·Φ(v)·xiCosDoubleKernel u v x y` after
`xiCosDoubleKernel_eq_deriv_cosKer`. -/
def DiffUnderDoubleIntegral (Phi : ℝ → ℝ) (A x y : ℝ) : Prop :=
  deriv (fun yy : ℝ =>
      ∫ u in (0 : ℝ)..A, ∫ v in (0 : ℝ)..A,
        Phi u * Phi v * cosKer u v (verticalLine x yy)) y
    = ∫ u in (0 : ℝ)..A, ∫ v in (0 : ℝ)..A,
        Phi u * Phi v *
          deriv (fun yy : ℝ => cosKer u v (verticalLine x yy)) y

/-! ## §5. Assembly — `KernelForm` for continuous `Φ` and finite `A` -/

/-- **PROVED — `KernelForm` from continuity + the one isolated interchange.**
For continuous `Φ` and `0 ≤ A`, the value expansion (Leg 1) rewrites the energy
as a `y`-function double integral, and the differentiation-under-the-integral
hypothesis (Leg 2) moves `∂_y` inside.  Since
`∂_y cosKer u v (verticalLine x ·) = xiCosDoubleKernel u v x y` definitionally, the
right-hand side is exactly `finiteDoubleKernelEnergy (xiCosData Phi) A x y`, i.e.
`KernelForm Phi A x y`. -/
theorem kernelForm_of_continuous {Phi : ℝ → ℝ} (hPhi : Continuous Phi)
    {A : ℝ} (hA : 0 ≤ A) (x y : ℝ)
    (hdiff : DiffUnderDoubleIntegral Phi A x y) :
    KernelForm Phi A x y := by
  unfold KernelForm
  -- Rewrite the energy as the double integral, as an equality of `y`-functions.
  have hfun :
      (fun yy : ℝ => ‖finiteCosTransform Phi A (verticalLine x yy)‖ ^ 2)
        = (fun yy : ℝ => ∫ u in (0 : ℝ)..A, ∫ v in (0 : ℝ)..A,
            Phi u * Phi v * cosKer u v (verticalLine x yy)) := by
    funext yy
    exact energy_eq_doubleIntegral hPhi hA (verticalLine x yy)
  rw [hfun, hdiff]
  -- The RHS is the finite double-kernel energy of the explicit-kernel data.
  unfold finiteDoubleKernelEnergy
  simp only [xiCosData_Phi, xiCosData_K, xiCosDoubleKernel_eq_deriv_cosKer]

end ScratchKernelForm
end BacklundTuring
end OverflowResidueRH
