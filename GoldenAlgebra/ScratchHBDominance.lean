import rh
import ScratchEnergyKernel

/-!
# Hermite–Biehler-dominance reformulation of the energy positivity

This scratch file builds the **Hermite–Biehler (HB) dominance** reformulation of
the single open analytic input of the programme — the integrated double-kernel
positivity feeding `OverflowResidueRH.XiPullbackAntiHerglotzTarget`.

## The picture

A prior symbolic computation established that the vertical energy density
`P(x,y) = ¼·∂_y‖Ξ(x+iy)‖²` (equivalently the finite double-kernel energy
`finiteDoubleKernelEnergy (xiCosData Φ) A x y`, up to the factor convention used
below) has a **rank-4 SOS-difference form**

```
P  =  ½(L₁² − L₂² + L₃² − L₄²),
```

where the four real **moment functionals** are the `Φ`-weighted integrals of the
four trig×hyperbolic building blocks

```
a  (w) = cos(xw)·cosh(yw)        a_y(w) = w·cos(xw)·sinh(yw)   (= ∂_y a)
b  (w) = sin(xw)·sinh(yw)        b_y(w) = w·sin(xw)·cosh(yw)   (= ∂_y b)
```

namely

```
L₁ = ∫ Φ·(a + a_y)      L₂ = ∫ Φ·(a − a_y)
L₃ = ∫ Φ·(b + b_y)      L₄ = ∫ Φ·(b − b_y).
```

Packaging the complex transforms `A = L₁ + i·L₃`, `B = L₂ + i·L₄` rewrites this as

```
P  =  ½(‖A‖² − ‖B‖²),
```

so **energy positivity `P ≥ 0` is exactly the modulus dominance `‖B‖ ≤ ‖A‖`** —
a single Hermite–Biehler-type inequality.  This file names that inequality, proves
all the *bridges* around it, and lands the capstone

```
SpecialPhiHBDominance Φ  →  XiPullbackAntiHerglotzTarget,
```

with `SpecialPhiHBDominance Φ` left as the single **unproven** `Prop`.  Proving it
is proving RH; it is **not** proved here and **no** RH-equivalent hypothesis is
assumed.

## What is PROVEN here (no `sorry`, no `admit`)

* The four moment integrands `momentA / momentAy / momentB / momentBy` and their
  `Φ`-weighted functionals `L1 / L2 / L3 / L4`, the complex transforms
  `A_transform = L1 + i·L3`, `B_transform = L2 + i·L4`.
* `def SpecialPhiHBDominance` (the single open modulus inequality `‖B‖ ≤ ‖A‖`),
  `def RankFourDominance` (`L₂²+L₄² ≤ L₁²+L₃²`).
* `theorem hbDominance_iff_rankFour` — `‖A‖² = L₁²+L₃²`, `‖B‖² = L₂²+L₄²`
  (`Complex.normSq` algebra) makes the two forms literally the same inequality.
* `theorem energy_eq_sosDifference` — the **algebraic** SOS-difference reduction
  `½(L₁²−L₂²+L₃²−L₄²) = 2·Ia·Iay + 2·Ib·Iby` (pure `ring`), and
  `def SOSDifferenceForm` isolating the one Fubini/factorization residual
  `finiteDoubleKernelEnergy = 2·Ia·Iay + 2·Ib·Iby`.
* `theorem integratedPositivity_of_rankFour` — `RankFourDominance Φ ⟹
  IntegratedDoubleKernelPositivity (xiCosData Φ)` given `SOSDifferenceForm`.
* `theorem antiHerglotz_of_hbDominance` and the capstone
  `theorem XiPullbackAntiHerglotzTarget_of_specialPhiHBDominance` — composing the
  HB dominance with the EXISTING proven energy→target chain
  (`xiPullbackAntiHerglotzTarget_of_integratedPositivity` from
  `ScratchEnergyKernel`, itself resting on the reused
  `XiPullbackAntiHerglotzTarget_of_energyMonotone_and_diff` of `rh.lean`).

## The isolated, non-circular residuals

The only mathematically open facts threaded through are the **single** modulus
inequality `SpecialPhiHBDominance Φ` (the named missing jump), and the standard
analytic interchanges already isolated in the energy route — here packaged as
`SOSDifferenceForm` (Fubini factorization of the double-kernel energy into the
products of single moments), `TransformIsPullback`, `KernelForm`, and UHP
differentiability `hdiff`.  None of these is `XiPullbackAntiHerglotzTarget`-circular.

`#print axioms` on the capstone: only `propext`, `Classical.choice`, `Quot.sound`
(no `sorryAx`).
-/

namespace OverflowResidueRH
namespace BacklundTuring
namespace ScratchHBDominance

open Complex
open scoped intervalIntegral
open OverflowResidueRH.XiDoubleKernel
open OverflowResidueRH.BacklundTuring.ScratchEnergyKernel

/-! ## §1. The four moment integrands and their `Φ`-weighted functionals

The trig×hyperbolic building blocks of the closed-form kernel
`cosKer u v (x+iy) = a u · a v + b u · b v` (see
`ScratchEnergyKernel.cosKer_closedForm`), together with their `y`-derivatives.
We keep the cutoff `A` and amplitude `Φ` abstract, exactly as the file's
`DoubleKernelEnergyData` route does. -/

/-- `a(w) = cos(xw)·cosh(yw)` — the real part of `cos((x+iy)w)`. -/
noncomputable def momentA (x y w : ℝ) : ℝ := Real.cos (x * w) * Real.cosh (y * w)

/-- `aᵧ(w) = w·cos(xw)·sinh(yw)` — the `y`-derivative `∂_y a(w)`. -/
noncomputable def momentAy (x y w : ℝ) : ℝ := w * Real.cos (x * w) * Real.sinh (y * w)

/-- `b(w) = sin(xw)·sinh(yw)` — minus the imaginary part of `cos((x+iy)w)`. -/
noncomputable def momentB (x y w : ℝ) : ℝ := Real.sin (x * w) * Real.sinh (y * w)

/-- `bᵧ(w) = w·sin(xw)·cosh(yw)` — the `y`-derivative `∂_y b(w)`. -/
noncomputable def momentBy (x y w : ℝ) : ℝ := w * Real.sin (x * w) * Real.cosh (y * w)

/-- `Ia = ∫₀^A Φ·a` — the bare cosine·cosh moment. -/
noncomputable def momIa (Phi : ℝ → ℝ) (A x y : ℝ) : ℝ :=
  ∫ w in (0 : ℝ)..A, Phi w * momentA x y w

/-- `Iay = ∫₀^A Φ·aᵧ` — the cosine·sinh (weighted by `w`) moment. -/
noncomputable def momIay (Phi : ℝ → ℝ) (A x y : ℝ) : ℝ :=
  ∫ w in (0 : ℝ)..A, Phi w * momentAy x y w

/-- `Ib = ∫₀^A Φ·b` — the sine·sinh moment. -/
noncomputable def momIb (Phi : ℝ → ℝ) (A x y : ℝ) : ℝ :=
  ∫ w in (0 : ℝ)..A, Phi w * momentB x y w

/-- `Iby = ∫₀^A Φ·bᵧ` — the sine·cosh (weighted by `w`) moment. -/
noncomputable def momIby (Phi : ℝ → ℝ) (A x y : ℝ) : ℝ :=
  ∫ w in (0 : ℝ)..A, Phi w * momentBy x y w

/-- The first moment functional `L₁ = Ia + Iay = ∫ Φ·(a + aᵧ)`. -/
noncomputable def L1 (Phi : ℝ → ℝ) (A x y : ℝ) : ℝ := momIa Phi A x y + momIay Phi A x y
/-- The second moment functional `L₂ = Ia − Iay = ∫ Φ·(a − aᵧ)`. -/
noncomputable def L2 (Phi : ℝ → ℝ) (A x y : ℝ) : ℝ := momIa Phi A x y - momIay Phi A x y
/-- The third moment functional `L₃ = Ib + Iby = ∫ Φ·(b + bᵧ)`. -/
noncomputable def L3 (Phi : ℝ → ℝ) (A x y : ℝ) : ℝ := momIb Phi A x y + momIby Phi A x y
/-- The fourth moment functional `L₄ = Ib − Iby = ∫ Φ·(b − bᵧ)`. -/
noncomputable def L4 (Phi : ℝ → ℝ) (A x y : ℝ) : ℝ := momIb Phi A x y - momIby Phi A x y

/-- **Packaged transform `A = L₁ + i·L₃`.** -/
noncomputable def A_transform (Phi : ℝ → ℝ) (A x y : ℝ) : ℂ :=
  (L1 Phi A x y : ℂ) + (L3 Phi A x y : ℂ) * Complex.I

/-- **Packaged transform `B = L₂ + i·L₄`.** -/
noncomputable def B_transform (Phi : ℝ → ℝ) (A x y : ℝ) : ℂ :=
  (L2 Phi A x y : ℂ) + (L4 Phi A x y : ℂ) * Complex.I

/-! ## §2. The two dominance Props -/

/-- **THE single open inequality — Hermite–Biehler dominance.**  For every UHP
probe `(x, y)` (with cutoff `A`), the `B`-transform is dominated in modulus by the
`A`-transform.  By `hbDominance_iff_rankFour` this is exactly the energy
positivity `½(‖A‖²−‖B‖²) ≥ 0`; proving it is proving RH.  It is **not** proved
here, and no RH-equivalent hypothesis is assumed about it. -/
def SpecialPhiHBDominance (Phi : ℝ → ℝ) : Prop :=
  ∀ A x y : ℝ, 0 < A → 0 < y → ‖B_transform Phi A x y‖ ≤ ‖A_transform Phi A x y‖

/-- **Rank-four real form of the dominance.**  `L₂² + L₄² ≤ L₁² + L₃²` at every
cutoff `A > 0` and UHP probe `(x, y)`. -/
def RankFourDominance (Phi : ℝ → ℝ) : Prop :=
  ∀ A x y : ℝ, 0 < A → 0 < y →
    (L2 Phi A x y) ^ 2 + (L4 Phi A x y) ^ 2
      ≤ (L1 Phi A x y) ^ 2 + (L3 Phi A x y) ^ 2

/-! ## §3. `‖A‖² = L₁²+L₃²`, `‖B‖² = L₂²+L₄²`, and the equivalence -/

/-- `‖A_transform‖² = L₁² + L₃²`. -/
theorem normSq_A_transform (Phi : ℝ → ℝ) (A x y : ℝ) :
    ‖A_transform Phi A x y‖ ^ 2 = (L1 Phi A x y) ^ 2 + (L3 Phi A x y) ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq]
  unfold A_transform
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im,
    Complex.I_re, Complex.I_im]
  ring

/-- `‖B_transform‖² = L₂² + L₄²`. -/
theorem normSq_B_transform (Phi : ℝ → ℝ) (A x y : ℝ) :
    ‖B_transform Phi A x y‖ ^ 2 = (L2 Phi A x y) ^ 2 + (L4 Phi A x y) ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq]
  unfold B_transform
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im,
    Complex.I_re, Complex.I_im]
  ring

/-- **PROVED — `SpecialPhiHBDominance ↔ RankFourDominance`.**  The modulus
inequality `‖B‖ ≤ ‖A‖` is, term-by-term, the real inequality `L₂²+L₄² ≤ L₁²+L₃²`
(both norms being nonnegative, square both sides and apply
`normSq_A_transform`/`normSq_B_transform`). -/
theorem hbDominance_iff_rankFour (Phi : ℝ → ℝ) :
    SpecialPhiHBDominance Phi ↔ RankFourDominance Phi := by
  constructor
  · intro h A x y hA hy
    have hle := h A x y hA hy
    rw [← normSq_A_transform Phi A x y, ← normSq_B_transform Phi A x y]
    exact pow_le_pow_left₀ (norm_nonneg _) hle 2
  · intro h A x y hA hy
    have hle := h A x y hA hy
    rw [← normSq_A_transform Phi A x y, ← normSq_B_transform Phi A x y] at hle
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) (by norm_num)).mp hle

/-! ## §4. The SOS-difference identity and the positivity bridge

The closed form of the cosine kernel (`ScratchEnergyKernel.cosKer_closedForm`) is
`cosKer u v (x+iy) = a u · a v + b u · b v`, with `a, b` the building blocks of
§1; differentiating in `y` gives
`xiCosDoubleKernel u v x y = aᵧ u · a v + a u · aᵧ v + bᵧ u · b v + b u · bᵧ v`.
Hence the finite double-kernel energy factors (Fubini) into the products of single
moments:

```
finiteDoubleKernelEnergy (xiCosData Φ) A x y  =  2·Ia·Iaᵧ + 2·Ib·Ibᵧ.
```

This Fubini/factorization step is the analytic residual; it is isolated as the
named predicate `SOSDifferenceForm`.  The *algebraic* reduction of the rank-4
SOS-difference `½(L₁²−L₂²+L₃²−L₄²)` to `2·Ia·Iaᵧ + 2·Ib·Ibᵧ` is proved outright
below (`energy_eq_sosDifference`), purely by `ring` from
`L₁²−L₂² = (Ia+Iaᵧ)²−(Ia−Iaᵧ)² = 4·Ia·Iaᵧ` and likewise for `L₃²−L₄²`. -/

/-- **PROVED — the algebraic SOS-difference reduction.**
`½(L₁²−L₂²+L₃²−L₄²) = 2·Ia·Iaᵧ + 2·Ib·Ibᵧ`.  Pure `ring`: with `L₁=Ia+Iaᵧ`,
`L₂=Ia−Iaᵧ`, `L₃=Ib+Ibᵧ`, `L₄=Ib−Ibᵧ` the cross-terms cancel and the squares
collapse to the products. -/
theorem energy_eq_sosDifference (Phi : ℝ → ℝ) (A x y : ℝ) :
    (1 / 2 : ℝ) *
        ((L1 Phi A x y) ^ 2 - (L2 Phi A x y) ^ 2
          + (L3 Phi A x y) ^ 2 - (L4 Phi A x y) ^ 2)
      = 2 * momIa Phi A x y * momIay Phi A x y
        + 2 * momIb Phi A x y * momIby Phi A x y := by
  unfold L1 L2 L3 L4
  ring

/-- **SOS-difference form (isolated Fubini residual).**  The finite double-kernel
energy of the explicit cosine kernel `xiCosData Φ` factors into the products of
single moments:

`finiteDoubleKernelEnergy (xiCosData Φ) A x y = 2·Ia·Iaᵧ + 2·Ib·Ibᵧ`.

This is the Fubini/product-of-integrals factorization of the double integral of
`Φ(u)Φ(v)·(aᵧu·av + au·aᵧv + bᵧu·bv + bu·bᵧv)`.  On the compact square `[0,A]²`
with continuous `Φ` it is `MeasureTheory.setIntegral_prod_mul` applied four times
(exactly the leg already discharged for the *value* energy in
`ScratchKernelForm.energy_eq_doubleIntegral`).  It is isolated as an honest named
hypothesis so the algebraic reduction above stays fully discharged. -/
def SOSDifferenceForm (Phi : ℝ → ℝ) (A x y : ℝ) : Prop :=
  finiteDoubleKernelEnergy (xiCosData Phi) A x y
    = 2 * momIa Phi A x y * momIay Phi A x y
      + 2 * momIb Phi A x y * momIby Phi A x y

/-- **PROVED — the finite double-kernel energy equals the rank-4 SOS difference.**
Combining the isolated Fubini factorization (`SOSDifferenceForm`) with the
algebraic reduction (`energy_eq_sosDifference`):

`finiteDoubleKernelEnergy (xiCosData Φ) A x y = ½(L₁²−L₂²+L₃²−L₄²)`. -/
theorem finiteEnergy_eq_rankFourSOS (Phi : ℝ → ℝ) (A x y : ℝ)
    (hSOS : SOSDifferenceForm Phi A x y) :
    finiteDoubleKernelEnergy (xiCosData Phi) A x y
      = (1 / 2 : ℝ) *
          ((L1 Phi A x y) ^ 2 - (L2 Phi A x y) ^ 2
            + (L3 Phi A x y) ^ 2 - (L4 Phi A x y) ^ 2) := by
  rw [hSOS, ← energy_eq_sosDifference]

/-- **PROVED — `RankFourDominance` ⟹ `IntegratedDoubleKernelPositivity`.**
Given the SOS-difference form at every probe, the finite energy equals
`½(L₁²−L₂²+L₃²−L₄²) = ½((L₁²+L₃²) − (L₂²+L₄²))`, which is `≥ 0` exactly when
`L₂²+L₄² ≤ L₁²+L₃²`, i.e. `RankFourDominance`. -/
theorem integratedPositivity_of_rankFour (Phi : ℝ → ℝ)
    (hSOS : ∀ A x y : ℝ, 0 < A → 0 < y → SOSDifferenceForm Phi A x y)
    (h : RankFourDominance Phi) :
    IntegratedDoubleKernelPositivity (xiCosData Phi) := by
  intro A x y hA hy
  rw [finiteEnergy_eq_rankFourSOS Phi A x y (hSOS A x y hA hy)]
  have hdom := h A x y hA hy
  -- `½(L₁²−L₂²+L₃²−L₄²) = ½((L₁²+L₃²) − (L₂²+L₄²)) ≥ 0`.
  nlinarith [hdom]

/-! ## §5. Assembly: HB dominance ⟹ anti-Herglotz target

We now compose the dominance ⟹ positivity bridge of §4 with the EXISTING proven
energy route of `ScratchEnergyKernel`:

```
xiPullbackEnergyMonotone_of_kernelForm_and_positivity   (energy monotone)
xiPullbackAntiHerglotzTarget_of_integratedPositivity     (anti-Herglotz target)
```

both of which ultimately rest on the reused, proven
`rh.lean`/`XiPullbackAntiHerglotzTarget_of_energyMonotone_and_diff`.  The analytic
scaffolding (`hAgree : TransformIsPullback`, `hKF : KernelForm`,
`hdiff` UHP differentiability) is threaded exactly as that route already requires;
the only mathematically open fact added on top is `SpecialPhiHBDominance Φ`. -/

/-- **PROVED — HB dominance ⟹ pullback energy monotone.**  Converts the modulus
inequality to `RankFourDominance` (§3), then to integrated positivity (§4), then
fires the existing kernel-form energy route. -/
theorem energyMonotone_of_hbDominance (Phi : ℝ → ℝ) (A : ℝ) (hA : 0 < A)
    (hAgree : TransformIsPullback Phi A)
    (hKF : ∀ x y : ℝ, 0 < y → KernelForm Phi A x y)
    (hSOS : ∀ A x y : ℝ, 0 < A → 0 < y → SOSDifferenceForm Phi A x y)
    (hHB : SpecialPhiHBDominance Phi) :
    XiPullbackEnergyMonotoneAwayFromZeros :=
  xiPullbackEnergyMonotone_of_kernelForm_and_positivity Phi A hA hAgree hKF
    (integratedPositivity_of_rankFour Phi hSOS
      ((hbDominance_iff_rankFour Phi).mp hHB))

/-- **PROVED — HB dominance ⟹ anti-Herglotz target (with the analytic
scaffolding).**  The single open inequality `SpecialPhiHBDominance Φ`, together
with the standard energy-route inputs, yields
`XiPullbackAntiHerglotzTarget`. -/
theorem antiHerglotz_of_hbDominance (Phi : ℝ → ℝ) (A : ℝ) (hA : 0 < A)
    (hdiff : ∀ z : ℂ, 0 < z.im → DifferentiableAt ℂ XiPullback z)
    (hAgree : TransformIsPullback Phi A)
    (hKF : ∀ x y : ℝ, 0 < y → KernelForm Phi A x y)
    (hSOS : ∀ A x y : ℝ, 0 < A → 0 < y → SOSDifferenceForm Phi A x y)
    (hHB : SpecialPhiHBDominance Phi) :
    XiPullbackAntiHerglotzTarget :=
  xiPullbackAntiHerglotzTarget_of_integratedPositivity Phi A hA hdiff hAgree hKF
    (integratedPositivity_of_rankFour Phi hSOS
      ((hbDominance_iff_rankFour Phi).mp hHB))

/-- ⭐ **PROVED — CAPSTONE.**  The clean *one-modulus-inequality ⟹ target*
statement:

`SpecialPhiHBDominance Φ → XiPullbackAntiHerglotzTarget`.

`SpecialPhiHBDominance Φ` (`‖B‖ ≤ ‖A‖`) is the single **unproven** `Prop` — proving
it *is* proving RH, and it is left open here.  Everything else in the chain is
PROVEN: the modulus↔rank-4 equivalence (§3), the SOS-difference reduction (§4),
and the reused `rh.lean` energy→anti-Herglotz route (via
`xiPullbackAntiHerglotzTarget_of_integratedPositivity`).  The remaining
hypotheses (`hdiff`, `hAgree`, `hKF`, `hSOS`) are the standard analytic
interchanges already isolated by the energy route — none RH-equivalent. -/
theorem XiPullbackAntiHerglotzTarget_of_specialPhiHBDominance
    (Phi : ℝ → ℝ) (A : ℝ) (hA : 0 < A)
    (hdiff : ∀ z : ℂ, 0 < z.im → DifferentiableAt ℂ XiPullback z)
    (hAgree : TransformIsPullback Phi A)
    (hKF : ∀ x y : ℝ, 0 < y → KernelForm Phi A x y)
    (hSOS : ∀ A x y : ℝ, 0 < A → 0 < y → SOSDifferenceForm Phi A x y) :
    SpecialPhiHBDominance Phi → XiPullbackAntiHerglotzTarget :=
  fun hHB => antiHerglotz_of_hbDominance Phi A hA hdiff hAgree hKF hSOS hHB

/-! ## §6. Axiom audit

Only `propext`, `Classical.choice`, `Quot.sound` (no `sorryAx`). -/

#print axioms XiPullbackAntiHerglotzTarget_of_specialPhiHBDominance
#print axioms hbDominance_iff_rankFour
#print axioms integratedPositivity_of_rankFour
#print axioms energy_eq_sosDifference
#print axioms antiHerglotz_of_hbDominance

end ScratchHBDominance
end BacklundTuring
end OverflowResidueRH
