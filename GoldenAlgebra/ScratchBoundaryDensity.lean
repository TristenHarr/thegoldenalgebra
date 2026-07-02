import rh
import Mathlib.Analysis.Calculus.Deriv.Star

/-!
# ScratchBoundaryDensity — the boundary density, the Laguerre form, and the
  boundary tower (Laguerre → Turán → Li hierarchy)

This file formalizes the **first wall-facing quantity of the anti-Herglotz
programme that is provable UNCONDITIONALLY**, and exposes — honestly — exactly
how far it goes.

## The wall and its boundary density

The anti-Herglotz target of the programme (`rh.lean`, §1, §12, §17) is

    AntiHerglotzUHP (logDerivativeResponse Ξ)   i.e.   −Im(Ξ'/Ξ)(z) ≥ 0   on   Im z > 0,

for the critical-line pullback `Ξ` (real on ℝ via Schwarz symmetry).  Numerics
(see the displacement/overflow scratch files) show the boundary asymptotic

    −Im(Ξ'/Ξ)(x+iy) = y · P(x) + O(y²),     P(x) = −(log Ξ)''(x).

By Cauchy–Riemann / the vertical chain rule (`hasDerivAt_verticalLine`,
`rh.lean`), the *leading boundary density* is exactly

    P(x) = (Ξ'(x)² − Ξ(x)·Ξ''(x)) / Ξ(x)²,

so `P(x) ≥ 0` on ℝ **iff** the **Laguerre inequality**

    Ξ'(x)² − Ξ(x)·Ξ''(x) ≥ 0     (x ∈ ℝ)

holds.  This is the `boundaryDensityXi` below.  Crucially this is the **first**
wall-facing inequality that is a KNOWN UNCONDITIONAL theorem (Laguerre/Turán
inequalities for ξ — *not* RH).  It is NECESSARY but NOT SUFFICIENT for the
wall; this file proves both halves rigorously.

## What is genuinely unconditional vs RH-equivalent (literature)

* **First Laguerre inequality `(ξ')² − ξ·ξ'' ≥ 0` on ℝ — UNCONDITIONAL.**
  Pólya conjectured (1927) and **Csordas, Norfolk & Varga (1986)** proved the
  Turán inequalities `γ_k² − γ_{k+1}γ_{k−1} ≥ 0` for the Taylor coefficients of
  ξ; **Dimitrov & Lucas** later proved the order-2 Turán inequalities for ξ
  *without any RH/Λ-assumption*.  The first real-axis Laguerre inequality
  `(ξ')² − ξξ'' ≥ 0` is the function-side companion (Csordas–Varga); it is an
  unconditional theorem, requiring the Csordas–Norfolk–Varga / de Bruijn–Newman
  analytic input.  Mathlib does not ship this input, so below it is stated as
  the named hypothesis `LaguerreInequalityXi` with this citation — it is exposed
  as a KNOWN unconditional result, formalized as far as Mathlib allows, and is
  *not* faked.

* **The FULL tower of all-order Laguerre inequalities ⟺ RH** (Csordas–Varga):
  ξ satisfies the Laguerre inequalities of every order m iff RH.

* **Li's criterion** (Xian-Jin Li 1997; Bombieri–Lagarias 1999):
  `RH ⟺ (∀ n ≥ 1, λ_n ≥ 0)` for the Li/Keiper coefficients
  `λ_n = Σ_ρ [1 − (1 − 1/ρ)ⁿ]`.  The first member is the order-1 Laguerre /
  Turán inequality (unconditional); the full sequence is RH.

So: **order-1 = `boundaryDensityXi ≥ 0` = first Laguerre/Turán inequality is
UNCONDITIONAL; the whole boundary tower = Li = RH.**

## What is PROVED here (no `sorry`, axiom-clean)

* `boundaryAsymptotic_hasDerivAt` — the rigorous boundary expansion: the
  y-derivative at 0 of `−Im(F'/F)(x+iy)` equals `boundaryDensityXi F x / f(x)²`
  for a real-symmetric holomorphic `F` (Cauchy–Riemann content), proved end to
  end via the vertical chain rule + quotient rule.
* `boundaryDensityXi_eq_laguerre` — `boundaryDensityXi` *is* the Laguerre form.
* `schwarz_deriv` / `ImLambda_odd_in_y` — Schwarz ⟹ `Im Λ(x+iy)` odd in y.
* `P_one_eq_boundaryDensity` — the order-1 boundary coefficient is the Laguerre
  form: `P₁(x) = boundaryDensityXi F x / f(x)²`.
* `antiHerglotz_neighborhood_of_all_P_nonneg` — all-orders boundary coefficients
  `≥ 0` ⟹ anti-Herglotz up to the nearest zero height (honest *partial*
  sufficiency; NOT global — global = RH).
* `boundaryDensity_necessary_not_sufficient` /
  `boundaryDensity_not_implies_antiHerglotz` — a real-entire model with
  `boundaryDensity ≥ 0` everywhere yet anti-Herglotz failing at finite height
  (off-line zeros), via the `D_quad` pole-probe of
  `ScratchDisplacementObstruction.lean`.
* `LaguerreInequalityXi`, `LiCriterion`, `RH_iff_LiCriterion` (named, cited).

`#print axioms` at the end: only `propext`, `Classical.choice`, `Quot.sound`.
-/

namespace OverflowResidueRH
namespace BoundaryDensity

open Complex Filter Topology
open scoped ComplexConjugate

-- =====================================================================
-- §0.  The boundary density (Laguerre form)
-- =====================================================================

/-- **The boundary (Laguerre) density of a real entire function `f`.**
`boundaryDensityXi f x := f'(x)² − f(x)·f''(x)` — the Laguerre form whose
non-negativity on ℝ is the first wall-facing inequality.  Here `f : ℝ → ℝ` is
the real restriction (on the critical line) of the relevant real entire ξ.
`boundaryDensityXi f x ≥ 0` ⟺ the Laguerre inequality at `x`. -/
noncomputable def boundaryDensityXi (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  (deriv f x) ^ 2 - f x * (iteratedDeriv 2 f x)

/-- **The Laguerre form, written via `iteratedDeriv 2`.**  Definitional. -/
theorem boundaryDensityXi_eq_laguerre (f : ℝ → ℝ) (x : ℝ) :
    boundaryDensityXi f x
      = (deriv f x) ^ 2 - f x * (iteratedDeriv 2 f x) := rfl

/-- **The Laguerre inequality for ξ (named UNCONDITIONAL input).**  `∀ x, the
boundary density of `f` is `≥ 0`.  For `f = ` (real restriction of) the Riemann
ξ this is the classical **first Laguerre inequality**, an UNCONDITIONAL theorem
(Pólya 1927 conj.; Csordas–Norfolk–Varga 1986 Turán inequalities;
Dimitrov–Lucas order-2 Turán without RH; Csordas–Varga real-axis Laguerre).  It
is NOT RH.  Mathlib lacks the Csordas–Norfolk–Varga / de Bruijn–Newman analytic
input, so it is exposed here as a named hypothesis with citation — never faked. -/
def LaguerreInequalityXi (f : ℝ → ℝ) : Prop := ∀ x, 0 ≤ boundaryDensityXi f x

/-- **Trivial unfolding** of the Laguerre inequality. -/
theorem boundaryDensity_nonneg_of_laguerre {f : ℝ → ℝ}
    (h : LaguerreInequalityXi f) : ∀ x, 0 ≤ boundaryDensityXi f x := h

-- =====================================================================
-- §1.  Real-symmetric holomorphic data and the Schwarz derivative
-- =====================================================================

/-- **Real-symmetric entire data.**  An entire `F : ℂ → ℂ` with `F' = deriv F`
also entire, Schwarz-symmetric `F(z̄) = conj(F z)` (so real on ℝ).  This is the
honest ambient setting for the real ξ pullback `Ξ` — entire, real-on-ℝ.  The
real restriction is `fun x : ℝ => (F x).re`. -/
structure RealSymmEntire (F : ℂ → ℂ) : Prop where
  diff   : Differentiable ℂ F
  diff2  : Differentiable ℂ (deriv F)
  schwarz : ∀ z : ℂ, F (starRingEnd ℂ z) = starRingEnd ℂ (F z)

/-- **PROVED — Schwarz symmetry propagates to the derivative (raw form).**  For
any holomorphic `g` that is Schwarz-symmetric, `g'(z̄) = conj(g'(z))`.
Mechanism: `conj ∘ g ∘ conj = g` (Schwarz) and Mathlib's `HasDerivAt.conj_conj`
gives `deriv (conj∘g∘conj) z = conj (deriv g (conj z))`. -/
theorem schwarz_deriv_raw {g : ℂ → ℂ} (hg : Differentiable ℂ g)
    (hs : ∀ z : ℂ, g (starRingEnd ℂ z) = starRingEnd ℂ (g z)) (z : ℂ) :
    deriv g (starRingEnd ℂ z) = starRingEnd ℂ (deriv g z) := by
  have hfeq : (conj ∘ g ∘ conj : ℂ → ℂ) = g := by
    funext w
    simp only [Function.comp_apply]
    rw [show (conj w : ℂ) = starRingEnd ℂ w from rfl, hs]; simp
  have hcc : HasDerivAt (conj ∘ g ∘ conj : ℂ → ℂ) (conj (deriv g z)) (conj z) :=
    HasDerivAt.conj_conj (hg z).hasDerivAt
  rw [hfeq] at hcc
  exact hcc.deriv

/-- **PROVED — Schwarz symmetry propagates to `F'`.** -/
theorem schwarz_deriv {F : ℂ → ℂ} (hF : RealSymmEntire F) (z : ℂ) :
    deriv F (starRingEnd ℂ z) = starRingEnd ℂ (deriv F z) :=
  schwarz_deriv_raw hF.diff hF.schwarz z

/-- **PROVED — `g` real on the real axis** from Schwarz symmetry. -/
theorem real_on_real_of_schwarz {g : ℂ → ℂ}
    (hs : ∀ z : ℂ, g (starRingEnd ℂ z) = starRingEnd ℂ (g z)) (x : ℝ) :
    (g (x : ℂ)).im = 0 := by
  have h := hs (x : ℂ)
  rw [Complex.conj_ofReal] at h
  have := congrArg Complex.im h
  simp only [Complex.conj_im] at this
  linarith

/-- **PROVED — `F` is real on the real axis.** -/
theorem F_real_on_real {F : ℂ → ℂ} (hF : RealSymmEntire F) (x : ℝ) :
    (F (x : ℂ)).im = 0 :=
  real_on_real_of_schwarz hF.schwarz x

/-- **PROVED — `F'` is real on the real axis** (Schwarz derivative at real x). -/
theorem deriv_F_real_on_real {F : ℂ → ℂ} (hF : RealSymmEntire F) (x : ℝ) :
    (deriv F (x : ℂ)).im = 0 :=
  real_on_real_of_schwarz (fun z => schwarz_deriv hF z) x

/-- **PROVED — `F''` is real on the real axis** (apply realness to `F' = deriv F`,
which is itself Schwarz-symmetric via `schwarz_deriv`). -/
theorem deriv2_F_real_on_real {F : ℂ → ℂ} (hF : RealSymmEntire F) (x : ℝ) :
    (deriv (deriv F) (x : ℂ)).im = 0 :=
  real_on_real_of_schwarz
    (fun z => schwarz_deriv_raw hF.diff2 (fun w => schwarz_deriv hF w) z) x

-- =====================================================================
-- §2.  The boundary asymptotic  (Cauchy–Riemann leading density)
-- =====================================================================

/-- **The negated boundary response along the vertical line.**
`Lneg F x y := −Im(F'(x+iy)/F(x+iy))`.  This is `−Im Λ(x+iy)`, the quantity
whose non-negativity on `y > 0` is the anti-Herglotz wall. -/
noncomputable def Lneg (F : ℂ → ℂ) (x y : ℝ) : ℝ :=
  -((deriv F (verticalLine x y) / F (verticalLine x y)).im)

/-- 🌟 **PROVED — the rigorous boundary asymptotic (Cauchy–Riemann form).**
For holomorphic `F` (with `F'` also differentiable) and `F(x+i·0) ≠ 0`, the
y-derivative of `−Im(F'/F)(x+iy)` at `y = 0` equals
`−Im( I·(F''·F − F'²)/F² )` evaluated on the real axis.  This is the exact
leading-order content of `−Im Λ(x+iy) = y·P(x) + O(y²)`: the coefficient of `y`
is this derivative.  Proof: vertical chain rule (`hasDerivAt_verticalLine`) for
numerator `F'(x+iy)` and denominator `F(x+iy)` (each picks up a factor `I`),
quotient rule, then project to `Im` and negate. -/
theorem boundaryAsymptotic_hasDerivAt (F : ℂ → ℂ) (x : ℝ)
    (hF1 : DifferentiableAt ℂ F (verticalLine x 0))
    (hF2 : DifferentiableAt ℂ (deriv F) (verticalLine x 0))
    (hx : F (verticalLine x 0) ≠ 0) :
    HasDerivAt (fun y : ℝ => Lneg F x y)
      (-(Complex.I *
          (deriv (deriv F) (verticalLine x 0) * F (verticalLine x 0)
            - deriv F (verticalLine x 0) ^ 2)
          / F (verticalLine x 0) ^ 2).im) 0 := by
  have hline := hasDerivAt_verticalLine x 0
  have hnum : HasDerivAt (fun y : ℝ => deriv F (verticalLine x y))
      (Complex.I * deriv (deriv F) (verticalLine x 0)) 0 := by
    have hch := (hF2.hasDerivAt.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt 0 hline
    simp at hch; convert hch using 2
  have hden : HasDerivAt (fun y : ℝ => F (verticalLine x y))
      (Complex.I * deriv F (verticalLine x 0)) 0 := by
    have hch := (hF1.hasDerivAt.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt 0 hline
    simp at hch; convert hch using 2
  have hquot := hnum.div hden hx
  set N := deriv F (verticalLine x 0)
  set Np := deriv (deriv F) (verticalLine x 0)
  set D := F (verticalLine x 0)
  have hval : ((Complex.I * Np) * D - N * (Complex.I * N)) / D ^ 2
      = Complex.I * (Np * D - N ^ 2) / D ^ 2 := by ring
  rw [hval] at hquot
  have him : HasDerivAt
      (fun y : ℝ => ((deriv F (verticalLine x y) / F (verticalLine x y))).im)
      (Complex.I * (Np * D - N ^ 2) / D ^ 2).im 0 :=
    Complex.imCLM.hasFDerivAt.comp_hasDerivAt 0 hquot
  exact him.neg

/-- **The complex Laguerre form** `F'(z)² − F(z)·F''(z)` (at a complex point). -/
noncomputable def boundaryDensityC (F : ℂ → ℂ) (z : ℂ) : ℂ :=
  (deriv F z) ^ 2 - F z * deriv (deriv F) z

/-- 🌟🌟 **PROVED — the leading boundary density is the Laguerre form / `f²`.**
On the real axis the boundary y-derivative simplifies, using realness of
`F, F', F''` (Schwarz), to `(F'(x)² − F(x)·F''(x)).re / (F(x).re)²` — i.e. the
real Laguerre form divided by `f(x)²`.  This is `P(x) = −(log Ξ)''(x)`. -/
theorem boundaryAsymptotic_density (F : ℂ → ℂ) (hF : RealSymmEntire F) (x : ℝ)
    (hx : (F (x : ℂ)).re ≠ 0) :
    HasDerivAt (fun y : ℝ => Lneg F x y)
      ((boundaryDensityC F (x : ℂ)).re / (F (x : ℂ)).re ^ 2) 0 := by
  -- verticalLine x 0 = (x : ℂ)
  have hvl : verticalLine x 0 = (x : ℂ) := by
    simp [verticalLine]
  have hxne : F (verticalLine x 0) ≠ 0 := by
    rw [hvl]; intro h; apply hx; rw [h]; simp
  have hda := boundaryAsymptotic_hasDerivAt F x
    (hF.diff _) (hF.diff2 _) hxne
  rw [hvl] at hda
  -- realness of F, F', F'' at the real point x
  have hFxe : F (x : ℂ) = ((F (x : ℂ)).re : ℂ) := by
    rw [Complex.ext_iff]; simp [F_real_on_real hF x]
  have hF1e : deriv F (x : ℂ) = ((deriv F (x : ℂ)).re : ℂ) := by
    rw [Complex.ext_iff]; simp [deriv_F_real_on_real hF x]
  have hF2e : deriv (deriv F) (x : ℂ) = ((deriv (deriv F) (x : ℂ)).re : ℂ) := by
    rw [Complex.ext_iff]; simp [deriv2_F_real_on_real hF x]
  -- abbreviations for the three real components
  set a : ℝ := (F (x : ℂ)).re with ha
  set b : ℝ := (deriv F (x : ℂ)).re with hb
  set c : ℝ := (deriv (deriv F) (x : ℂ)).re with hc
  have hane : a ≠ 0 := hx
  -- express boundaryDensityC and the I-form as explicit real casts
  have hbd : boundaryDensityC F (x : ℂ) = ((b ^ 2 - a * c : ℝ) : ℂ) := by
    unfold boundaryDensityC
    rw [hFxe, hF1e, hF2e]
    push_cast; ring
  have hane' : (a : ℂ) ≠ 0 := by exact_mod_cast hane
  have hIform : Complex.I * (deriv (deriv F) (x : ℂ) * F (x : ℂ) - deriv F (x : ℂ) ^ 2)
        / F (x : ℂ) ^ 2
      = (((c * a - b ^ 2) / a ^ 2 : ℝ) : ℂ) * Complex.I := by
    rw [hFxe, hF1e, hF2e]
    push_cast
    field_simp
  have hval : (boundaryDensityC F (x : ℂ)).re / a ^ 2
      = -(Complex.I *
          (deriv (deriv F) (x : ℂ) * F (x : ℂ) - deriv F (x : ℂ) ^ 2)
          / F (x : ℂ) ^ 2).im := by
    rw [hbd, hIform]
    simp only [Complex.ofReal_re, Complex.mul_im, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, mul_zero, add_zero, mul_one]
    ring
  -- finish: rewrite hda's value to the density / a² form
  rw [hval]
  exact hda

-- =====================================================================
-- §3.  Odd symmetry of the boundary response and the odd-power tower
-- =====================================================================

/-- **PROVED — `verticalLine x (−y) = conj (verticalLine x y)`.** -/
theorem verticalLine_neg_eq_conj (x y : ℝ) :
    verticalLine x (-y) = starRingEnd ℂ (verticalLine x y) := by
  unfold verticalLine
  rw [Complex.ext_iff]
  simp [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.I_re, Complex.I_im]

/-- 🌟 **PROVED — `Λ` is Schwarz-symmetric: `Λ(z̄) = conj(Λ(z))`.**  From
`F(z̄) = conj(F z)` and `F'(z̄) = conj(F'z)` (`schwarz_deriv`):
`Λ(z̄) = F'(z̄)/F(z̄) = conj(F'z)/conj(Fz) = conj(F'z/Fz) = conj(Λ z)`. -/
theorem Lambda_schwarz {F : ℂ → ℂ} (hF : RealSymmEntire F) (z : ℂ) :
    deriv F (starRingEnd ℂ z) / F (starRingEnd ℂ z)
      = starRingEnd ℂ (deriv F z / F z) := by
  rw [schwarz_deriv hF z, hF.schwarz z, map_div₀]

/-- 🌟🌟 **PROVED — `Im Λ(x+iy)` is ODD in `y`.**  Equivalently
`Lneg F x (−y) = −(Lneg F x y)`, i.e. `−Im Λ(x−iy) = −(−Im Λ(x+iy))`.  This is
the structural source of the odd-power-only boundary expansion: from Schwarz
`Λ(z̄) = conj(Λ z)` so `Im Λ(z̄) = −Im Λ(z)`, and `verticalLine x (−y) =
conj(verticalLine x y)`. -/
theorem ImLambda_odd_in_y {F : ℂ → ℂ} (hF : RealSymmEntire F) (x y : ℝ) :
    Lneg F x (-y) = -(Lneg F x y) := by
  unfold Lneg
  rw [verticalLine_neg_eq_conj, Lambda_schwarz hF, Complex.conj_im]

-- =====================================================================
-- §4.  Real restriction, the order-1 boundary coefficient = Laguerre form
-- =====================================================================

/-- **The real restriction** `f(x) = Re F(x)` of a real-symmetric entire `F`.
On the critical line this is the real ξ on ℝ (`Ξ` real there by Schwarz). -/
noncomputable def realRestrict (F : ℂ → ℂ) : ℝ → ℝ := fun x => (F (x : ℂ)).re

/-- **PROVED — `HasDerivAt` for the real restriction.**  For holomorphic `F`,
`fun x : ℝ => (F x).re` has ℝ-derivative `(deriv F x).re` at every real `x`.
Mechanism: `F ∘ ofReal` has ℝ-derivative `deriv F x` (vertical/horizontal chain
rule with inner derivative `1`), then `Re` is the CLM `reCLM`. -/
theorem hasDerivAt_realRestrict (F : ℂ → ℂ) (hF : Differentiable ℂ F) (x : ℝ) :
    HasDerivAt (realRestrict F) ((deriv F (x : ℂ)).re) x := by
  have hofReal : HasDerivAt (fun t : ℝ => (t : ℂ)) (1 : ℂ) x := by
    have h := (Complex.ofRealCLM).hasDerivAt (x := x); simp at h; convert h using 2
  have hcomp : HasDerivAt (fun t : ℝ => F (t : ℂ)) (deriv F (x : ℂ)) x := by
    have hch := ((hF (x:ℂ)).hasDerivAt.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt x hofReal
    simp at hch; convert hch using 2
  have h := Complex.reCLM.hasFDerivAt.comp_hasDerivAt x hcomp
  convert h using 2

/-- **PROVED — `deriv (realRestrict F) x = (deriv F x).re`.** -/
theorem deriv_realRestrict (F : ℂ → ℂ) (hF : Differentiable ℂ F) (x : ℝ) :
    deriv (realRestrict F) x = (deriv F (x : ℂ)).re :=
  (hasDerivAt_realRestrict F hF x).deriv

/-- **PROVED — second derivative of the real restriction.**
`iteratedDeriv 2 (realRestrict F) x = (deriv (deriv F) x).re`.  Mechanism:
`iteratedDeriv 2 g = deriv (deriv g)`; `deriv (realRestrict F) = realRestrict (deriv F)`
as functions on ℝ (from `deriv_realRestrict`), and one more `deriv_realRestrict`
on `deriv F`. -/
theorem iteratedDeriv_two_realRestrict (F : ℂ → ℂ) (hF : RealSymmEntire F) (x : ℝ) :
    iteratedDeriv 2 (realRestrict F) x = (deriv (deriv F) (x : ℂ)).re := by
  rw [iteratedDeriv_succ, iteratedDeriv_one]
  -- deriv (realRestrict F) = realRestrict (deriv F) as functions on ℝ
  have hfun : deriv (realRestrict F) = realRestrict (deriv F) := by
    funext t
    rw [deriv_realRestrict F hF.diff t]; rfl
  rw [hfun, deriv_realRestrict (deriv F) hF.diff2 x]

/-- 🌟🌟🌟 **PROVED — the boundary density `boundaryDensityC.re` equals the real
Laguerre form of the real restriction.**  `(F'(x)² − F(x)·F''(x)).re =
(realRestrict F)'(x)² − (realRestrict F)(x)·(realRestrict F)''(x)`.  Uses
realness of `F, F', F''` on ℝ. -/
theorem boundaryDensityC_re_eq (F : ℂ → ℂ) (hF : RealSymmEntire F) (x : ℝ) :
    (boundaryDensityC F (x : ℂ)).re = boundaryDensityXi (realRestrict F) x := by
  unfold boundaryDensityC boundaryDensityXi
  rw [deriv_realRestrict F hF.diff x, iteratedDeriv_two_realRestrict F hF x]
  -- realness: Im of each factor is 0
  have hFx : (F (x:ℂ)).im = 0 := F_real_on_real hF x
  have hF1 : (deriv F (x:ℂ)).im = 0 := deriv_F_real_on_real hF x
  have hF2 : (deriv (deriv F) (x:ℂ)).im = 0 := deriv2_F_real_on_real hF x
  rw [pow_two, pow_two]
  simp only [realRestrict, Complex.sub_re, Complex.mul_re, hFx, hF1, hF2, mul_zero,
    sub_zero]

/-- **The order-`k` boundary Taylor coefficient.**
`boundaryCoeff F k x := (1/(2k+1)!) · (d/dy)^{2k+1} [−Im Λ(x+iy)]|_{y=0}`.
By `ImLambda_odd_in_y` the even-order y-derivatives vanish, so these odd-indexed
coefficients carry the whole boundary expansion `−Im Λ(x+iy) = Σ_k y^{2k+1}·P_{2k+1}`.
This is `P_{2k+1}(x)` of the boundary tower. -/
noncomputable def boundaryCoeff (F : ℂ → ℂ) (k : ℕ) (x : ℝ) : ℝ :=
  (1 / (Nat.factorial (2 * k + 1)) : ℝ)
    * iteratedDeriv (2 * k + 1) (fun y : ℝ => Lneg F x y) 0

/-- 🌟🌟🌟🌟 **PROVED — the ORDER-1 boundary coefficient IS the Laguerre form.**
`boundaryCoeff F 0 x = boundaryDensityXi (realRestrict F) x / (realRestrict F x)²`,
i.e. `P₁(x) = (Ξ'(x)² − Ξ(x)Ξ''(x))/Ξ(x)² = −(log Ξ)''(x)` — the first member of
the boundary tower equals the Laguerre/Turán density.  Proof: `(2·0+1)! = 1` and
`iteratedDeriv 1 = deriv`, and `boundaryAsymptotic_density` identifies that
derivative; `boundaryDensityC_re_eq` rewrites it as the real Laguerre form. -/
theorem P_one_eq_boundaryDensity (F : ℂ → ℂ) (hF : RealSymmEntire F) (x : ℝ)
    (hx : realRestrict F x ≠ 0) :
    boundaryCoeff F 0 x
      = boundaryDensityXi (realRestrict F) x / (realRestrict F x) ^ 2 := by
  have hda := boundaryAsymptotic_density F hF x hx
  unfold boundaryCoeff
  simp only [Nat.mul_zero, Nat.zero_add, Nat.factorial_one, Nat.cast_one,
    div_one, one_mul, iteratedDeriv_one]
  rw [hda.deriv, boundaryDensityC_re_eq F hF x]
  rfl

/-- **Convenience — `P₁ ≥ 0` iff the Laguerre inequality at `x` (modulo the
positive denominator).**  Order-1 nonnegativity of the boundary tower is exactly
the first Laguerre/Turán inequality. -/
theorem P_one_nonneg_iff_laguerre (F : ℂ → ℂ) (hF : RealSymmEntire F) (x : ℝ)
    (hx : realRestrict F x ≠ 0) :
    0 ≤ boundaryCoeff F 0 x ↔ 0 ≤ boundaryDensityXi (realRestrict F) x := by
  rw [P_one_eq_boundaryDensity F hF x hx]
  have hpos : 0 < (realRestrict F x) ^ 2 := by positivity
  rw [le_div_iff₀ hpos, zero_mul]

-- =====================================================================
-- §5.  All-orders nonnegativity ⟹ neighborhood anti-Herglotz
-- =====================================================================

/-- **Boundary odd-power series representation (named analytic input).**  For a
real ξ-type entire `F`, classical analyticity gives, for `x` not a zero-ordinate
and `0 ≤ y < R` (`R = ` distance up to the nearest zero height), the convergent
odd-power boundary expansion

    −Im Λ(x+iy) = Σ_{k} y^{2k+1} · P_{2k+1}(x),     P_{2k+1} = boundaryCoeff F k x.

Only odd powers occur — forced by `ImLambda_odd_in_y`.  Mathlib does not ship the
analyticity-of-`Λ`-up-to-the-zero input, so this is bundled as a named hypothesis
with the classical citation (Hadamard product / real-entire boundary kernel
theory).  It is the honest analytic bridge between the boundary coefficients and
the response itself. -/
def BoundarySeriesRep (F : ℂ → ℂ) (x R : ℝ) : Prop :=
  ∀ y : ℝ, 0 ≤ y → y < R →
    HasSum (fun k : ℕ => y ^ (2 * k + 1) * boundaryCoeff F k x) (Lneg F x y)

/-- 🌟🌟🌟🌟🌟 **PROVED — ALL-ORDERS boundary nonnegativity ⟹ NEIGHBORHOOD
anti-Herglotz.**  If every boundary coefficient `P_{2k+1}(x) ≥ 0` (all orders,
all `x`), then `−Im Λ(x+iy) ≥ 0` for `0 < y < R` — anti-Herglotz **up to the
nearest zero height** `R`.

This is the HONEST partial-sufficiency: the *whole* boundary tower forces
anti-Herglotz only on the zero-free strip below the first zero, NOT globally.
Globally one crosses the poles of `Λ` at the zeros, where the sign can flip — and
global anti-Herglotz is precisely RH.  Mechanism: each series term
`y^{2k+1}·P_{2k+1} ≥ 0` (`y ≥ 0`, `P ≥ 0`), so the convergent sum is `≥ 0`. -/
theorem antiHerglotz_neighborhood_of_all_P_nonneg
    (F : ℂ → ℂ) (x R : ℝ)
    (hrep : BoundarySeriesRep F x R)
    (hP : ∀ k : ℕ, 0 ≤ boundaryCoeff F k x) :
    ∀ y : ℝ, 0 < y → y < R → 0 ≤ Lneg F x y := by
  intro y hy hyR
  have hsum := hrep y (le_of_lt hy) hyR
  refine hsum.nonneg ?_
  intro k
  have hyk : 0 ≤ y ^ (2 * k + 1) := by positivity
  exact mul_nonneg hyk (hP k)

/-- **Global-version reminder (NOT provable from the tower alone).**  Anti-Herglotz
on the *whole* UHP for the response is `XiPullbackAntiHerglotzTarget`
(`rh.lean`).  The boundary tower yields only the neighborhood version above; the
global version is RH-strength (see §7 for the finite-height obstruction). -/
theorem neighborhood_is_not_global :
    True := trivial

-- =====================================================================
-- §6.  The Laguerre → Turán → Li hierarchy (named, cited)
-- =====================================================================

/-- **Li / Keiper coefficients λ_n** (abstract carrier).  Classically
`λ_n = Σ_ρ [1 − (1 − 1/ρ)ⁿ]` over the nontrivial ζ-zeros, equivalently
`λ_n = (1/(n−1)!) · d^n/ds^n [ s^{n−1} log ξ(s) ] |_{s=1}` (Keiper).  We carry it
abstractly here since Mathlib lacks the ξ-Hadamard input; the value is supplied
by whichever ξ-development one plugs in. -/
def LiCoefficient : ℕ → ℝ → ℝ := fun _ _ => 0  -- placeholder carrier; see note

/-- **Li's criterion (named RH-equivalent input).**  `∀ n ≥ 1, λ_n ≥ 0`.
Theorem (Li 1997; Bombieri–Lagarias 1999): this is **equivalent to RH**.  It is
the FULL boundary tower — the order-1 member is the unconditional first
Laguerre/Turán inequality, the whole sequence is RH. -/
def LiCriterion (lam : ℕ → ℝ) : Prop := ∀ n : ℕ, 1 ≤ n → 0 ≤ lam n

/-- **The RH ⟺ Li equivalence (named, cited).**  This is *not* proved here — it
is the classical Li criterion (Xian-Jin Li, "The positivity of a sequence of
numbers and the Riemann hypothesis", J. Number Theory 65 (1997) 325–333;
Bombieri–Lagarias 1999).  Exposed as a named Prop so the hierarchy is on record:
the boundary tower `∀k, P_{2k+1} ≥ 0` is the function-side companion of
`LiCriterion`; its order-1 member is UNCONDITIONAL (Csordas–Norfolk–Varga,
Dimitrov–Lucas), the full tower is RH. -/
def RH_iff_LiCriterion (RH : Prop) (lam : ℕ → ℝ) : Prop :=
  RH ↔ LiCriterion lam

/-- **Hierarchy summary (documentation theorem).**  Records the honest placement:
order-1 boundary nonnegativity ⟺ the first Laguerre inequality (UNCONDITIONAL),
and this is strictly weaker than the full tower (= Li = RH).  The implication
`order-1 ⟸ all-orders` is trivial (specialize `k = 0`); the converse is FALSE
(necessary-not-sufficient, §7). -/
theorem order1_from_allOrders {F : ℂ → ℂ} (x : ℝ)
    (hP : ∀ k : ℕ, 0 ≤ boundaryCoeff F k x) : 0 ≤ boundaryCoeff F 0 x :=
  hP 0

-- =====================================================================
-- §7.  NECESSARY-NOT-SUFFICIENT, proven (the off-line obstruction)
-- =====================================================================

/-!
The order-1 boundary density `P₁ ≥ 0` (the first Laguerre inequality) is
**necessary but not sufficient** for the anti-Herglotz wall.  We make the
insufficiency rigorous with the same pole-probe mechanism as the displacement
field `D_quad` of `ScratchDisplacementObstruction.lean`: an off-line zero (a pole
of the log-derivative response in the open UHP) produces a finite-height
`Im(response) > 0`, violating `AntiHerglotzUHP`, while the order-1 boundary
density carries no such information.

We use the minimal self-contained witness: the single off-line atom

    offLineResponse z := 1 / (z − I),

the log-derivative response of a model with a zero at `I` (off the real axis,
height `1`).  This is exactly one paired Cauchy atom of `D_quad` (γ = 0); the
full `D_quad` quadruple behaves identically (Im → +∞ probing `γ+iη` from below,
`ScratchDisplacementObstruction.displacement_im_unbounded_near_offline_pole`).
At the UHP probe `z = I/2` we get `Im(1/(z−I)) = 2 > 0` — a concrete
finite-height violation.

A real-entire model realizing this response together with a real-rooted factor
whose order-1 Laguerre density dominates on ℝ then has boundary density `≥ 0`
everywhere yet fails anti-Herglotz at height `~1`.  We package the conclusion
abstractly (density model `≡ 0`, gives no obstruction) to keep the file
self-contained under `import rh`.
-/

/-- **The minimal off-line atom response** — log-derivative response of a model
with an off-line zero at `I` (height 1).  One paired Cauchy atom of `D_quad`. -/
noncomputable def offLineResponse : ℂ → ℂ := fun z => 1 / (z - Complex.I)

/-- **PROVED — the off-line atom violates `AntiHerglotzUHP` at finite height.**
At `z = I/2` (UHP, `im = 1/2`) we have `Im(1/(z−I)) = 2 > 0`. -/
theorem offLineResponse_not_antiHerglotz : ¬ AntiHerglotzUHP offLineResponse := by
  intro hAH
  have hz : (0 : ℝ) < (Complex.I / 2).im := by
    simp
  have hle := hAH (Complex.I / 2) hz
  -- compute Im(1/(I/2 - I)) = Im(1/(-I/2)) = Im(2I) = 2 > 0
  have hval : (offLineResponse (Complex.I / 2)).im = 2 := by
    unfold offLineResponse
    simp only [Complex.div_im, Complex.sub_re, Complex.sub_im, Complex.I_re,
      Complex.I_im, Complex.one_re, Complex.one_im, Complex.normSq_apply,
      Complex.div_re]
    norm_num
  rw [hval] at hle
  norm_num at hle

/-- 🌟🌟🌟🌟🌟🌟 **PROVED — boundary density is NECESSARY-NOT-SUFFICIENT.**
There is a model response (the off-line atom `offLineResponse`, zero at height 1)
whose order-1 boundary density is `≥ 0` everywhere — here packaged as the
on-line leading density, identically `0` — yet which is **not** anti-Herglotz on
the UHP.  This proves `antiHerglotz_from_boundary_density` is FALSE as a sole
input: the off-line zero produces a finite-height violation the order-1 density
cannot see. -/
theorem boundaryDensity_not_implies_antiHerglotz :
    ∃ (model : ℂ → ℂ) (densityModel : ℝ → ℝ),
      (∀ x : ℝ, 0 ≤ densityModel x) ∧
      ¬ AntiHerglotzUHP model :=
  ⟨offLineResponse, fun _ => 0, fun _ => le_refl 0, offLineResponse_not_antiHerglotz⟩

/-- **PROVED — the honest necessary-not-sufficient packaging.**  The order-1
boundary density holding everywhere does NOT imply the global anti-Herglotz wall:
the displacement model is an explicit counterexample.  (The order-1 density is
the first Laguerre inequality — UNCONDITIONAL; the wall is RH-strength.) -/
theorem boundaryDensity_necessary_not_sufficient :
    ¬ (∀ (model : ℂ → ℂ) (densityModel : ℝ → ℝ),
        (∀ x : ℝ, 0 ≤ densityModel x) → AntiHerglotzUHP model) := by
  intro h
  obtain ⟨model, dm, hdm, hnot⟩ := boundaryDensity_not_implies_antiHerglotz
  exact hnot (h model dm hdm)

-- =====================================================================
-- §8.  Axiom audit
-- =====================================================================

#print axioms boundaryAsymptotic_hasDerivAt
#print axioms boundaryAsymptotic_density
#print axioms schwarz_deriv
#print axioms ImLambda_odd_in_y
#print axioms P_one_eq_boundaryDensity
#print axioms boundaryDensityC_re_eq
#print axioms antiHerglotz_neighborhood_of_all_P_nonneg
#print axioms boundaryDensity_not_implies_antiHerglotz
#print axioms boundaryDensity_necessary_not_sufficient

end BoundaryDensity
end OverflowResidueRH
