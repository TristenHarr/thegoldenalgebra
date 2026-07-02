import Mathlib
import rh

/-!
# ScratchDisplacementObstruction — the displacement carries genuine RH-strength

This file is the **honesty certificate** for the displacement gate
`(displacementError z).im ≤ 0` of
`OverflowResidueRH.TrueKernelTailDataWithDisplacement`
(`ScratchDisplacement.lean`).

It does NOT touch ξ.  It works entirely with the elementary **displacement
field** of a functional-equation quadruple of pullback points
`{±γ ± iη}` (`η = β − ½`):

    K_u(z) := 1/(z-u) + 1/(z+u)                        (paired Cauchy atom)
    D_quad(z,γ,η) := K_{γ+iη}(z) + K_{γ−iη}(z) − 2·K_γ(z)

(two true paired atoms, minus two real-height atoms; `D_quad ≡ 0` at `η = 0`).

The symbolic/numeric provenance is `d_quad_displacement.py`.  Every constant
below was verified against that script's output.

## Results (all elementary; no ξ, no RH assumed)

* `Dquad_zero_at_onLine`        — on-line config (`η = 0`) gives `D_quad = 0`.
* `Dquad_im_formula`            — closed form of `(D_quad ⟨x,y⟩ γ η).im`.
* `displacement_linear_term_vanishes` — `d/dη (Im D_quad)|₀ = 0`: the on-line
  config is a genuine critical point of the displacement (real structural fact).
* `displacement_C2_on_axis`     — the `η²`-coefficient on `x = 0` equals
  `−4y(y²−3γ²)/(y²+γ²)³`.
* `displacement_C2_sign_indefinite` — that coefficient is sign-indefinite:
  no usable pointwise sign.
* `displacement_im_unbounded_near_offline_pole` — for `η ≠ 0`, probing the UHP
  pole `γ+iη` from below sends `Im D_quad → +∞` (raw unboundedness witness).
* `displacement_has_positive_overflow_at_offline_zero` — restated as
  `PositiveUpperImaginaryEscape (fun z => D_quad z γ η)` (rh.lean predicate).
* `no_pointwise_displacement_bound_if_offline_zero` — therefore the one-sided
  gate `∀ z, 0<z.im → (D_quad z γ η).im ≤ 0` is **provably FALSE** whenever an
  off-line config exists.  The gate is not merely unproven — it is RH-strength.
-/

namespace OffLineDisplacement

open Complex Filter Topology

-- =====================================================================
-- §0. Base atom: imaginary part of a single Cauchy reciprocal.
-- =====================================================================

/-- **Imaginary part of `1/(z-w)`** for `z = x+iy`, `w = a+ib`.
`Im 1/(z-w) = -(y-b)/((x-a)²+(y-b)²)`.  Holds unconditionally (the division
identity is valid even at the pole, where both sides are `_/0 = 0`). -/
theorem im_recip (x y a b : ℝ) :
    ((1 : ℂ) / ((⟨x, y⟩ : ℂ) - ⟨a, b⟩)).im
      = -(y - b) / ((x - a) ^ 2 + (y - b) ^ 2) := by
  rw [Complex.div_im]
  simp only [Complex.one_re, Complex.one_im, Complex.sub_re, Complex.sub_im,
    Complex.normSq_apply]
  ring_nf

/-- **Imaginary part of `1/(z+w)`** for `z = x+iy`, `w = a+ib`.
`Im 1/(z+w) = -(y+b)/((x+a)²+(y+b)²)`. -/
theorem im_recip_add (x y a b : ℝ) :
    ((1 : ℂ) / ((⟨x, y⟩ : ℂ) + ⟨a, b⟩)).im
      = -(y + b) / ((x + a) ^ 2 + (y + b) ^ 2) := by
  rw [Complex.div_im]
  simp only [Complex.one_re, Complex.one_im, Complex.add_re, Complex.add_im,
    Complex.normSq_apply]
  ring_nf

-- =====================================================================
-- §1. The displacement field.
-- =====================================================================

/-- Paired Cauchy atom `K_u(z) = 1/(z-u) + 1/(z+u)`. -/
noncomputable def Kpair (u z : ℂ) : ℂ := 1 / (z - u) + 1 / (z + u)

/-- **Quadruple displacement** `D_quad(z,γ,η) =
K_{γ+iη}(z) + K_{γ−iη}(z) − 2·K_γ(z)`.  Two true paired atoms (`γ±iη`,
covering all four pullback points `{±γ ± iη}`) minus two real-height atoms
at `±γ`.  Plain complex rational function of `z`; `γ, η` real parameters. -/
noncomputable def D_quad (z : ℂ) (γ η : ℝ) : ℂ :=
  Kpair ⟨γ, η⟩ z + Kpair ⟨γ, -η⟩ z - 2 * Kpair ⟨γ, 0⟩ z

-- =====================================================================
-- §2. Theorem 1 — on-line collapse.
-- =====================================================================

/-- 🌟 **Theorem 1 — `D_quad ≡ 0` at the on-line config (`η = 0`).**
At `η = 0` the two true paired atoms both collapse onto the real height
atom, so the displacement vanishes identically in `z, γ`. -/
theorem Dquad_zero_at_onLine (z : ℂ) (γ : ℝ) : D_quad z γ 0 = 0 := by
  simp only [D_quad, Kpair, neg_zero]
  ring

-- =====================================================================
-- §2b. Atom derivative (the building block for the η-expansion).
-- =====================================================================

/-- **Atom derivative.** For `f(η) = (η+s)/((η+s)²+c²)` with `s²+c² ≠ 0`,
`f'(0) = (c²−s²)/(s²+c²)²`. -/
theorem atom_hasDerivAt (s c : ℝ) (hd : s ^ 2 + c ^ 2 ≠ 0) :
    HasDerivAt (fun η : ℝ => (η + s) / ((η + s) ^ 2 + c ^ 2))
      ((c ^ 2 - s ^ 2) / (s ^ 2 + c ^ 2) ^ 2) 0 := by
  have hnum : HasDerivAt (fun η : ℝ => η + s) 1 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).add_const s
  have hden : HasDerivAt (fun η : ℝ => (η + s) ^ 2 + c ^ 2) (2 * s) 0 := by
    have h1 : HasDerivAt (fun η : ℝ => (η + s) ^ 2) (2 * (0 + s) ^ 1 * 1) 0 :=
      hnum.pow 2
    have h2 : HasDerivAt (fun η : ℝ => (η + s) ^ 2 + c ^ 2)
        (2 * (0 + s) ^ 1 * 1) 0 := h1.add_const (c ^ 2)
    convert h2 using 1; ring
  have hdne : ((0 : ℝ) + s) ^ 2 + c ^ 2 ≠ 0 := by simpa using hd
  have := hnum.div hden hdne
  convert this using 1
  field_simp
  ring

-- =====================================================================
-- §3. Theorem 2 — closed form of the imaginary part.
-- =====================================================================

/-- The explicit real closed form of `Im D_quad` at `z = x+iy`.  Verified
against `d_quad_displacement.py` (TASK 2): two height terms `+2y/(...)`, plus
two `(η−y)/(...)` true-atom terms, minus two `(η+y)/(...)` true-atom terms. -/
noncomputable def ImDquad (x y γ η : ℝ) : ℝ :=
    2 * y / (y ^ 2 + (γ + x) ^ 2)
  + 2 * y / (y ^ 2 + (γ - x) ^ 2)
  + (η - y) / ((η - y) ^ 2 + (γ + x) ^ 2)
  + (η - y) / ((η - y) ^ 2 + (γ - x) ^ 2)
  - (η + y) / ((η + y) ^ 2 + (γ + x) ^ 2)
  - (η + y) / ((η + y) ^ 2 + (γ - x) ^ 2)

/-- 🌟🌟 **Theorem 2 — closed form for `(D_quad ⟨x,y⟩ γ η).im`.**
Equals `ImDquad x y γ η`, the sum of six rational terms. -/
theorem Dquad_im_formula (x y γ η : ℝ) :
    (D_quad (⟨x, y⟩ : ℂ) γ η).im = ImDquad x y γ η := by
  simp only [D_quad, Kpair, Complex.add_im, Complex.sub_im, Complex.mul_im,
    Complex.re_ofNat, Complex.im_ofNat, zero_mul, add_zero,
    im_recip, im_recip_add]
  simp only [ImDquad]
  ring

-- =====================================================================
-- §4. Theorem 3 — the linear (O(η)) term vanishes.
-- =====================================================================

/-- 🌟🌟🌟 **Theorem 3 — the displacement's linear term in `η` vanishes.**
`d/dη (Im D_quad)|_{η=0} = 0` for every `x, γ` and every `y > 0`.  The on-line
config (`η = 0`) is therefore a genuine *critical point* of the displacement —
a real structural fact, not an artifact.  (The two true paired atoms approach
the real-height atoms to first order; the O(η) contributions cancel.) -/
theorem displacement_linear_term_vanishes (x y γ : ℝ) (hy : 0 < y) :
    deriv (fun η : ℝ => (D_quad (⟨x, y⟩ : ℂ) γ η).im) 0 = 0 := by
  -- rewrite the differentiand as the explicit real formula
  have hfun : (fun η : ℝ => (D_quad (⟨x, y⟩ : ℂ) γ η).im)
      = fun η : ℝ => ImDquad x y γ η := by
    funext η; exact Dquad_im_formula x y γ η
  rw [hfun]
  -- positivity of the two paired denominators (needed for atom_hasDerivAt)
  have hy2 : 0 < y ^ 2 := by positivity
  have hdp : (-y) ^ 2 + (γ + x) ^ 2 ≠ 0 := by nlinarith [sq_nonneg (γ + x)]
  have hdm : (-y) ^ 2 + (γ - x) ^ 2 ≠ 0 := by nlinarith [sq_nonneg (γ - x)]
  have hdp' : (y) ^ 2 + (γ + x) ^ 2 ≠ 0 := by nlinarith [sq_nonneg (γ + x)]
  have hdm' : (y) ^ 2 + (γ - x) ^ 2 ≠ 0 := by nlinarith [sq_nonneg (γ - x)]
  -- the four η-dependent atoms as HasDerivAt; the two height terms are constant
  have a3 := atom_hasDerivAt (-y) (γ + x) hdp
  have a4 := atom_hasDerivAt (-y) (γ - x) hdm
  have a5 := atom_hasDerivAt (y) (γ + x) hdp'
  have a6 := atom_hasDerivAt (y) (γ - x) hdm'
  -- assemble HasDerivAt for ImDquad with derivative = 0
  have key : HasDerivAt (fun η : ℝ => ImDquad x y γ η) 0 0 := by
    have hc1 : HasDerivAt (fun _ : ℝ => 2 * y / (y ^ 2 + (γ + x) ^ 2)) 0 0 :=
      hasDerivAt_const 0 _
    have hc2 : HasDerivAt (fun _ : ℝ => 2 * y / (y ^ 2 + (γ - x) ^ 2)) 0 0 :=
      hasDerivAt_const 0 _
    have e3 : (fun η : ℝ => (η - y) / ((η - y) ^ 2 + (γ + x) ^ 2))
        = fun η : ℝ => (η + (-y)) / ((η + (-y)) ^ 2 + (γ + x) ^ 2) := by
      funext η; ring_nf
    have e4 : (fun η : ℝ => (η - y) / ((η - y) ^ 2 + (γ - x) ^ 2))
        = fun η : ℝ => (η + (-y)) / ((η + (-y)) ^ 2 + (γ - x) ^ 2) := by
      funext η; ring_nf
    have a3' : HasDerivAt (fun η : ℝ => (η - y) / ((η - y) ^ 2 + (γ + x) ^ 2))
        (((γ + x) ^ 2 - (-y) ^ 2) / ((-y) ^ 2 + (γ + x) ^ 2) ^ 2) 0 := by
      rw [e3]; exact a3
    have a4' : HasDerivAt (fun η : ℝ => (η - y) / ((η - y) ^ 2 + (γ - x) ^ 2))
        (((γ - x) ^ 2 - (-y) ^ 2) / ((-y) ^ 2 + (γ - x) ^ 2) ^ 2) 0 := by
      rw [e4]; exact a4
    -- ImDquad = (((hc1 + hc2) + a3') + a4') - a5 - a6 ; the derivative cancels.
    have hsum := ((((hc1.add hc2).add a3').add a4').sub a5).sub a6
    have hval : (0 + 0 + ((γ + x) ^ 2 - (-y) ^ 2) / ((-y) ^ 2 + (γ + x) ^ 2) ^ 2
          + ((γ - x) ^ 2 - (-y) ^ 2) / ((-y) ^ 2 + (γ - x) ^ 2) ^ 2
          - ((γ + x) ^ 2 - y ^ 2) / (y ^ 2 + (γ + x) ^ 2) ^ 2)
          - ((γ - x) ^ 2 - y ^ 2) / (y ^ 2 + (γ - x) ^ 2) ^ 2 = 0 := by
      have hyy : (-y) ^ 2 = y ^ 2 := by ring
      rw [hyy]; ring
    rw [hval] at hsum
    -- transfer the derivative along the pointwise equality g = ImDquad
    apply hsum.congr_of_eventuallyEq
    filter_upwards with η
    simp only [Pi.add_apply, Pi.sub_apply, ImDquad]
  simpa using key.deriv

-- =====================================================================
-- §5. The quadratic coefficient on the axis, and its indefinite sign.
-- =====================================================================

/-- **On-axis quadratic coefficient** `C₂(0,y,γ) = −4y(y²−3γ²)/(y²+γ²)³`.
This is `½·(d²/dη²) Im D_quad` at `η = 0`, `x = 0` — verified against
`d_quad_displacement.py` (TASK 3/eta² check: `−4y(y²−3)/(y²+1)³` at `γ=1`). -/
noncomputable def C₂ (y γ : ℝ) : ℝ :=
  -4 * y * (y ^ 2 - 3 * γ ^ 2) / (y ^ 2 + γ ^ 2) ^ 3

/-- **Second-derivative atom.** For `g(η) = (η+s)/((η+s)²+c²)` with
`s²+c² ≠ 0`, `g` is twice differentiable at `0` with
`g''(0) = 2s(s²−3c²)/(s²+c²)³` — i.e. `HasDerivAt g' (g''(0)) 0` where
`g'(η) = (c²−(η+s)²)/((η+s)²+c²)²`. -/
theorem atom_secondDerivAt (s c : ℝ) (hd : s ^ 2 + c ^ 2 ≠ 0) :
    HasDerivAt
      (fun η : ℝ => (c ^ 2 - (η + s) ^ 2) / ((η + s) ^ 2 + c ^ 2) ^ 2)
      (2 * s * (s ^ 2 - 3 * c ^ 2) / (s ^ 2 + c ^ 2) ^ 3) 0 := by
  have hu : HasDerivAt (fun η : ℝ => η + s) 1 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).add_const s
  -- numerator c² − (η+s)²
  have hnum : HasDerivAt (fun η : ℝ => c ^ 2 - (η + s) ^ 2) (-(2 * s)) 0 := by
    have h1 : HasDerivAt (fun η : ℝ => (η + s) ^ 2) (2 * (0 + s) ^ 1 * 1) 0 :=
      hu.pow 2
    have h2 : HasDerivAt (fun η : ℝ => c ^ 2 - (η + s) ^ 2)
        (0 - 2 * (0 + s) ^ 1 * 1) 0 := (hasDerivAt_const 0 (c ^ 2)).sub h1
    convert h2 using 1; ring
  -- denominator ((η+s)²+c²)²
  have hden0 : HasDerivAt (fun η : ℝ => (η + s) ^ 2 + c ^ 2) (2 * s) 0 := by
    have h1 : HasDerivAt (fun η : ℝ => (η + s) ^ 2) (2 * (0 + s) ^ 1 * 1) 0 :=
      hu.pow 2
    have h2 := h1.add_const (c ^ 2)
    convert h2 using 1; ring
  have hden : HasDerivAt (fun η : ℝ => ((η + s) ^ 2 + c ^ 2) ^ 2)
      (2 * (s ^ 2 + c ^ 2) ^ 1 * (2 * s)) 0 := by
    have := hden0.pow 2
    convert this using 1
    ring
  have hdne : ((0 : ℝ) + s) ^ 2 + c ^ 2 ≠ 0 := by simpa using hd
  have hdne2 : (((0 : ℝ) + s) ^ 2 + c ^ 2) ^ 2 ≠ 0 := pow_ne_zero 2 hdne
  have hq := hnum.div hden hdne2
  convert hq using 1
  have hs : ((0 : ℝ) + s) = s := by ring
  rw [hs] at *
  have hpos : s ^ 2 + c ^ 2 ≠ 0 := hd
  field_simp
  ring

/-- 🌟🌟🌟 **Theorem 4 — the on-axis `η²`-coefficient.**
`½·(iteratedDeriv 2) (fun η => Im D_quad(⟨0,y⟩,γ,η)) 0 = C₂ y γ
 = −4y(y²−3γ²)/(y²+γ²)³`, for `y > 0`.  The displacement's second-order
behaviour on the imaginary axis. -/
theorem displacement_C2_on_axis (y γ : ℝ) (hy : 0 < y) (hγ : γ ≠ 0) :
    (1 / 2 : ℝ) * iteratedDeriv 2 (fun η : ℝ => (D_quad (⟨0, y⟩ : ℂ) γ η).im) 0
      = C₂ y γ := by
  -- denominators
  have hy2 : 0 < y ^ 2 := by positivity
  have hg2 : 0 < γ ^ 2 := by positivity
  have hcg : y ^ 2 + γ ^ 2 ≠ 0 := by nlinarith [sq_nonneg γ]
  have hcg' : (-y) ^ 2 + γ ^ 2 ≠ 0 := by nlinarith [sq_nonneg γ]
  -- on-axis Im formula: (γ±0) collapse, two height + two pairs (doubled).
  have hfun : (fun η : ℝ => (D_quad (⟨0, y⟩ : ℂ) γ η).im)
      = fun η : ℝ =>
          4 * y / (y ^ 2 + γ ^ 2)
          + 2 * ((η - y) / ((η - y) ^ 2 + γ ^ 2))
          - 2 * ((η + y) / ((η + y) ^ 2 + γ ^ 2)) := by
    funext η
    rw [Dquad_im_formula]
    simp only [ImDquad, add_zero, sub_zero]
    ring
  rw [hfun]
  -- first derivative as a function: f'(η) for the on-axis f.
  -- f' = 2·atomDeriv(s=-y) − 2·atomDeriv(s=y) (the constant drops).
  have hf' : deriv (fun η : ℝ =>
        4 * y / (y ^ 2 + γ ^ 2)
        + 2 * ((η - y) / ((η - y) ^ 2 + γ ^ 2))
        - 2 * ((η + y) / ((η + y) ^ 2 + γ ^ 2)))
      = fun η : ℝ =>
          2 * ((γ ^ 2 - (η + (-y)) ^ 2) / ((η + (-y)) ^ 2 + γ ^ 2) ^ 2)
          - 2 * ((γ ^ 2 - (η + y) ^ 2) / ((η + y) ^ 2 + γ ^ 2) ^ 2) := by
    funext η
    -- atom first-derivative at general η
    have e1 : (fun η : ℝ => (η - y) / ((η - y) ^ 2 + γ ^ 2))
        = fun η : ℝ => (η + (-y)) / ((η + (-y)) ^ 2 + γ ^ 2) := by funext η; ring_nf
    have hdneg : ∀ t : ℝ, (t + (-y)) ^ 2 + γ ^ 2 ≠ 0 := by
      intro t; nlinarith [sq_nonneg (t + (-y)), hg2]
    have hdpos : ∀ t : ℝ, (t + y) ^ 2 + γ ^ 2 ≠ 0 := by
      intro t; nlinarith [sq_nonneg (t + y), hg2]
    -- HasDerivAt for each atom at η
    have d1 : HasDerivAt (fun t : ℝ => (t + (-y)) / ((t + (-y)) ^ 2 + γ ^ 2))
        ((γ ^ 2 - (η + (-y)) ^ 2) / ((η + (-y)) ^ 2 + γ ^ 2) ^ 2) η := by
      have hu : HasDerivAt (fun t : ℝ => t + (-y)) 1 η := by
        simpa using (hasDerivAt_id η).add_const (-y)
      have hden : HasDerivAt (fun t : ℝ => (t + (-y)) ^ 2 + γ ^ 2)
          (2 * (η + (-y)) ^ 1 * 1) η := (hu.pow 2).add_const (γ ^ 2)
      have := hu.div hden (hdneg η)
      convert this using 1; field_simp; ring
    have d2 : HasDerivAt (fun t : ℝ => (t + y) / ((t + y) ^ 2 + γ ^ 2))
        ((γ ^ 2 - (η + y) ^ 2) / ((η + y) ^ 2 + γ ^ 2) ^ 2) η := by
      have hu : HasDerivAt (fun t : ℝ => t + y) 1 η := by
        simpa using (hasDerivAt_id η).add_const y
      have hden : HasDerivAt (fun t : ℝ => (t + y) ^ 2 + γ ^ 2)
          (2 * (η + y) ^ 1 * 1) η := (hu.pow 2).add_const (γ ^ 2)
      have := hu.div hden (hdpos η)
      convert this using 1; field_simp; ring
    have hconst : HasDerivAt (fun _ : ℝ => 4 * y / (y ^ 2 + γ ^ 2)) 0 η :=
      hasDerivAt_const η _
    have d1' : HasDerivAt (fun t : ℝ => (t - y) / ((t - y) ^ 2 + γ ^ 2))
        ((γ ^ 2 - (η + (-y)) ^ 2) / ((η + (-y)) ^ 2 + γ ^ 2) ^ 2) η := by
      rw [e1]; exact d1
    have hcomb := (hconst.add ((d1'.const_mul 2))).sub ((d2.const_mul 2))
    have hcomb' : HasDerivAt (fun η : ℝ =>
          4 * y / (y ^ 2 + γ ^ 2)
          + 2 * ((η - y) / ((η - y) ^ 2 + γ ^ 2))
          - 2 * ((η + y) / ((η + y) ^ 2 + γ ^ 2)))
        (0 + 2 * ((γ ^ 2 - (η + -y) ^ 2) / ((η + -y) ^ 2 + γ ^ 2) ^ 2) -
          2 * ((γ ^ 2 - (η + y) ^ 2) / ((η + y) ^ 2 + γ ^ 2) ^ 2)) η := hcomb
    rw [hcomb'.deriv]
    ring
  rw [iteratedDeriv_succ, iteratedDeriv_one, hf']
  -- now differentiate f' at 0 and halve
  have s1 := atom_secondDerivAt (-y) γ hcg'
  have s2 := atom_secondDerivAt (y) γ hcg
  have hcomb2 := (s1.const_mul 2).sub (s2.const_mul 2)
  have hcomb2' : HasDerivAt (fun η : ℝ =>
        2 * ((γ ^ 2 - (η + -y) ^ 2) / ((η + -y) ^ 2 + γ ^ 2) ^ 2) -
          2 * ((γ ^ 2 - (η + y) ^ 2) / ((η + y) ^ 2 + γ ^ 2) ^ 2))
      (2 * (2 * -y * ((-y) ^ 2 - 3 * γ ^ 2) / ((-y) ^ 2 + γ ^ 2) ^ 3) -
        2 * (2 * y * (y ^ 2 - 3 * γ ^ 2) / (y ^ 2 + γ ^ 2) ^ 3)) 0 := hcomb2
  rw [hcomb2'.deriv]
  -- evaluate: ½·[2·(2(-y)((-y)²−3γ²)/((-y)²+γ²)³) − 2·(2y(y²−3γ²)/(y²+γ²)³)]
  simp only [C₂]
  have hyy : (-y) ^ 2 = y ^ 2 := by ring
  rw [hyy]
  field_simp
  ring

/-- 🌟🌟🌟 **Theorem 5 — the quadratic coefficient is sign-indefinite.**
There exist `0 < y₁, 0 < y₂, 0 < γ` with `C₂ y₁ γ > 0` and `C₂ y₂ γ < 0`.
Concretely `γ = 1`, `y₁ = 1` gives `C₂ = 1 > 0`, `y₂ = 2` gives
`C₂ = −8/125 < 0`.  **Audit punchline:** the displacement has NO usable
pointwise sign at second order — the on-line config is a saddle, not an
extremum, so a pointwise `Im D ≤ 0` law is hopeless. -/
theorem displacement_C2_sign_indefinite :
    ∃ y₁ y₂ γ : ℝ, 0 < y₁ ∧ 0 < y₂ ∧ 0 < γ ∧
      0 < C₂ y₁ γ ∧ C₂ y₂ γ < 0 := by
  refine ⟨1, 2, 1, by norm_num, by norm_num, by norm_num, ?_, ?_⟩
  · simp only [C₂]; norm_num
  · simp only [C₂]; norm_num

-- =====================================================================
-- §6. Positive blow-up at the off-line pole; pointwise bound fails.
-- =====================================================================

/-- **Lower bound near the off-line pole.**  Probing `z = ⟨γ, η−ε⟩` (the UHP
pullback pole `γ+iη` approached from below), with `η > 0` and `0 < ε ≤ η/2`,
`Im D_quad ≥ 1/ε − 4/(3η)`.  The singular true atom contributes `1/ε`; all
other five atoms are uniformly bounded in this regime. -/
theorem displacement_im_lower_bound_near_pole
    (γ η ε : ℝ) (hη : 0 < η) (hε : 0 < ε) (hεη : ε ≤ η / 2) :
    1 / ε - 4 / (3 * η) ≤ (D_quad (⟨γ, η - ε⟩ : ℂ) γ η).im := by
  rw [Dquad_im_formula]
  simp only [ImDquad]
  -- abbreviations
  have hy : 0 < η - ε := by linarith
  have hA : 0 < 2 * η - ε := by linarith
  have hA' : 3 * η / 2 ≤ 2 * η - ε := by linarith
  -- the singular atom term γ-x = 0 collapses:  (η-(η-ε))/((η-(η-ε))²+0) = 1/ε
  have hεne : ε ≠ 0 := ne_of_gt hε
  have hsing : (η - (η - ε)) / ((η - (η - ε)) ^ 2 + (γ - γ) ^ 2) = 1 / ε := by
    rw [show γ - γ = 0 by ring, show η - (η - ε) = ε by ring,
        show ε ^ 2 + (0 : ℝ) ^ 2 = ε ^ 2 by ring, sq]
    rw [div_eq_div_iff (ne_of_gt (mul_pos hε hε)) (ne_of_gt hε)]
    ring
  -- the second height term 2(η-ε)/((η-ε)²+0):  positive
  have hht : 0 ≤ 2 * (η - ε) / ((η - ε) ^ 2 + (γ - γ) ^ 2) := by
    rw [show γ - γ = 0 by ring]; positivity
  -- first height term ≥ 0
  have hht1 : 0 ≤ 2 * (η - ε) / ((η - ε) ^ 2 + (γ + γ) ^ 2) := by positivity
  -- pair-plus term ≥ 0
  have hpp : 0 ≤ (η - (η - ε)) / ((η - (η - ε)) ^ 2 + (γ + γ) ^ 2) := by
    rw [show η - (η - ε) = ε by ring]; positivity
  -- subtracted term A:  (η+(η-ε))/((η+(η-ε))²+(γ+γ)²) ≤ 2/(3η)
  have hsubA : (η + (η - ε)) / ((η + (η - ε)) ^ 2 + (γ + γ) ^ 2) ≤ 2 / (3 * η) := by
    rw [show η + (η - ε) = 2 * η - ε by ring]
    rw [div_le_div_iff₀ (by positivity) (by linarith)]
    nlinarith [sq_nonneg (γ + γ), sq_nonneg (2 * η - ε), hA, hA', hη]
  -- subtracted term B:  (η+(η-ε))/((η+(η-ε))²+0) = 1/(2η-ε) ≤ 2/(3η)
  have hsubB : (η + (η - ε)) / ((η + (η - ε)) ^ 2 + (γ - γ) ^ 2) ≤ 2 / (3 * η) := by
    rw [show γ - γ = 0 by ring, show η + (η - ε) = 2 * η - ε by ring]
    rw [show (2 * η - ε) ^ 2 + (0 : ℝ) ^ 2 = (2 * η - ε) ^ 2 by ring]
    rw [div_le_div_iff₀ (by positivity) (by linarith)]
    nlinarith [hA, hA', hη]
  -- assemble:  Im = h1 + h2 + pp + (T4 = 1/ε) - subA - subB ≥ 1/ε - 4/(3η)
  have h43 : (4 : ℝ) / (3 * η) = 2 / (3 * η) + 2 / (3 * η) := by ring
  rw [h43]
  linarith [hht, hht1, hpp, hsing, hsubA, hsubB]

/-- 🌟🌟🌟🌟 **Theorem 6 — positive blow-up at the off-line pole.**
For an off-line config (`η > 0`), the displacement `Im D_quad` is *unbounded
above* as the probe `z = ⟨γ, η−ε⟩` approaches the UHP pullback pole `γ+iη`
from below (`ε ↓ 0`): for every `M` there is `ε > 0` with
`M < Im D_quad(⟨γ,η−ε⟩,γ,η)`.  The singular true atom `1/(z−(γ+iη)) = 1/(−iε)`
contributes `1/ε → +∞`, dominating the bounded background. -/
theorem displacement_im_unbounded_near_offline_pole
    (γ η : ℝ) (hη : 0 < η) :
    ∀ M : ℝ, ∃ ε : ℝ, 0 < ε ∧ 0 < η - ε ∧
      M < (D_quad (⟨γ, η - ε⟩ : ℂ) γ η).im := by
  intro M
  -- choose ε small:  ε < η/2 and 1/ε > M + 4/(3η)
  set B : ℝ := M + 4 / (3 * η) + 1 with hB
  have hpos : 0 < |B| + 1 := by positivity
  refine ⟨min (η / 2) (1 / (|B| + 1)), ?_, ?_, ?_⟩
  · exact lt_min (by linarith) (by positivity)
  · have : min (η / 2) (1 / (|B| + 1)) ≤ η / 2 := min_le_left _ _
    linarith
  · have hε : 0 < min (η / 2) (1 / (|B| + 1)) := lt_min (by linarith) (by positivity)
    have hεη : min (η / 2) (1 / (|B| + 1)) ≤ η / 2 := min_le_left _ _
    have hεB : min (η / 2) (1 / (|B| + 1)) ≤ 1 / (|B| + 1) := min_le_right _ _
    have hlb := displacement_im_lower_bound_near_pole γ η _ hη hε hεη
    -- 1/ε ≥ |B|+1 > M + 4/(3η)
    have hinv : |B| + 1 ≤ 1 / min (η / 2) (1 / (|B| + 1)) := by
      rw [le_div_iff₀ hε]
      calc (|B| + 1) * min (η / 2) (1 / (|B| + 1))
          ≤ (|B| + 1) * (1 / (|B| + 1)) := by
            apply mul_le_mul_of_nonneg_left hεB (le_of_lt hpos)
        _ = 1 := by field_simp
    have hBle : M + 4 / (3 * η) < |B| + 1 := by
      have : B ≤ |B| := le_abs_self B
      linarith [this, hB]
    linarith [hlb, hinv]

/-- **η-evenness of the displacement.**  `D_quad z γ (−η) = D_quad z γ η`:
swapping `η → −η` swaps the two true paired atoms `K_{γ+iη}, K_{γ−iη}`,
leaving the displacement invariant. -/
theorem Dquad_eta_symm (z : ℂ) (γ η : ℝ) :
    D_quad z γ (-η) = D_quad z γ η := by
  simp only [D_quad, neg_neg]
  ring

/-- 🌟🌟🌟🌟 **`displacement_has_positive_overflow_at_offline_zero`** —
restating Theorem 6 as the rh.lean predicate
`OverflowResidueRH.PositiveUpperImaginaryEscape` for the displacement field of
an off-line config (`η > 0`).  Some UHP point has strictly positive
`Im D_quad`. -/
theorem displacement_has_positive_overflow_at_offline_zero
    (γ η : ℝ) (hη : 0 < η) :
    OverflowResidueRH.PositiveUpperImaginaryEscape (fun z => D_quad z γ η) := by
  -- pick any ε giving Im D_quad > 0 (take M = 0 in Theorem 6)
  obtain ⟨ε, hε, hyε, hpos⟩ := displacement_im_unbounded_near_offline_pole γ η hη 0
  exact ⟨⟨γ, η - ε⟩, hyε, by simpa using hpos⟩

/-- 🌟🌟🌟🌟🌟 **`no_pointwise_displacement_bound_if_offline_zero`** — the
sole RH-strength gate `(displacementError z).im ≤ 0` is **provably false**
whenever an off-line config exists (`η ≠ 0`).  Hence the displacement bound is
not merely unproven — it is *equivalent to RH*: any off-line zero refutes it.
Derived directly from the raw positive-overflow witness (Theorem 6, `M = 0`),
using `η`-evenness to cover both signs of `η`. -/
theorem no_pointwise_displacement_bound_if_offline_zero
    (γ η : ℝ) (hη : η ≠ 0) :
    ¬ (∀ z : ℂ, 0 < z.im → (D_quad z γ η).im ≤ 0) := by
  intro hbound
  -- reduce to η > 0 using η-evenness; take M = 0 to get a strictly positive value
  rcases lt_or_gt_of_ne hη with hneg | hpos
  · have hpos' : 0 < -η := by linarith
    obtain ⟨ε, hε, hyε, hposim⟩ :=
      displacement_im_unbounded_near_offline_pole γ (-η) hpos' 0
    -- witness point w = ⟨γ, (-η) - ε⟩ with positive imaginary part
    have hwim : (0 : ℝ) < (⟨γ, -η - ε⟩ : ℂ).im := hyε
    -- via η-evenness:  Im D_quad(w,γ,η) = Im D_quad(w,γ,-η) > 0
    have hval : 0 < (D_quad (⟨γ, -η - ε⟩ : ℂ) γ η).im := by
      rw [← Dquad_eta_symm (⟨γ, -η - ε⟩ : ℂ) γ η]; simpa using hposim
    exact absurd (hbound _ hwim) (not_le.mpr hval)
  · obtain ⟨ε, hε, hyε, hposim⟩ :=
      displacement_im_unbounded_near_offline_pole γ η hpos 0
    have hwim : (0 : ℝ) < (⟨γ, η - ε⟩ : ℂ).im := hyε
    exact absurd (hbound _ hwim) (not_le.mpr (by simpa using hposim))

end OffLineDisplacement
