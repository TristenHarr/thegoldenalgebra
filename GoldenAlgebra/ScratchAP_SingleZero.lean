import rh

/-!
# ScratchAP_SingleZero: AP1 — the single-zero residue of the logarithmic derivative

This file proves the foundational brick of the argument principle:

  For `f : ℂ → ℂ` that factors on the closed rectangle as `f z = (z - a)^m · g z`
  with `g` analytic and non-vanishing on the closed rectangle and `a` strictly
  inside, the boundary contour integral of the logarithmic derivative is

      `∮_{∂R} f'/f = 2πi · m`,   equivalently   `(2πi)⁻¹ ∮_{∂R} f'/f = m`.

## Strategy

`f'/f = logDeriv f`.  Using the global factorization `f = (· - a)^m * g`,

  `logDeriv f z = m/(z - a) + logDeriv g z = principalKernel m a z + logDeriv g z`

at every boundary point `z` (where `z ≠ a` and `g z ≠ 0`, both forced by `a`
being interior and `g` non-vanishing).  The rectangle contour integral splits by
linearity into

  `∮ logDeriv f = ∮ principalKernel m a  +  ∮ logDeriv g`.

* The **pole part** `∮ principalKernel m a = 2πi · m` is the atomic residue
  computation of `ScratchResidue.lean`.  That file cannot be imported (it is not
  a library target), so its self-contained proof — which depends only on `rh.lean`
  and Mathlib — is reproduced here in the local namespace `ResidueBrick`, reusing
  the exact `ZetaRectangle` edge API (`bottomEdge`, `deriv_bottomEdge`,
  `hasDerivAt_bottomEdge`, `ContainsOpen`, `principalKernel`,
  `principalKernelRectangleIntegral`, `twoPiI`).

* The **analytic remainder** `∮ logDeriv g = 0` is Cauchy–Goursat: `logDeriv g =
  deriv g / g` is analytic on the closed rectangle since `g` is analytic and
  non-vanishing there.  We feed this through `rh.lean`'s unconditional
  `globalRectangleCauchyGoursatBridge` (the same engine `ScratchGoursat.lean`
  re-exports as `rectangleIntegral_eq_zero_of_analyticOn_closed`).

The only genuinely-missing Mathlib content (gluing an order-`m` interior zero
with no other zeros into a *global* analytic non-vanishing `g`) is isolated as the
hypothesis structure `GlobalOrderFactorization`, whose meaning and provenance are
documented on the structure itself.
-/

open Complex intervalIntegral
open scoped Real

namespace OverflowResidueRH
namespace BacklundTuring
namespace ScratchAPSingleZero

open ZetaRectangle

/-! ## Part 1 — The atomic residue brick (reproduced from `ScratchResidue.lean`)

`ScratchResidue.lean` is not a library target and cannot be `import`ed.  Its proof
of `∮ principalKernel m a = 2πi·m` depends only on `rh.lean` + Mathlib, so we
reproduce it verbatim here in a private namespace.  This keeps the pole residue
PROVEN (no axiom, no `sorry`). -/

namespace ResidueBrick

/-- One affine-edge integral of the unit kernel, evaluated by FTC with the
principal-log antiderivative. -/
theorem edge_integral_log
    (γ : ℝ → ℂ) (d a : ℂ)
    (hγ : ∀ t : ℝ, HasDerivAt γ d t)
    (hslit : ∀ t ∈ Set.uIcc (0:ℝ) 1, (γ t - a) ∈ slitPlane) :
    (∫ t in (0:ℝ)..1, (γ t - a)⁻¹ * d) =
      Complex.log (γ 1 - a) - Complex.log (γ 0 - a) := by
  have hF : ∀ t ∈ Set.uIcc (0:ℝ) 1,
      HasDerivAt (fun s => Complex.log (γ s - a)) ((γ t - a)⁻¹ * d) t := by
    intro t ht
    have hsub : HasDerivAt (fun s => γ s - a) d t := (hγ t).sub_const a
    have := hsub.clog_real (hslit t ht)
    simpa [div_eq_inv_mul] using this
  have hcont : ContinuousOn (fun t => (γ t - a)⁻¹ * d) (Set.uIcc (0:ℝ) 1) := by
    intro t ht
    have hne : γ t - a ≠ 0 := by
      have := hslit t ht
      rw [mem_slitPlane_iff] at this
      rcases this with h | h
      · intro hz; rw [hz] at h; simp at h
      · intro hz; rw [hz] at h; simp at h
    have hγc : ContinuousAt (fun s => γ s - a) t :=
      ((hγ t).continuousAt.sub continuousAt_const)
    have : ContinuousAt (fun s => (γ s - a)⁻¹ * d) t :=
      (hγc.inv₀ hne).mul continuousAt_const
    exact this.continuousWithinAt
  have hint : IntervalIntegrable (fun t => (γ t - a)⁻¹ * d) MeasureTheory.volume 0 1 :=
    hcont.intervalIntegrable
  exact integral_eq_sub_of_hasDerivAt hF hint

/-- Variant using the `log(a - γ)` branch (for the left edge). -/
theorem edge_integral_log_neg
    (γ : ℝ → ℂ) (d a : ℂ)
    (hγ : ∀ t : ℝ, HasDerivAt γ d t)
    (hslit : ∀ t ∈ Set.uIcc (0:ℝ) 1, (a - γ t) ∈ slitPlane) :
    (∫ t in (0:ℝ)..1, (γ t - a)⁻¹ * d) =
      Complex.log (a - γ 1) - Complex.log (a - γ 0) := by
  have hF : ∀ t ∈ Set.uIcc (0:ℝ) 1,
      HasDerivAt (fun s => Complex.log (a - γ s)) ((γ t - a)⁻¹ * d) t := by
    intro t ht
    have hsub : HasDerivAt (fun s => a - γ s) (-d) t := ((hγ t).const_sub a)
    have hlog := hsub.clog_real (hslit t ht)
    have heq : (-d) / (a - γ t) = (γ t - a)⁻¹ * d := by
      have hrw : a - γ t = -(γ t - a) := by ring
      rw [hrw, div_neg, neg_div, neg_neg, div_eq_inv_mul]
    rw [heq] at hlog
    exact hlog
  have hcont : ContinuousOn (fun t => (γ t - a)⁻¹ * d) (Set.uIcc (0:ℝ) 1) := by
    intro t ht
    have hne : a - γ t ≠ 0 := by
      have := hslit t ht
      rw [mem_slitPlane_iff] at this
      rcases this with h | h
      · intro hz; rw [hz] at h; simp at h
      · intro hz; rw [hz] at h; simp at h
    have hne' : γ t - a ≠ 0 := by
      intro hz; apply hne; rw [← neg_sub, hz, neg_zero]
    have hγc : ContinuousAt (fun s => γ s - a) t :=
      ((hγ t).continuousAt.sub continuousAt_const)
    have : ContinuousAt (fun s => (γ s - a)⁻¹ * d) t :=
      (hγc.inv₀ hne').mul continuousAt_const
    exact this.continuousWithinAt
  have hint : IntervalIntegrable (fun t => (γ t - a)⁻¹ * d) MeasureTheory.volume 0 1 :=
    hcont.intervalIntegrable
  exact integral_eq_sub_of_hasDerivAt hF hint

/-- For `w` in the second quadrant (`im > 0`), `log w - log (-w) = π·I`. -/
theorem log_sub_log_neg_im_pos {w : ℂ} (him : 0 < w.im) :
    Complex.log w - Complex.log (-w) = (Real.pi : ℂ) * Complex.I := by
  have hnorm : ‖-w‖ = ‖w‖ := by rw [norm_neg]
  rw [Complex.log, Complex.log, hnorm]
  rw [Complex.arg_neg_eq_arg_sub_pi_of_im_pos him]
  push_cast
  ring

/-- For `w` in the third quadrant (`im < 0`), `log w - log (-w) = -π·I`. -/
theorem log_sub_log_neg_im_neg {w : ℂ} (him : w.im < 0) :
    Complex.log w - Complex.log (-w) = -((Real.pi : ℂ) * Complex.I) := by
  have hnorm : ‖-w‖ = ‖w‖ := by rw [norm_neg]
  rw [Complex.log, Complex.log, hnorm]
  rw [Complex.arg_neg_eq_arg_add_pi_of_im_neg him]
  push_cast
  ring

/-- Bottom edge integral. -/
theorem bottom_edge_eq (R : ZetaRectangle) (a : ℂ) (ha : R.ContainsOpen a) :
    (∫ t in (0:ℝ)..1, (R.bottomEdge t - a)⁻¹ * deriv R.bottomEdge t) =
      Complex.log ((⟨R.right, R.bottom⟩ : ℂ) - a)
        - Complex.log ((⟨R.left, R.bottom⟩ : ℂ) - a) := by
  rw [show (fun t => (R.bottomEdge t - a)⁻¹ * deriv R.bottomEdge t)
        = fun t => (R.bottomEdge t - a)⁻¹ * ((R.right - R.left : ℝ) : ℂ) by
        funext t; rw [R.deriv_bottomEdge t]]
  have hslit : ∀ t ∈ Set.uIcc (0:ℝ) 1, (R.bottomEdge t - a) ∈ slitPlane := by
    intro t _
    rw [mem_slitPlane_iff]
    right
    have him : (R.bottomEdge t - a).im = R.bottom - a.im := by
      simp [ZetaRectangle.bottomEdge]
    rw [him]
    have := ha.2.2.1
    intro h; linarith [sub_eq_zero.mp h]
  have key := edge_integral_log R.bottomEdge ((R.right - R.left : ℝ) : ℂ) a
    (fun t => R.hasDerivAt_bottomEdge t) hslit
  rw [key, R.bottomEdge_one, R.bottomEdge_zero]

/-- Right edge integral. -/
theorem right_edge_eq (R : ZetaRectangle) (a : ℂ) (ha : R.ContainsOpen a) :
    (∫ t in (0:ℝ)..1, (R.rightEdge t - a)⁻¹ * deriv R.rightEdge t) =
      Complex.log ((⟨R.right, R.top⟩ : ℂ) - a)
        - Complex.log ((⟨R.right, R.bottom⟩ : ℂ) - a) := by
  rw [show (fun t => (R.rightEdge t - a)⁻¹ * deriv R.rightEdge t)
        = fun t => (R.rightEdge t - a)⁻¹ * (((R.top - R.bottom : ℝ) : ℂ) * Complex.I) by
        funext t; rw [R.deriv_rightEdge t]]
  have hslit : ∀ t ∈ Set.uIcc (0:ℝ) 1, (R.rightEdge t - a) ∈ slitPlane := by
    intro t _
    rw [mem_slitPlane_iff]
    left
    have hre : (R.rightEdge t - a).re = R.right - a.re := by
      simp [ZetaRectangle.rightEdge]
    rw [hre]
    have := ha.2.1
    linarith
  have key := edge_integral_log R.rightEdge (((R.top - R.bottom : ℝ) : ℂ) * Complex.I) a
    (fun t => R.hasDerivAt_rightEdge t) hslit
  rw [key, R.rightEdge_one, R.rightEdge_zero]

/-- Top edge integral. -/
theorem top_edge_eq (R : ZetaRectangle) (a : ℂ) (ha : R.ContainsOpen a) :
    (∫ t in (0:ℝ)..1, (R.topEdge t - a)⁻¹ * deriv R.topEdge t) =
      Complex.log ((⟨R.left, R.top⟩ : ℂ) - a)
        - Complex.log ((⟨R.right, R.top⟩ : ℂ) - a) := by
  rw [show (fun t => (R.topEdge t - a)⁻¹ * deriv R.topEdge t)
        = fun t => (R.topEdge t - a)⁻¹ * (-((R.right - R.left : ℝ) : ℂ)) by
        funext t; rw [R.deriv_topEdge t]]
  have hslit : ∀ t ∈ Set.uIcc (0:ℝ) 1, (R.topEdge t - a) ∈ slitPlane := by
    intro t _
    rw [mem_slitPlane_iff]
    right
    have him : (R.topEdge t - a).im = R.top - a.im := by
      simp [ZetaRectangle.topEdge]
    rw [him]
    have := ha.2.2.2
    intro h; linarith [sub_eq_zero.mp h]
  have key := edge_integral_log R.topEdge (-((R.right - R.left : ℝ) : ℂ)) a
    (fun t => R.hasDerivAt_topEdge t) hslit
  rw [key, R.topEdge_one, R.topEdge_zero]

/-- Left edge integral (crosses the principal branch cut; use `log (a - edge)`). -/
theorem left_edge_eq (R : ZetaRectangle) (a : ℂ) (ha : R.ContainsOpen a) :
    (∫ t in (0:ℝ)..1, (R.leftEdge t - a)⁻¹ * deriv R.leftEdge t) =
      Complex.log (a - (⟨R.left, R.bottom⟩ : ℂ))
        - Complex.log (a - (⟨R.left, R.top⟩ : ℂ)) := by
  rw [show (fun t => (R.leftEdge t - a)⁻¹ * deriv R.leftEdge t)
        = fun t => (R.leftEdge t - a)⁻¹ * (-(((R.top - R.bottom : ℝ) : ℂ) * Complex.I)) by
        funext t; rw [R.deriv_leftEdge t]]
  have hslit : ∀ t ∈ Set.uIcc (0:ℝ) 1, (a - R.leftEdge t) ∈ slitPlane := by
    intro t _
    rw [mem_slitPlane_iff]
    left
    have hre : (a - R.leftEdge t).re = a.re - R.left := by
      simp [ZetaRectangle.leftEdge]
    rw [hre]
    have := ha.1
    linarith
  have key := edge_integral_log_neg R.leftEdge (-(((R.top - R.bottom : ℝ) : ℂ) * Complex.I)) a
    (fun t => R.hasDerivAt_leftEdge t) hslit
  rw [key, R.leftEdge_one, R.leftEdge_zero]

/-- **Atomic residue computation.**  For `a` strictly inside the rectangle, the
unit principal-kernel rectangle contour integral equals `2πi`. -/
theorem unitPrincipalKernelRectangleIntegral_eq_twoPiI
    (R : ZetaRectangle) (a : ℂ) (ha : R.ContainsOpen a) :
    R.principalKernelRectangleIntegral 1 a = ZetaRectangle.twoPiI := by
  have hkernel : ∀ (edge : ℝ → ℂ),
      (∫ t in (0:ℝ)..1, ZetaRectangle.principalKernel 1 a (edge t) * deriv edge t)
        = ∫ t in (0:ℝ)..1, (edge t - a)⁻¹ * deriv edge t := by
    intro edge
    refine intervalIntegral.integral_congr (fun t _ => ?_)
    unfold ZetaRectangle.principalKernel
    rw [Int.cast_one, one_div]
  unfold ZetaRectangle.principalKernelRectangleIntegral
  rw [hkernel R.bottomEdge, hkernel R.rightEdge, hkernel R.topEdge, hkernel R.leftEdge]
  rw [bottom_edge_eq R a ha, right_edge_eq R a ha, top_edge_eq R a ha,
      left_edge_eq R a ha]
  set BL : ℂ := (⟨R.left, R.bottom⟩ : ℂ) with hBL
  set TL : ℂ := (⟨R.left, R.top⟩ : ℂ) with hTL
  have hBLneg : a - BL = -(BL - a) := by ring
  have hTLneg : a - TL = -(TL - a) := by ring
  rw [hBLneg, hTLneg]
  have hTL_jump : Complex.log (TL - a) - Complex.log (-(TL - a))
      = (Real.pi : ℂ) * Complex.I := by
    apply log_sub_log_neg_im_pos
    have : (TL - a).im = R.top - a.im := by rw [hTL]; simp
    rw [this]; linarith [ha.2.2.2]
  have hBL_jump : Complex.log (BL - a) - Complex.log (-(BL - a))
      = -((Real.pi : ℂ) * Complex.I) := by
    apply log_sub_log_neg_im_neg
    have : (BL - a).im = R.bottom - a.im := by rw [hBL]; simp
    rw [this]; linarith [ha.2.2.1]
  unfold ZetaRectangle.twoPiI
  linear_combination hTL_jump - hBL_jump

/-- The unit Cauchy-index structure, inhabited by the atomic computation. -/
noncomputable def unitPrincipalKernelIntegralTheorem
    (R : ZetaRectangle) (a : ℂ) (ha : R.ContainsOpen a) :
    R.UnitPrincipalKernelIntegralTheorem a where
  inside := ha
  boundary_avoids := by
    intro z hz heq; subst heq; exact hz.2 ha
  integral_eq := by
    unfold ZetaRectangle.unitPrincipalKernelRectangleIntegral
    exact unitPrincipalKernelRectangleIntegral_eq_twoPiI R a ha

/-- The general-`k` residue: `∮ k/(z-a) = 2πi·k` for `a` strictly inside `R`. -/
theorem principalKernelRectangleIntegral_eq_twoPiI_mul
    (R : ZetaRectangle) (k : ℤ) (a : ℂ) (ha : R.ContainsOpen a) :
    R.principalKernelRectangleIntegral k a = ZetaRectangle.twoPiI * (k : ℂ) :=
  ((unitPrincipalKernelIntegralTheorem R a ha).toUnnormalized k).integral_eq

end ResidueBrick

/-! ## Part 2 — Goursat: the analytic remainder vanishes

We reuse `rh.lean`'s unconditional `globalRectangleCauchyGoursatBridge`. -/

/-- **Cauchy–Goursat (four-edge form).**  An `f` analytic at every point of the
closed rectangle has vanishing four-edge boundary integral.  This is exactly
`ScratchGoursat.lean`'s `rectangleIntegral_eq_zero_of_analyticOn_closed`, here
re-derived from the same engine `globalRectangleCauchyGoursatBridge`. -/
theorem rectangleIntegral_eq_zero_of_analyticOn_closed
    (R : ZetaRectangle) (f : ℂ → ℂ)
    (hf : ∀ z ∈ {z : ℂ | R.ContainsClosed z}, AnalyticAt ℂ f z) :
    R.rectangleIntegral f = 0 :=
  globalRectangleCauchyGoursatBridge.cauchyGoursat R f hf

/-! ## Part 3 — The global order-`m` factorization hypothesis

The interior order-`m` zero with no other zeros on the rectangle produces a
*global* analytic non-vanishing cofactor `g` with `f = (· - a)^m · g`.  Gluing the
local Mathlib factorization (`AnalyticAt.analyticOrderAt_eq_natCast`) across the
rectangle into a single global `g`, analytic *and non-vanishing on the closed
rectangle*, is a removable-singularity argument we do not re-derive here.  It is
captured by this hypothesis, which is precisely the data AP1 consumes. -/

/-- **Global order-`m` factorization on the closed rectangle.**

`f z = (z - a)^m · g z` for all `z`, with `g` analytic at every point of the
closed rectangle and non-vanishing there, and `a` strictly interior.  This is the
output of "isolated order-`m` zero at `a`, no other zeros on the rectangle". -/
structure GlobalOrderFactorization
    (R : ZetaRectangle) (f g : ℂ → ℂ) (a : ℂ) (m : ℕ) : Prop where
  /-- `a` lies strictly inside the rectangle. -/
  interior : R.ContainsOpen a
  /-- The global factorization `f = (· - a)^m · g`. -/
  factor : f = fun z => (z - a) ^ m * g z
  /-- `g` is analytic at every point of the closed rectangle. -/
  g_analytic : ∀ z ∈ {z : ℂ | R.ContainsClosed z}, AnalyticAt ℂ g z
  /-- `g` does not vanish on the closed rectangle. -/
  g_ne_zero : ∀ z ∈ {z : ℂ | R.ContainsClosed z}, g z ≠ 0

/-! ## Part 4 — `logDeriv g` is analytic on the closed rectangle -/

/-- `logDeriv g = deriv g / g` is analytic wherever `g` is analytic and nonzero. -/
theorem analyticAt_logDeriv_of_analytic_ne_zero
    {g : ℂ → ℂ} {z : ℂ} (hg : AnalyticAt ℂ g z) (hgz : g z ≠ 0) :
    AnalyticAt ℂ (logDeriv g) z := by
  have hd : AnalyticAt ℂ (deriv g) z := hg.deriv
  have : AnalyticAt ℂ (deriv g / g) z := hd.div hg hgz
  -- `logDeriv g = deriv g / g` definitionally.
  exact this

/-! ## Part 5 — The integrand split: `logDeriv f = principalKernel m a + logDeriv g`

This holds at every point `z` with `z ≠ a` and `g z ≠ 0` (boundary points satisfy
both). -/

/-- At a point `z ≠ a` with `g` analytic and non-vanishing, the logarithmic
derivative of the factored `f` splits into the principal kernel plus `logDeriv g`. -/
theorem logDeriv_factor_split
    {g : ℂ → ℂ} {a z : ℂ} {m : ℕ}
    (hza : z ≠ a) (hg : AnalyticAt ℂ g z) (hgz : g z ≠ 0) :
    logDeriv (fun w => (w - a) ^ m * g w) z
      = ZetaRectangle.principalKernel (m : ℤ) a z + logDeriv g z := by
  have hsub : z - a ≠ 0 := sub_ne_zero.mpr hza
  have hpow_ne : (z - a) ^ m ≠ 0 := pow_ne_zero m hsub
  -- differentiability of the two factors at `z`
  have hd_pow : DifferentiableAt ℂ (fun w => (w - a) ^ m) z := by fun_prop
  have hd_g : DifferentiableAt ℂ g z := hg.differentiableAt
  rw [logDeriv_mul z hpow_ne hgz hd_pow hd_g]
  -- `logDeriv (fun w => (w - a)^m) z = m / (z - a)`
  have hbase : DifferentiableAt ℂ (fun w => w - a) z := by fun_prop
  have hpow : logDeriv (fun w => (w - a) ^ m) z = (m : ℂ) * logDeriv (fun w => w - a) z :=
    logDeriv_fun_pow (f := fun w => w - a) (x := z) hbase m
  have hbaselog : logDeriv (fun w => w - a) z = 1 / (z - a) := by
    rw [logDeriv_apply]
    have hderiv : deriv (fun w => w - a) z = 1 := (((hasDerivAt_id z).sub_const a).deriv)
    rw [hderiv]
  rw [hpow, hbaselog]
  -- assemble against `principalKernel`
  unfold ZetaRectangle.principalKernel
  push_cast
  rw [mul_one_div]

/-! ## Part 6 — Per-edge integral split

For one rectangle edge `γ` (affine, with constant derivative `d`), whose image on
`[0,1]` lies in the closed rectangle and avoids `a`, the edge integral of
`logDeriv f · γ'` splits into the principal-kernel edge integral plus the
`logDeriv g` edge integral.  Hypotheses are stated only on `[0,1] = uIcc 0 1`. -/

/-- Per-edge split of the log-derivative integral.  `γ` is one rectangle edge
(`HasDerivAt γ d t` everywhere, continuous), with image on `[0,1]` in the closed
rectangle and avoiding `a`, and `g` analytic + non-vanishing on the closed
rectangle. -/
theorem edge_logDeriv_split
    {R : ZetaRectangle} {g : ℂ → ℂ} {a : ℂ} {m : ℕ}
    {γ : ℝ → ℂ} {d : ℂ}
    (hγ : ∀ t, HasDerivAt γ d t)
    (hclosed : ∀ t ∈ Set.uIcc (0:ℝ) 1, R.ContainsClosed (γ t))
    (hne : ∀ t ∈ Set.uIcc (0:ℝ) 1, γ t ≠ a)
    (hg : ∀ z ∈ {z : ℂ | R.ContainsClosed z}, AnalyticAt ℂ g z)
    (hgz : ∀ z ∈ {z : ℂ | R.ContainsClosed z}, g z ≠ 0) :
    (∫ t in (0:ℝ)..1, logDeriv (fun w => (w - a) ^ m * g w) (γ t) * deriv γ t)
      = (∫ t in (0:ℝ)..1, ZetaRectangle.principalKernel (m : ℤ) a (γ t) * deriv γ t)
        + (∫ t in (0:ℝ)..1, logDeriv g (γ t) * deriv γ t) := by
  -- continuity of the two pieces on [0,1]
  have hcontK : ContinuousOn
      (fun t => ZetaRectangle.principalKernel (m : ℤ) a (γ t) * deriv γ t)
      (Set.uIcc (0:ℝ) 1) := by
    intro t ht
    have hsub : γ t - a ≠ 0 := sub_ne_zero.mpr (hne t ht)
    have h1 : ContinuousAt (fun s => ZetaRectangle.principalKernel (m : ℤ) a (γ s)) t := by
      unfold ZetaRectangle.principalKernel
      have hγc : ContinuousAt (fun s => γ s - a) t :=
        ((hγ t).continuousAt.sub continuousAt_const)
      exact (continuousAt_const).div hγc hsub
    have h2 : ContinuousAt (fun s => deriv γ s) t := by
      simp only [(hγ _).deriv]; exact continuousAt_const
    exact (h1.mul h2).continuousWithinAt
  have hcontG : ContinuousOn (fun t => logDeriv g (γ t) * deriv γ t)
      (Set.uIcc (0:ℝ) 1) := by
    intro t ht
    have hmem : γ t ∈ {z : ℂ | R.ContainsClosed z} := hclosed t ht
    have hlog : AnalyticAt ℂ (logDeriv g) (γ t) :=
      analyticAt_logDeriv_of_analytic_ne_zero (hg _ hmem) (hgz _ hmem)
    have h1 : ContinuousAt (fun s => logDeriv g (γ s)) t :=
      hlog.continuousAt.comp (hγ t).continuousAt
    have h2 : ContinuousAt (fun s => deriv γ s) t := by
      simp only [(hγ _).deriv]; exact continuousAt_const
    exact (h1.mul h2).continuousWithinAt
  have hintK : IntervalIntegrable
      (fun t => ZetaRectangle.principalKernel (m : ℤ) a (γ t) * deriv γ t)
      MeasureTheory.volume 0 1 := hcontK.intervalIntegrable
  have hintG : IntervalIntegrable (fun t => logDeriv g (γ t) * deriv γ t)
      MeasureTheory.volume 0 1 := hcontG.intervalIntegrable
  rw [← intervalIntegral.integral_add hintK hintG]
  refine intervalIntegral.integral_congr (fun t ht => ?_)
  have hmem : γ t ∈ {z : ℂ | R.ContainsClosed z} := hclosed t ht
  have hsplit := logDeriv_factor_split (g := g) (a := a) (z := γ t) (m := m)
    (hne t ht) (hg _ hmem) (hgz _ hmem)
  rw [hsplit]; ring

/-! ## Part 7 — AP1: the single-zero residue identity -/

/-- Edges of `R` avoid an interior point `a`: every edge point is on the boundary,
which is disjoint from the open rectangle containing `a`. -/
private theorem edge_ne_of_interior
    {R : ZetaRectangle} {a : ℂ} (ha : R.ContainsOpen a)
    {z : ℂ} (hb : R.ContainsBoundary z) : z ≠ a := by
  intro heq; subst heq; exact hb.2 ha

/-- **AP1 (unnormalized).**  For `f` factoring globally as `f z = (z - a)^m · g z`
with `g` analytic and non-vanishing on the closed rectangle and `a` strictly
interior, the rectangle contour integral of the logarithmic derivative `f'/f` is
`2πi · m`.

* The pole part `∮ m/(z-a) = 2πi·m` is the atomic residue computation
  (`ResidueBrick.principalKernelRectangleIntegral_eq_twoPiI_mul`).
* The analytic remainder `∮ logDeriv g = 0` is Cauchy–Goursat
  (`rectangleIntegral_eq_zero_of_analyticOn_closed`). -/
theorem rectangleIntegral_logDeriv_eq_twoPiI_mul_order
    {R : ZetaRectangle} {f g : ℂ → ℂ} {a : ℂ} {m : ℕ}
    (H : GlobalOrderFactorization R f g a m) :
    R.rectangleIntegral (logDeriv f) = ZetaRectangle.twoPiI * (m : ℂ) := by
  -- Per-edge hypotheses.
  have hclosedB : ∀ t ∈ Set.uIcc (0:ℝ) 1, R.ContainsClosed (R.bottomEdge t) := by
    intro t ht; rw [Set.uIcc_of_le (by norm_num)] at ht
    exact R.bottomEdge_mem_closed ht.1 ht.2
  have hclosedR : ∀ t ∈ Set.uIcc (0:ℝ) 1, R.ContainsClosed (R.rightEdge t) := by
    intro t ht; rw [Set.uIcc_of_le (by norm_num)] at ht
    exact R.rightEdge_mem_closed ht.1 ht.2
  have hclosedT : ∀ t ∈ Set.uIcc (0:ℝ) 1, R.ContainsClosed (R.topEdge t) := by
    intro t ht; rw [Set.uIcc_of_le (by norm_num)] at ht
    exact R.topEdge_mem_closed ht.1 ht.2
  have hclosedL : ∀ t ∈ Set.uIcc (0:ℝ) 1, R.ContainsClosed (R.leftEdge t) := by
    intro t ht; rw [Set.uIcc_of_le (by norm_num)] at ht
    exact R.leftEdge_mem_closed ht.1 ht.2
  have hneB : ∀ t ∈ Set.uIcc (0:ℝ) 1, R.bottomEdge t ≠ a := by
    intro t ht; rw [Set.uIcc_of_le (by norm_num)] at ht
    exact edge_ne_of_interior H.interior (R.bottomEdge_mem_boundary ht.1 ht.2)
  have hneR : ∀ t ∈ Set.uIcc (0:ℝ) 1, R.rightEdge t ≠ a := by
    intro t ht; rw [Set.uIcc_of_le (by norm_num)] at ht
    exact edge_ne_of_interior H.interior (R.rightEdge_mem_boundary ht.1 ht.2)
  have hneT : ∀ t ∈ Set.uIcc (0:ℝ) 1, R.topEdge t ≠ a := by
    intro t ht; rw [Set.uIcc_of_le (by norm_num)] at ht
    exact edge_ne_of_interior H.interior (R.topEdge_mem_boundary ht.1 ht.2)
  have hneL : ∀ t ∈ Set.uIcc (0:ℝ) 1, R.leftEdge t ≠ a := by
    intro t ht; rw [Set.uIcc_of_le (by norm_num)] at ht
    exact edge_ne_of_interior H.interior (R.leftEdge_mem_boundary ht.1 ht.2)
  -- Rewrite `f` by its factorization, then split each of the four edges.
  rw [H.factor]
  unfold ZetaRectangle.rectangleIntegral
  rw [edge_logDeriv_split (m := m) R.hasDerivAt_bottomEdge hclosedB hneB H.g_analytic H.g_ne_zero,
      edge_logDeriv_split (m := m) R.hasDerivAt_rightEdge hclosedR hneR H.g_analytic H.g_ne_zero,
      edge_logDeriv_split (m := m) R.hasDerivAt_topEdge hclosedT hneT H.g_analytic H.g_ne_zero,
      edge_logDeriv_split (m := m) R.hasDerivAt_leftEdge hclosedL hneL H.g_analytic H.g_ne_zero]
  -- Group: (pole edges) + (remainder edges).
  have hgroup :
      ((∫ t in (0:ℝ)..1, ZetaRectangle.principalKernel (m : ℤ) a (R.bottomEdge t)
          * deriv R.bottomEdge t)
        + (∫ t in (0:ℝ)..1, logDeriv g (R.bottomEdge t) * deriv R.bottomEdge t))
      + ((∫ t in (0:ℝ)..1, ZetaRectangle.principalKernel (m : ℤ) a (R.rightEdge t)
          * deriv R.rightEdge t)
        + (∫ t in (0:ℝ)..1, logDeriv g (R.rightEdge t) * deriv R.rightEdge t))
      + ((∫ t in (0:ℝ)..1, ZetaRectangle.principalKernel (m : ℤ) a (R.topEdge t)
          * deriv R.topEdge t)
        + (∫ t in (0:ℝ)..1, logDeriv g (R.topEdge t) * deriv R.topEdge t))
      + ((∫ t in (0:ℝ)..1, ZetaRectangle.principalKernel (m : ℤ) a (R.leftEdge t)
          * deriv R.leftEdge t)
        + (∫ t in (0:ℝ)..1, logDeriv g (R.leftEdge t) * deriv R.leftEdge t))
      = R.principalKernelRectangleIntegral (m : ℤ) a + R.rectangleIntegral (logDeriv g) := by
    unfold ZetaRectangle.principalKernelRectangleIntegral ZetaRectangle.rectangleIntegral
    ring
  rw [hgroup]
  -- Pole part: atomic residue.  Remainder: Goursat (logDeriv g analytic).
  rw [ResidueBrick.principalKernelRectangleIntegral_eq_twoPiI_mul R (m : ℤ) a H.interior]
  have hrem : R.rectangleIntegral (logDeriv g) = 0 := by
    refine rectangleIntegral_eq_zero_of_analyticOn_closed R (logDeriv g) ?_
    intro z hz
    exact analyticAt_logDeriv_of_analytic_ne_zero (H.g_analytic z hz) (H.g_ne_zero z hz)
  rw [hrem, add_zero]
  push_cast
  ring

/-- **AP1 (normalized).**  `(2πi)⁻¹ ∮_{∂R} f'/f = m`. -/
theorem normalized_rectangleIntegral_logDeriv_eq_order
    {R : ZetaRectangle} {f g : ℂ → ℂ} {a : ℂ} {m : ℕ}
    (H : GlobalOrderFactorization R f g a m) :
    (ZetaRectangle.twoPiI)⁻¹ * R.rectangleIntegral (logDeriv f) = (m : ℂ) := by
  rw [rectangleIntegral_logDeriv_eq_twoPiI_mul_order H]
  rw [← mul_assoc, inv_mul_cancel₀ ZetaRectangle.twoPiI_ne_zero, one_mul]

end ScratchAPSingleZero
end BacklundTuring
end OverflowResidueRH

/-! ## Axiom audit

Must show only the standard classical/quotient axioms (`propext`,
`Classical.choice`, `Quot.sound`) and NO `sorryAx`. -/

#print axioms
  OverflowResidueRH.BacklundTuring.ScratchAPSingleZero.ResidueBrick.principalKernelRectangleIntegral_eq_twoPiI_mul
#print axioms
  OverflowResidueRH.BacklundTuring.ScratchAPSingleZero.rectangleIntegral_eq_zero_of_analyticOn_closed
#print axioms
  OverflowResidueRH.BacklundTuring.ScratchAPSingleZero.logDeriv_factor_split
#print axioms
  OverflowResidueRH.BacklundTuring.ScratchAPSingleZero.edge_logDeriv_split
#print axioms
  OverflowResidueRH.BacklundTuring.ScratchAPSingleZero.rectangleIntegral_logDeriv_eq_twoPiI_mul_order
#print axioms
  OverflowResidueRH.BacklundTuring.ScratchAPSingleZero.normalized_rectangleIntegral_logDeriv_eq_order
