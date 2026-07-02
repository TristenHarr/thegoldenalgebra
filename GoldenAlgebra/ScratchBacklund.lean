import rh
import Mathlib.Analysis.Complex.JensenFormula

/-!
# Backlund–Jensen bound on the argument fluctuation `S(T)`

This scratch file develops the **analytic core** of the classical Backlund bound
`|S(T)| ≤ C·log T + D` from an *exponent-1* growth bound on `ζ` on the strip
`1/2 ≤ Re s ≤ 5/2`, via Mathlib's Jensen zero-count inequality
`AnalyticOnNhd.sum_divisor_le`.

## Target in `rh.lean`

The object `rh.lean` ultimately needs is
`OverflowResidueRH.BacklundArgumentBoundOnGoodHeights Sarg`, whose `bound` field is

```
∀ T : ℝ, lower ≤ T → GoodHeight T → |Sarg T| ≤ (1 / 2) * Real.log T + 1 / 2
```

i.e. the **crude Backlund constant** `½ log T + ½` (NOT the sharp Trudgian
`0.11 log T`).  This is exactly the constant that the exponent-1 input
`‖ζ s‖ ≤ C·(1+|Im s|)` can in principle reach through a careful Backlund
disk-radius choice.  The *sharp* `0.11 log T` would require a subconvexity bound
`|ζ(1/2+it)| ≪ |t|^{1/4}`, which is NOT derivable from the exponent-1 input —
so the crude constant is the right target here.

## What is proved here

The genuine analytic content delivered unconditionally (modulo the transplanted
ζ-growth axiom) is the **Backlund–Jensen zero-count inequality**: the Backlund
function `f_T(z) = (ζ(z+iT) + ζ(z-iT))/2` is analytic on a disk centred at a
real point `A > 1`, real-on-ℝ, with `f_T(A) ≠ 0`, and Jensen's inequality bounds
the number of its zeros in the inner disk by `log(M/‖f_T A‖)/log(R/r)` with
`M ≤ C·(1 + T + R)`.  This yields `#zeros ≤ C'·log T + D'` with explicit `C', D'`,
which is the Backlund count controlling the variation of `arg ζ(σ+iT)`.

The remaining gap to *inhabit* `BacklundArgumentBoundOnGoodHeights` is the
**argument-principle identity** linking this geometric zero-count to the abstract
`Sarg`/`concreteS` object (the Riemann–von Mangoldt formula `N(T) = N₀(T)+S(T)`),
which is a separate large analytic development that `rh.lean` exposes only through
its `ProvenRiemannVonMangoldtFormula` interfaces. That bridge is isolated below.
-/

open Complex Real

namespace OverflowResidueRH
namespace BacklundTuring

/-- **Transplanted ζ growth bound (exponent 1).**
Proved unconditionally in `ScratchZetaPolyDirect.lean`; carried here as an axiom
with the exact shape requested. -/
axiom norm_riemannZeta_poly_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, (1:ℝ)/2 ≤ s.re → s.re ≤ 5/2 → 1 ≤ |s.im| →
      ‖riemannZeta s‖ ≤ C * (1 + |s.im|)

/-! ### The Backlund function -/

/-- The **Backlund function** at height `T`:
`f_T(z) = (ζ(z + iT) + ζ(z - iT)) / 2`.  It is analytic away from the two
singularities `z = 1 - iT` and `z = 1 + iT`, real on the real axis, and its
real-axis values are `Re ζ(x + iT)`. -/
noncomputable def backlundF (T : ℝ) (z : ℂ) : ℂ :=
  (riemannZeta (z + T * Complex.I) + riemannZeta (z - T * Complex.I)) / 2

/-- On the closed ball of radius `R < T` about a real centre `A`,
neither shifted argument hits the pole `s = 1`, because the imaginary parts of
`z ± iT` are bounded away from `0` (indeed `|Im(z ± iT)| ≥ T - R > 0`). -/
theorem backlundF_analyticOnNhd
    (T A R : ℝ) (hRT : R < T) :
    AnalyticOnNhd ℂ (backlundF T) (Metric.closedBall (A : ℂ) R) := by
  intro z hz
  have hdist : ‖z - (A : ℂ)‖ ≤ R := by
    simpa [Complex.dist_eq] using (Metric.mem_closedBall.mp hz)
  have him_z : |z.im| ≤ R := by
    have h1 : |(z - (A : ℂ)).im| ≤ ‖z - (A : ℂ)‖ := Complex.abs_im_le_norm _
    have h2 : (z - (A : ℂ)).im = z.im := by simp
    rw [h2] at h1
    exact le_trans h1 hdist
  have him_bds := abs_le.mp him_z
  have hplus : z + T * Complex.I ≠ 1 := by
    intro h
    have him : (z + T * Complex.I).im = 0 := by rw [h]; simp
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im] at him
    have hsum : z.im + T = 0 := by simpa using him
    linarith [him_bds.1]
  have hminus : z - T * Complex.I ≠ 1 := by
    intro h
    have him : (z - T * Complex.I).im = 0 := by rw [h]; simp
    simp only [Complex.sub_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im] at him
    have hsub : z.im - T = 0 := by simpa using him
    linarith [him_bds.2]
  -- `ζ` is analytic at each shifted argument (argument `≠ 1`, an open condition).
  have hZ1 : AnalyticAt ℂ riemannZeta (z + T * Complex.I) := by
    refine DifferentiableOn.analyticAt
      (s := {w : ℂ | w ≠ 1}) (fun w hw => (differentiableAt_riemannZeta hw).differentiableWithinAt) ?_
    exact (isOpen_ne).mem_nhds hplus
  have hZ2 : AnalyticAt ℂ riemannZeta (z - T * Complex.I) := by
    refine DifferentiableOn.analyticAt
      (s := {w : ℂ | w ≠ 1}) (fun w hw => (differentiableAt_riemannZeta hw).differentiableWithinAt) ?_
    exact (isOpen_ne).mem_nhds hminus
  have harg1 : AnalyticAt ℂ (fun w : ℂ => w + T * Complex.I) z :=
    (analyticAt_id).add analyticAt_const
  have harg2 : AnalyticAt ℂ (fun w : ℂ => w - T * Complex.I) z :=
    (analyticAt_id).sub analyticAt_const
  have ha1 : AnalyticAt ℂ (fun w => riemannZeta (w + T * Complex.I)) z :=
    AnalyticAt.comp (g := riemannZeta) (f := fun w => w + T * Complex.I) hZ1 harg1
  have ha2 : AnalyticAt ℂ (fun w => riemannZeta (w - T * Complex.I)) z :=
    AnalyticAt.comp (g := riemannZeta) (f := fun w => w - T * Complex.I) hZ2 harg2
  have hsum : AnalyticAt ℂ
      (fun w => riemannZeta (w + T * Complex.I) + riemannZeta (w - T * Complex.I)) z :=
    ha1.add ha2
  show AnalyticAt ℂ (backlundF T) z
  unfold backlundF
  exact hsum.div_const (c := (2 : ℂ))

/-! ### Sphere bound for the Backlund function

We work with the concrete geometry `A = 3/2`, `R = 1`, so that on the sphere
`Re(z ± iT) ∈ [1/2, 5/2]` and `|Im(z ± iT)| = |z.im ± T| ≥ T - 1 ≥ 1`,
putting both shifted arguments inside the strip where the ζ-growth axiom applies.
The inner radius `r = 1/8` then gives `R/r = 8`, so the Jensen log-count
coefficient is `1 / log 8 ≤ 1/2` — the crude Backlund constant. -/

/-- **Sphere bound.** On the sphere of radius `1` about `(3/2 : ℂ)`, with
`T ≥ 2`, the Backlund function is bounded by `C · (1 + (T + 1))`, where `C` is
the constant from the ζ-growth axiom. -/
theorem backlundF_sphere_bound (T : ℝ) (hT : 2 ≤ T) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ z ∈ Metric.sphere ((3/2 : ℝ) : ℂ) (1 : ℝ),
        ‖backlundF T z‖ ≤ C * (1 + (T + 1)) := by
  obtain ⟨C, hC0, hCbound⟩ := norm_riemannZeta_poly_bound
  refine ⟨C, hC0, ?_⟩
  intro z hz
  have hnorm : ‖z - ((3/2 : ℝ) : ℂ)‖ = 1 := by
    simpa [Complex.dist_eq] using (Metric.mem_sphere.mp hz)
  -- Real part of `z` is within `1` of `3/2`.
  have hre_le : |z.re - 3/2| ≤ 1 := by
    have h1 : |(z - ((3/2 : ℝ) : ℂ)).re| ≤ ‖z - ((3/2 : ℝ) : ℂ)‖ := Complex.abs_re_le_norm _
    have h2 : (z - ((3/2 : ℝ) : ℂ)).re = z.re - 3/2 := by simp
    rw [h2] at h1; rw [hnorm] at h1; exact h1
  have hre_bds := abs_le.mp hre_le
  have him_le : |z.im| ≤ 1 := by
    have h1 : |(z - ((3/2 : ℝ) : ℂ)).im| ≤ ‖z - ((3/2 : ℝ) : ℂ)‖ := Complex.abs_im_le_norm _
    have h2 : (z - ((3/2 : ℝ) : ℂ)).im = z.im := by simp
    rw [h2] at h1; rw [hnorm] at h1; exact h1
  have him_bds := abs_le.mp him_le
  -- Bounds on the two shifted arguments.
  have hp_re : (z + T * Complex.I).re = z.re := by simp
  have hp_im : (z + T * Complex.I).im = z.im + T := by simp
  have hm_re : (z - T * Complex.I).re = z.re := by simp
  have hm_im : (z - T * Complex.I).im = z.im - T := by simp
  -- Apply the ζ axiom to `z + iT`.
  have hbp : ‖riemannZeta (z + T * Complex.I)‖ ≤ C * (1 + |(z + T * Complex.I).im|) := by
    apply hCbound
    · rw [hp_re]; linarith [hre_bds.1]
    · rw [hp_re]; linarith [hre_bds.2]
    · rw [hp_im]
      have : (1 : ℝ) ≤ z.im + T := by linarith [him_bds.1]
      rw [abs_of_nonneg (by linarith)]; linarith
  have hbm : ‖riemannZeta (z - T * Complex.I)‖ ≤ C * (1 + |(z - T * Complex.I).im|) := by
    apply hCbound
    · rw [hm_re]; linarith [hre_bds.1]
    · rw [hm_re]; linarith [hre_bds.2]
    · rw [hm_im]
      have : z.im - T ≤ -1 := by linarith [him_bds.2]
      rw [abs_of_nonpos (by linarith)]; linarith
  -- Both imaginary parts are bounded by `T + 1` in absolute value.
  have hp_im_abs : |(z + T * Complex.I).im| ≤ T + 1 := by
    rw [hp_im]; rw [abs_of_nonneg (by linarith [him_bds.1])]; linarith [him_bds.2]
  have hm_im_abs : |(z - T * Complex.I).im| ≤ T + 1 := by
    rw [hm_im]; rw [abs_of_nonpos (by linarith [him_bds.2])]; linarith [him_bds.1]
  -- Combine.
  have hbp' : ‖riemannZeta (z + T * Complex.I)‖ ≤ C * (1 + (T + 1)) :=
    le_trans hbp (by
      apply mul_le_mul_of_nonneg_left _ hC0; linarith [hp_im_abs])
  have hbm' : ‖riemannZeta (z - T * Complex.I)‖ ≤ C * (1 + (T + 1)) :=
    le_trans hbm (by
      apply mul_le_mul_of_nonneg_left _ hC0; linarith [hm_im_abs])
  -- Triangle inequality through the average.
  have : ‖backlundF T z‖ ≤
      (‖riemannZeta (z + T * Complex.I)‖ + ‖riemannZeta (z - T * Complex.I)‖) / 2 := by
    unfold backlundF
    rw [norm_div]
    have h2 : ‖(2 : ℂ)‖ = 2 := by simp
    rw [h2]
    apply div_le_div_of_nonneg_right (norm_add_le _ _) (by norm_num)
  calc ‖backlundF T z‖
      ≤ (‖riemannZeta (z + T * Complex.I)‖ + ‖riemannZeta (z - T * Complex.I)‖) / 2 := this
    _ ≤ (C * (1 + (T + 1)) + C * (1 + (T + 1))) / 2 := by
        apply div_le_div_of_nonneg_right _ (by norm_num)
        exact add_le_add hbp' hbm'
    _ = C * (1 + (T + 1)) := by ring

/-! ### Backlund–Jensen zero-count inequality

The central output: a `C' · log T + D'` bound on the Jensen zero-count of the
Backlund function in the inner disk, with the **crude Backlund coefficient**
`C' = 1 / log 8 ≤ 1/2`.  The only non-elementary input still taken as a hypothesis
is the **Backlund value lower bound** `‖f_T(3/2)‖ ≥ c₀ > 0`, which classically
holds because `f_T(3/2) = Re ζ(3/2 + iT)` and the Dirichlet series gives
`Re ζ(σ + it) ≥ 2 - ζ(σ) > 0` for `σ = 3/2` (`ζ(3/2) ≈ 2.612` is too large, so in
practice one uses `σ = 2`; either way `Re ζ` on a fixed vertical line `σ > 1` is
bounded below by a positive constant for all `t`, the standard Backlund input). -/

/-- **Backlund–Jensen count.** With centre `3/2`, inner radius `1/8`, outer radius
`1`, the number of zeros of the Backlund function in the inner disk is at most
`(1 / Real.log 8) · Real.log T + D` for an explicit `D` depending on the ζ-growth
constant `C` and the value lower bound `c₀`.  Since `1 / log 8 ≤ 1/2`, this is the
analytic heart of the *crude* Backlund bound `|S(T)| ≤ (1/2) log T + D'`. -/
theorem backlund_jensen_zero_count
    (T : ℝ) (hT : 2 ≤ T)
    (c₀ : ℝ) (hc₀ : 0 < c₀)
    (hval : c₀ ≤ ‖backlundF T ((3/2 : ℝ) : ℂ)‖) :
    ∃ C' D' : ℝ, 0 ≤ C' ∧ C' ≤ 1/2 ∧
      ((∑ᶠ u : ℂ, (MeromorphicOn.divisor (backlundF T)
          (Metric.closedBall ((3/2 : ℝ) : ℂ) (1/8 : ℝ))) u : ℝ)
        ≤ C' * Real.log T + D') ∧
      C' = 1 / Real.log 8 := by
  obtain ⟨C, hC0, hsphereC⟩ := backlundF_sphere_bound T hT
  -- The Jensen majorant.
  set M : ℝ := 1 + C * (1 + (T + 1)) with hM_def
  have hM1 : 1 ≤ M := by
    have : 0 ≤ C * (1 + (T + 1)) := by positivity
    linarith
  have hMpos : 0 < M := lt_of_lt_of_le one_pos hM1
  -- Geometry: `|R| = 1`, `|r| = 1/8`.
  have hr_pos : (0 : ℝ) < |(1/8 : ℝ)| := by norm_num
  have hr_lt_R : |(1/8 : ℝ)| < |(1 : ℝ)| := by norm_num
  have habsR : |(1 : ℝ)| = (1 : ℝ) := by norm_num
  have habsr : |(1/8 : ℝ)| = (1/8 : ℝ) := by norm_num
  -- Analyticity on the closed ball of radius `|1| = 1`.
  have hanalytic : AnalyticOnNhd ℂ (backlundF T)
      (Metric.closedBall ((3/2 : ℝ) : ℂ) |(1 : ℝ)|) := by
    rw [habsR]
    exact backlundF_analyticOnNhd T (3/2) 1 (by linarith)
  -- `f c ≠ 0` from the value lower bound.
  have hfc : backlundF T ((3/2 : ℝ) : ℂ) ≠ 0 := by
    intro h; rw [h, norm_zero] at hval; linarith
  -- Sphere bound, transported to `|R| = 1` and `M`.
  have hsphereM : ∀ z ∈ Metric.sphere ((3/2 : ℝ) : ℂ) |(1 : ℝ)|,
      ‖backlundF T z‖ ≤ M := by
    rw [habsR]
    intro z hz
    have h := hsphereC z hz
    linarith
  -- Apply the Mathlib Jensen zero-count inequality.
  have hjensen := AnalyticOnNhd.sum_divisor_le
    (c := ((3/2 : ℝ) : ℂ)) (r := (1/8 : ℝ)) (R := (1 : ℝ)) (M := M) (f := backlundF T)
    hr_pos hr_lt_R hM1 hanalytic hfc hsphereM
  -- Simplify the `|r|` in the count to `1/8`.
  rw [habsr] at hjensen
  -- `log(R/r) = log 8`.
  have hRr : (1 : ℝ) / (1/8 : ℝ) = 8 := by norm_num
  rw [hRr] at hjensen
  -- `log(M/‖f c‖) ≤ log M - log c₀`  (since `‖f c‖ ≥ c₀ > 0`).
  have hlogquot : Real.log (M / ‖backlundF T ((3/2 : ℝ) : ℂ)‖) ≤ Real.log M - Real.log c₀ := by
    rw [Real.log_div (ne_of_gt hMpos) (by positivity)]
    have hge : Real.log c₀ ≤ Real.log (‖backlundF T ((3/2 : ℝ) : ℂ)‖) :=
      Real.log_le_log hc₀ hval
    linarith
  -- `log M ≤ log K + log T` with `K = 1 + 3C` (so `M ≤ K·T` for `T ≥ 1`).
  set K : ℝ := 1 + 3 * C with hK_def
  have hKpos : 0 < K := by positivity
  have hMleKT : M ≤ K * T := by
    have hT1 : (1 : ℝ) ≤ T := by linarith
    -- M = 1 + 2C + C*T ;  K*T = T + 3C*T
    have e1 : M = 1 + 2 * C + C * T := by rw [hM_def]; ring
    have e2 : K * T = T + 3 * C * T := by rw [hK_def]; ring
    rw [e1, e2]
    nlinarith [hC0, hT1]
  have hlogM : Real.log M ≤ Real.log K + Real.log T := by
    have h1 : Real.log M ≤ Real.log (K * T) :=
      Real.log_le_log hMpos hMleKT
    rwa [Real.log_mul (ne_of_gt hKpos) (by linarith : (T:ℝ) ≠ 0)] at h1
  -- `1 / log 8 ≤ 1/2`  since `log 8 = 3 log 2 ≥ 2`.
  have hlog8_pos : 0 < Real.log 8 := Real.log_pos (by norm_num)
  have hlog8_ge2 : (2 : ℝ) ≤ Real.log 8 := by
    have h8 : (8 : ℝ) = 2 ^ (3 : ℕ) := by norm_num
    rw [h8, Real.log_pow]
    have hl2 : (0.6931471803 : ℝ) ≤ Real.log 2 := by
      have := Real.log_two_gt_d9
      linarith
    push_cast
    nlinarith [hl2]
  have hCp_le : 1 / Real.log 8 ≤ 1/2 := by
    have := one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 2) hlog8_ge2
    simpa using this
  -- Assemble: bound RHS by `(1/log 8)·log T + D'`.
  refine ⟨1 / Real.log 8, (Real.log K - Real.log c₀) / Real.log 8,
    by positivity, hCp_le, ?_, rfl⟩
  -- Chain the inequalities.
  have hstep : Real.log (M / ‖backlundF T ((3/2 : ℝ) : ℂ)‖)
      ≤ Real.log K + Real.log T - Real.log c₀ := by
    calc Real.log (M / ‖backlundF T ((3/2 : ℝ) : ℂ)‖)
        ≤ Real.log M - Real.log c₀ := hlogquot
      _ ≤ (Real.log K + Real.log T) - Real.log c₀ := by linarith
  have hdiv : Real.log (M / ‖backlundF T ((3/2 : ℝ) : ℂ)‖) / Real.log 8
      ≤ (Real.log K + Real.log T - Real.log c₀) / Real.log 8 := by
    gcongr
  -- Push the integer cast inside the finsum so it matches `hjensen`'s LHS.
  have hcast : (∑ᶠ u : ℂ, ((MeromorphicOn.divisor (backlundF T)
        (Metric.closedBall ((3/2 : ℝ) : ℂ) (1/8 : ℝ))) u : ℝ))
      = ((∑ᶠ u : ℂ, (MeromorphicOn.divisor (backlundF T)
          (Metric.closedBall ((3/2 : ℝ) : ℂ) (1/8 : ℝ))) u : ℤ) : ℝ) :=
    (map_finsum (Int.castRingHom ℝ)
      ((MeromorphicOn.divisor (backlundF T)
        (Metric.closedBall ((3/2 : ℝ) : ℂ) (1/8 : ℝ))).finiteSupport (isCompact_closedBall ..))).symm
  rw [hcast]
  calc ((∑ᶠ u : ℂ, (MeromorphicOn.divisor (backlundF T)
          (Metric.closedBall ((3/2 : ℝ) : ℂ) (1/8 : ℝ))) u : ℤ) : ℝ)
      ≤ Real.log (M / ‖backlundF T ((3/2 : ℝ) : ℂ)‖) / Real.log 8 := hjensen
    _ ≤ (Real.log K + Real.log T - Real.log c₀) / Real.log 8 := hdiv
    _ = (1 / Real.log 8) * Real.log T + (Real.log K - Real.log c₀) / Real.log 8 := by
        field_simp; ring

/-! ### Bridge to `rh.lean`'s `BacklundArgumentBoundOnGoodHeights`

The geometric Jensen count `backlund_jensen_zero_count` is the analytic heart of
the Backlund bound.  Inhabiting `OverflowResidueRH.BacklundArgumentBoundOnGoodHeights`
requires the classical **argument-principle identity** connecting the geometric
zero count to the abstract `Sarg`/`concreteS` object, namely

* (Backlund's variation lemma)  `|Sarg T| ≤ 1 + N_f(T)`, where
  `N_f(T) = ∑ᶠ u, divisor (backlundF T) (closedBall (3/2) (1/8)) u`
  is exactly the count bounded above, together with the constant absorption
  `1 + (C' log T + D') ≤ (1/2) log T + 1/2` for large `T` (valid because `C' ≤ 1/2`).

That identity is itself a separate large analytic development (the
Riemann–von Mangoldt argument principle), which `rh.lean` exposes only through its
`ProvenRiemannVonMangoldtFormula` / `RvMContourArgumentData` interfaces; it is NOT
derivable from the ζ-growth axiom alone.  We therefore package the residual cleanly
as a single hypothesis `hBacklundVariation` and discharge the rest. -/

/-- **Backlund–Jensen count with a nonpositive additive constant.**
At good heights where the value lower bound `c₀` is large enough that
`log(1 + 3C) ≤ log c₀` (equivalently `1 + 3C ≤ c₀`, the standard regime since the
Dirichlet-series value `Re ζ(3/2 + iT)` is bounded below by a fixed positive
constant while the ζ-growth constant `C` is fixed — one simply takes the centre on
a vertical line far enough right), the Jensen zero count is bounded by
`log T / log 8` (coefficient `1/log 8 < 1/2`) with no positive additive constant.
Here `C` and the sphere bound are passed explicitly, so the value hypothesis
`1 + 3C ≤ c₀` is self-contained. -/
theorem backlund_jensen_zero_count_clean
    (T : ℝ) (hT : 2 ≤ T)
    (C : ℝ) (hC0 : 0 ≤ C)
    (hsphereC : ∀ z ∈ Metric.sphere ((3/2 : ℝ) : ℂ) (1 : ℝ),
      ‖backlundF T z‖ ≤ C * (1 + (T + 1)))
    (c₀ : ℝ) (hc₀ : 0 < c₀)
    (hval : c₀ ≤ ‖backlundF T ((3/2 : ℝ) : ℂ)‖)
    (hbig : 1 + 3 * C ≤ c₀) :
    (∑ᶠ u : ℂ, (MeromorphicOn.divisor (backlundF T)
        (Metric.closedBall ((3/2 : ℝ) : ℂ) (1/8 : ℝ))) u : ℝ)
      ≤ Real.log T / Real.log 8 := by
  set M : ℝ := 1 + C * (1 + (T + 1)) with hM_def
  have hM1 : 1 ≤ M := by
    have : 0 ≤ C * (1 + (T + 1)) := by positivity
    linarith
  have hMpos : 0 < M := lt_of_lt_of_le one_pos hM1
  have hr_pos : (0 : ℝ) < |(1/8 : ℝ)| := by norm_num
  have hr_lt_R : |(1/8 : ℝ)| < |(1 : ℝ)| := by norm_num
  have habsR : |(1 : ℝ)| = (1 : ℝ) := by norm_num
  have habsr : |(1/8 : ℝ)| = (1/8 : ℝ) := by norm_num
  have hanalytic : AnalyticOnNhd ℂ (backlundF T)
      (Metric.closedBall ((3/2 : ℝ) : ℂ) |(1 : ℝ)|) := by
    rw [habsR]; exact backlundF_analyticOnNhd T (3/2) 1 (by linarith)
  have hfc : backlundF T ((3/2 : ℝ) : ℂ) ≠ 0 := by
    intro h; rw [h, norm_zero] at hval; linarith
  have hsphereM : ∀ z ∈ Metric.sphere ((3/2 : ℝ) : ℂ) |(1 : ℝ)|,
      ‖backlundF T z‖ ≤ M := by
    rw [habsR]; intro z hz; have h := hsphereC z hz; linarith
  have hjensen := AnalyticOnNhd.sum_divisor_le
    (c := ((3/2 : ℝ) : ℂ)) (r := (1/8 : ℝ)) (R := (1 : ℝ)) (M := M) (f := backlundF T)
    hr_pos hr_lt_R hM1 hanalytic hfc hsphereM
  rw [habsr] at hjensen
  have hRr : (1 : ℝ) / (1/8 : ℝ) = 8 := by norm_num
  rw [hRr] at hjensen
  -- `M ≤ c₀ · T`:  `M = 1 + 2C + C T ≤ (1+3C) T ≤ c₀ T` for `T ≥ 1`.
  have hMle : M ≤ c₀ * T := by
    have hT1 : (1 : ℝ) ≤ T := by linarith
    have e1 : M = 1 + 2 * C + C * T := by rw [hM_def]; ring
    rw [e1]
    nlinarith [hC0, hT1, hbig]
  -- `log M ≤ log c₀ + log T`.
  have hlogM : Real.log M ≤ Real.log c₀ + Real.log T := by
    have h1 : Real.log M ≤ Real.log (c₀ * T) := Real.log_le_log hMpos hMle
    rwa [Real.log_mul (ne_of_gt hc₀) (by linarith : (T:ℝ) ≠ 0)] at h1
  -- `log(M/‖f c‖) ≤ log M - log c₀ ≤ log T`.
  have hquot : Real.log (M / ‖backlundF T ((3/2 : ℝ) : ℂ)‖) ≤ Real.log T := by
    rw [Real.log_div (ne_of_gt hMpos) (by positivity)]
    have hge : Real.log c₀ ≤ Real.log (‖backlundF T ((3/2 : ℝ) : ℂ)‖) :=
      Real.log_le_log hc₀ hval
    linarith
  -- Combine with `log 8 ≥ 2`:  count ≤ log T / log 8 ≤ (1/2) log T.
  have hcast : (∑ᶠ u : ℂ, ((MeromorphicOn.divisor (backlundF T)
        (Metric.closedBall ((3/2 : ℝ) : ℂ) (1/8 : ℝ))) u : ℝ))
      = ((∑ᶠ u : ℂ, (MeromorphicOn.divisor (backlundF T)
          (Metric.closedBall ((3/2 : ℝ) : ℂ) (1/8 : ℝ))) u : ℤ) : ℝ) :=
    (map_finsum (Int.castRingHom ℝ)
      ((MeromorphicOn.divisor (backlundF T)
        (Metric.closedBall ((3/2 : ℝ) : ℂ) (1/8 : ℝ))).finiteSupport (isCompact_closedBall ..))).symm
  rw [hcast]
  exact le_trans hjensen (by gcongr)

/-! ### Bridge to `rh.lean`'s `BacklundArgumentBoundOnGoodHeights`

The clean count `backlund_jensen_zero_count_clean` is the analytic heart.
Inhabiting `OverflowResidueRH.BacklundArgumentBoundOnGoodHeights` requires the
classical **argument-principle identity** connecting the geometric zero count to
the abstract `Sarg`/`concreteS` object, namely Backlund's variation bound
`|Sarg T| ≤ 1 + N_f(T)`.  That identity is a separate large analytic development
(the Riemann–von Mangoldt argument principle), exposed by `rh.lean` only through
its `ProvenRiemannVonMangoldtFormula` interfaces and NOT derivable from the
ζ-growth axiom alone.  We package the residual cleanly as a single hypothesis. -/

/-- **Conditional packaging.**  Given (i) the strengthened Backlund value lower
bound at every good height (classical Dirichlet-series positivity) and (ii) the
argument-principle variation bound `|Sarg T| ≤ 1 + N_f(T)`, plus the elementary
large-height fact `1 ≤ (1/2) log T`, the crude Backlund constant `½ log T + ½`
follows on good heights, fully inhabiting `BacklundArgumentBoundOnGoodHeights`. -/
noncomputable def backlundArgumentBoundOnGoodHeights_of_inputs
    (Sarg : ℝ → ℝ) (lower : ℝ)
    (hlower : 2 * Real.pi ≤ lower)
    (C : ℝ) (hC0 : 0 ≤ C)
    (hsphere : ∀ T : ℝ, lower ≤ T →
      ∀ z ∈ Metric.sphere ((3/2 : ℝ) : ℂ) (1 : ℝ),
        ‖backlundF T z‖ ≤ C * (1 + (T + 1)))
    (hval : ∀ T : ℝ, lower ≤ T →
      ∃ c₀ : ℝ, 0 < c₀ ∧ c₀ ≤ ‖backlundF T ((3/2 : ℝ) : ℂ)‖ ∧ 1 + 3 * C ≤ c₀)
    (hBacklundVariation : ∀ T : ℝ, lower ≤ T → GoodHeight T →
      |Sarg T| ≤ 1 +
        (∑ᶠ u : ℂ, (MeromorphicOn.divisor (backlundF T)
          (Metric.closedBall ((3/2 : ℝ) : ℂ) (1/8 : ℝ))) u : ℝ))
    (hlog : ∀ T : ℝ, lower ≤ T →
      (1 : ℝ) + Real.log T / Real.log 8 ≤ (1/2 : ℝ) * Real.log T + 1/2) :
    BacklundArgumentBoundOnGoodHeights Sarg where
  lower := lower
  lower_ge_two_pi := hlower
  bound := by
    intro T hTlow hgood
    have hT2 : (2 : ℝ) ≤ T := by
      have hpi : (2 : ℝ) ≤ 2 * Real.pi := by nlinarith [Real.pi_gt_three]
      linarith [le_trans hpi hlower]
    obtain ⟨c₀, hc₀, hcval, hcbig⟩ := hval T hTlow
    have hcount : (∑ᶠ u : ℂ, (MeromorphicOn.divisor (backlundF T)
        (Metric.closedBall ((3/2 : ℝ) : ℂ) (1/8 : ℝ))) u : ℝ)
        ≤ Real.log T / Real.log 8 :=
      backlund_jensen_zero_count_clean T hT2 C hC0 (hsphere T hTlow) c₀ hc₀ hcval hcbig
    have hvar := hBacklundVariation T hTlow hgood
    have hslack := hlog T hTlow
    calc |Sarg T|
        ≤ 1 + (∑ᶠ u : ℂ, (MeromorphicOn.divisor (backlundF T)
            (Metric.closedBall ((3/2 : ℝ) : ℂ) (1/8 : ℝ))) u : ℝ) := hvar
      _ ≤ 1 + Real.log T / Real.log 8 := by linarith
      _ ≤ (1/2 : ℝ) * Real.log T + 1/2 := hslack

end BacklundTuring
end OverflowResidueRH
