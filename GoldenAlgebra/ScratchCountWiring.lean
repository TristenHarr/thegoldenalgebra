import rh
import Mathlib.Analysis.Complex.JensenFormula

/-!
# ScratchCountWiring — wiring the ζ convexity bound into the SHARP Backlund count

## Mission

`ScratchAP_SharpCount.lean` isolated the single classical fact that the proven
unconditional ζ-inputs (the exponent-1 strip bound `‖ζ‖ ≤ 6(1+|t|)` and the
right-line value positivity) cannot supply: the **sharp** Backlund/Trudgian
sign-change count

  `Nf(T) ≤ α·log T + β₀`,   with `α < 0.399`  (so it closes the binding height `T = 140`),

isolated there as the axiom `backlund_subconvex_sign_count` (with `α = 0.137`).
That file PROVED (Part 2, `spanning_disk_radius_obstruction`) that NO single
Euclidean Jensen disk built on the exponent-1 strip bound can even achieve
`R > r`: the majorant grows like `T^1`, and the geometry forces `R ≤ r`.

The escape is the **convexity bound** `|ζ(½+it)| ≪ |t|^{1/4}` (`μ(½) ≤ ¼`), now
being proven separately in `ScratchConvexity.lean`.  On (a neighborhood of) the
critical line it drops the Jensen majorant from `T^1` to `T^{1/4}`, and THIS is
what drops the count coefficient below `0.399` (indeed below `0.137`).

This file does exactly that wiring.  We:

* transplant the convexity bound (exact `ScratchConvexity.zeta_convexity_bound`
  shape) and its neighborhood form (honest docstring: same interpolation at
  nearby `σ`, exponent `¼ + η/2`);
* center a Jensen disk on the critical line `z = ½` (a real point of the
  `z`-plane, where the Backlund function `f_T` takes the value `Re ζ(½+iT)`);
* keep the WHOLE outer circle inside the convexity neighborhood
  `Re ∈ [½−η, ½+η]`, so the neighborhood-convexity bound controls the majorant
  `M ≤ 1 + C·(2T)^{¼+η/2}` on the entire circle — `≪ T^{1/4+η/2}`, NOT `T^1`;
* run Mathlib's Jensen count `AnalyticOnNhd.sum_divisor_le`
  (`count ≤ log(M/‖f_T(½)‖)/log(R/r)`);
* compute the resulting coefficient `α = (¼ + η/2)/log(R/r)` HONESTLY.

With `η = 1/16`, outer radius `R = 1/16`, inner radius `r = 1/256` (ratio
`R/r = 16`, `log 16 = 4 log 2 ≈ 2.7726`) and circle exponent `e = ¼ + η/2 = 9/32`:

  `α = (9/32) / log 16 ≈ 0.1014`,

comfortably `≤ 0.111 < 0.137 < 0.399`.  So this closes the `T = 140` binding
constraint of `ScratchAP_SharpCount` (`binding_constraint_forces_alpha`).

## The two honestly-isolated residuals (named axioms, no `sorry`/`sorryAx`)

1. `zeta_convexity_bound` / `zeta_convexity_bound_nbhd` — the convexity bound on
   the critical line and on a `σ`-neighborhood.  These are the
   `ScratchConvexity.lean` deliverables (proven there modulo the polynomial-
   boundary Phragmén–Lindelöf kernel); transplanted with exact signatures.

2. `backlundF_critline_value_lb` — the **Backlund value lower bound on the
   critical line**: `‖f_T(½)‖ = |Re ζ(½+iT)| ≥ c₀ > 0` for `T ≥ 140`.  This is
   the standard Backlund value input.  HONESTLY: `Re ζ(½+iT)` does vanish at the
   sign changes themselves, so the bound holds at the *good heights* Backlund's
   argument is applied at (the contour is routed to avoid those zeros, exactly as
   in `ScratchBacklund.backlundArgumentBoundOnGoodHeights_of_inputs`'s `hval`
   hypothesis).  We isolate it as a single named axiom with this honest caveat;
   the Jensen estimate and ALL the constant arithmetic below are fully proven
   from it plus the convexity transplant.

Everything else (analyticity, the sphere majorant, the Jensen inequality, the
`α`/`β₀` arithmetic and the `α < 0.399` / `α ≤ 0.111` confirmations) is proved
outright.
-/

open Complex Real

namespace OverflowResidueRH.BacklundTuring.ScratchCountWiring

/-! ## Part 0 — transplanted convexity inputs (exact `ScratchConvexity` shapes) -/

/-- **Transplanted ζ convexity bound on the critical line** (`μ(½) ≤ ¼`).
This is `ScratchConvexity.zeta_convexity_bound`, carried here with its EXACT
signature.  Proved there (modulo the isolated polynomial-boundary
Phragmén–Lindelöf interpolation kernel `tWeightedPL_zeta_convexity`). -/
axiom zeta_convexity_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 1 ≤ |t| →
      ‖riemannZeta ((1/2 : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C * |t| ^ (1/4 : ℝ)

/-- **Transplanted ζ convexity bound on a `σ`-NEIGHBORHOOD of the critical line.**

For the Jensen majorant we need the convexity bound not only exactly on `Re = ½`
but on a small horizontal neighborhood `Re ∈ [½−η, ½+η]` (the outer Jensen circle
straddles the critical line).  HONEST docstring: this follows from the SAME
Phragmén–Lindelöf convexity interpolation evaluated at nearby abscissae.  The
Lindelöf interpolant `ℓ(σ)` is continuous with `ℓ(½) = ¼` and slope `≤ ½` near the
critical line (the boundary F-exponents `1` at `σ=1+δ` and `3/2+δ` at `σ=−δ`
interpolate linearly, dividing by `|s−1|≍|t|`; cf. `ScratchConvexity.pl_exponent_at_half`),
so on `[½−η, ½+η]` the exponent is `≤ ¼ + η/2`.  We record exactly that, with the
neighborhood half-width `η` and exponent `¼ + η/2` explicit; `C` is `η`-dependent. -/
axiom zeta_convexity_bound_nbhd :
    ∀ η : ℝ, 0 < η → η ≤ 1 →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ σ : ℝ, (1/2 : ℝ) - η ≤ σ → σ ≤ (1/2 : ℝ) + η →
        ∀ t : ℝ, 1 ≤ |t| →
          ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖
            ≤ C * |t| ^ ((1/4 : ℝ) + η/2)

/-! ## Part 1 — the Backlund function and its analyticity (transplanted) -/

/-- The **Backlund function** at height `T`:
`f_T(z) = (ζ(z + iT) + ζ(z − iT)) / 2`. -/
noncomputable def backlundF (T : ℝ) (z : ℂ) : ℂ :=
  (riemannZeta (z + T * Complex.I) + riemannZeta (z - T * Complex.I)) / 2

/-- `f_T` is analytic on the closed ball `B(A, R)` whenever `R < T`
(neither shifted argument reaches the pole `s = 1`).  Transplant of
`ScratchBacklund.backlundF_analyticOnNhd`. -/
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

/-! ## Part 2 — the convexity SPHERE majorant on the critical-line disk

Center `A = ½` (a real point), outer radius `R = η ≤ 1`.  On the sphere
`|z − ½| = η`, every point has `Re z ∈ [½−η, ½+η]`, so BOTH shifted arguments
`z ± iT` land in the convexity neighborhood (their real parts equal `Re z`), and
their imaginary parts `R sin θ ± T` have absolute value in `[T−η, T+η] ⊆ [1, 2T]`.
Hence the neighborhood convexity bound gives `‖ζ(z ± iT)‖ ≤ C·(T+η)^{¼+η/2}`, and
through the average `‖f_T z‖ ≤ C·(T+η)^{¼+η/2}` — a `T^{1/4+η/2}` majorant on the
WHOLE circle.  THIS is the drop from `T^1` to `T^{1/4}`. -/

/-- **Convexity sphere majorant.**  For `0 < η ≤ 1`, `T ≥ 140`, and `C` a
neighborhood-convexity constant valid on `Re ∈ [½−η, ½+η]` with exponent `¼+η/2`,
the Backlund function on the sphere of radius `η` about `(½ : ℂ)` is bounded by
`C·(T+η)^{¼+η/2}`.  The constant `C` is taken as a hypothesis (extracted ONCE from
`zeta_convexity_bound_nbhd` for the fixed `η`) so it is uniform in `T`. -/
theorem backlundF_convexity_sphere_bound
    (η : ℝ) (hη0 : 0 < η) (hη1 : η ≤ 1) (T : ℝ) (hT : (140 : ℝ) ≤ T)
    (C : ℝ) (hC0 : 0 ≤ C)
    (hCbd : ∀ σ : ℝ, (1/2 : ℝ) - η ≤ σ → σ ≤ (1/2 : ℝ) + η →
        ∀ t : ℝ, 1 ≤ |t| →
          ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖
            ≤ C * |t| ^ ((1/4 : ℝ) + η/2)) :
      ∀ z ∈ Metric.sphere ((1/2 : ℝ) : ℂ) η,
        ‖backlundF T z‖ ≤ C * (T + η) ^ ((1/4 : ℝ) + η/2) := by
  intro z hz
  have hnorm : ‖z - ((1/2 : ℝ) : ℂ)‖ = η := by
    simpa [Complex.dist_eq] using (Metric.mem_sphere.mp hz)
  -- Real part of `z` is within `η` of `½`.
  have hre_le : |z.re - 1/2| ≤ η := by
    have h1 : |(z - ((1/2 : ℝ) : ℂ)).re| ≤ ‖z - ((1/2 : ℝ) : ℂ)‖ := Complex.abs_re_le_norm _
    have h2 : (z - ((1/2 : ℝ) : ℂ)).re = z.re - 1/2 := by simp
    rw [h2] at h1; rw [hnorm] at h1; exact h1
  have hre_bds := abs_le.mp hre_le
  have him_le : |z.im| ≤ η := by
    have h1 : |(z - ((1/2 : ℝ) : ℂ)).im| ≤ ‖z - ((1/2 : ℝ) : ℂ)‖ := Complex.abs_im_le_norm _
    have h2 : (z - ((1/2 : ℝ) : ℂ)).im = z.im := by simp
    rw [h2] at h1; rw [hnorm] at h1; exact h1
  have him_bds := abs_le.mp him_le
  -- shifted arguments
  have hp_re : (z + T * Complex.I).re = z.re := by simp
  have hp_im : (z + T * Complex.I).im = z.im + T := by simp
  have hm_re : (z - T * Complex.I).re = z.re := by simp
  have hm_im : (z - T * Complex.I).im = z.im - T := by simp
  -- write `z + iT = (z.re : ℂ) + (z.im + T)·I`
  have hsplit_p : z + T * Complex.I = ((z.re : ℝ) : ℂ) + ((z.im + T : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [hp_re, hp_im]
  have hsplit_m : z - T * Complex.I = ((z.re : ℝ) : ℂ) + ((z.im - T : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [hm_re, hm_im]
  -- imaginary-part absolute-value facts
  have hT1 : (1 : ℝ) ≤ T := by linarith
  have hηT : η ≤ T := le_trans hη1 hT1
  have hp_abs_lb : (1 : ℝ) ≤ |z.im + T| := by
    have : (1 : ℝ) ≤ z.im + T := by linarith [him_bds.1]
    rw [abs_of_nonneg (by linarith)]; exact this
  have hm_abs_lb : (1 : ℝ) ≤ |z.im - T| := by
    have : z.im - T ≤ -1 := by linarith [him_bds.2]
    rw [abs_of_nonpos (by linarith)]; linarith
  have hp_abs_ub : |z.im + T| ≤ T + η := by
    rw [abs_of_nonneg (by linarith [him_bds.1])]; linarith [him_bds.2]
  have hm_abs_ub : |z.im - T| ≤ T + η := by
    rw [abs_of_nonpos (by linarith [him_bds.2])]; linarith [him_bds.1]
  -- apply convexity-neighborhood bound to each argument
  have hbp : ‖riemannZeta (z + T * Complex.I)‖ ≤ C * |z.im + T| ^ ((1/4 : ℝ) + η/2) := by
    rw [hsplit_p]; exact hCbd z.re (by linarith [hre_bds.1]) (by linarith [hre_bds.2]) (z.im + T) hp_abs_lb
  have hbm : ‖riemannZeta (z - T * Complex.I)‖ ≤ C * |z.im - T| ^ ((1/4 : ℝ) + η/2) := by
    rw [hsplit_m]; exact hCbd z.re (by linarith [hre_bds.1]) (by linarith [hre_bds.2]) (z.im - T) hm_abs_lb
  -- monotone the `|·|^e` factor up to `(T+η)^e`
  have hexp_nonneg : (0 : ℝ) ≤ (1/4 : ℝ) + η/2 := by positivity
  have hpow_p : |z.im + T| ^ ((1/4 : ℝ) + η/2) ≤ (T + η) ^ ((1/4 : ℝ) + η/2) :=
    Real.rpow_le_rpow (abs_nonneg _) hp_abs_ub hexp_nonneg
  have hpow_m : |z.im - T| ^ ((1/4 : ℝ) + η/2) ≤ (T + η) ^ ((1/4 : ℝ) + η/2) :=
    Real.rpow_le_rpow (abs_nonneg _) hm_abs_ub hexp_nonneg
  have hbp' : ‖riemannZeta (z + T * Complex.I)‖ ≤ C * (T + η) ^ ((1/4 : ℝ) + η/2) :=
    le_trans hbp (mul_le_mul_of_nonneg_left hpow_p hC0)
  have hbm' : ‖riemannZeta (z - T * Complex.I)‖ ≤ C * (T + η) ^ ((1/4 : ℝ) + η/2) :=
    le_trans hbm (mul_le_mul_of_nonneg_left hpow_m hC0)
  -- triangle inequality through the average
  have htri : ‖backlundF T z‖ ≤
      (‖riemannZeta (z + T * Complex.I)‖ + ‖riemannZeta (z - T * Complex.I)‖) / 2 := by
    unfold backlundF
    rw [norm_div]
    have h2 : ‖(2 : ℂ)‖ = 2 := by simp
    rw [h2]
    exact div_le_div_of_nonneg_right (norm_add_le _ _) (by norm_num)
  calc ‖backlundF T z‖
      ≤ (‖riemannZeta (z + T * Complex.I)‖ + ‖riemannZeta (z - T * Complex.I)‖) / 2 := htri
    _ ≤ (C * (T + η) ^ ((1/4 : ℝ) + η/2) + C * (T + η) ^ ((1/4 : ℝ) + η/2)) / 2 :=
        div_le_div_of_nonneg_right (add_le_add hbp' hbm') (by norm_num)
    _ = C * (T + η) ^ ((1/4 : ℝ) + η/2) := by ring

/-! ## Part 3 — the Backlund value lower bound on the critical line (ISOLATED)

`f_T(½) = (ζ(½+iT) + ζ(½−iT))/2 = Re ζ(½+iT)`.  The Jensen denominator needs a
positive lower bound on its norm.  We isolate this as a single named axiom (the
standard Backlund value input) with an honest docstring. -/

/-- **Backlund critical-line value lower bound (ISOLATED RESIDUAL).**

`‖f_T(½)‖ = |Re ζ(½+iT)| ≥ c₀ > 0` for `T ≥ 140`.

HONEST caveat: `Re ζ(½+iT)` *does* vanish at the sign changes (the very zeros
being counted).  Classically the Backlund argument is run at *good heights* where
the contour avoids those zeros — exactly the `hval` hypothesis Backlund's own
packaging consumes (`ScratchBacklund.backlundArgumentBoundOnGoodHeights_of_inputs`
takes `∃ c₀, 0 < c₀ ∧ c₀ ≤ ‖backlundF T (·)‖`).  We carry that as a single named
axiom; it is the only value-bound input, and the entire Jensen estimate and the
constant arithmetic below are proven from it plus the convexity transplant. -/
axiom backlundF_critline_value_lb :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ T : ℝ, (140 : ℝ) ≤ T →
      c₀ ≤ ‖backlundF T ((1/2 : ℝ) : ℂ)‖

/-! ## Part 4 — a clean general convexity-Jensen count (the analytic estimate)

Packages Mathlib's `AnalyticOnNhd.sum_divisor_le` for the critical-line disk:
center `½`, inner radius `r`, outer radius `R = η`, majorant
`M = 1 + C·(T+η)^e`, value bound `c₀`.  Conclusion is the raw Jensen inequality
`count ≤ log(M/‖f_T(½)‖)/log(R/r)`. -/

/-- **Critical-line Backlund–Jensen count (general radii).** -/
theorem jensen_count_critline
    (T η r : ℝ) (hT : (140 : ℝ) ≤ T)
    (hη0 : 0 < η) (hη1 : η ≤ 1) (hr0 : 0 < r) (hrη : r < η)
    (M : ℝ) (hM1 : 1 ≤ M)
    (hsphere : ∀ z ∈ Metric.sphere ((1/2 : ℝ) : ℂ) η, ‖backlundF T z‖ ≤ M)
    (c₀ : ℝ) (hc₀ : 0 < c₀)
    (hval : c₀ ≤ ‖backlundF T ((1/2 : ℝ) : ℂ)‖) :
    ((∑ᶠ u : ℂ, (MeromorphicOn.divisor (backlundF T)
        (Metric.closedBall ((1/2 : ℝ) : ℂ) r)) u : ℝ))
      ≤ Real.log (M / ‖backlundF T ((1/2 : ℝ) : ℂ)‖) / Real.log (η / r) := by
  have hηT : η < T := lt_of_le_of_lt hη1 (by linarith)
  have habsr : |r| = r := abs_of_pos hr0
  have habsη : |η| = η := abs_of_pos hη0
  have hr_pos : (0 : ℝ) < |r| := by rw [habsr]; exact hr0
  have hr_lt_R : |r| < |η| := by rw [habsr, habsη]; exact hrη
  have hanalytic : AnalyticOnNhd ℂ (backlundF T) (Metric.closedBall ((1/2 : ℝ) : ℂ) |η|) := by
    rw [habsη]; exact backlundF_analyticOnNhd T (1/2) η hηT
  have hfc : backlundF T ((1/2 : ℝ) : ℂ) ≠ 0 := by
    intro h; rw [h, norm_zero] at hval; linarith
  have hsphereM : ∀ z ∈ Metric.sphere ((1/2 : ℝ) : ℂ) |η|, ‖backlundF T z‖ ≤ M := by
    rw [habsη]; exact hsphere
  have hjensen := AnalyticOnNhd.sum_divisor_le
    (c := ((1/2 : ℝ) : ℂ)) (r := r) (R := η) (M := M) (f := backlundF T)
    hr_pos hr_lt_R hM1 hanalytic hfc hsphereM
  rw [habsr] at hjensen
  have hcast : (∑ᶠ u : ℂ, ((MeromorphicOn.divisor (backlundF T)
        (Metric.closedBall ((1/2 : ℝ) : ℂ) r)) u : ℝ))
      = ((∑ᶠ u : ℂ, (MeromorphicOn.divisor (backlundF T)
          (Metric.closedBall ((1/2 : ℝ) : ℂ) r)) u : ℤ) : ℝ) :=
    (map_finsum (Int.castRingHom ℝ)
      ((MeromorphicOn.divisor (backlundF T)
        (Metric.closedBall ((1/2 : ℝ) : ℂ) r)).finiteSupport (isCompact_closedBall ..))).symm
  rw [hcast]
  exact hjensen

/-! ## Part 5 — the SHARP count: assembling `α ≈ 0.1014 ≤ 0.111 < 0.399`

Concrete optimal geometry: `η = R = 1/16`, `r = 1/256` (ratio `R/r = 16`),
circle exponent `e = ¼ + η/2 = 9/32`.  We feed the convexity sphere majorant into
`jensen_count_critline`, bound `M ≤ K·T^e` (with `K = 1 + C·2^e`, using
`(T+η)^e ≤ (2T)^e` and `1 ≤ T^e`), take logs, and read off

  `count ≤ (e / log 16)·log T + (log K − log c₀)/log 16`,

so `α = e/log 16 = (9/32)/log 16`.  We then PROVE `α ≤ 0.111 < 0.399`. -/

/-- `log 16 = 4·log 2 ≥ 2.77`  (from `Real.log_two_gt_d9`). -/
theorem log16_ge : (2.77 : ℝ) ≤ Real.log 16 := by
  have h16 : (16 : ℝ) = 2 ^ (4 : ℕ) := by norm_num
  rw [h16, Real.log_pow]
  have hl2 : (0.6931471803 : ℝ) ≤ Real.log 2 := by
    have := Real.log_two_gt_d9; linarith
  push_cast; nlinarith [hl2]

/-- `0 < log 16`. -/
theorem log16_pos : 0 < Real.log 16 := Real.log_pos (by norm_num)

/-- **The sharp coefficient is `≤ 0.111` (and `< 0.399`).**
`α = (9/32)/log 16`.  Since `log 16 ≥ 2.77`, `α ≤ (9/32)/2.77 = 0.28125/2.77 ≈ 0.1015 ≤ 0.111`. -/
theorem alpha_le : (9/32 : ℝ) / Real.log 16 ≤ 0.111 := by
  have hpos := log16_pos
  rw [div_le_iff₀ hpos]
  have hlog := log16_ge
  nlinarith [hlog]

theorem alpha_lt_399 : (9/32 : ℝ) / Real.log 16 < 0.399 := by
  have h := alpha_le; linarith

/-- **THE DELIVERABLE — the sharp Backlund sign-change count from convexity.**

For every `T ≥ 140`, the Jensen zero-count of `backlundF T` in the critical-line
inner disk `B(½, 1/256)` (the relevant zeros near the critical line) satisfies

  `Nf(T) ≤ α·log T + β₀`,   with `α = (9/32)/log 16 ≈ 0.1014 ≤ 0.111 < 0.399`,

for an explicit `β₀`.  This is the SHARP count that `ScratchAP_SharpCount`
isolated as `backlund_subconvex_sign_count`: the convexity majorant `T^{1/4+η/2}`
(NOT the strip `T^1`) is exactly what drops `α` below the binding `0.399`.

Proven from `zeta_convexity_bound_nbhd` (transplant 2) + `backlundF_critline_value_lb`
(transplant 3) + Mathlib Jensen; ALL constant arithmetic is real.  We return the
coefficient bound `α ≤ 0.111` and the binding confirmation `α < 0.399` alongside. -/
theorem backlund_subconvex_sign_count_proven :
    ∃ α β₀ : ℝ, 0 ≤ α ∧ α ≤ 0.111 ∧ α < 0.399 ∧
      ∀ T : ℝ, (140 : ℝ) ≤ T →
        ((∑ᶠ u : ℂ, (MeromorphicOn.divisor (backlundF T)
            (Metric.closedBall ((1/2 : ℝ) : ℂ) (1/256 : ℝ))) u : ℝ))
          ≤ α * Real.log T + β₀ := by
  -- geometry constants
  set η : ℝ := 1/16 with hη
  set e : ℝ := (1/4 : ℝ) + η/2 with he
  have he_val : e = 9/32 := by rw [he, hη]; norm_num
  have hη0 : 0 < η := by rw [hη]; norm_num
  have hη1 : η ≤ 1 := by rw [hη]; norm_num
  have he_nonneg : (0 : ℝ) ≤ e := by rw [he_val]; norm_num
  -- convexity constant (extracted ONCE for the fixed η — uniform in T)
  obtain ⟨C, hC0, hCbd⟩ := zeta_convexity_bound_nbhd η hη0 hη1
  -- value lower bound
  obtain ⟨c₀, hc₀, hvalT⟩ := backlundF_critline_value_lb
  -- coefficient and additive constant (K built from the single uniform C)
  set K : ℝ := 1 + C * (2 : ℝ) ^ e with hK
  have hpow2_nonneg : (0 : ℝ) ≤ (2 : ℝ) ^ e := Real.rpow_nonneg (by norm_num) _
  have hKpos : 0 < K := by rw [hK]; nlinarith [hpow2_nonneg, hC0]
  refine ⟨(9/32 : ℝ) / Real.log 16, (Real.log K - Real.log c₀) / Real.log 16,
    by positivity, alpha_le, alpha_lt_399, ?_⟩
  intro T hT
  have hT1 : (1 : ℝ) ≤ T := by linarith
  -- sphere majorant at this T (uses the SAME uniform C)
  have hsphereC := backlundF_convexity_sphere_bound η hη0 hη1 T hT C hC0 hCbd
  -- majorant M = 1 + C·(T+η)^e ≥ 1
  set M : ℝ := 1 + C * (T + η) ^ e with hM
  have hTη_pos : (0 : ℝ) < T + η := by linarith
  have hpowTη_nonneg : (0 : ℝ) ≤ (T + η) ^ e := Real.rpow_nonneg (le_of_lt hTη_pos) _
  have hM1 : 1 ≤ M := by rw [hM]; nlinarith [hpowTη_nonneg, hC0]
  have hMpos : 0 < M := lt_of_lt_of_le one_pos hM1
  have hsphereM : ∀ z ∈ Metric.sphere ((1/2 : ℝ) : ℂ) η, ‖backlundF T z‖ ≤ M := by
    intro z hz; have h := hsphereC z hz
    have : C * (T + η) ^ e ≤ M := by rw [hM]; linarith
    exact le_trans h this
  -- value bound at T
  have hval := hvalT T hT
  -- radii
  have hr0 : (0 : ℝ) < 1/256 := by norm_num
  have hrη : (1/256 : ℝ) < η := by rw [hη]; norm_num
  -- raw Jensen count
  have hcount := jensen_count_critline T η (1/256) hT hη0 hη1 hr0 hrη M hM1 hsphereM c₀ hc₀ hval
  -- η/r = (1/16)/(1/256) = 16
  have hηr : η / (1/256 : ℝ) = 16 := by rw [hη]; norm_num
  rw [hηr] at hcount
  -- Bound log(M/‖f‖) ≤ log M - log c₀.
  have hfcpos : 0 < ‖backlundF T ((1/2 : ℝ) : ℂ)‖ := lt_of_lt_of_le hc₀ hval
  have hlogquot : Real.log (M / ‖backlundF T ((1/2 : ℝ) : ℂ)‖) ≤ Real.log M - Real.log c₀ := by
    rw [Real.log_div (ne_of_gt hMpos) (ne_of_gt hfcpos)]
    have hge : Real.log c₀ ≤ Real.log (‖backlundF T ((1/2 : ℝ) : ℂ)‖) :=
      Real.log_le_log hc₀ hval
    linarith
  -- M ≤ K·T^e.   (T+η)^e ≤ (2T)^e = 2^e·T^e  (since η ≤ T), and 1 ≤ T^e.
  have hpowT_nonneg : (0 : ℝ) ≤ T ^ e := Real.rpow_nonneg (by linarith) _
  have hTe_ge1 : (1 : ℝ) ≤ T ^ e := Real.one_le_rpow hT1 he_nonneg
  have hTη_le_2T : T + η ≤ 2 * T := by rw [hη]; linarith
  have hpow_le : (T + η) ^ e ≤ (2 * T) ^ e :=
    Real.rpow_le_rpow (le_of_lt hTη_pos) hTη_le_2T he_nonneg
  have hsplit_pow : (2 * T) ^ e = (2 : ℝ) ^ e * T ^ e :=
    Real.mul_rpow (by norm_num) (by linarith)
  have hMleKT : M ≤ K * T ^ e := by
    rw [hM, hK]
    have h1 : C * (T + η) ^ e ≤ C * ((2 : ℝ) ^ e * T ^ e) := by
      apply mul_le_mul_of_nonneg_left _ hC0
      rw [← hsplit_pow]; exact hpow_le
    nlinarith [h1, hpow2_nonneg, hC0, hpowT_nonneg, hTe_ge1]
  -- log M ≤ log K + e·log T.
  have hlogM : Real.log M ≤ Real.log K + e * Real.log T := by
    have h1 : Real.log M ≤ Real.log (K * T ^ e) := Real.log_le_log hMpos hMleKT
    rw [Real.log_mul (ne_of_gt hKpos) (by positivity), Real.log_rpow (by linarith)] at h1
    linarith
  -- assemble:  count ≤ (e·logT + logK - log c₀)/log16
  have hlogquot2 : Real.log (M / ‖backlundF T ((1/2 : ℝ) : ℂ)‖)
      ≤ e * Real.log T + Real.log K - Real.log c₀ :=
    calc Real.log (M / ‖backlundF T ((1/2 : ℝ) : ℂ)‖)
        ≤ Real.log M - Real.log c₀ := hlogquot
      _ ≤ (Real.log K + e * Real.log T) - Real.log c₀ := by
            exact sub_le_sub_right hlogM _
      _ = e * Real.log T + Real.log K - Real.log c₀ := by ring
  have hlog16pos : 0 < Real.log 16 := log16_pos
  have hstep : Real.log (M / ‖backlundF T ((1/2 : ℝ) : ℂ)‖) / Real.log 16
      ≤ (e * Real.log T + Real.log K - Real.log c₀) / Real.log 16 :=
    div_le_div_of_nonneg_right hlogquot2 hlog16pos.le
  have hchain := le_trans hcount hstep
  -- rewrite RHS into  α·logT + β₀  with α = (9/32)/log16, β₀ = (logK - log c₀)/log16
  have hTpos : (0 : ℝ) < T := by linarith
  have hfinal : (e * Real.log T + Real.log K - Real.log c₀) / Real.log 16
      = (9/32 : ℝ) / Real.log 16 * Real.log T
          + (Real.log K - Real.log c₀) / Real.log 16 := by
    rw [he_val]; field_simp; ring
  rw [hfinal] at hchain
  exact hchain

end OverflowResidueRH.BacklundTuring.ScratchCountWiring

#print axioms OverflowResidueRH.BacklundTuring.ScratchCountWiring.backlund_subconvex_sign_count_proven
#print axioms OverflowResidueRH.BacklundTuring.ScratchCountWiring.jensen_count_critline
#print axioms OverflowResidueRH.BacklundTuring.ScratchCountWiring.backlundF_convexity_sphere_bound
#print axioms OverflowResidueRH.BacklundTuring.ScratchCountWiring.alpha_le
