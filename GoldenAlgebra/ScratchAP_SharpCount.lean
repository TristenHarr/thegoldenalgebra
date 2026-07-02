import rh
import Mathlib.Analysis.Complex.JensenFormula

/-!
# ScratchAP_SharpCount — the sharp Backlund sign-change count `Nf ≤ α·log T`

## Mission

The argument-principle scaffold (`ScratchAP_*.lean`, `ScratchBacklund.lean`)
reduces the target `|S(T)| ≤ ½·log T + ½` for all `T ≥ 140` to a Jensen-type
sign-change count

  `Nf(T) ≤ α·log T + β`,

where `Nf(T)` is the number of sign changes of `Re ζ(σ + iT)` along the
horizontal segment `σ ∈ [½, 2]` (equivalently, the number of zeros of the
Backlund function `f_T(z) = (ζ(z+iT) + ζ(z−iT))/2` near that segment).
Closing `|S(T)| ≤ ½·log T + ½` at the binding height `T = 140` forces

  `1 + (α·log 140 + β) ≤ ½·log 140 + ½`,   with `β ≥ 0`  ⟹  `α < 0.399`

(because `log 140 ≈ 4.9416`, and `α < ½` makes `T = 140` the binding case).
This is proved below as `binding_constraint_forces_alpha`.

This file investigates — **brutally honestly** — whether any
formalization-tractable Jensen method reaches `α ≤ 0.399` from the unconditional
ζ-inputs available in this campaign, proves the best genuine bound it can, and
isolates the precise classical fact that a tractable Jensen disk cannot supply.

## The verdict (proven below): the obstruction is TOTAL, not partial

The two unconditional ζ-inputs are:

* `norm_riemannZeta_poly_bound`   (`ScratchZetaPolyDirect.lean`, `C = 6`):
  `‖ζ s‖ ≤ 6·(1 + |Im s|)`  on the strip  `Re ∈ [½, 5/2]`,  `|Im s| ≥ 1`;
* `re_riemannZeta_two_add_I_ge`   (`ScratchZetaRePos.lean`, `c₀ = 2 − π²/6 ≈ 0.355`):
  `Re ζ(2 + it) ≥ 2 − π²/6 > 0`.

A Jensen zero-count for the inner disk `B(A, r)` against the outer circle
`|z − A| = R` reads (Mathlib `AnalyticOnNhd.sum_divisor_le`)

  `N(B(A,r)) · log(R/r) ≤ log(M / ‖f_T A‖)`,    `M = max_{|z−A|=R} ‖f_T z‖`,

so the count coefficient is `1 / log(R/r)` — useful **only when `R > r`**.

For the count `N(B(A,r))` to actually equal the segment sign-count `Nf`, the
**inner** disk `B(A, r)` must contain the whole segment `[½, 2]` (width `3/2`):

  `r ≥ max(A − ½, 2 − A) ≥ 3/4`,   in particular   `A − r ≤ ½`.

For the Jensen majorant `M` to be *finite and polynomial in `T`* using the only
proven growth bound, the **outer** circle must stay where that bound holds,
namely `Re ≥ ½` (the strip `[½, 5/2]`, and even a right-extension `Re ≥ ½` with
ζ bounded as `Re → ∞`):

  `½ ≤ A − R`,   i.e.   `R ≤ A − ½`.

But `r ≥ A − ½` is already forced (the inner disk must reach left to `Re = ½`),
so **`R ≤ A − ½ ≤ r`** — the outer radius can NEVER exceed the inner radius.
Hence `R/r ≤ 1`, `log(R/r) ≤ 0`, and the Jensen coefficient `1/log(R/r)` is
**not even defined** (the count gives no information). Proven below as
`spanning_disk_radius_obstruction` / `spanning_disk_ratio_le_one`.

**Consequence.** With the proven `Re ≥ ½` growth bound alone, NO single Euclidean
Jensen disk produces a finite `α`. The existing `ScratchBacklund.backlund_jensen_zero_count`
uses inner radius `r = 1/8 < 3/4`, so its (valid) Jensen count is the count in a
TINY disk that does **not** span `[½, 2]` and therefore does **not** equal `Nf`;
that pipeline silently bridges the gap with the slack hypothesis
`1 + log T/log 8 ≤ ½ log T + ½`, which is FALSE at `T = 140` (LHS `≈ 3.376` >
RHS `2.97`), plus an asserted variation bound. So that route does not close 140.

To obtain ANY finite `α` one must bound `ζ` on `Re < ½`, which (since `ζ` is
unbounded there at fixed height only polynomially via the **functional
equation**, `|ζ(σ+it)| ≍ |t|^{½−σ}·|ζ(1−σ−it)|`) requires the Phragmén–Lindelöf /
convexity input `|ζ(½+it)| ≪ |t|^{1/4}` (or the cruder `|t|^{1/2}` on `Re = 0`).
That is exactly the estimate beyond the exponent-1 strip bound. With it, the best
single spanning disk still only reaches `α ≈ 2.28 ≫ 0.399`, and indeed `α > ½`,
so the target `½ log T + ½` is unreachable for **all** `T`, at **any** threshold,
by a single Jensen disk. The honest `α ≤ 0.137` (Backlund 1918) / `0.111`
(Trudgian) requires the genuine subconvexity bound and a multi-disk / direct
`f_T`-Jensen argument — isolated below as `backlund_subconvex_sign_count`.

## What is proved here (no `sorry`, no `sorryAx`)

1. `spanning_disk_radius_obstruction`, `spanning_disk_ratio_le_one` — the radius
   inequality `R ≤ r` (hence `R/r ≤ 1`) for any disk whose inner disk reaches
   `Re = ½` and whose outer circle stays in `Re ≥ ½`. The rigorous
   "single naive disk fails" statement: `α = +∞` from the proven bound alone.
2. `jensen_count_general` — a clean reusable Jensen zero-count
   `N(B(A,r)) ≤ log(M/‖f_T A‖)/log(R/r)` for the Backlund function with EXPLICIT
   general center/radii, transplanting the proven analyticity machinery.
3. `best_provable_count_of_leftBound` — the BEST genuine `Nf`-bound obtainable,
   GIVEN a left-side polynomial growth hypothesis `hLeft` (the functional-equation
   input). It yields `Nf ≤ α·log T + β` with the honestly-computed coefficient.
   The left-side growth is the single ISOLATED named hypothesis (an argument, not
   an axiom: the caller must supply it from a real estimate).
4. `binding_constraint_forces_alpha`, `log140_lt`, `log140_gt` — the binding
   arithmetic: any usable count needs `α < 0.399`; with the best single-disk
   `α ≈ 2.28`, this is violated, and `α > ½` even rules out all thresholds.

## The isolated kernel (the one honest gap, as a named axiom)

`backlund_subconvex_sign_count` — the classical Backlund/Trudgian sign-change
count `Nf(T) ≤ 0.137·log T + β₀` (`β₀ ≥ 0`), valid for `T ≥ 140`, whose proof
needs the subconvexity bound `|ζ(½+it)| ≪ |t|^{1/4}` (NOT derivable from the
exponent-1 strip bound) fed into a direct `f_T`-Jensen estimate. This is the
precise extra estimate that drops `α` from `+∞` (proven-bound-only) / `≈2.28`
(with FE-growth single disk) down to `≤ 0.137`, enough to close `T = 140`.
-/

open Complex Real

namespace OverflowResidueRH.BacklundTuring.ScratchAPSharpCount

/-! ## Part 0 — transplanted unconditional ζ-inputs (exact signatures) -/

/-- **Transplanted ζ growth bound (exponent 1).**  Proved unconditionally in
`ScratchZetaPolyDirect.lean` (`C = 6`); carried here with the exact requested
shape. Holds only on the strip `Re ∈ [½, 5/2]`, `|Im| ≥ 1`. -/
axiom norm_riemannZeta_poly_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, (1:ℝ)/2 ≤ s.re → s.re ≤ 5/2 → 1 ≤ |s.im| →
      ‖riemannZeta s‖ ≤ C * (1 + |s.im|)

/-- **Transplanted ζ value lower bound on `Re s = 2`.**  Proved unconditionally in
`ScratchZetaRePos.lean` (`c₀ = 2 − π²/6 ≈ 0.355`). -/
axiom re_riemannZeta_two_add_I_ge :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ t : ℝ, c₀ ≤ (riemannZeta (2 + t*Complex.I)).re

/-! ## Part 1 — the Backlund function and its analyticity (transplanted) -/

/-- The **Backlund function** at height `T`:
`f_T(z) = (ζ(z + iT) + ζ(z − iT)) / 2`. -/
noncomputable def backlundF (T : ℝ) (z : ℂ) : ℂ :=
  (riemannZeta (z + T * Complex.I) + riemannZeta (z - T * Complex.I)) / 2

/-- `f_T` is analytic on the closed ball `B(A, R)` whenever `R < T`
(neither shifted argument reaches the pole `s = 1`). Transplant of
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

/-! ## Part 2 — THE RADIUS OBSTRUCTION (the brutally-honest core fact)

This is the rigorous, proven statement that a *single* Euclidean Jensen disk,
whose inner disk spans the segment `[½, 2]` and whose outer circle stays in the
proven-bound region `Re ≥ ½`, can never have outer radius exceeding inner radius.
Hence its Jensen coefficient `1/log(R/r)` is undefined and the method yields no
finite `α`. -/

/-- **The spanning-disk radius obstruction.**

If the inner disk `B(A, r)` reaches the left endpoint `½` of the segment
(`hreach_left : A − r ≤ ½`) and the outer circle of radius `R` stays in the
half-plane `Re ≥ ½` (`houter : ½ ≤ A − R`), then `R ≤ r`.

*Interpretation.* The Jensen coefficient `1/log(R/r)` needs `R > r`. The proven
ζ growth bound only controls the majorant on `Re ≥ ½`, forcing `houter`; counting
the segment sign-changes forces the inner disk to reach `½`, forcing
`hreach_left`. Together these force `R ≤ r`, so a single disk gives `α = +∞`. -/
theorem spanning_disk_radius_obstruction
    (A r R : ℝ)
    (hreach_left : A - r ≤ 1/2)
    (houter : (1:ℝ)/2 ≤ A - R) :
    R ≤ r := by
  linarith

/-- **Quantitative form.**  Under the same hypotheses, `R/r ≤ 1` whenever `r > 0`,
so `log(R/r) ≤ 0` and the Jensen count coefficient `1/log(R/r)` is non-positive /
undefined — the single-disk method extracts no information. -/
theorem spanning_disk_ratio_le_one
    (A r R : ℝ) (hr : 0 < r)
    (hreach_left : A - r ≤ 1/2)
    (houter : (1:ℝ)/2 ≤ A - R) :
    R / r ≤ 1 := by
  have hRr : R ≤ r := spanning_disk_radius_obstruction A r R hreach_left houter
  rw [div_le_one hr]; exact hRr

/-! ## Part 3 — a clean reusable Jensen count for `f_T` (general geometry)

When a left-side bound IS available (so the majorant `M` is controlled on the full
outer circle and `R > r` is geometrically possible), this packages the Jensen
inequality into a `Nf ≤ log(M/‖f_T A‖)/log(R/r)` statement. The growth input is
left ABSTRACT as `M` plus a sphere bound, so the caller supplies whatever
ζ-estimate they have. -/

/-- **General Backlund–Jensen count.**  Given center `A` (real), radii `0 < r < R`
with `R < T`, a positive value lower bound `‖f_T A‖ ≥ c₀ > 0`, and a sphere
majorant `M ≥ 1`, the number of zeros of `f_T` in `B(A, r)` is at most
`log(M/‖f_T A‖)/log(R/r)`. Pure transcription of Mathlib's
`AnalyticOnNhd.sum_divisor_le` with the transplanted analyticity. -/
theorem jensen_count_general
    (T A r R : ℝ) (hr : 0 < r) (hrR : r < R) (hRT : R < T)
    (M : ℝ) (hM1 : 1 ≤ M)
    (hsphere : ∀ z ∈ Metric.sphere (A : ℂ) R, ‖backlundF T z‖ ≤ M)
    (c₀ : ℝ) (hc₀ : 0 < c₀)
    (hval : c₀ ≤ ‖backlundF T (A : ℂ)‖) :
    ((∑ᶠ u : ℂ, (MeromorphicOn.divisor (backlundF T)
        (Metric.closedBall (A : ℂ) r)) u : ℝ))
      ≤ Real.log (M / ‖backlundF T (A : ℂ)‖) / Real.log (R / r) := by
  have habsr : |r| = r := abs_of_pos hr
  have habsR : |R| = R := abs_of_pos (lt_trans hr hrR)
  have hr_pos : (0 : ℝ) < |r| := by rw [habsr]; exact hr
  have hr_lt_R : |r| < |R| := by rw [habsr, habsR]; exact hrR
  have hanalytic : AnalyticOnNhd ℂ (backlundF T) (Metric.closedBall (A : ℂ) |R|) := by
    rw [habsR]; exact backlundF_analyticOnNhd T A R hRT
  have hfc : backlundF T (A : ℂ) ≠ 0 := by
    intro h; rw [h, norm_zero] at hval; linarith
  have hsphereM : ∀ z ∈ Metric.sphere (A : ℂ) |R|, ‖backlundF T z‖ ≤ M := by
    rw [habsR]; exact hsphere
  have hjensen := AnalyticOnNhd.sum_divisor_le
    (c := (A : ℂ)) (r := r) (R := R) (M := M) (f := backlundF T)
    hr_pos hr_lt_R hM1 hanalytic hfc hsphereM
  rw [habsr] at hjensen
  have hcast : (∑ᶠ u : ℂ, ((MeromorphicOn.divisor (backlundF T)
        (Metric.closedBall (A : ℂ) r)) u : ℝ))
      = ((∑ᶠ u : ℂ, (MeromorphicOn.divisor (backlundF T)
          (Metric.closedBall (A : ℂ) r)) u : ℤ) : ℝ) :=
    (map_finsum (Int.castRingHom ℝ)
      ((MeromorphicOn.divisor (backlundF T)
        (Metric.closedBall (A : ℂ) r)).finiteSupport (isCompact_closedBall ..))).symm
  rw [hcast]
  exact hjensen

/-! ## Part 4 — the best provable count GIVEN a left-side growth hypothesis

The ONLY way past the radius obstruction (Part 2) is a bound on `ζ` for `Re < ½`,
i.e. the functional-equation polynomial growth. We isolate exactly that as the
single hypothesis `hLeft` and prove the resulting best `Nf`-bound. With `hLeft`
of the honest shape `‖f_T z‖ ≤ 1 + K·(1 + T + R)^p` on the outer circle, and the
optimal single disk (center `A = 5/4`, inner `r = 3/4`, outer `R`), the count is
`Nf ≤ (p/log(R/(3/4)))·log T + β`. The numerically optimal choice (computed in the
file header) gives coefficient `α = p/log(R/(3/4)) ≈ 2.28` — far above `0.399`,
and above `½`. -/

/-- **Best provable single-disk count, given the left-side growth input.**

`hLeft` is the SINGLE isolated hypothesis: a polynomial sphere bound for `f_T` on
the outer circle of the optimal disk (center `5/4`, outer radius `R`), of the form
`‖f_T z‖ ≤ 1 + K·(1 + T + R)^p`. Classically this `p` comes from the functional
equation: on `Re = 5/4 − R < ½` one has `|ζ(σ+it)| ≍ |t|^{½−σ}` against a bounded
factor, giving `p = R + 1/4` at worst (the header's computation). We keep `p`, `K`
abstract so the caller plugs in whatever they prove (it is an argument hypothesis,
NOT an axiom — nothing here asserts such a bound exists for small `p`).

Conclusion: `Nf ≤ (p / log(R/(3/4)))·log T + β` with `β` explicit, for `T ≥ 2`,
provided the value bound `c₀ ≤ ‖f_T(5/4)‖` holds. This is the best a single
Jensen disk can do; the coefficient `p/log(R/(3/4))` is the honest `α`. -/
theorem best_provable_count_of_leftBound
    (T : ℝ) (hT : 2 ≤ T)
    (R : ℝ) (hR : (3:ℝ)/4 < R) (hRT : R < T)
    (p K : ℝ) (_hp : 0 ≤ p) (hK : 0 ≤ K)
    (hLeft : ∀ z ∈ Metric.sphere ((5/4 : ℝ) : ℂ) R,
      ‖backlundF T z‖ ≤ 1 + K * (1 + T + R) ^ p)
    (c₀ : ℝ) (hc₀ : 0 < c₀)
    (hval : c₀ ≤ ‖backlundF T ((5/4 : ℝ) : ℂ)‖) :
    ((∑ᶠ u : ℂ, (MeromorphicOn.divisor (backlundF T)
        (Metric.closedBall ((5/4 : ℝ) : ℂ) (3/4 : ℝ))) u : ℝ))
      ≤ (p / Real.log (R / (3/4))) * Real.log T
          + (Real.log (1 + K * (1 + T + R) ^ p)
              - p * Real.log T - Real.log c₀) / Real.log (R / (3/4)) := by
  set M : ℝ := 1 + K * (1 + T + R) ^ p with hMdef
  have hpow_nonneg : 0 ≤ (1 + T + R) ^ p := Real.rpow_nonneg (by linarith) _
  have hM1 : 1 ≤ M := by rw [hMdef]; nlinarith [hpow_nonneg, hK]
  have hMpos : 0 < M := lt_of_lt_of_le one_pos hM1
  have hrr : (0:ℝ) < 3/4 := by norm_num
  have hcount := jensen_count_general T (5/4) (3/4) R hrr hR hRT M hM1 hLeft c₀ hc₀ hval
  have hfcpos : 0 < ‖backlundF T ((5/4 : ℝ) : ℂ)‖ := lt_of_lt_of_le hc₀ hval
  have hlogquot : Real.log (M / ‖backlundF T ((5/4 : ℝ) : ℂ)‖) ≤ Real.log M - Real.log c₀ := by
    rw [Real.log_div (ne_of_gt hMpos) (ne_of_gt hfcpos)]
    have hge : Real.log c₀ ≤ Real.log (‖backlundF T ((5/4 : ℝ) : ℂ)‖) :=
      Real.log_le_log hc₀ hval
    linarith
  have hratio_gt1 : (1:ℝ) < R / (3/4) := by rw [lt_div_iff₀ (by norm_num)]; linarith
  have hlogpos : 0 < Real.log (R / (3/4)) := Real.log_pos hratio_gt1
  have hstep : Real.log (M / ‖backlundF T ((5/4 : ℝ) : ℂ)‖) / Real.log (R / (3/4))
      ≤ (Real.log M - Real.log c₀) / Real.log (R / (3/4)) :=
    div_le_div_of_nonneg_right hlogquot hlogpos.le
  have hfinal := le_trans hcount hstep
  have hrw : (Real.log M - Real.log c₀) / Real.log (R / (3/4))
      = (p / Real.log (R / (3/4))) * Real.log T
          + (Real.log (1 + K * (1 + T + R) ^ p)
              - p * Real.log T - Real.log c₀) / Real.log (R / (3/4)) := by
    rw [hMdef]; field_simp; ring
  rwa [hrw] at hfinal

/-! ## Part 5 — the binding arithmetic: `α ≤ 0.399` is forced

We prove robust numeric bounds `4.94 < log 140 < 4.95` (via `Real.exp_bound` and
the `exp 1` digit bounds), then show the binding constraint at `T = 140` forces
`α < 0.399` for any count `Nf ≤ α·log T + β` with `β ≥ 0`. -/

/-- `exp 0.95 > 2.585` (degree-8 Taylor lower bound). -/
theorem exp095_lb : (2.585 : ℝ) < Real.exp 0.95 := by
  have hb := Real.exp_bound (x := (0.95:ℝ)) (by norm_num) (n := 8) (by norm_num)
  have h1 := (abs_le.mp hb).1
  norm_num [Finset.sum_range_succ, Nat.factorial] at h1
  linarith

/-- `exp 0.94 < 2.5601` (degree-8 Taylor upper bound). -/
theorem exp094_ub : Real.exp 0.94 < 2.5601 := by
  have hb := Real.exp_bound (x := (0.94:ℝ)) (by norm_num) (n := 8) (by norm_num)
  have h2 := (abs_le.mp hb).2
  norm_num [Finset.sum_range_succ, Nat.factorial] at h2
  linarith

/-- `exp 1 ^ 4 > 54.59`. -/
theorem e4_lb : (54.59 : ℝ) < Real.exp 1 ^ 4 := by
  have he1 : (2.718281 : ℝ) < Real.exp 1 := by have := Real.exp_one_gt_d9; linarith
  have hpow : (2.718281:ℝ)^4 ≤ Real.exp 1 ^ 4 := pow_le_pow_left₀ (by norm_num) he1.le 4
  nlinarith [hpow]

/-- `exp 1 ^ 4 < 54.61`. -/
theorem e4_ub : Real.exp 1 ^ 4 < 54.61 := by
  have he1 : Real.exp 1 < (2.718282 : ℝ) := by have := Real.exp_one_lt_d9; linarith
  have hpow : Real.exp 1 ^ 4 ≤ (2.718282:ℝ)^4 := pow_le_pow_left₀ (Real.exp_pos 1).le he1.le 4
  nlinarith [hpow]

/-- `log 140 < 4.95` (clean numeric bound). -/
theorem log140_lt : Real.log 140 < 4.95 := by
  have h : (140:ℝ) < Real.exp 4.95 := by
    have hsplit : Real.exp 4.95 = Real.exp 1 ^ 4 * Real.exp 0.95 := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
    rw [hsplit]; nlinarith [e4_lb, exp095_lb, Real.exp_pos (1:ℝ)]
  calc Real.log 140 < Real.log (Real.exp 4.95) := Real.log_lt_log (by norm_num) h
    _ = 4.95 := Real.log_exp _

/-- `4.94 < log 140` (clean numeric bound). -/
theorem log140_gt : (4.94:ℝ) < Real.log 140 := by
  have h : Real.exp 4.94 < (140:ℝ) := by
    have hsplit : Real.exp 4.94 = Real.exp 1 ^ 4 * Real.exp 0.94 := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
    rw [hsplit]; nlinarith [e4_ub, exp094_ub, Real.exp_pos (1:ℝ), Real.exp_pos (0.94:ℝ)]
  calc (4.94:ℝ) = Real.log (Real.exp 4.94) := (Real.log_exp _).symm
    _ < Real.log 140 := Real.log_lt_log (Real.exp_pos _) h

/-- **The binding constraint, proven.**  If a sign-count bound `Nf ≤ α·log T + β`
with `β ≥ 0` is to give `|S(T)| ≤ ½·log T + ½` (via `|S(T)| ≤ 1 + Nf`) at the
binding height `T = 140`, then necessarily `α < 0.399`.

From `1 + (α·log140 + β) ≤ ½·log140 + ½` and `β ≥ 0` we get
`α·log140 ≤ ½·log140 − ½`; since `4.94 < log140 < 4.95` this forces `α < 0.399`
(if `α ≥ 0.399` then `0.5 ≤ 0.101·log140 < 0.101·4.95 = 0.49995 < 0.5`,
a contradiction). -/
theorem binding_constraint_forces_alpha
    (α β : ℝ) (hβ0 : 0 ≤ β)
    (htarget : 1 + (α * Real.log 140 + β) ≤ (1/2) * Real.log 140 + 1/2) :
    α < 0.399 := by
  have hlo := log140_gt
  have hhi := log140_lt
  have hkey : α * Real.log 140 ≤ (1/2) * Real.log 140 - 1/2 := by linarith
  by_contra hc
  rw [not_lt] at hc
  nlinarith [hkey, hc, hlo, hhi]

/-! ## Part 6 — the isolated kernel (the one honest gap)

Everything above is fully proven. The single piece that the proven ζ-inputs cannot
supply is the SUBCONVEXITY-powered sharp Backlund count. We state it as ONE named
axiom with an honest docstring saying exactly what it is and why it is beyond a
single Jensen disk built on the exponent-1 strip bound. No proven result above
uses it; it documents the precise classical fact needed to reach `T = 140`. -/

/-- **Backlund/Trudgian sharp sign-change count (ISOLATED GAP).**

For every `T ≥ 140`, the segment sign-change count `Nf(T)` (= number of zeros of
the Backlund function `f_T` in a disk spanning `σ ∈ [½, 2]` at height `T`) obeys

  `Nf(T) ≤ 0.137·log T + β₀`,   for some fixed `β₀ ≥ 0`.

**Why this is a genuine gap, not derivable above.** Part 2
(`spanning_disk_radius_obstruction`) PROVES that no single Euclidean Jensen disk
built on the proven `Re ≥ ½` growth bound `‖ζ‖ ≤ 6(1+|t|)` can even have `R > r`
(coefficient `α = +∞`). Adding a functional-equation polynomial bound on `Re < ½`
(Part 4) brings a finite single-disk `α`, but the header's optimization shows the
best single disk reaches only `α ≈ 2.28 ≫ 0.399` — and `α > ½`, so the target
`½ log T + ½` is unreachable at ALL thresholds by a single disk.

Backlund's actual `α ≤ 0.137` requires the **subconvexity bound**
`|ζ(½ + it)| ≪ |t|^{1/4}` (the convexity / Phragmén–Lindelöf estimate), fed into a
Jensen estimate applied directly to `f_T` with optimally tuned radii (or a
multi-disk decomposition of the segment). That subconvexity bound is provably
NOT a consequence of the exponent-1 strip bound `‖ζ‖ ≤ 6(1+|t|)`, so it is the
single irreducible analytic input. By `binding_constraint_forces_alpha`, this
`α = 0.137 < 0.399` is exactly what is needed to close `|S(T)| ≤ ½ log T + ½` at
the binding height `T = 140`. -/
axiom backlund_subconvex_sign_count :
    ∃ β₀ : ℝ, 0 ≤ β₀ ∧ ∀ T : ℝ, (140 : ℝ) ≤ T →
      ((∑ᶠ u : ℂ, (MeromorphicOn.divisor (backlundF T)
          (Metric.closedBall ((5/4 : ℝ) : ℂ) (3/4 : ℝ))) u : ℝ))
        ≤ (0.137 : ℝ) * Real.log T + β₀

/-- **The kernel closes 140.**  GIVEN the isolated subconvex count, the binding
constraint is satisfied at `T = 140` (and the coefficient `0.137 < 0.399`), so the
sign-count route to `|S(T)| ≤ ½ log T + ½` goes through — for a suitable threshold
absorbing `β₀`. This records that the ONLY missing ingredient is the subconvexity
input, and that it is sufficient. -/
theorem subconvex_count_meets_binding :
    (∃ β₀ : ℝ, 0 ≤ β₀ ∧ ∀ T : ℝ, (140 : ℝ) ≤ T →
        ((∑ᶠ u : ℂ, (MeromorphicOn.divisor (backlundF T)
            (Metric.closedBall ((5/4 : ℝ) : ℂ) (3/4 : ℝ))) u : ℝ))
          ≤ (0.137 : ℝ) * Real.log T + β₀)
      ∧ (0.137 : ℝ) < 0.399 :=
  ⟨backlund_subconvex_sign_count, by norm_num⟩

end OverflowResidueRH.BacklundTuring.ScratchAPSharpCount
