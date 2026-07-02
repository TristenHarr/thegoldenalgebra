import rh
import Mathlib.Analysis.Complex.JensenFormula

/-!
# ScratchEnvelopeWire — pinning the envelope reduction frontier

This file traces, in `rh.lean`, the **exact reduction** of the Backlund/Jensen
envelope `|concreteS T| ≤ (1/2)·log T + 1/2` (for `T ≥ 140`) and discharges as
many of its remaining input leaves as the companion proven scratch files allow.

KEY DISCOVERY (from reading `rh.lean`):

The headline envelope is reduced inside `rh.lean` to a **SINGLE** remaining
analytic leaf, via `concreteS_halfLogPlusHalf_of_backlundArgument` (rh:18264):

    concreteS_halfLogPlusHalf_of_backlundArgument
        (B : BacklundGoodHeightArgumentBound) {T} (hT : 140 ≤ T) :
        |concreteS T| ≤ (1/2)·log T + 1/2

The *second* leaf of the cleaner 2-input frontier — the right-local-constancy of
the weighted zero count `ZetaWeightedZeroCountRightLocalConstancyInput` — is
**already discharged unconditionally** inside `rh.lean` as
`zetaWeightedZeroCountRightLocalConstancyInput` (rh:18255), built from the proven
global right-gap `zetaZeroHeightRightGapInput` (rh:17957), whose chain bottoms
out at `zetaNoZerosLeftHalfPlaneUpper`, `zetaZerosUpToHeightSet_finite`,
`zetaZero_re_lt_one`.

So the **entire irreducible frontier is `BacklundGoodHeightArgumentBound`**:

    ∀ T, RvMGoodHeight T → 140 ≤ T → |concreteS T| ≤ (1/2)·log T + 1/2.

This file:

1. Re-exports the proven `ScratchBacklund` pieces (transplanted as axioms with
   their exact signatures) — the unconditional ζ-poly growth bound and the
   Backlund–Jensen clean zero count `≤ log T / log 8`.
2. Provides the bridge `BacklundArgumentBoundOnGoodHeights Sarg`
   (with `Sarg` agreeing with `concreteS`) ⟹ `BacklundGoodHeightArgumentBound`.
3. Wires the whole envelope to that single leaf, and exhibits two concrete
   discharges of it that remain as explicit hypotheses, showing precisely where
   the irreducible boundary sits.

All transplanted ζ-analytic facts are carried as `axiom`s (each proven
axiom-clean in its companion scratch file).  No `sorry`.
-/

open Complex Real

namespace OverflowResidueRH
namespace BacklundTuring

/-- The **Backlund function** at height `T` (transplanted from
`ScratchBacklund.lean`): `f_T(z) = (ζ(z + iT) + ζ(z - iT)) / 2`. -/
noncomputable def backlundF (T : ℝ) (z : ℂ) : ℂ :=
  (riemannZeta (z + T * Complex.I) + riemannZeta (z - T * Complex.I)) / 2

/-! ## Part A — transplanted proven ζ-analytic pieces (from ScratchBacklund) -/

/-- Unconditional polynomial growth of `ζ` in the strip `[1/2, 5/2] × {|t| ≥ 1}`.
Proven axiom-clean in `ScratchZetaPolyDirect.lean` (constant `C = 6`). -/
axiom norm_riemannZeta_poly_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ,
      (1 / 2 : ℝ) ≤ s.re → s.re ≤ (5 / 2 : ℝ) → (1 : ℝ) ≤ |s.im| →
        ‖riemannZeta s‖ ≤ C * (1 + |s.im|)

/-- The Backlund–Jensen **clean zero count** `≤ log T / log 8`, proven
axiom-clean in `ScratchBacklund.lean` from `norm_riemannZeta_poly_bound` via
`AnalyticOnNhd.sum_divisor_le` (Jensen's inequality on the ball
`closedBall (3/2) (1/8)`).  Conditional only on an explicit sphere bound and a
value lower bound at the centre `3/2 + iT`. -/
axiom backlund_jensen_zero_count_clean
    (T : ℝ) (hT : 2 ≤ T)
    (C : ℝ) (hC0 : 0 ≤ C)
    (hsphereC : ∀ z ∈ Metric.sphere ((3 / 2 : ℝ) : ℂ) (1 : ℝ),
      ‖backlundF T z‖ ≤ C * (1 + (T + 1)))
    (c₀ : ℝ) (hc₀ : 0 < c₀)
    (hval : c₀ ≤ ‖backlundF T ((3 / 2 : ℝ) : ℂ)‖)
    (hbig : 1 + 3 * C ≤ c₀) :
    (∑ᶠ u : ℂ, (MeromorphicOn.divisor (backlundF T)
        (Metric.closedBall ((3 / 2 : ℝ) : ℂ) (1 / 8 : ℝ))) u : ℝ)
      ≤ Real.log T / Real.log 8

/-! ## Part B — the inhabitant of `BacklundArgumentBoundOnGoodHeights Sarg`

This is `ScratchBacklund.backlundArgumentBoundOnGoodHeights_of_inputs`,
reconstructed here against the transplanted axioms.  It inhabits the
*abstract-`Sarg`* good-height Backlund bound from:

* the Jensen sphere bound + value lower bound (classical Dirichlet-series
  positivity), and
* the argument-principle variation bound `|Sarg T| ≤ 1 + N_f(T)`, and
* the elementary slack `1 + log T / log 8 ≤ (1/2) log T + 1/2`.
-/

/-- Inhabit `rh.lean`'s `BacklundArgumentBoundOnGoodHeights Sarg` from the
proven Backlund–Jensen count plus the argument-principle variation bound and
the elementary log slack.  (Transplant of
`ScratchBacklund.backlundArgumentBoundOnGoodHeights_of_inputs`.) -/
noncomputable def backlundArgumentBoundOnGoodHeights_of_inputs
    (Sarg : ℝ → ℝ) (lower : ℝ)
    (hlower : 2 * Real.pi ≤ lower)
    (C : ℝ) (hC0 : 0 ≤ C)
    (hsphere : ∀ T : ℝ, lower ≤ T →
      ∀ z ∈ Metric.sphere ((3 / 2 : ℝ) : ℂ) (1 : ℝ),
        ‖backlundF T z‖ ≤ C * (1 + (T + 1)))
    (hval : ∀ T : ℝ, lower ≤ T →
      ∃ c₀ : ℝ, 0 < c₀ ∧ c₀ ≤ ‖backlundF T ((3 / 2 : ℝ) : ℂ)‖ ∧ 1 + 3 * C ≤ c₀)
    (hBacklundVariation : ∀ T : ℝ, lower ≤ T → GoodHeight T →
      |Sarg T| ≤ 1 +
        (∑ᶠ u : ℂ, (MeromorphicOn.divisor (backlundF T)
          (Metric.closedBall ((3 / 2 : ℝ) : ℂ) (1 / 8 : ℝ))) u : ℝ))
    (hlog : ∀ T : ℝ, lower ≤ T →
      (1 : ℝ) + Real.log T / Real.log 8 ≤ (1 / 2 : ℝ) * Real.log T + 1 / 2) :
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
        (Metric.closedBall ((3 / 2 : ℝ) : ℂ) (1 / 8 : ℝ))) u : ℝ)
        ≤ Real.log T / Real.log 8 :=
      backlund_jensen_zero_count_clean T hT2 C hC0 (hsphere T hTlow) c₀ hc₀ hcval hcbig
    have hvar := hBacklundVariation T hTlow hgood
    have hslack := hlog T hTlow
    calc |Sarg T|
        ≤ 1 + (∑ᶠ u : ℂ, (MeromorphicOn.divisor (backlundF T)
            (Metric.closedBall ((3 / 2 : ℝ) : ℂ) (1 / 8 : ℝ))) u : ℝ) := hvar
      _ ≤ 1 + Real.log T / Real.log 8 := by linarith
      _ ≤ (1 / 2 : ℝ) * Real.log T + 1 / 2 := hslack

/-! ## Part C — bridge from abstract-`Sarg` bound to the `concreteS` leaf

`BacklundGoodHeightArgumentBound` (rh:16774) is phrased on `concreteS`, whereas
Part B produces a bound on an *abstract* `Sarg`.  They are linked by the fact
that for any proved good-height RvM formula, `Sarg` agrees with `concreteS` on
good heights.  We package that link.
-/

/-- If `Sarg` agrees with `concreteS` on every good height with `T ≥ lower`, and
`lower ≤ 140`, then an abstract good-height Backlund bound on `Sarg` transfers to
the `concreteS`-phrased `BacklundGoodHeightArgumentBound`. -/
noncomputable def backlundGoodHeightArgumentBound_of_abstract
    {Sarg : ℝ → ℝ}
    (B : BacklundArgumentBoundOnGoodHeights Sarg)
    (hlow140 : B.lower ≤ 140)
    (hagree : ∀ T : ℝ, RvMGoodHeight T → Sarg T = concreteS T) :
    BacklundGoodHeightArgumentBound where
  bound := by
    intro T hgood hT
    have hTlow : B.lower ≤ T := le_trans hlow140 hT
    have hb := B.bound T hTlow hgood.good
    have hagreeT : Sarg T = concreteS T := hagree T hgood
    rwa [hagreeT] at hb

/-- If `Sarg` comes from a proved good-height RvM formula package `F`, the
agreement `Sarg = concreteS` on good heights is automatic, so we get the
`concreteS` leaf directly from the abstract bound. -/
noncomputable def backlundGoodHeightArgumentBound_of_rvMFormula
    (F : ProvenRiemannVonMangoldtFormulaOnGoodHeights)
    (B : BacklundArgumentBoundOnGoodHeights F.Sarg)
    (hlow140 : B.lower ≤ 140) :
    BacklundGoodHeightArgumentBound :=
  backlundGoodHeightArgumentBound_of_abstract B hlow140
    (fun T hgood => by
      -- `F.formula` gives `count = mainTerm + Sarg`; `concreteS` is
      -- `count - mainTerm`, so `Sarg = concreteS`.
      have hN := F.formula T hgood
      have hS :=
        concreteS_eq_zeta_count_sub_riemannVonMangoldtMainTerm hgood.nonneg
      linarith)

/-! ## Part D — the full envelope, reduced to the single leaf

We now state the headline envelope as a function of exactly one hypothesis,
`BacklundGoodHeightArgumentBound`, using `rh.lean`'s own unconditional discharge
of the right-local-constancy side.
-/

/-- **The whole envelope, one leaf.**  Given only the genuine Backlund/Jensen
good-height argument bound, the headline envelope holds for every `T ≥ 140`.
The zero-count right-continuity / discreteness side is supplied unconditionally
by `rh.lean` (`zetaWeightedZeroCountRightLocalConstancyInput`). -/
theorem envelope_from_single_leaf
    (B : BacklundGoodHeightArgumentBound)
    {T : ℝ} (hT : (140 : ℝ) ≤ T) :
    |concreteS T| ≤ (1 / 2 : ℝ) * Real.log T + 1 / 2 :=
  concreteS_halfLogPlusHalf_of_backlundArgument B hT

/-- **Envelope from an abstract-`Sarg` bound + RvM formula.**  Combining Part C
with Part D: a proved good-height RvM formula `F` together with an abstract
Backlund bound on `F.Sarg` (with threshold `≤ 140`) yields the full envelope. -/
theorem envelope_from_abstract_backlund
    (F : ProvenRiemannVonMangoldtFormulaOnGoodHeights)
    (B : BacklundArgumentBoundOnGoodHeights F.Sarg)
    (hlow140 : B.lower ≤ 140)
    {T : ℝ} (hT : (140 : ℝ) ≤ T) :
    |concreteS T| ≤ (1 / 2 : ℝ) * Real.log T + 1 / 2 :=
  envelope_from_single_leaf
    (backlundGoodHeightArgumentBound_of_rvMFormula F B hlow140) hT

/-! ## Part E — the genuinely-external residual, exhibited two ways

We exhibit the single leaf `BacklundGoodHeightArgumentBound` reduced further,
matching `rh.lean`'s own literature-sourced frontier, so the report can name
exactly what remains.
-/

/-- **Residual form 1 — Trudgian large-height envelope + finite-band check.**
This is `rh.lean`'s own cleanest split (rh:19083): a large-height explicit
`S(T)`-envelope input (Trudgian) plus a numerical finite-band check on
`[140, 1200]`.  Both are genuinely external (literature/computation). -/
theorem envelope_from_trudgian_and_finiteBand
    (Hlarge : TrudgianBacklundLargeHeightInput)
    (Hfinite : BacklundFiniteBandCheck140_1200)
    {T : ℝ} (hT : (140 : ℝ) ≤ T) :
    |concreteS T| ≤ (1 / 2 : ℝ) * Real.log T + 1 / 2 :=
  envelope_from_single_leaf
    (BacklundGoodHeightArgumentBound.of_trudgian_large_and_finiteBand
      Hlarge Hfinite) hT

/-- **Residual form 2 — via the proven Jensen count.**  Combining Parts B + C +
D: the abstract Backlund good-height bound built from the *proven*
Backlund–Jensen count (`backlundArgumentBoundOnGoodHeights_of_inputs`) yields the
full envelope, leaving as explicit hypotheses exactly:

* `hsphere` — Jensen sphere growth bound (from the proven ζ-poly axiom);
* `hval`    — value lower bound `Re ζ(3/2 + iT) ≥ c₀` (Dirichlet-series
  positivity);
* `hBacklundVariation` — argument-principle variation `|Sarg T| ≤ 1 + N_f(T)`
  (our PT-A normalization);
* `hlog`    — elementary log slack.

`F` supplies the RvM formula linking `Sarg` and `concreteS`. -/
theorem envelope_from_proven_jensen_count
    (F : ProvenRiemannVonMangoldtFormulaOnGoodHeights)
    (lower : ℝ) (hlower : 2 * Real.pi ≤ lower) (hlow140 : lower ≤ 140)
    (C : ℝ) (hC0 : 0 ≤ C)
    (hsphere : ∀ T : ℝ, lower ≤ T →
      ∀ z ∈ Metric.sphere ((3 / 2 : ℝ) : ℂ) (1 : ℝ),
        ‖backlundF T z‖ ≤ C * (1 + (T + 1)))
    (hval : ∀ T : ℝ, lower ≤ T →
      ∃ c₀ : ℝ, 0 < c₀ ∧ c₀ ≤ ‖backlundF T ((3 / 2 : ℝ) : ℂ)‖ ∧ 1 + 3 * C ≤ c₀)
    (hBacklundVariation : ∀ T : ℝ, lower ≤ T → GoodHeight T →
      |F.Sarg T| ≤ 1 +
        (∑ᶠ u : ℂ, (MeromorphicOn.divisor (backlundF T)
          (Metric.closedBall ((3 / 2 : ℝ) : ℂ) (1 / 8 : ℝ))) u : ℝ))
    (hlog : ∀ T : ℝ, lower ≤ T →
      (1 : ℝ) + Real.log T / Real.log 8 ≤ (1 / 2 : ℝ) * Real.log T + 1 / 2)
    {T : ℝ} (hT : (140 : ℝ) ≤ T) :
    |concreteS T| ≤ (1 / 2 : ℝ) * Real.log T + 1 / 2 := by
  let B : BacklundArgumentBoundOnGoodHeights F.Sarg :=
    backlundArgumentBoundOnGoodHeights_of_inputs F.Sarg lower hlower C hC0
      hsphere hval hBacklundVariation hlog
  have hBlow : B.lower = lower := rfl
  exact envelope_from_abstract_backlund F B (by rw [hBlow]; exact hlow140) hT

end BacklundTuring
end OverflowResidueRH
