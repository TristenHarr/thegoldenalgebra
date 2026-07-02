import Mathlib

open Complex Filter Topology MeasureTheory

/-!
# Cartan's lemma (elementary circle-avoidance) for the genus-1 product

This file builds the **circle-avoidance / radius-selection** half of Cartan's lemma — the missing
ingredient isolated by `ScratchLogSumCore.CartanCircleAvoidance`. The classical Hadamard
minimum-modulus argument needs, given finitely many zeros `ρ` of the genus-1 product inside a disk,
a radius `R` in a controlled range `[r, 2r]` such that the circle `‖z‖ = R` **avoids** all the small
exceptional disks `‖z − ρ‖ < δ_ρ` (with `Σ_ρ δ_ρ` controlled). On that good circle every factor is
bounded below: `‖z − ρ‖ ≥ δ_ρ`, hence `log‖1 − z/ρ‖ ≥ log(δ_ρ/‖ρ‖) ≥ −C·log‖z‖`.

Cartan's lemma proper is **absent from Mathlib**. The genuinely missing mathematical content is the
**pigeonhole / measure estimate**: the set of *bad* radii (those `R` for which the circle `‖z‖=R`
meets some exceptional disk) has total length `≤ 2·Σ_ρ δ_ρ`; if this is `< (b − a)` then some radius
in `[a, b]` is good. This file proves exactly that, fully and unconditionally, via Lebesgue measure
on `ℝ`.

## What is PROVEN here (no `sorry`, no `sorryAx`)

1. `bad_set_measure_le` — the bad-radius set `⋃_{i∈s} Ioo (c i − δ i) (c i + δ i)` has Lebesgue
   measure `≤ ofReal (Σ_{i∈s} 2·δ i)`. (`measure_biUnion_finset_le` + `Real.volume_Ioo`.)

2. `exists_avoiding_radius` — **the elementary Cartan pigeonhole.** If `Σ_{i∈s} 2·δ i < b − a` then
   there is `R ∈ Icc a b` with `δ i ≤ |R − c i|` for every `i ∈ s` (R avoids every open interval
   `(c i − δ i, c i + δ i)`). This is the radius-selection core.

3. `dist_ge_of_radius_sep` — geometric bridge (reverse triangle inequality): if `δ ≤ |‖z‖ − ‖ρ‖|`
   then `‖z − ρ‖ ≥ δ`. So modulus separation (what the radius pigeonhole controls) already gives the
   FULL planar separation needed for the factor lower bound.

4. `exists_good_radius` — packaged for the genus-1 setting: given a `Finset` of zeros with
   nonnegative radii `δ` and `Σ_{i∈s} δ i < (b − a)/2`, there is `R ∈ [a, b]` such that for every
   zero in the finset, `δ i ≤ |R − ‖loc i‖|`.

5. `log_factor_lower_of_sep` — **the payoff.** If `δ ≤ ‖z − ρ‖`, `0 < δ`, `ρ ≠ 0`, then
   `log‖1 − z/ρ‖ ≥ log δ − log‖ρ‖`. With `‖ρ‖ ≤ 2‖z‖` this is `≥ log δ − log(2‖z‖)`, the per-near-zero
   Cartan lower bound that (with `δ = ‖ρ‖^{-2}`-type choices and the `O(‖z‖log‖z‖)` near count) yields
   `CartanCircleAvoidance`.

6. `cartanCircleAvoidance_of_radius` — assembles, for the finitely-many near zeros on a good circle,
   the lower bound `Σ_{near} log‖1 − z/ρ‖ ≥ −(near count)·(log‖ρ‖_max − log δ_min)` shape, conditional
   only on the quantitative radius choice (which the downstream count supplies).

## Honest residual

The radius pigeonhole, the geometric reverse-triangle bridge, and the per-factor log lower bound are
all CLOSED here. What is NOT done is fixing the *quantitative* per-zero radius `δ_ρ` and bounding
`Σ log‖ρ‖` against the order-1 near-count — that is bookkeeping on top of `Scratch.xi_zero_count_bigO`
and is left as the explicit hypotheses of `cartanCircleAvoidance_of_radius`. The deep, previously
missing analytic step (Cartan radius selection) is now mechanized.

Build: `cd /Users/tristen/Desktop/goldenalgebra/GoldenAlgebra && lake env lean ScratchCartan.lean`.
-/

namespace OverflowResidueRH.BacklundTuring.ScratchCartan

/-! ## Part 1 — the elementary measure pigeonhole (Cartan radius selection) -/

/-- **Bad-radius set measure bound.** The union of open intervals `(c i − δ i, c i + δ i)` over a
finite index set `s` has Lebesgue measure `≤ ofReal (Σ_{i∈s} 2·δ i)`, when the `δ i` are nonnegative. -/
theorem bad_set_measure_le {ι : Type*} (s : Finset ι) (c δ : ι → ℝ)
    (hδ : ∀ i ∈ s, 0 ≤ δ i) :
    volume (⋃ i ∈ s, Set.Ioo (c i - δ i) (c i + δ i))
      ≤ ENNReal.ofReal (∑ i ∈ s, 2 * δ i) := by
  refine le_trans (measure_biUnion_finset_le s _) ?_
  rw [ENNReal.ofReal_sum_of_nonneg (fun i hi => by have := hδ i hi; linarith)]
  refine Finset.sum_le_sum (fun i _ => ?_)
  rw [Real.volume_Ioo]
  apply le_of_eq
  congr 1
  ring

/-- **The elementary Cartan pigeonhole / radius selection.** If the total length of the bad
intervals is strictly less than the length of `[a, b]`, there is a radius `R ∈ [a, b]` avoiding
every open interval `(c i − δ i, c i + δ i)` — equivalently `δ i ≤ |R − c i|` for all `i ∈ s`. -/
theorem exists_avoiding_radius {ι : Type*} (s : Finset ι) (c δ : ι → ℝ)
    (hδ : ∀ i ∈ s, 0 ≤ δ i) {a b : ℝ} (_hab : a ≤ b)
    (hlen : ∑ i ∈ s, 2 * δ i < b - a) :
    ∃ R ∈ Set.Icc a b, ∀ i ∈ s, δ i ≤ |R - c i| := by
  set bad : Set ℝ := ⋃ i ∈ s, Set.Ioo (c i - δ i) (c i + δ i) with hbad
  -- The bad set has measure < volume (Icc a b).
  have hbadlt : volume bad < volume (Set.Icc a b) := by
    refine lt_of_le_of_lt (bad_set_measure_le s c δ hδ) ?_
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_lt_ofReal_iff_of_nonneg
      (by have := hlen; nlinarith [Finset.sum_nonneg (fun i hi => by have := hδ i hi; linarith :
        ∀ i ∈ s, (0:ℝ) ≤ 2 * δ i)]) |>.mpr hlen
  -- Hence Icc a b is not contained in bad: there is a good radius.
  have hnsub : ¬ Set.Icc a b ⊆ bad := by
    intro hsub
    exact absurd (measure_mono hsub) (not_le.mpr hbadlt)
  rw [Set.not_subset] at hnsub
  obtain ⟨R, hRmem, hRbad⟩ := hnsub
  refine ⟨R, hRmem, fun i hi => ?_⟩
  -- R ∉ bad ⇒ R ∉ Ioo (c i − δ i)(c i + δ i) ⇒ δ i ≤ |R − c i|
  have hRi : R ∉ Set.Ioo (c i - δ i) (c i + δ i) := by
    intro hmem
    apply hRbad
    rw [hbad]
    exact Set.mem_biUnion hi hmem
  rw [Set.mem_Ioo, not_and_or, not_lt, not_lt] at hRi
  rcases hRi with h | h
  · -- R ≤ c i − δ i ⇒ c i − R ≥ δ i ⇒ |R − c i| ≥ δ i
    rw [abs_sub_comm, le_abs]
    left; linarith
  · -- c i + δ i ≤ R ⇒ R − c i ≥ δ i
    rw [le_abs]; left; linarith

/-! ## Part 2 — geometric bridge (modulus separation ⇒ planar separation) -/

/-- **Reverse-triangle bridge.** If `δ ≤ |‖z‖ − ‖ρ‖|` then `δ ≤ ‖z − ρ‖`. So the radius pigeonhole's
modulus separation gives the full planar separation the factor lower bound needs. -/
theorem dist_ge_of_radius_sep {z ρ : ℂ} {δ : ℝ} (h : δ ≤ |‖z‖ - ‖ρ‖|) :
    δ ≤ ‖z - ρ‖ := by
  have := abs_norm_sub_norm_le z ρ
  linarith

/-! ## Part 3 — packaged good-radius existence and the factor log lower bound -/

/-- **Good-radius existence (genus-1 packaging).** Given a finset of zeros (`loc`), nonnegative
per-zero radii `δ` with `Σ_{i∈s} δ i < (b − a)/2`, there is `R ∈ [a, b]` separated in modulus from
every `‖loc i‖` by `δ i`. -/
theorem exists_good_radius {ι : Type*} (loc : ι → ℂ) (s : Finset ι) (δ : ι → ℝ)
    (hδ : ∀ i ∈ s, 0 ≤ δ i) {a b : ℝ} (hab : a ≤ b)
    (hsum : ∑ i ∈ s, δ i < (b - a) / 2) :
    ∃ R ∈ Set.Icc a b, ∀ i ∈ s, δ i ≤ |R - ‖loc i‖| := by
  have hlen : ∑ i ∈ s, 2 * δ i < b - a := by
    rw [← Finset.mul_sum]; linarith
  exact exists_avoiding_radius s (fun i => ‖loc i‖) δ hδ hab hlen

/-- **Per-factor log lower bound off the exceptional disk.** If `δ ≤ ‖z − ρ‖`, `0 < δ`, `ρ ≠ 0`,
then `‖1 − z/ρ‖ ≥ δ/‖ρ‖` and hence `log‖1 − z/ρ‖ ≥ log δ − log‖ρ‖`. -/
theorem log_factor_lower_of_sep {z ρ : ℂ} {δ : ℝ} (hδ : 0 < δ) (hρ : ρ ≠ 0)
    (hsep : δ ≤ ‖z - ρ‖) :
    Real.log δ - Real.log ‖ρ‖ ≤ Real.log ‖1 - z / ρ‖ := by
  have hρpos : 0 < ‖ρ‖ := by simpa [norm_pos_iff] using hρ
  -- ‖1 − z/ρ‖ = ‖ρ − z‖/‖ρ‖ = ‖z − ρ‖/‖ρ‖ ≥ δ/‖ρ‖.
  have hfac : ‖1 - z / ρ‖ = ‖z - ρ‖ / ‖ρ‖ := by
    rw [show (1 : ℂ) - z / ρ = (ρ - z) / ρ by field_simp, norm_div, norm_sub_rev]
  have hge : δ / ‖ρ‖ ≤ ‖1 - z / ρ‖ := by
    rw [hfac]
    gcongr
  have hfacpos : 0 < ‖1 - z / ρ‖ := lt_of_lt_of_le (by positivity) hge
  calc Real.log δ - Real.log ‖ρ‖
      = Real.log (δ / ‖ρ‖) := by rw [Real.log_div (ne_of_gt hδ) (ne_of_gt hρpos)]
    _ ≤ Real.log ‖1 - z / ρ‖ := Real.log_le_log (by positivity) hge

/-- **Assembled Cartan lower bound on a good circle (the near-zeros contribution).**
For the finitely-many near zeros `s`, on a radius `R` separated in modulus from each `‖loc i‖` by the
per-zero radius `δ i` (as supplied by `exists_good_radius`), and for any `z` on the circle `‖z‖ = R`,
each near factor satisfies `log‖1 − z/loc i‖ ≥ log(δ i) − log‖loc i‖`. Summing over the finset gives
the near-zeros log-sum lower bound. -/
theorem cartanCircleAvoidance_of_radius {ι : Type*} (loc : ι → ℂ) (s : Finset ι) (δ : ι → ℝ)
    (hδpos : ∀ i ∈ s, 0 < δ i) (hne : ∀ i ∈ s, loc i ≠ 0)
    {z : ℂ} (hsep : ∀ i ∈ s, δ i ≤ |‖z‖ - ‖loc i‖|) :
    ∑ i ∈ s, (Real.log (δ i) - Real.log ‖loc i‖) ≤ ∑ i ∈ s, Real.log ‖1 - z / loc i‖ := by
  refine Finset.sum_le_sum (fun i hi => ?_)
  have hplanar : δ i ≤ ‖z - loc i‖ := dist_ge_of_radius_sep (hsep i hi)
  exact log_factor_lower_of_sep (hδpos i hi) (hne i hi) hplanar

end OverflowResidueRH.BacklundTuring.ScratchCartan
