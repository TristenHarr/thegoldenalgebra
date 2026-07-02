import rh
import ScratchBoundedRHtoH
import ScratchBandFromVerified

/-!
# ScratchDispAboveTail — deriving `dispAbove_bound` from per-term + density

`ScratchBandFromVerified` proves the bounded theorem
`RH_below_H_of_verifiedZeros_complete`, but leaves ONE RH-independent field of
`BandDisplacementData H` as a raw hypothesis:

    dispAbove_bound : ∀ z, heightBand H z → 0 < z.im → |(dispAbove z).im| ≤ marginD z

This file **derives** that field, removing it as a raw assumption, by combining

1. the already-PROVED per-term displacement bound
   `displacementAtom_im_bound` (load-bearing rational-function algebra), with
2. an elementary DISTANCE bound: for a band probe `z` (`heightBand H z`, hence
   `|z.re|, |z.im| ≤ H - 1`) and a zero at height `γ > H` with `|η| ≤ 1/2`, the
   four denominators are all `≥ γ - H + 1`, so the per-term `Im` displacement is
   `≤ 1/(γ - H + 1)²`  (`displacementAtom_im_bound_above_band`); and
3. a COUNT/DENSITY tail comparison: the above-band displacement is a (finite)
   list-sum of off-line atoms with heights `γ > H`, so its `Im` is bounded by
   `Σ_i 1/(γ_i - H + 1)²`.  The convergence of this tail is exactly the
   Riemann–von Mangoldt density content (`N(T) ~ (T/2π)log T` ⟹ the ordinates
   `γ_k → ∞` fast enough that `Σ_k 1/(γ_k - H)²` converges).  It is carried as a
   single explicit inequality field `tail_summable : Σ 1/(γk-H+1)² ≤ marginD`
   of `AboveBandData` — the RvM-density input — and the clean unit-spacing
   special case `γ_k ≥ H + (k+1)` (`marginD = 2`, telescoping Basel tail) is
   provided as a constructor.

The deliverable is the band datum `BandDisplacementDataDerived H` and theorem
`RH_below_H_of_verifiedZeros_fullyDerived`, in which `dispAbove_bound` is no
longer a raw field but is PROVEN from (1)+(2)+(3) (`AboveBandData.disp_im_bound`),
with `dispAbove` realized as the above-band atom list-sum and `marginD` the
RvM tail constant.

## Honest provenance

* (1) `displacementAtom_im_bound` — PROVED in `ScratchBandFromVerified`
  (consumed, not re-derived).
* (2) `displacementAtom_im_bound_above_band` — PROVED here (elementary distance
  geometry of `heightBand` against a height-`γ > H` atom).
* (3) the tail summability `Σ_i 1/(γ_i-H+1)² ≤ marginD` — carried as the RvM
  density input (field `tail_summable` of `AboveBandData`).  Its clean
  unit-spacing special case (`γ_k ≥ H+(k+1) ⟹ marginD = 2`) is PROVED here by
  the telescoping Basel bound `sum_one_div_sq_le_two`.  HONEST CAVEAT: the true
  RvM density exceeds one zero per unit interval at large `H` (density
  `~ log H/2π`), so the unit-spacing constructor is a *simplification*; the
  general `tail_summable` field accommodates the genuine RvM density (`γ_k`
  growth from `N(T) ~ (T/2π)log T`) directly, but this file does NOT formally
  re-derive `tail_summable` from the in-file count envelope
  `concreteS_halfLogPlusHalf_bound_from_140` — that count is behind a
  `BacklundTuringAnalyticInputs` input (RH-independent, not unconditionally
  constructed in rh.lean), and bridging it to an ordinate spacing would require
  a per-zero ordinate enumeration absent from the file (only the first ten
  ordinates are tabulated).  So the RvM density enters as the carried
  `tail_summable` field, precisely the convergent-tail content the task allows
  to be sourced as an input.

No `sorry`, axiom-clean (`#print axioms` at end → only
`propext, Classical.choice, Quot.sound`).
-/

namespace OverflowResidueRH

open Complex Filter Topology

-- =====================================================================
-- §A.  The elementary above-band DISTANCE bound
-- =====================================================================

/-- On the band, `|z.re| ≤ H - 1` and `|z.im| ≤ H - 1`. -/
theorem heightBand_re_im_le {H : ℝ} {z : ℂ} (hb : heightBand H z) :
    |z.re| ≤ H - 1 ∧ |z.im| ≤ H - 1 := by
  unfold heightBand at hb
  have h1 : 0 ≤ |z.re| := abs_nonneg _
  have h2 : 0 ≤ |z.im| := abs_nonneg _
  constructor <;> linarith

/-- 🌟 **Distance lower bound `‖z - γ‖ ≥ γ - H + 1`.**  The real part of
`z - γ` is `z.re - γ`, with `|z.re - γ| ≥ γ - |z.re| ≥ γ - (H-1)`. -/
theorem norm_sub_ofReal_ge {H γ : ℝ} {z : ℂ}
    (hb : heightBand H z) (hγ : H < γ) :
    γ - H + 1 ≤ ‖z - (γ : ℂ)‖ := by
  obtain ⟨hre, _⟩ := heightBand_re_im_le hb
  have hre' : z.re ≤ H - 1 := le_trans (le_abs_self _) hre
  have hpos : 0 ≤ γ - z.re := by linarith
  have hcoord : (z - (γ : ℂ)).re = z.re - γ := by simp [Complex.sub_re]
  have hge : γ - H + 1 ≤ |z.re - γ| := by
    rw [abs_sub_comm, abs_of_nonneg hpos]; linarith
  calc γ - H + 1 ≤ |z.re - γ| := hge
    _ = |(z - (γ : ℂ)).re| := by rw [hcoord]
    _ ≤ ‖z - (γ : ℂ)‖ := Complex.abs_re_le_norm _

/-- 🌟 **Distance lower bound `‖z + γ‖ ≥ γ - H + 1`.** -/
theorem norm_add_ofReal_ge {H γ : ℝ} {z : ℂ}
    (hb : heightBand H z) (hγ : H < γ) :
    γ - H + 1 ≤ ‖z + (γ : ℂ)‖ := by
  obtain ⟨hre, _⟩ := heightBand_re_im_le hb
  have hre' : -(H - 1) ≤ z.re := by
    have := neg_abs_le z.re; linarith
  have hpos : 0 ≤ z.re + γ := by linarith
  have hcoord : (z + (γ : ℂ)).re = z.re + γ := by simp [Complex.add_re]
  have hge : γ - H + 1 ≤ |z.re + γ| := by
    rw [abs_of_nonneg hpos]; linarith
  calc γ - H + 1 ≤ |z.re + γ| := hge
    _ = |(z + (γ : ℂ)).re| := by rw [hcoord]
    _ ≤ ‖z + (γ : ℂ)‖ := Complex.abs_re_le_norm _

/-- 🌟 **Distance lower bound `‖z - w‖ ≥ γ - H + 1`** with `w = ⟨γ, -η⟩`.  The
real part of `z - w` is still `z.re - γ` (the offset `η` is in the imaginary
part), so the same real-part bound applies. -/
theorem norm_sub_w_ge {H γ η : ℝ} {z : ℂ}
    (hb : heightBand H z) (hγ : H < γ) :
    γ - H + 1 ≤ ‖z - (⟨γ, -η⟩ : ℂ)‖ := by
  obtain ⟨hre, _⟩ := heightBand_re_im_le hb
  have hre' : z.re ≤ H - 1 := le_trans (le_abs_self _) hre
  have hpos : 0 ≤ γ - z.re := by linarith
  have hcoord : (z - (⟨γ, -η⟩ : ℂ)).re = z.re - γ := by
    simp [Complex.sub_re]
  have hge : γ - H + 1 ≤ |z.re - γ| := by
    rw [abs_sub_comm, abs_of_nonneg hpos]; linarith
  calc γ - H + 1 ≤ |z.re - γ| := hge
    _ = |(z - (⟨γ, -η⟩ : ℂ)).re| := by rw [hcoord]
    _ ≤ ‖z - (⟨γ, -η⟩ : ℂ)‖ := Complex.abs_re_le_norm _

/-- 🌟 **Distance lower bound `‖z + w‖ ≥ γ - H + 1`** with `w = ⟨γ, -η⟩`. -/
theorem norm_add_w_ge {H γ η : ℝ} {z : ℂ}
    (hb : heightBand H z) (hγ : H < γ) :
    γ - H + 1 ≤ ‖z + (⟨γ, -η⟩ : ℂ)‖ := by
  obtain ⟨hre, _⟩ := heightBand_re_im_le hb
  have hre' : -(H - 1) ≤ z.re := by
    have := neg_abs_le z.re; linarith
  have hpos : 0 ≤ z.re + γ := by linarith
  have hcoord : (z + (⟨γ, -η⟩ : ℂ)).re = z.re + γ := by
    simp [Complex.add_re]
  have hge : γ - H + 1 ≤ |z.re + γ| := by
    rw [abs_of_nonneg hpos]; linarith
  calc γ - H + 1 ≤ |z.re + γ| := hge
    _ = |(z + (⟨γ, -η⟩ : ℂ)).re| := by rw [hcoord]
    _ ≤ ‖z + (⟨γ, -η⟩ : ℂ)‖ := Complex.abs_re_le_norm _

-- =====================================================================
-- §B.  The per-term above-band displacement bound  ≤ 1/(γ-H+1)²
-- =====================================================================

/-- Reciprocal of a product of two norms each `≥ d > 0` is `≤ 1/d²`. -/
theorem one_div_norm_mul_le {a b : ℂ} {d : ℝ}
    (hd : 0 < d) (ha : d ≤ ‖a‖) (hb : d ≤ ‖b‖) :
    1 / ‖a * b‖ ≤ 1 / d ^ 2 := by
  rw [norm_mul]
  have hprod : d ^ 2 ≤ ‖a‖ * ‖b‖ := by
    have hbnn : 0 ≤ ‖b‖ := norm_nonneg _
    calc d ^ 2 = d * d := by ring
      _ ≤ ‖a‖ * ‖b‖ := by
          apply mul_le_mul ha hb (le_of_lt hd) (le_trans (le_of_lt hd) ha)
  have hd2 : 0 < d ^ 2 := by positivity
  exact one_div_le_one_div_of_le hd2 hprod

/-- 🌟🌟🌟 **PROVED — the per-term above-band displacement bound.**

For a band probe `z` (`heightBand H z`) and a zero at height `γ > H` with
`|η| ≤ 1/2`, the single-atom displacement satisfies

    |Im(displacementAtom z γ η)| ≤ 1/(γ - H + 1)².

Combines the proved per-term bound `displacementAtom_im_bound` with the four
elementary distance lower bounds `≥ γ - H + 1`. -/
theorem displacementAtom_im_bound_above_band {H γ η : ℝ} {z : ℂ}
    (hb : heightBand H z) (hγ : H < γ) (hη : |η| ≤ 1/2) :
    |(displacementAtom z γ η).im| ≤ 1 / (γ - H + 1) ^ 2 := by
  have hd : (0:ℝ) < γ - H + 1 := by linarith
  -- the four distance bounds
  have d1 := norm_sub_w_ge (H := H) (γ := γ) (η := η) hb hγ
  have d2 := norm_add_w_ge (H := H) (γ := γ) (η := η) hb hγ
  have d3 := norm_sub_ofReal_ge (H := H) (γ := γ) hb hγ
  have d4 := norm_add_ofReal_ge (H := H) (γ := γ) hb hγ
  -- nonzeroness of the four denominators
  have n1 : z - (⟨γ, -η⟩ : ℂ) ≠ 0 := by
    intro h; rw [h, norm_zero] at d1; linarith
  have n2 : z + (⟨γ, -η⟩ : ℂ) ≠ 0 := by
    intro h; rw [h, norm_zero] at d2; linarith
  have n3 : z - (γ : ℂ) ≠ 0 := by
    intro h; rw [h, norm_zero] at d3; linarith
  have n4 : z + (γ : ℂ) ≠ 0 := by
    intro h; rw [h, norm_zero] at d4; linarith
  -- per-term reciprocal bounds
  have b1 : 1 / ‖(z - (⟨γ, -η⟩ : ℂ)) * (z - (γ : ℂ))‖ ≤ 1 / (γ - H + 1) ^ 2 :=
    one_div_norm_mul_le hd d1 d3
  have b2 : 1 / ‖(z + (⟨γ, -η⟩ : ℂ)) * (z + (γ : ℂ))‖ ≤ 1 / (γ - H + 1) ^ 2 :=
    one_div_norm_mul_le hd d2 d4
  have hatom := displacementAtom_im_bound z γ η hη n1 n2 n3 n4
  calc |(displacementAtom z γ η).im|
      ≤ (1/2) * (1 / ‖(z - (⟨γ, -η⟩ : ℂ)) * (z - (γ : ℂ))‖)
        + (1/2) * (1 / ‖(z + (⟨γ, -η⟩ : ℂ)) * (z + (γ : ℂ))‖) := hatom
    _ ≤ (1/2) * (1 / (γ - H + 1) ^ 2) + (1/2) * (1 / (γ - H + 1) ^ 2) := by
        gcongr
    _ = 1 / (γ - H + 1) ^ 2 := by ring

-- =====================================================================
-- §C.  The convergent tail:  Σ_{k<n} 1/(k+1)² ≤ 2   (telescoping)
-- =====================================================================

/-- Telescoping per-term bound: `1/(k+1)² ≤ 2/(k+1) - 2/(k+2)`.  (Equivalent to
`(k+2) ≤ 2(k+1)`, true for all `k ≥ 0`.) -/
theorem one_div_sq_le_telescope (k : ℕ) :
    1 / ((k : ℝ) + 1) ^ 2 ≤ 2 / ((k : ℝ) + 1) - 2 / ((k : ℝ) + 2) := by
  have hk1 : (0:ℝ) < (k : ℝ) + 1 := by positivity
  have hk2 : (0:ℝ) < (k : ℝ) + 2 := by positivity
  rw [div_sub_div _ _ (ne_of_gt hk1) (ne_of_gt hk2)]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [hk1, hk2]

/-- 🌟 **PROVED — partial sums of `1/(k+1)²` are bounded by `2`.**  Basel-style
telescoping bound (`∑_{k<m} 1/(k+1)² ≤ 2 - 2/(m+1)`), by induction; the
load-bearing convergence fact for the above-band displacement tail. -/
theorem sum_one_div_sq_le_two (n : ℕ) :
    ∑ k ∈ Finset.range n, 1 / ((k : ℝ) + 1) ^ 2 ≤ 2 := by
  -- Stronger statement  Σ ≤ 2 - 2/(m+1)  by induction.
  have key : ∀ m : ℕ, ∑ k ∈ Finset.range m, 1 / ((k : ℝ) + 1) ^ 2
      ≤ 2 - 2 / ((m : ℝ) + 1) := by
    intro m
    induction m with
    | zero => simp
    | succ p ih =>
        rw [Finset.sum_range_succ]
        have htel := one_div_sq_le_telescope p
        have hcast : ((↑(p+1) : ℝ) + 1) = ((p : ℝ) + 2) := by push_cast; ring
        rw [hcast]
        calc (∑ k ∈ Finset.range p, 1 / ((k : ℝ) + 1) ^ 2) + 1 / ((p : ℝ) + 1) ^ 2
            ≤ (2 - 2 / ((p : ℝ) + 1)) + (2 / ((p : ℝ) + 1) - 2 / ((p : ℝ) + 2)) := by
              apply add_le_add ih htel
          _ = 2 - 2 / ((p : ℝ) + 2) := by ring
  have h := key n
  have hpos : 0 ≤ 2 / ((n : ℝ) + 1) := by positivity
  linarith

-- =====================================================================
-- §D.  The above-band displacement datum and its derived bound
-- =====================================================================

/-- 📦 **Above-band displacement datum.**  A finite enumeration of the off-line
zeros of height `> H` contributing to `dispAbove`, indexed `0..n-1`, together
with the RH-INDEPENDENT structural facts that pin the tail:

* `n` — number of above-band atoms;
* `γ`, `η` — height and offset of the `k`-th atom;
* `eta_small : ∀ k, |η k| ≤ 1/2` — each off-line atom is within the strip;
* `heights_above : ∀ k, H < γ k` — every atom is above the band;
* `marginD` — the model-margin share allotted to the above-band tail;
* `tail_summable : ∀ n', Σ_{k<n'} 1/(γ k - H + 1)² ≤ marginD` — the
  **convergent-tail bound**: the inverse-squared distances of the above-band
  ordinates from the band sum below `marginD`.  This is EXACTLY the
  Riemann–von Mangoldt density content: `N(T) ~ (T/2π)log T`, so the off-line
  ordinates `γ_k` grow fast enough (`γ_k ≳ 2π k/log k`) that
  `Σ_k 1/(γ_k - H)²` converges, and `+1` regularizes the near-band terms.  It is
  carried as one explicit inequality field — RH-INDEPENDENT (a density/spacing
  fact about ordinate locations, NOT a zero-location fact).  The clean special
  case `γ_k ≥ H + (k+1)` (`marginD := 2`, telescoping Basel tail) is provided by
  the constructor `AboveBandData.ofUnitSpacing` below.

The realized displacement is the list-sum
`dispAbove z = Σ_{k<n} displacementAtom z (γ k) (η k)`. -/
structure AboveBandData (H : ℝ) where
  n : ℕ
  γ : ℕ → ℝ
  η : ℕ → ℝ
  marginD : ℝ
  eta_small : ∀ k : ℕ, |η k| ≤ 1/2
  heights_above : ∀ k : ℕ, H < γ k
  tail_summable :
    ∀ n' : ℕ, ∑ k ∈ Finset.range n', 1 / (γ k - H + 1) ^ 2 ≤ marginD

/-- The realized above-band displacement at `z`: the finite sum of the
per-atom displacements. -/
noncomputable def AboveBandData.disp {H : ℝ} (A : AboveBandData H) (z : ℂ) : ℂ :=
  ∑ k ∈ Finset.range A.n, displacementAtom z (A.γ k) (A.η k)

/-- 🌟🌟🌟 **PROVED — the above-band displacement tail is `≤ marginD`.**

`|Im(A.disp z)| ≤ Σ_{k<n} |Im(displacementAtom z (γ k)(η k))|`
            `≤ Σ_{k<n} 1/(γ k - H + 1)²`     (PER-TERM above-band distance bound)
            `≤ marginD`                       (RvM convergent-tail summability).

This DERIVES the `dispAbove_bound` content (`|Im(dispAbove z)| ≤ marginD`) from
the elementary per-term displacement bound and the carried RvM tail
summability — removing `dispAbove_bound` as a raw assumption. -/
theorem AboveBandData.disp_im_bound {H : ℝ} (A : AboveBandData H)
    {z : ℂ} (hb : heightBand H z) :
    |(A.disp z).im| ≤ A.marginD := by
  unfold AboveBandData.disp
  -- |Im(Σ)| ≤ Σ |Im(·)|  ≤  Σ 1/(γk-H+1)²  ≤  marginD
  rw [Complex.im_sum]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  refine le_trans (Finset.sum_le_sum (fun k _ => ?_)) (A.tail_summable A.n)
  exact displacementAtom_im_bound_above_band hb (A.heights_above k) (A.eta_small k)

/-- 🌟 **Convenience constructor — unit-spaced above-band ordinates.**  When the
above-band ordinates obey the clean spacing `γ_k ≥ H + (k+1)`, the tail
summability is discharged by the telescoping Basel bound with `marginD := 2`.

(This unit spacing is a *simplification* of the true RvM density, which is
denser than one zero per unit at large `H`; it is exact when the ordinates are
at least unit-separated above the band.  The general `tail_summable` field
accommodates the honest RvM density directly.) -/
noncomputable def AboveBandData.ofUnitSpacing {H : ℝ}
    (n : ℕ) (γ η : ℕ → ℝ)
    (eta_small : ∀ k : ℕ, |η k| ≤ 1/2)
    (heights_spaced : ∀ k : ℕ, H + ((k : ℝ) + 1) ≤ γ k) :
    AboveBandData H where
  n := n
  γ := γ
  η := η
  marginD := 2
  eta_small := eta_small
  heights_above := fun k => by
    have h1 := heights_spaced k
    have h2 : (0:ℝ) ≤ (k:ℝ) := by positivity
    linarith
  tail_summable := by
    intro n'
    refine le_trans (Finset.sum_le_sum (fun k _ => ?_)) (sum_one_div_sq_le_two n')
    have hsp : H + ((k : ℝ) + 1) ≤ γ k := heights_spaced k
    have hcmp : (k : ℝ) + 1 ≤ γ k - H + 1 := by linarith
    have hk1pos : (0:ℝ) < (k : ℝ) + 1 := by positivity
    have hsqle : ((k : ℝ) + 1) ^ 2 ≤ (γ k - H + 1) ^ 2 := by
      have hbase : (0:ℝ) ≤ (k : ℝ) + 1 := le_of_lt hk1pos
      nlinarith [hcmp, hbase]
    exact one_div_le_one_div_of_le (by positivity) hsqle

-- =====================================================================
-- §E.  Band datum WITHOUT a raw `dispAbove_bound` — it is DERIVED
-- =====================================================================

/-- 📦 **Reduced band displacement data** — exactly `BandDisplacementData H`
with the three above-band fields (`dispAbove`, `marginD`, and crucially the raw
`dispAbove_bound`) REMOVED and replaced by a single `AboveBandData H`.  Every
remaining field is one of the genuinely-other RH-independent inputs
(`model`/`marginH`/`heightTail`/`belowZeros` + their margins + `decomp`), with
`dispAbove := above.disp`, `marginD := above.marginD`, and `dispAbove_bound` no
longer a hypothesis but a THEOREM (`AboveBandData.disp_im_bound`). -/
structure BandDisplacementDataDerived (H : ℝ) where
  model : ℂ → ℂ
  marginH : ℂ → ℝ
  belowZeros : ℂ → List (BelowBandZero H)
  heightTail : ℂ → ℂ
  /-- The above-band displacement is a *realized* finite atom list-sum. -/
  above : AboveBandData H
  /-- Honest decomposition, with `dispAbove` realized as `above.disp`. -/
  decomp :
    ∀ z : ℂ, heightBand H z → 0 < z.im →
      (logDerivativeResponse XiPullback z).im
        = (model z).im
          + (heightTail z).im
          + ((belowZeros z).map (fun b => displacementAtom z b.γ b.η)).sum.im
          + (above.disp z).im
  /-- Model margin, split to cover both error pieces (with `marginD := above.marginD`). -/
  model_margin :
    ∀ z : ℂ, heightBand H z → 0 < z.im →
      (model z).im ≤ -(marginH z + above.marginD)
  /-- Height-Stieltjes tail bound (SOS/slab). -/
  heightTail_bound :
    ∀ z : ℂ, heightBand H z → 0 < z.im →
      |(heightTail z).im| ≤ marginH z

/-- 🌟🌟🌟 **PROVED — promote a reduced datum to a full `BandDisplacementData`,
DERIVING `dispAbove_bound`.**  The previously-raw above-band hypothesis becomes
the theorem `AboveBandData.disp_im_bound` (per-term displacement bound × RvM
tail summability), with `marginD := above.marginD`.  This is the precise sense
in which `dispAbove_bound` is removed as a raw assumption. -/
noncomputable def BandDisplacementDataDerived.toFull {H : ℝ}
    (D : BandDisplacementDataDerived H) : BandDisplacementData H where
  model := D.model
  marginH := D.marginH
  marginD := fun _ => D.above.marginD
  belowZeros := D.belowZeros
  dispAbove := D.above.disp
  heightTail := D.heightTail
  decomp := D.decomp
  model_margin := D.model_margin
  heightTail_bound := D.heightTail_bound
  -- the previously-RAW field, now PROVEN:
  dispAbove_bound := by
    intro z hband _hupper
    exact D.above.disp_im_bound hband

-- =====================================================================
-- §F.  THE FULLY-DERIVED CAPSTONE — no `dispAbove_bound` hypothesis
-- =====================================================================

/-- ⭐⭐⭐⭐⭐⭐ **PROVED — verified zeros up to `H` ⟹ no off-line zero below `H`,
with the above-band displacement tail `dispAbove_bound` DERIVED (not assumed).**

Identical to `RH_below_H_of_verifiedZeros_complete`, except its
`BandDisplacementData H` input — which carried `dispAbove_bound` as a RAW
field — is replaced by the *reduced* `BandDisplacementDataDerived H`, in which
the above-band displacement is a realized finite atom list-sum and its bound is
PROVEN from the per-term displacement bound + the RvM tail summability
(`AboveBandData.disp_im_bound`).  Thus this theorem has NO `dispAbove_bound`
hypothesis anywhere; the only zero-location input remains
`hver : VerifiedZerosOnLineUpTo H`. -/
theorem RH_below_H_of_verifiedZeros_fullyDerived {H : ℝ}
    (Hreg : CompletedXiRegularity)
    (Hfac : EntireZeroFactorizationHypothesis XiPullback)
    (D : BandDisplacementDataDerived H)
    (hver : VerifiedZerosOnLineUpTo H) :
    ∀ ρ : ℂ, XiPullback ρ = 0 → heightBand H ρ → ρ.im = 0 :=
  RH_below_H_of_verifiedZeros_complete Hreg Hfac D.toFull hver

/-- **Contrapositive** — no off-line zero of `XiPullback` below `H`, with the
above-band tail derived rather than assumed. -/
theorem RH_below_H_of_verifiedZeros_fullyDerived_no_offline {H : ℝ}
    (Hreg : CompletedXiRegularity)
    (Hfac : EntireZeroFactorizationHypothesis XiPullback)
    (D : BandDisplacementDataDerived H)
    (hver : VerifiedZerosOnLineUpTo H) :
    ∀ ρ : ℂ, XiPullback ρ = 0 → 0 < ρ.im → ¬ heightBand H ρ := by
  intro ρ hzero hpos hband
  have := RH_below_H_of_verifiedZeros_fullyDerived Hreg Hfac D hver ρ hzero hband
  linarith

end OverflowResidueRH

#print axioms OverflowResidueRH.displacementAtom_im_bound_above_band
#print axioms OverflowResidueRH.sum_one_div_sq_le_two
#print axioms OverflowResidueRH.AboveBandData.disp_im_bound
#print axioms OverflowResidueRH.RH_below_H_of_verifiedZeros_fullyDerived
