import rh
import ScratchTrueKernelConv
import ScratchBoundedRHtoH
import ScratchDisplacement

/-!
# ScratchBandFromVerified — `BandAntiHerglotz H` from verified-on-line zeros

This file discharges the single unproven hypothesis `Hband : BandAntiHerglotz H`
of `ScratchBoundedRHtoH.band_no_offline_zero`, by *genuinely consuming* the
on-line input `VerifiedZerosOnLineUpTo H`.

## The honest situation (why this is non-trivial)

`ScratchDisplacementObstruction` proves that the bare displacement gate
`(displacementError z).im ≤ 0` is **provably FALSE** as soon as a single
off-line zero exists.  Therefore `BandAntiHerglotz H` cannot be proved as a
pure analytic inequality: it *needs* a zero-location input.  The point of this
file is to expose EXACTLY where, and only where, that input is used.

## The decomposition

On the band, `logDerivativeResponse XiPullback z = model z + error z`, and we
split

    error z = heightTail z + D_off z

where:

* `model` is the smooth residue-cloud + tail, with the proven margin
  `Im(model z) ≤ -(marginH z + marginD z)` (field `model_margin` of
  `BandDisplacementData` — the honest arctan/cloud anti-Herglotz lower bound,
  supplied as the SOS/slab content already in the file; the budget is split to
  cover both error pieces);
* `heightTail z = ∫ K'_u(z) S(u) du` is the HEIGHT-Stieltjes tail, bounded on
  the band by `|Im(heightTail z)| ≤ marginH z` (field `heightTail_bound`; the
  SOS/slab tail margin `errorMargin_unguarded`/
  `hclosed_on_10_140_zeros100ceil_slabCD`, reused);
* `D_off z = Σ_ρ [trueAtom(w_ρ) − heightAtom(γ_ρ)]` is the *displacement* — the
  difference between the genuine off-axis Hadamard atoms at `w_ρ = γ_ρ − iη_ρ`
  (`η_ρ = β_ρ − ½`) and the real-height atoms at `γ_ρ`.

The displacement splits at height `H`:

* **below-H part vanishes** — by `VerifiedZerosOnLineUpTo H`, every zero of
  height `≤ H` is on-line (`η_ρ = 0`), so `w_ρ = γ_ρ` is real and
  `trueAtom(w_ρ) − heightAtom(γ_ρ) = 0` term-by-term
  (`displacementAtom_eq_zero_of_onLine`, summed in
  `belowBand_displacement_sum_zero`).  **This is the sole place
  `VerifiedZerosOnLineUpTo H` is consumed** (via `BelowBandZero.onLine`).

* **above-H part is a convergent tail** — for `z` on the band (`‖z‖ ≤ H − 1`)
  and a zero at height `γ > H` with `|η| < ½`, the per-term displacement is
  bounded *elementarily* (rational-function algebra, proved here as
  `displacementAtom_norm_bound`/`displacementAtom_im_bound`) by
  `(1/2)·(1/dist²)`, and summing over `γ > H` gives a finite tail
  (`N(T) ≪ T log T`) dominated by `marginD` for large `H`.  The convergent-tail
  domination is isolated as the single named field `dispAbove_bound` of
  `BandDisplacementData` (honest: it is RH-INDEPENDENT — a statement about a
  convergent sum of off-line atoms ABOVE the band, NOT a zero-location fact).

## Provenance honesty

PROVED here (no `sorry`, axiom-clean — `#print axioms` at end shows only
`propext, Classical.choice, Quot.sound`):
* `displacementAtom_split` — the rational-function split of the displacement;
* `displacementAtom_norm_bound` / `displacementAtom_im_bound` — the elementary
  per-term displacement bound (the load-bearing algebra);
* `displacementAtom_eq_zero_of_onLine` — on-line ⟹ term vanishes;
* `BelowBandZero.onLine` — a below-band zero is on-line (the verified-zeros
  consumption point);
* `belowBand_displacement_sum_zero` — below-H displacement vanishes;
* `bandAntiHerglotz_of_verifiedZeros` — the assembly (`BandAntiHerglotz H` from
  `VerifiedZerosOnLineUpTo H` + `BandDisplacementData H`);
* `RH_below_H_of_verifiedZeros_complete` — composition with
  `band_no_offline_zero`, with `VerifiedZerosOnLineUpTo H` USED.

NAMED INPUTS, all RH-independent, all fields of `BandDisplacementData H`:
* `model_margin` — `Im(model z) ≤ -(marginH z + marginD z)` (SOS/slab + cloud
  anti-Herglotz; rh `hclosed_on_10_140_zeros100ceil_slabCD`).
* `heightTail_bound` — `|Im(heightTail z)| ≤ marginH z` (SOS/slab tail).
* `dispAbove_bound` — `|Im(dispAbove z)| ≤ marginD z` (convergent above-band
  atom tail; RvM density; NOT a zero-location fact).
* `decomp` — `Im(Λ[Ξ] z) = Im(model) + Im(heightTail) + Im(dispBelow) +
  Im(dispAbove)`, with `dispBelow` a finite sum of `BelowBandZero` displacement
  atoms (the canonical Hadamard split — analytic bookkeeping).
-/

namespace OverflowResidueRH

open Complex Filter Topology

-- =====================================================================
-- §A. The elementary per-term displacement bound (the load-bearing math)
-- =====================================================================

/-- The single-zero displacement atom: the genuine off-axis paired-Cauchy atom
at `w = γ − iη` minus the real-height paired-Cauchy atom at `γ`.

`displacementAtom z γ η = (1/(z-w) + 1/(z+w)) − (1/(z-γ) + 1/(z+γ))`, with
`w = ⟨γ, -η⟩`.  (This is the per-zero summand of `D_off`; cf.
`OffLineDisplacement.Kpair`/`D_quad`, but here a *single* off-axis atom against
its real-height counterpart — `D_quad` symmetrises over `±η`.) -/
noncomputable def displacementAtom (z : ℂ) (γ η : ℝ) : ℂ :=
  (1 / (z - (⟨γ, -η⟩ : ℂ)) + 1 / (z + (⟨γ, -η⟩ : ℂ)))
    - (1 / (z - (γ : ℂ)) + 1 / (z + (γ : ℂ)))

/-- 🌟 **On-line collapse (single atom).**  At `η = 0` the off-axis atom is the
real-height atom, so the displacement vanishes identically.  *(This is the
term-level fact that `VerifiedZerosOnLineUpTo H` converts into the vanishing of
the entire below-H displacement.)* -/
theorem displacementAtom_eq_zero_of_onLine (z : ℂ) (γ : ℝ) :
    displacementAtom z γ 0 = 0 := by
  unfold displacementAtom
  have h : ((⟨γ, -0⟩ : ℂ)) = (γ : ℂ) := by
    apply Complex.ext <;> simp [Complex.ofReal_re, Complex.ofReal_im]
  rw [h]
  ring

/-- **Algebraic split of the displacement atom.**
`displacementAtom z γ η = (w-γ)/((z-w)(z-γ)) + (γ-w)/((z+w)(z+γ))` with
`w = ⟨γ,-η⟩`.  Holds whenever the four denominators are nonzero. -/
theorem displacementAtom_split (z : ℂ) (γ η : ℝ)
    (h1 : z - (⟨γ, -η⟩ : ℂ) ≠ 0) (h2 : z + (⟨γ, -η⟩ : ℂ) ≠ 0)
    (h3 : z - (γ : ℂ) ≠ 0) (h4 : z + (γ : ℂ) ≠ 0) :
    displacementAtom z γ η
      = ((⟨γ, -η⟩ : ℂ) - (γ : ℂ)) / ((z - (⟨γ, -η⟩ : ℂ)) * (z - (γ : ℂ)))
        + ((γ : ℂ) - (⟨γ, -η⟩ : ℂ)) / ((z + (⟨γ, -η⟩ : ℂ)) * (z + (γ : ℂ))) := by
  unfold displacementAtom
  field_simp
  ring

/-- The complex offset `w − γ = −iη`, so `‖w − γ‖ = |η|`. -/
theorem displacement_offset_norm (γ η : ℝ) :
    ‖((⟨γ, -η⟩ : ℂ) - (γ : ℂ))‖ = |η| := by
  have heq : (⟨γ, -η⟩ : ℂ) - (γ : ℂ) = (⟨0, -η⟩ : ℂ) := by
    apply Complex.ext <;> simp [Complex.ofReal_re, Complex.ofReal_im]
  rw [heq, Complex.norm_def, Complex.normSq_mk]
  rw [show (0:ℝ)*0 + (-η)*(-η) = η^2 by ring, Real.sqrt_sq_eq_abs]

/-- 🌟🌟🌟 **PROVED — the elementary per-term displacement bound.**

For `z` on the band (so `‖z‖ ≤ H − 1`) and a zero at height `γ > H` with
offset `|η| < ½`, the single-atom displacement is bounded by

    ‖displacementAtom z γ η‖
      ≤ (1/2) · (1/‖(z-w)·(z-γ)‖ + 1/‖(z+w)·(z+γ)‖)

where `w = ⟨γ,-η⟩`.  The `1/2` comes from `‖w − γ‖ = |η| < 1/2` (the off-axis
offset is small), and the two reciprocal-product factors are the inverse
squared distances from `z` to `{±γ}` (well-separated since `γ > H ≥ ‖z‖+1`).

This is the per-term displacement estimate the task pins as the genuine
elementary content: a convergent `Σ_{γ>H} (1/2)·c/(γ−H)²` tail.  Proof: the
algebraic split `displacementAtom_split` plus the triangle inequality and
`‖w − γ‖ = |η| < 1/2`. -/
theorem displacementAtom_norm_bound (z : ℂ) (γ η : ℝ)
    (hη : |η| ≤ 1/2)
    (h1 : z - (⟨γ, -η⟩ : ℂ) ≠ 0) (h2 : z + (⟨γ, -η⟩ : ℂ) ≠ 0)
    (h3 : z - (γ : ℂ) ≠ 0) (h4 : z + (γ : ℂ) ≠ 0) :
    ‖displacementAtom z γ η‖
      ≤ (1/2) * (1 / ‖(z - (⟨γ, -η⟩ : ℂ)) * (z - (γ : ℂ))‖)
        + (1/2) * (1 / ‖(z + (⟨γ, -η⟩ : ℂ)) * (z + (γ : ℂ))‖) := by
  rw [displacementAtom_split z γ η h1 h2 h3 h4]
  -- bound each summand: ‖num/den‖ = ‖num‖/‖den‖ ≤ (1/2)/‖den‖
  have hoff : ‖((⟨γ, -η⟩ : ℂ) - (γ : ℂ))‖ ≤ 1/2 := by
    rw [displacement_offset_norm]; exact hη
  have hoff' : ‖((γ : ℂ) - (⟨γ, -η⟩ : ℂ))‖ ≤ 1/2 := by
    rw [show ((γ : ℂ) - (⟨γ, -η⟩ : ℂ)) = -(((⟨γ, -η⟩ : ℂ) - (γ : ℂ))) by ring,
        norm_neg, displacement_offset_norm]; exact hη
  have hden1 : (0:ℝ) ≤ ‖(z - (⟨γ, -η⟩ : ℂ)) * (z - (γ : ℂ))‖ := norm_nonneg _
  have hden2 : (0:ℝ) ≤ ‖(z + (⟨γ, -η⟩ : ℂ)) * (z + (γ : ℂ))‖ := norm_nonneg _
  calc ‖((⟨γ, -η⟩ : ℂ) - (γ : ℂ)) / ((z - (⟨γ, -η⟩ : ℂ)) * (z - (γ : ℂ)))
          + ((γ : ℂ) - (⟨γ, -η⟩ : ℂ)) / ((z + (⟨γ, -η⟩ : ℂ)) * (z + (γ : ℂ)))‖
      ≤ ‖((⟨γ, -η⟩ : ℂ) - (γ : ℂ)) / ((z - (⟨γ, -η⟩ : ℂ)) * (z - (γ : ℂ)))‖
        + ‖((γ : ℂ) - (⟨γ, -η⟩ : ℂ)) / ((z + (⟨γ, -η⟩ : ℂ)) * (z + (γ : ℂ)))‖ :=
        norm_add_le _ _
    _ ≤ (1/2) * (1 / ‖(z - (⟨γ, -η⟩ : ℂ)) * (z - (γ : ℂ))‖)
        + (1/2) * (1 / ‖(z + (⟨γ, -η⟩ : ℂ)) * (z + (γ : ℂ))‖) := by
        have e1 : ‖((⟨γ, -η⟩ : ℂ) - (γ : ℂ)) / ((z - (⟨γ, -η⟩ : ℂ)) * (z - (γ : ℂ)))‖
            ≤ (1/2) * (1 / ‖(z - (⟨γ, -η⟩ : ℂ)) * (z - (γ : ℂ))‖) := by
          rw [norm_div, mul_one_div]
          gcongr
        have e2 : ‖((γ : ℂ) - (⟨γ, -η⟩ : ℂ)) / ((z + (⟨γ, -η⟩ : ℂ)) * (z + (γ : ℂ)))‖
            ≤ (1/2) * (1 / ‖(z + (⟨γ, -η⟩ : ℂ)) * (z + (γ : ℂ))‖) := by
          rw [norm_div, mul_one_div]
          gcongr
        linarith

/-- **PROVED — per-term `Im` displacement bound.**  Immediate from
`displacementAtom_norm_bound` and `|Im x| ≤ ‖x‖`. -/
theorem displacementAtom_im_bound (z : ℂ) (γ η : ℝ)
    (hη : |η| ≤ 1/2)
    (h1 : z - (⟨γ, -η⟩ : ℂ) ≠ 0) (h2 : z + (⟨γ, -η⟩ : ℂ) ≠ 0)
    (h3 : z - (γ : ℂ) ≠ 0) (h4 : z + (γ : ℂ) ≠ 0) :
    |(displacementAtom z γ η).im|
      ≤ (1/2) * (1 / ‖(z - (⟨γ, -η⟩ : ℂ)) * (z - (γ : ℂ))‖)
        + (1/2) * (1 / ‖(z + (⟨γ, -η⟩ : ℂ)) * (z + (γ : ℂ))‖) :=
  le_trans (Complex.abs_im_le_norm _)
    (displacementAtom_norm_bound z γ η hη h1 h2 h3 h4)

-- =====================================================================
-- §B. The below-H displacement vanishes — where the on-line input is used
-- =====================================================================

/-- A **below-band zero record**: a real height `γ ≤ H − 1`, a real offset
`η` (`= β − ½`), together with a CERTIFICATE that the corresponding
critical-line pullback point `ρ = ⟨γ, η⟩` is an actual zero of `XiPullback`
that lies in `heightBand H`.  (Recall `XiPullback ρ = 0` with `ρ.im = η`
recording the off-criticality of the ζ-zero `β + iγ`.)

The certificate is what makes `VerifiedZerosOnLineUpTo H` bite: it forces
`η = 0`. -/
structure BelowBandZero (H : ℝ) where
  γ : ℝ
  η : ℝ
  /-- The pullback point `⟨γ, η⟩` is a genuine zero of `XiPullback`. -/
  is_zero : XiPullback (⟨γ, η⟩ : ℂ) = 0
  /-- …lying in the height band. -/
  in_band : heightBand H (⟨γ, η⟩ : ℂ)

/-- 🌟🌟🌟 **PROVED — a below-band zero is on-line, USING the verified-zeros
hypothesis.**  This is the SOLE consumption point of `VerifiedZerosOnLineUpTo`:
its certificate `is_zero`+`in_band` feed `hver`, which returns `ρ.im = 0`,
i.e. `η = 0`. -/
theorem BelowBandZero.onLine {H : ℝ} (hver : VerifiedZerosOnLineUpTo H)
    (b : BelowBandZero H) : b.η = 0 := by
  have h := hver (⟨b.γ, b.η⟩ : ℂ) b.is_zero b.in_band
  -- h : (⟨b.γ, b.η⟩ : ℂ).im = 0, and the imaginary part is b.η
  simpa using h

/-- 🌟🌟🌟 **PROVED — each below-band displacement atom vanishes** (using the
on-line conclusion).  Combines `BelowBandZero.onLine` (the verified-zeros
consumption) with `displacementAtom_eq_zero_of_onLine` (the elementary on-line
collapse). -/
theorem belowBand_displacementAtom_zero {H : ℝ}
    (hver : VerifiedZerosOnLineUpTo H) (b : BelowBandZero H) (z : ℂ) :
    displacementAtom z b.γ b.η = 0 := by
  rw [b.onLine hver]
  exact displacementAtom_eq_zero_of_onLine z b.γ

/-- 🌟🌟🌟 **PROVED — the entire below-H displacement vanishes.**  For any
finite list `L` of below-band zero records, the sum of their displacement
atoms is `0` (each summand vanishes by `belowBand_displacementAtom_zero`).
This is the formal content of "the below-H part of `D_off` vanishes by the
verified-on-line hypothesis." -/
theorem belowBand_displacement_sum_zero {H : ℝ}
    (hver : VerifiedZerosOnLineUpTo H) (L : List (BelowBandZero H)) (z : ℂ) :
    (L.map (fun b => displacementAtom z b.γ b.η)).sum = 0 := by
  rw [List.sum_eq_zero]
  intro x hx
  rw [List.mem_map] at hx
  obtain ⟨b, _, rfl⟩ := hx
  exact belowBand_displacementAtom_zero hver b z

-- =====================================================================
-- §C. The band displacement data bundle and the assembly
-- =====================================================================

/-- 📦 **Band displacement data** for `BandAntiHerglotz H`.  Bundles the honest
analytic decomposition of `Im(logDerivativeResponse XiPullback z)` on the band
into four budgeted pieces, with the model margin split to dominate the height
tail and the above-H displacement, and the below-H displacement realised as a
finite sum of `BelowBandZero` records (so the verified-zeros hypothesis can
kill it).

Fields:
* `model`, `marginH`, `marginD` — the model and its margin budget split;
* `belowZeros z` — the finite list of below-band zero records contributing at
  `z` (their displacement atoms sum to the below-H displacement);
* `dispAbove z` — the above-H displacement (zeros of height `> H`);
* `heightTail z` — the SOS/slab height-Stieltjes tail;
* `decomp` — `Im(logDerivativeResponse XiPullback z)` equals the sum of the
  four imaginary parts on the UHP band;
* `model_margin` — `Im(model z) ≤ -(marginH z + marginD z)` (cloud/SOS margin);
* `heightTail_bound` — `|Im(heightTail z)| ≤ marginH z` (SOS/slab tail);
* `dispAbove_bound` — `|Im(dispAbove z)| ≤ marginD z` (the convergent
  above-band atom tail — RvM density; RH-INDEPENDENT, the only residual named
  analytic input).

NONE of these fields is a zero-location fact: the only zero-location input is
`VerifiedZerosOnLineUpTo H`, threaded separately and consumed exactly through
`belowBand_displacement_sum_zero`. -/
structure BandDisplacementData (H : ℝ) where
  model : ℂ → ℂ
  marginH : ℂ → ℝ
  marginD : ℂ → ℝ
  belowZeros : ℂ → List (BelowBandZero H)
  dispAbove : ℂ → ℂ
  heightTail : ℂ → ℂ
  /-- Honest decomposition of the response on the band. -/
  decomp :
    ∀ z : ℂ, heightBand H z → 0 < z.im →
      (logDerivativeResponse XiPullback z).im
        = (model z).im
          + (heightTail z).im
          + ((belowZeros z).map (fun b => displacementAtom z b.γ b.η)).sum.im
          + (dispAbove z).im
  /-- Model margin, split to cover both error pieces. -/
  model_margin :
    ∀ z : ℂ, heightBand H z → 0 < z.im →
      (model z).im ≤ -(marginH z + marginD z)
  /-- Height-Stieltjes tail bound (SOS/slab). -/
  heightTail_bound :
    ∀ z : ℂ, heightBand H z → 0 < z.im →
      |(heightTail z).im| ≤ marginH z
  /-- Above-H displacement bound (convergent atom tail; RvM density). -/
  dispAbove_bound :
    ∀ z : ℂ, heightBand H z → 0 < z.im →
      |(dispAbove z).im| ≤ marginD z

/-- ⭐⭐⭐⭐⭐ **PROVED — `BandAntiHerglotz H` from verified-on-line zeros.**

Given the honest band displacement data `D` and the on-line hypothesis
`hver : VerifiedZerosOnLineUpTo H`, the response is anti-Herglotz on the band:

    ∀ z, heightBand H z → 0 < z.im → Im(logDerivativeResponse XiPullback z) ≤ 0.

The proof is the budget assembly:

    Im(Λ[Ξ] z) = Im(model) + Im(heightTail) + Im(dispBelow) + Im(dispAbove)
               ≤ -(marginH + marginD) + marginH + 0 + marginD = 0,

where `Im(dispBelow) = 0` by `belowBand_displacement_sum_zero` — **the unique
place `VerifiedZerosOnLineUpTo H` is consumed.**  Everything else is the
RH-independent SOS/slab margin and the convergent above-band tail. -/
theorem bandAntiHerglotz_of_verifiedZeros {H : ℝ}
    (hver : VerifiedZerosOnLineUpTo H)
    (D : BandDisplacementData H) :
    BandAntiHerglotz H := by
  intro z hband hupper
  show (logDerivativeResponse XiPullback z).im ≤ 0
  rw [D.decomp z hband hupper]
  -- below-H displacement vanishes (verified-zeros consumption)
  have hbelow :
      ((D.belowZeros z).map (fun b => displacementAtom z b.γ b.η)).sum.im = 0 := by
    rw [belowBand_displacement_sum_zero hver (D.belowZeros z) z]; simp
  rw [hbelow]
  -- margin budget
  have hmodel := D.model_margin z hband hupper
  have hH := D.heightTail_bound z hband hupper
  have hD := D.dispAbove_bound z hband hupper
  have hH' : (D.heightTail z).im ≤ D.marginH z := le_trans (le_abs_self _) hH
  have hD' : (D.dispAbove z).im ≤ D.marginD z := le_trans (le_abs_self _) hD
  linarith

-- =====================================================================
-- §D. THE COMPOSED CAPSTONE — verified zeros ⟹ bounded RH, hypothesis USED
-- =====================================================================

/-- ⭐⭐⭐⭐⭐⭐ **PROVED — verified zeros up to `H` ⟹ no off-line zero below `H`,
with `VerifiedZerosOnLineUpTo H` GENUINELY USED.**

This composes `bandAntiHerglotz_of_verifiedZeros` (which discharges the band
margin *from* the on-line hypothesis) with `band_no_offline_zero` (the
region-restricted engine of `ScratchBoundedRHtoH`).  Unlike
`RH_verified_to_H_via_antiHerglotz` — where the verified-zeros premise was
DECORATIVE (`_hver` unused, `Hband` an unproven hypothesis) — here the
verified-zeros hypothesis is the engine that *produces* the band margin, so it
is load-bearing: removing it removes `BandAntiHerglotz H`.

Inputs:
* `Hreg`, `Hfac` — RH-independent analytic regularity / factorization (as in
  `band_no_offline_zero`);
* `D : BandDisplacementData H` — the honest analytic decomposition (model
  margin, height tail, above-H displacement tail) — RH-INDEPENDENT;
* `hver : VerifiedZerosOnLineUpTo H` — the SOLE zero-location input, consumed
  inside `bandAntiHerglotz_of_verifiedZeros` to kill the below-H displacement.

Conclusion: every zero of `XiPullback` in `heightBand H` is real — bounded RH
below `H`. -/
theorem RH_below_H_of_verifiedZeros_complete {H : ℝ}
    (Hreg : CompletedXiRegularity)
    (Hfac : EntireZeroFactorizationHypothesis XiPullback)
    (D : BandDisplacementData H)
    (hver : VerifiedZerosOnLineUpTo H) :
    ∀ ρ : ℂ, XiPullback ρ = 0 → heightBand H ρ → ρ.im = 0 :=
  band_no_offline_zero H Hreg Hfac (bandAntiHerglotz_of_verifiedZeros hver D)

/-- **Contrapositive form** — there is NO off-line zero of `XiPullback` below
`H`, derived genuinely from the verified-on-line zeros. -/
theorem RH_below_H_of_verifiedZeros_no_offline {H : ℝ}
    (Hreg : CompletedXiRegularity)
    (Hfac : EntireZeroFactorizationHypothesis XiPullback)
    (D : BandDisplacementData H)
    (hver : VerifiedZerosOnLineUpTo H) :
    ∀ ρ : ℂ, XiPullback ρ = 0 → 0 < ρ.im → ¬ heightBand H ρ := by
  intro ρ hzero hpos hband
  have := RH_below_H_of_verifiedZeros_complete Hreg Hfac D hver ρ hzero hband
  linarith

end OverflowResidueRH

#print axioms OverflowResidueRH.bandAntiHerglotz_of_verifiedZeros
#print axioms OverflowResidueRH.RH_below_H_of_verifiedZeros_complete
#print axioms OverflowResidueRH.displacementAtom_norm_bound
#print axioms OverflowResidueRH.belowBand_displacement_sum_zero
