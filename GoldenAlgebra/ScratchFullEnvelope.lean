import rh

/-!
# ScratchFullEnvelope — the FULL-RANGE `concreteS` envelope from verified zeros + Backlund

## Goal

`ScratchTrueFluctuation.lean` de-vacuums the front-door fluctuation envelope by
routing through the TRUE fluctuation `concreteS u = N(u) − N₀(u)` (the genuine
ζ-zero count minus the smooth main term, `rh:7782`).  Its key hypothesis is the
`ConcreteSEnvelope` — a bound `|concreteS u| ≤ ½·log u + C` valid for the WHOLE
range `u ≥ T0` with `T0 ≤ 10`.

* On the **high range** `u ≥ 140` the project's proven Backlund/Turing theorem
  shape gives `|concreteS u| ≤ ½·log u + ½`
  (`BacklundTuringAnalyticInputs.concreteS_halfLogPlusHalf`, threshold `140`).
* The **low range** `[10, 140]` is the open piece this file CLOSES, from the
  **182 verified Backlund/Turing zeros**.

## The closure (this file)

On `[10, 140] ⊂ [10, 369]`, the 182-zero table certificate pins the EXACT zero
count: `N` is a step function with `N(140) = 48` (`count_eq_zeroUpperRat` at the
grid endpoint `0`, whose height is exactly `140`).  Because `N` is monotone and
`N₀` is monotone on `[2π, ∞)` (with `10 ≥ 2π`), on the compact `[10, 140]`:

    concreteS u = N(u) − N₀(u),
    0 ≤ N(u) ≤ N(140) = 48,        (monotone integer count, capped at 140)
    N₀(10) ≤ N₀(u) ≤ N₀(140) ≤ 70. (monotone smooth term, explicit bound)

Hence `−70 ≤ concreteS u ≤ 48 + 1/20 ≤ 49`, so `|concreteS u| ≤ 70` — an EXPLICIT
constant `C₀ = 70` on `[10, 140]`.  (The constant is loose-but-honest: `48 ≤ N₀(140)`
forces `C₀ ≥ 48`, and we round `N₀(140) ≤ 70` from a coarse `log(140/2π) ≤ 4` to
avoid sharp `π`/`exp` arithmetic.)

Combining the two pieces gives the **full-range** envelope
`|concreteS u| ≤ ½·log u + 70` on `[10, ∞)` (since on `[10,140]` the constant `70`
absorbs into `½·log u + 70`, and on `[140,∞)` the Backlund `½·log u + ½ ≤ ½·log u + 70`).

## Residual (honest)

* The **table certificate** `C` (which `count_eq_zeroUpperRat` consumes) is
  itself inhabited — in *existence* form — from `HardyZSignData` (the 182
  numerical sign-changes + Turing count/separation) via
  `ScratchZeroCert.bracketExistenceCertificate_of_data` ⟶ `.toTableCertificate`.
  We carry `C` as an explicit hypothesis here (those Scratch files are not
  registered as importable libs); the only genuine external input behind it is
  `HardyZSignData`.
* The **high range** `u ≥ 140` envelope is the project's proven Backlund/Turing
  bound, carried as the named hypothesis `HighEnvelope` (inhabited by
  `BacklundTuringAnalyticInputs.concreteS_halfLogPlusHalf`).

NEVER bare sorry/admit; every genuine gap is a named hypothesis with a docstring.
-/

open Filter Topology
open OverflowResidueRH
open OverflowResidueRH.BacklundTuring

namespace OverflowResidueRH.BacklundTuring.ScratchFullEnvelope

-- =====================================================================
-- §1. The verified count at height 140 from the 182-zero table certificate
-- =====================================================================

/-- ⭐ **PROVED — `N(140) = 48` from the table certificate.**
The grid endpoint of index `0` has height exactly `140`
(`backlundGrid2EndpointHeight … 0 = 140 + 2·0 = 140`), and the certificate's
`count_eq_zeroUpperRat` equates the weighted zero count there to the executable
table value `backlundGrid2EndpointCountFromZeroUpperRat … 0`, which evaluates
(`native_decide`) to `48`. -/
theorem count_140_eq_48
    (C : BacklundGrid2First182ZeroBracketTableCertificate140_369075049_1000000) :
    zetaWeightedZeroCountUpToHeight (140 : ℝ) (by norm_num) = 48 := by
  have h0 : backlundGrid2EndpointHeight140_369075049_1000000 ⟨0, by omega⟩ = 140 := by
    unfold backlundGrid2EndpointHeight140_369075049_1000000; norm_num
  have hcount := C.count_eq_zeroUpperRat ⟨0, by omega⟩
  have hval :
      backlundGrid2EndpointCountFromZeroUpperRat140_369075049_1000000 ⟨0, by omega⟩ = 48 := by
    rw [backlundGrid2EndpointCount_eq_zeroUpperRat_count140_369075049_1000000]
    native_decide
  rw [hval] at hcount
  have htrans := zetaWeightedZeroCountUpToHeight_eq_of_eq h0
    (backlundGrid2EndpointHeight140_369075049_1000000_nonneg ⟨0, by omega⟩)
    (by norm_num)
  rw [← htrans]; exact hcount

/-- ⭐ **PROVED — the count is `≤ 48` on `[10, 140]`.**
By monotonicity of the weighted count and the exact value `N(140) = 48`. -/
theorem count_le_48_on_low
    (C : BacklundGrid2First182ZeroBracketTableCertificate140_369075049_1000000)
    {u : ℝ} (hu10 : (10 : ℝ) ≤ u) (hu140 : u ≤ 140) :
    (zetaWeightedZeroCountUpToHeight u (by linarith) : ℝ) ≤ 48 := by
  have hmono :
      zetaWeightedZeroCountUpToHeight u (by linarith)
        ≤ zetaWeightedZeroCountUpToHeight (140 : ℝ) (by norm_num) :=
    zetaWeightedZeroCountUpToHeight_mono (by linarith) (by norm_num) hu140
  rw [count_140_eq_48 C] at hmono
  exact_mod_cast hmono

-- =====================================================================
-- §2. The smooth main term `N₀` is between explicit constants on `[10, 140]`
-- =====================================================================

/-- ⭐ **PROVED — `140/(2π) ≤ 23`.** From `π > 3.141592`. -/
theorem ratio_140_le_23 : (140 : ℝ) / (2 * Real.pi) ≤ 23 := by
  have hpi : (3.141592 : ℝ) < Real.pi := Real.pi_gt_d6
  rw [div_le_iff₀ (by positivity)]
  nlinarith [hpi]

/-- ⭐ **PROVED — `log(140/(2π)) ≤ 4`.**
Coarse: `140/(2π) ≤ 23 ≤ exp 4` (via `exp 1 > 2.71`, `2.71⁴ > 23`). -/
theorem log_ratio_140_le_4 : Real.log ((140 : ℝ) / (2 * Real.pi)) ≤ 4 := by
  have hratio_pos : 0 < (140 : ℝ) / (2 * Real.pi) := by positivity
  have h_e_gt : (2.71 : ℝ) < Real.exp 1 :=
    lt_trans (by norm_num : (2.71 : ℝ) < 2.7182818283) Real.exp_one_gt_d9
  have h_exp4_eq : Real.exp (4 : ℝ) = (Real.exp 1) ^ 4 := by
    have h := Real.exp_one_pow 4
    have h_cast : ((4 : ℕ) : ℝ) = (4 : ℝ) := by norm_num
    rw [← h_cast]; exact h.symm
  have h_pow_lt : (2.71 : ℝ) ^ 4 < (Real.exp 1) ^ 4 :=
    pow_lt_pow_left₀ h_e_gt (by norm_num) (by norm_num)
  have h23_le_exp4 : (23 : ℝ) ≤ Real.exp 4 := by
    rw [h_exp4_eq]; nlinarith [h_pow_lt]
  have hratio_le_exp4 : (140 : ℝ) / (2 * Real.pi) ≤ Real.exp 4 :=
    le_trans ratio_140_le_23 h23_le_exp4
  have h := Real.log_le_log hratio_pos hratio_le_exp4
  rwa [Real.log_exp] at h

/-- ⭐ **PROVED — `N₀(140) ≤ 70`.**
`N₀(140) = (140/2π)·log(140/2π) − 140/2π + 7/8 ≤ 23·4 − 0 + 7/8`?  More precisely
the upper-log-ratio bound gives `≤ (140/2π)·4 − 140/2π + 7/8 = 3·(140/2π) + 7/8
≤ 3·23 + 7/8 = 69.875 ≤ 70`. -/
theorem N0_140_le_70 : smoothMainTerm (140 : ℝ) ≤ 70 := by
  refine smoothMainTerm_upper_bound_of_log_ratio_upper (by norm_num)
    log_ratio_140_le_4 ?_
  -- (140/2π)·4 − 140/2π + 7/8 = 3·(140/2π) + 7/8 ≤ 3·23 + 7/8 ≤ 70
  have hratio : (140 : ℝ) / (2 * Real.pi) ≤ 23 := ratio_140_le_23
  have hratio_nonneg : 0 ≤ (140 : ℝ) / (2 * Real.pi) := by positivity
  nlinarith [hratio, hratio_nonneg]

/-- ⭐ **PROVED — `N₀` is sandwiched on `[10, 140]`.**
By `MonotoneOn smoothZeroCountingN0 (Ici (2π))` with `2π ≤ 10 ≤ u ≤ 140`. -/
theorem N0_sandwich_on_low {u : ℝ} (hu10 : (10 : ℝ) ≤ u) (hu140 : u ≤ 140) :
    smoothMainTerm 10 ≤ smoothMainTerm u ∧ smoothMainTerm u ≤ smoothMainTerm 140 := by
  have h_pi_lt_four : Real.pi < 4 := Real.pi_lt_four
  have h_2pi_le_10 : (2 * Real.pi : ℝ) ≤ 10 := by linarith
  have hmono := smoothZeroCountingN0_monotoneOn_Ici_two_pi
  have h10_mem : (10 : ℝ) ∈ Set.Ici (2 * Real.pi) := Set.mem_Ici.mpr h_2pi_le_10
  have hu_mem : u ∈ Set.Ici (2 * Real.pi) := Set.mem_Ici.mpr (by linarith)
  have h140_mem : (140 : ℝ) ∈ Set.Ici (2 * Real.pi) := Set.mem_Ici.mpr (by linarith)
  refine ⟨?_, ?_⟩
  · simpa [smoothMainTerm] using hmono h10_mem hu_mem hu10
  · simpa [smoothMainTerm] using hmono hu_mem h140_mem hu140

-- =====================================================================
-- §3. The [10,140] CONSTANT bound on `concreteS`, `C₀ = 70`
-- =====================================================================

/-- 🌟🌟🌟 **PROVED — the verified-zero CONSTANT bound on `[10, 140]`.**

From the 182-zero table certificate `C`:

    concreteS u = N(u) − N₀(u),  0 ≤ N(u) ≤ 48,  N₀(10) ≤ N₀(u) ≤ N₀(140) ≤ 70,

so `−70 ≤ concreteS u ≤ 48 − N₀(10) ≤ 48 + 1/20 < 70`, giving `|concreteS u| ≤ 70`.

This is the low-range piece of the full envelope: an explicit constant bound
that the `concreteS` Backlund work alone cannot supply (it only kicks in at
`u ≥ 140`), pinned here from the EXACT verified zero counts. -/
theorem concreteS_abs_le_70_on_low
    (C : BacklundGrid2First182ZeroBracketTableCertificate140_369075049_1000000)
    {u : ℝ} (hu10 : (10 : ℝ) ≤ u) (hu140 : u ≤ 140) :
    |concreteS u| ≤ 70 := by
  have hu0 : (0 : ℝ) ≤ u := by linarith
  -- concreteS u = N(u) − N₀(u)
  have hS : concreteS u
      = (zetaWeightedZeroCountUpToHeight u hu0 : ℝ) - smoothMainTerm u :=
    concreteS_eq_weighted_count_sub_smoothMainTerm hu0
  -- count facts
  have hNcount_le : (zetaWeightedZeroCountUpToHeight u hu0 : ℝ) ≤ 48 := by
    have := count_le_48_on_low C hu10 hu140
    -- proof-irrelevance of the nonnegativity witness
    simpa [zetaWeightedZeroCountUpToHeight_proof_irrel hu0 (by linarith)] using this
  have hNcount_nonneg : (0 : ℝ) ≤ (zetaWeightedZeroCountUpToHeight u hu0 : ℝ) := by
    positivity
  -- smooth facts
  obtain ⟨hN0_lo, hN0_hi⟩ := N0_sandwich_on_low hu10 hu140
  have hN0_140 : smoothMainTerm 140 ≤ 70 := N0_140_le_70
  have hN0_10_lo : -(1 / 20 : ℝ) ≤ smoothMainTerm 10 := by
    simpa [smoothMainTerm] using smoothZeroCountingN0_at_10_ge_neg_one_twentieth
  rw [abs_le]
  constructor
  · -- −70 ≤ concreteS u :  concreteS u ≥ 0 − N₀(u) ≥ −N₀(140) ≥ −70
    rw [hS]; nlinarith [hNcount_nonneg, hN0_hi, hN0_140]
  · -- concreteS u ≤ 70 :  concreteS u ≤ 48 − N₀(10) ≤ 48 + 1/20 < 70
    rw [hS]; nlinarith [hNcount_le, hN0_lo, hN0_10_lo]

-- =====================================================================
-- §4. The FULL-RANGE envelope: [10,140] verified ∪ [140,∞) Backlund
-- =====================================================================

/-- 📦 **`HighEnvelope`** — the PROVEN Backlund/Turing high-range envelope, in
hypothesis form: `∀ u ≥ 140, |concreteS u| ≤ ½·log u + ½`.  This is exactly the
conclusion of `BacklundTuringAnalyticInputs.concreteS_halfLogPlusHalf` at the
Backlund threshold `140` (`§4` inhabitant `highEnvelope_of_analyticInputs`). -/
def HighEnvelope : Prop :=
  ∀ {u : ℝ}, (140 : ℝ) ≤ u → |concreteS u| ≤ (1 / 2 : ℝ) * Real.log u + 1 / 2

/-- 🌟 **PROVED — `HighEnvelope` is INHABITED by the analytic package**, provided
its Backlund threshold is `≤ 140` (the project's threshold; e.g. the illustrative
`concreteS_halfLogPlusHalf_bound_from_140`).  Given a `BacklundTuringAnalyticInputs`
with `backlundGood.lower ≤ 140`, the half-log-plus-half output IS a `HighEnvelope`. -/
theorem highEnvelope_of_analyticInputs
    (I : BacklundTuringAnalyticInputs) (hlow : I.backlundGood.lower ≤ 140) :
    HighEnvelope :=
  fun hu => I.concreteS_halfLogPlusHalf (le_trans hlow hu)

/-- 📦 **`ConcreteSEnvelopeC lower C`** — the generalized-constant `concreteS`
envelope on `[lower, ∞)`: `|concreteS u| ≤ ½·log u + C`.  The `ScratchTrueFluctuation`
`ConcreteSEnvelope lower` is the `C = ½` special case (only available for `u ≥ 140`);
the full-range version below uses the larger verified-zero constant `C = 70`. -/
def ConcreteSEnvelopeC (lower C : ℝ) : Prop :=
  ∀ {u : ℝ}, lower ≤ u → |concreteS u| ≤ (1 / 2 : ℝ) * Real.log u + C

/-- 🌟🌟🌟🌟 **PROVED — the FULL-RANGE `concreteS` envelope on `[10, ∞)`.**

Assembles the two pieces:
* `[10, 140]` — the verified-zero constant bound `|concreteS u| ≤ 70` (§3).  Since
  `½·log u ≥ 0` for `u ≥ 10 ≥ 1`, `|concreteS u| ≤ 70 ≤ ½·log u + 70`.
* `[140, ∞)` — the Backlund `HighEnvelope` `½·log u + ½ ≤ ½·log u + 70`.

The result is `ConcreteSEnvelopeC 10 70`: `|concreteS u| ≤ ½·log u + 70` for ALL
`u ≥ 10`.  The only inputs are the table certificate `C` (verified zeros, low range)
and `HighEnvelope` (proven Backlund, high range). -/
theorem concreteSEnvelope_full
    (C : BacklundGrid2First182ZeroBracketTableCertificate140_369075049_1000000)
    (Hhigh : HighEnvelope) :
    ConcreteSEnvelopeC 10 70 := by
  intro u hu10
  by_cases hu140 : u ≤ 140
  · -- low range: constant bound absorbs into ½·log u + 70
    have hlow := concreteS_abs_le_70_on_low C hu10 hu140
    have hlog_nonneg : 0 ≤ (1 / 2 : ℝ) * Real.log u := by
      have : 0 ≤ Real.log u := Real.log_nonneg (by linarith)
      positivity
    linarith [hlow, hlog_nonneg]
  · -- high range: Backlund envelope, with ½ ≤ 70
    have hu140' : (140 : ℝ) ≤ u := by linarith [not_le.mp hu140]
    have hhi := Hhigh hu140'
    linarith [hhi]

-- =====================================================================
-- §5. Low-slab discharge — the `slabCD.1 = 0` slabs from the verified bound
-- =====================================================================
-- `rh`'s `slabCD` assigns coefficient `0` to the LOW slabs `T ≤ 32`, where the
-- envelope degenerates to a CONSTANT `(slabCD T).2`.  The §3 verified bound
-- `|concreteS u| ≤ 70` is itself constant — but it only holds on `[10, 140]`,
-- NOT for all `u ≥ T`.  The honest content of the discharge is therefore:
-- on the low slabs, RESTRICTED to the verified window `u ≤ 140`, the constant
-- envelope holds with constant `70`.  (For `u > 140` no constant bound on the
-- true fluctuation can hold — it grows like ½·log u — which is precisely why
-- `slabCD.1 = 0` for `T ≤ 32` is the architectural pressure point.)

/-- ⭐ **PROVED — `(slabCD T).2 = 1` on the slab `19 < T ≤ 32`.** -/
theorem slabCD_snd_19_32 {T : ℝ} (h19 : 19 < T) (h32 : T ≤ 32) :
    (slabCD T).2 = 1 := by
  unfold slabCD
  have h12 : ¬ T ≤ 12 := by linarith
  have h13 : ¬ T ≤ 13 := by linarith
  have h14 : ¬ T ≤ 14 := by linarith
  have h19' : ¬ T ≤ 19 := by linarith
  simp only [h12, h13, h14, h19', h32, if_true, if_false]

/-- 🌟🌟🌟 **PROVED — the low-slab CONSTANT envelope, on the verified window.**

On the low slab `19 < T ≤ 32` (`slabCD.1 = 0`, `slabCD.2 = 1`), the required
constant bound `|concreteS u| ≤ (slabCD T).2` does NOT hold (it would need
`|concreteS u| ≤ 1`, false already at `u = 140` where `N₀ ≈ 47`).  What the
verified zeros DO supply is the weaker constant `70`, valid on the verified
window `[T, 140]`.  This lemma states exactly that honest fact:

    ∀ u ∈ [T, 140],  |concreteS u| ≤ 70    (= the verified constant, NOT slabCD.2).

So the low-slab leg is discharged at the verified constant `70` on the verified
window — the genuine residual being that `rh`'s `slabCD.2 = 1` is SHARPER than
the verified bound can give, and that the window cannot extend past `140` for a
constant bound.  This pins precisely where the low slabs stand. -/
theorem lowSlab_const_envelope_on_window
    (C : BacklundGrid2First182ZeroBracketTableCertificate140_369075049_1000000)
    {T : ℝ} (h10 : (10 : ℝ) ≤ T) (_h32 : T ≤ 32)
    {u : ℝ} (hTu : T ≤ u) (hu140 : u ≤ 140) :
    |concreteS u| ≤ 70 :=
  concreteS_abs_le_70_on_low C (le_trans h10 hTu) hu140

-- =====================================================================
-- §6. Axiom audit — NO sorryAx
-- =====================================================================
#print axioms count_140_eq_48
#print axioms count_le_48_on_low
#print axioms N0_140_le_70
#print axioms N0_sandwich_on_low
#print axioms concreteS_abs_le_70_on_low
#print axioms highEnvelope_of_analyticInputs
#print axioms concreteSEnvelope_full
#print axioms slabCD_snd_19_32
#print axioms lowSlab_const_envelope_on_window

end OverflowResidueRH.BacklundTuring.ScratchFullEnvelope
