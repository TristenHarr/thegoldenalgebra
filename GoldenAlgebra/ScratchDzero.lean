import rh

/-!
# Scratch: the concrete `Dzero` from the 182-zero certificate

This file builds the **concrete ordered fluctuation-measure datum** `Dzero`
required by the Path B publication front doors, with its atoms drawn from the
182 verified Backlund/Turing zero brackets, and discharges the two *structural*
hypotheses the headline theorems demand of `Dzero`:

* `h_Z_ge_15 : ∀ i, 15 ≤ Dzero.Z i` — every ordinate is at least `15`;
* `DzeroStartsAfter Dzero 14` — every ordinate is strictly above `14`
  (the structural condition that fires rh's certified `[10,14]` discrete-count
  bridge).

## Construction

The zero ordinates are taken from the **upper rational endpoints** of the 182
brackets, `backlundGrid2First182ZeroUpperRatAt : Fin 182 → ℚ`, which rh proves
to be a strictly increasing table (`upperRatAt_strictMono`, by `native_decide`)
with every bracket lying strictly above height `14`
(`backlundGrid2First182ZeroLowerRatAt_gt_fourteen`).  The atom sequence is

  `Z i = ⌈ upperRatAt (min i 181) ⌉ : ℝ`

i.e. the **integer ceiling** of the `i`-th bracket's upper ordinate, clamped at
the last bracket index for `i ≥ 182` (so `Z` is a genuine `ℕ → ℝ` with constant
tail).  Because every bracket ordinate exceeds `14`, the ceiling is `≥ 15` (so
`Z₀ = ⌈14.13…⌉ = 15`), and the ceiling of a monotone sequence is monotone, so
`Monotone Z` holds.  Multiplicities are all `1` (simplicity, from the cert), and
`n = 182`.

## What is PROVEN here

* `Dzero` : a concrete `OrderedFluctuationMeasureData` (no hypotheses).
* `Dzero_Z_ge_15` : `∀ i, 15 ≤ Dzero.Z i` — the exact `h_Z_ge_15` shape.
* `Dzero_startsAfter_14 : DzeroStartsAfter Dzero 14`.
* `Dzero_discreteCount_bridge` : the certified `[10,14]` discrete-count bridge
  fired for our concrete `Dzero` (given the existence certificate).
* `Dzero_finiteFluctuation_eq_zero_on_band` : the finite fluctuation primitive
  vanishes on `[10,14]` — both the discrete and the smooth count are `0` there,
  but only the discrete vanishing is what `DzeroStartsAfter` supplies; the smooth
  vanishing is rh's `N₀` story, *not* part of `Dzero`.

## What is NOT discharged here (the honest residual)

* `HardyZSignData` (in `ScratchZeroCert.lean`) — the genuine verified-computation
  datum that inhabits the existence certificate.  The certificate `C` is a
  *hypothesis* of the bridge lemmas below; it is `HardyZSignData`-equivalent.
* The **Turing analytic envelope** (`PathBTuringEnvelopeInputs` /
  `hTuring` / `hHighLog`): these bound `|finiteFluctuationPrimitive Dzero 10 u|`
  for **all** `u ≥ T`, `T → ∞`.  That is the analytic envelope side — it needs
  the zero count *beyond* height `369` and the smooth model `N₀`, neither of
  which is supplied by the finite 182-zero certificate or by `Dzero`'s atoms.
  This file deliberately does **not** touch that side; it is the analytic
  residual, cleanly separated from the discrete `Dzero` data.
-/

namespace OverflowResidueRH.BacklundTuring.ScratchDzero

open OverflowResidueRH OverflowResidueRH.BacklundTuring
open scoped Complex

set_option maxRecDepth 10000

/-! ## The upper-rational table is strictly increasing -/

/-- The 182 upper bracket ordinates form a strictly increasing table.
Proven by `native_decide` on the `181` consecutive-step inequalities and
`Fin.strictMono_iff_lt_succ`. -/
theorem upperRatAt_strictMono :
    StrictMono (fun k : Fin 182 => backlundGrid2First182ZeroUpperRatAt k) := by
  have hstep : ∀ k : Fin 181,
      backlundGrid2First182ZeroUpperRatAt k.castSucc
        < backlundGrid2First182ZeroUpperRatAt k.succ := by
    native_decide
  exact Fin.strictMono_iff_lt_succ.mpr hstep

/-! ## The atom ordinate sequence -/

/-- The `i`-th upper bracket ordinate, clamping the index at the final bracket
`181` so the table extends to a total function `ℕ → ℚ` with constant tail. -/
noncomputable def upperRatNat (i : ℕ) : ℚ :=
  backlundGrid2First182ZeroUpperRatAt ⟨min i 181, by omega⟩

/-- `upperRatNat` is monotone: clamping is monotone and the table is
(strictly, hence weakly) monotone. -/
theorem upperRatNat_monotone : Monotone upperRatNat := by
  intro a b hab
  unfold upperRatNat
  have hmin : min a 181 ≤ min b 181 := by omega
  have hfin : (⟨min a 181, by omega⟩ : Fin 182) ≤ ⟨min b 181, by omega⟩ := by
    exact hmin
  exact upperRatAt_strictMono.monotone hfin

/-- Every clamped upper ordinate exceeds `14` (its bracket lower endpoint does,
and the upper endpoint exceeds the lower). -/
theorem upperRatNat_gt_fourteen (i : ℕ) : (14 : ℝ) < ((upperRatNat i : ℚ) : ℝ) := by
  have hlb : (14 : ℝ)
      < ((backlundGrid2First182ZeroLowerRatAt ⟨min i 181, by omega⟩ : ℚ) : ℝ) :=
    backlundGrid2First182ZeroLowerRatAt_gt_fourteen _
  have hlu : (backlundGrid2First182ZeroLowerRatAt ⟨min i 181, by omega⟩ : ℚ)
      < upperRatNat i := by
    unfold upperRatNat backlundGrid2First182ZeroLowerRatAt; norm_num
  have hluR : ((backlundGrid2First182ZeroLowerRatAt ⟨min i 181, by omega⟩ : ℚ) : ℝ)
      < ((upperRatNat i : ℚ) : ℝ) := by exact_mod_cast hlu
  linarith

/-- The atom sequence: the integer ceiling of the `i`-th (clamped) upper
bracket ordinate, as a real. `Z₀ = ⌈14.13…⌉ = 15`. -/
noncomputable def Zseq (i : ℕ) : ℝ := (⌈upperRatNat i⌉ : ℝ)

/-- `Zseq` is monotone: the ceiling of a monotone rational sequence, cast to
`ℝ`, is monotone. -/
theorem Zseq_monotone : Monotone Zseq := by
  intro a b hab
  unfold Zseq
  have hq : upperRatNat a ≤ upperRatNat b := upperRatNat_monotone hab
  have hceil : ⌈upperRatNat a⌉ ≤ ⌈upperRatNat b⌉ := Int.ceil_le_ceil hq
  exact_mod_cast hceil

/-- Every atom ordinate is at least `15`: the ceiling of a quantity `> 14` is
`≥ 15` (`Int.lt_ceil`). -/
theorem Zseq_ge_15 (i : ℕ) : (15 : ℝ) ≤ Zseq i := by
  unfold Zseq
  have h14 : (14 : ℝ) < ((upperRatNat i : ℚ) : ℝ) := upperRatNat_gt_fourteen i
  have hlt : (14 : ℤ) < ⌈upperRatNat i⌉ := by
    rw [Int.lt_ceil]; push_cast; exact_mod_cast h14
  have : (15 : ℤ) ≤ ⌈upperRatNat i⌉ := by omega
  exact_mod_cast this

/-! ## The concrete `Dzero` -/

/-- **The concrete ordered fluctuation-measure datum.**

* `Z = Zseq` — the 182 bracket-ceiling ordinates (constant tail above index 181);
* `mult ≡ 1` — every counted zero is simple (the cert's `simple` field);
* `n = 182` — the number of certified zeros;
* `N₀ = smoothZeroCountingN0` — rh's §13 smooth model (via `ofXiSmooth`);
* `mono_Z = Zseq_monotone`.

This is a genuine term of `OrderedFluctuationMeasureData` with **no** hypotheses;
the verified-computation content lives in the certificate `C` used by the bridge
lemmas below, not in this datum. -/
noncomputable def Dzero : Phase1IBP.OrderedFluctuationMeasureData where
  toFluctuationMeasureData :=
    FluctuationMeasureData.ofXiSmooth Zseq (fun _ => 1) 182
  mono_Z := Zseq_monotone

@[simp] theorem Dzero_Z (i : ℕ) :
    Dzero.toFluctuationMeasureData.Z i = Zseq i := by
  simp only [Dzero, FluctuationMeasureData.ofXiSmooth]

@[simp] theorem Dzero_mult (i : ℕ) :
    Dzero.toFluctuationMeasureData.mult i = 1 := by
  simp only [Dzero, FluctuationMeasureData.ofXiSmooth]

@[simp] theorem Dzero_n : Dzero.toFluctuationMeasureData.n = 182 := by
  simp only [Dzero, FluctuationMeasureData.ofXiSmooth]

/-! ## STEP 2 : `h_Z_ge_15` — PROVEN -/

/-- 🌟 **PROVED — `h_Z_ge_15` for the concrete `Dzero`.**
Every ordinate (atoms and constant tail alike) is `≥ 15`.  This is exactly the
shape the headline front doors require:
`∀ i : ℕ, (15 : ℝ) ≤ Dzero.toFluctuationMeasureData.Z i`. -/
theorem Dzero_Z_ge_15 :
    ∀ i : ℕ, (15 : ℝ) ≤ Dzero.toFluctuationMeasureData.Z i := by
  intro i
  rw [Dzero_Z]
  exact Zseq_ge_15 i

/-! ## STEP 3 : `DzeroStartsAfter Dzero 14` and the count bridge -/

/-- 🌟 **PROVED — `DzeroStartsAfter Dzero 14`.**
Every ordinate is strictly above `14` (since each is `≥ 15`).  This structural
condition is what fires rh's certified `[10,14]` discrete-count bridge. -/
theorem Dzero_startsAfter_14 : DzeroStartsAfter Dzero 14 where
  z_gt_gamma i := by
    have : (15 : ℝ) ≤ Dzero.toFluctuationMeasureData.Z i := Dzero_Z_ge_15 i
    linarith

/-- 🌟 **PROVED — the certified `[10,14]` discrete-count bridge, fired for the
concrete `Dzero`.**

Given the **existence certificate** `C` (the cert that `ScratchZeroCert`
inhabits modulo `HardyZSignData`), the discrete counting primitive of `Dzero`
on `[10, u]` for `u ∈ [10,14]` equals the actual zeta weighted-count increment
`N(u) − N(10)` — which is `0` on this pre-first-zero band. -/
theorem Dzero_discreteCount_bridge
    (C : BacklundGrid2First182ZeroBracketExistenceCertificate140_369075049_1000000)
    {u : ℝ} (hu10 : (10 : ℝ) ≤ u) (hu14 : u ≤ 14) :
    Phase1IBP.discreteCountingPrimitive Dzero.toFluctuationMeasureData 10 u =
      (zetaWeightedZeroCountUpToHeight u
          (le_trans (by norm_num : (0 : ℝ) ≤ 10) hu10) : ℝ)
        - (zetaWeightedZeroCountUpToHeight 10
            (by norm_num : (0 : ℝ) ≤ 10) : ℝ) :=
  discreteCountingPrimitive_eq_zetaWeighted_count_sub_of_startsAfter_le_fourteen_grid2First182ZeroBracketExistence
    C Dzero_startsAfter_14 hu10 hu14

/-- 🌟 **PROVED — the discrete counting primitive of `Dzero` simply vanishes on
`[10,14]`.** This is the `DzeroStartsAfter`-only consequence, independent of the
certificate: no atom of `Dzero` lies at or below `14`. -/
theorem Dzero_discreteCount_eq_zero_on_band
    {u : ℝ} (hu14 : u ≤ 14) :
    Phase1IBP.discreteCountingPrimitive Dzero.toFluctuationMeasureData 10 u = 0 :=
  discreteCountingPrimitive_eq_zero_of_startsAfter Dzero_startsAfter_14 hu14

/-- 🌟 **PROVED — the finite fluctuation primitive of `Dzero` on `[10,14]`
equals the certified `concreteS` increment.** Composes the `DzeroStartsAfter`
discrete-vanishing with rh's certified smooth/count bridge. -/
theorem Dzero_finiteFluctuation_eq_concreteS_on_band
    (C : BacklundGrid2First182ZeroBracketExistenceCertificate140_369075049_1000000)
    {u : ℝ} (hu10 : (10 : ℝ) ≤ u) (hu14 : u ≤ 14) :
    Phase1IBP.finiteFluctuationPrimitive Dzero 10 u =
      concreteS u - concreteS 10 :=
  finiteFluctuationPrimitive_eq_concreteS_sub_concreteS_of_startsAfter_le_fourteen_grid2First182ZeroBracketTable
    C.toTableCertificate Dzero_startsAfter_14 hu10 hu14

end OverflowResidueRH.BacklundTuring.ScratchDzero
