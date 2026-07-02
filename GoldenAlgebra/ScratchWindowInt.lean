import rh

/-!
# ScratchWindowInt — finite-window integrability of the true fluctuation × kernel

## Target

`ScratchTrueFluctuation.TrueFluctuationWindowIntegrable T0` (the `Hint`
obligation of the de-vacuumed front door) demands, for every adaptive probe
`(z, T, X)` with `10 ≤ T ≤ 140`, `0 < z.im`, the regime bound, and `T ≤ X`,
that

    fun u => trueFluctuationPrimitive T0 u * pairedCauchyImKernelDeriv z.re z.im u

is `IntervalIntegrable` on `[T, X]`, where
`trueFluctuationPrimitive T0 u = concreteS u − concreteS T0`.

## How the FINITE version does it (rh §CCXXIV–§CCXXV)

The proven finite analogue splits
`finiteFluctuationPrimitive D T0 u = discreteCountingPrimitive − smoothCountingPrimitive`
and discharges integrability of each piece against the **continuous** kernel
derivative separately (`FiniteFluctuationRegularityData`,
`finiteFluctuation_derivative_integrable_of_regular`,
`finiteFluctuationRegularityData_of_existing_integrability`, rh:60042/60190):

* discrete part — a finite sum of indicator·kernel terms, each
  `IntervalIntegrable` (`discreteCountingPrimitive_mul_kernelDeriv_intervalIntegrable_anyWindow`);
* smooth part — `smoothCountingPrimitive` is an explicit smooth primitive,
  integrable against the continuous kernel.

The kernel itself is **continuous** for `z.im > 0`
(`pairedCauchyImKernelDeriv_continuous`, rh:55328), and that is the engine: a
finite-window integrable factor times a `ContinuousOn` factor is
`IntervalIntegrable` (`IntervalIntegrable.mul_continuousOn`).

## How the TRUE version does it (this file)

We mirror the split, but the count component is the genuine abstract
`zetaWeightedZeroCountUpToHeight`, which is NOT a finite sum.  The decisive
structural facts we exploit:

* `concreteS u = concreteCountReal u − smoothMainTerm u` for ALL `u`, where
  `concreteCountReal` is the total real-valued zero count (= the `ℕ` count for
  `u ≥ 0`, `0` for `u < 0`).
* `concreteCountReal` is **MONOTONE** on `ℝ` (the zero count is monotone in the
  height, and nonnegative), hence `IntervalIntegrable` on every window
  (`Monotone.intervalIntegrable`) — this is the measure-theoretic replacement
  for the finite discrete sum.
* `smoothMainTerm` is **continuous** on `(0, ∞)`
  (`continuousAt_smoothMainTerm`), hence `ContinuousOn [[T, X]]` (window
  endpoints `≥ 10 > 0`), hence `IntervalIntegrable`.

So `concreteS` is `IntervalIntegrable` on `[T, X]` (difference of an integrable
monotone function and a continuous one), `trueFluctuationPrimitive T0` differs
from it by the constant `concreteS T0` (still integrable), and the kernel is
`ContinuousOn [[T, X]]`.  `IntervalIntegrable.mul_continuousOn` closes it.

**No bare sorry/admit, no extra named gap.**  Everything reduces to already-
proven `rh` facts (count monotonicity, smooth-term continuity, kernel
continuity) plus pure Mathlib measure theory.
-/

open Filter Topology MeasureTheory
open OverflowResidueRH
open OverflowResidueRH.BacklundTuring

namespace OverflowResidueRH.BacklundTuring.ScratchWindowInt

-- =====================================================================
-- §0. Local mirror of the `ScratchTrueFluctuation` definitions
-- =====================================================================
-- The deliverable target `TrueFluctuationWindowIntegrable` and the underlying
-- `trueFluctuationPrimitive` are declared in `ScratchTrueFluctuation.lean`,
-- which is a standalone scratch file with no compiled `.olean` on the search
-- path (it is not a `lean_lib` glob), so it cannot be `import`ed.  Per the
-- "edit ONLY ScratchWindowInt.lean" constraint we re-declare the two
-- definitions here VERBATIM (same body over `rh`'s `concreteS` /
-- `pairedCauchyImKernelDeriv`).  These are definitionally identical to
-- `ScratchTrueFluctuation.trueFluctuationPrimitive` /
-- `ScratchTrueFluctuation.TrueFluctuationWindowIntegrable`; the proof below
-- discharges that obligation, and transplanting it back into
-- `ScratchTrueFluctuation` is a one-line `exact` once the files share a build.

/-- **The true fluctuation primitive** (mirror of
`ScratchTrueFluctuation.trueFluctuationPrimitive`).  Anchored at base height
`T0`: `concreteS u − concreteS T0`. -/
noncomputable def trueFluctuationPrimitive (T0 : ℝ) : ℝ → ℝ :=
  fun u => concreteS u - concreteS T0

/-- **`TrueFluctuationWindowIntegrable T0`** (mirror of
`ScratchTrueFluctuation.TrueFluctuationWindowIntegrable`).  Finite-window
interval integrability of `trueFluctuationPrimitive T0 · pairedCauchyImKernelDeriv`
on every adaptive window. -/
def TrueFluctuationWindowIntegrable (T0 : ℝ) : Prop :=
  ∀ {z : ℂ} {T X : ℝ}, 10 ≤ T → T ≤ 140 → 0 < z.im →
    2 * (1 + |z.re| + z.im) ≤ T → T ≤ X →
    IntervalIntegrable
      (fun u => trueFluctuationPrimitive T0 u
                  * pairedCauchyImKernelDeriv z.re z.im u)
      MeasureTheory.volume T X

-- =====================================================================
-- §1. The total real-valued zero count  `concreteCountReal`
-- =====================================================================

/-- **Total real-valued ζ-zero count.**  Equal to the genuine weighted zero
count `zetaWeightedZeroCountUpToHeight u` (cast to `ℝ`) for `u ≥ 0`, and `0`
for `u < 0`.  This is `concreteS`'s count component, made into a total
`ℝ → ℝ` function (dropping the `0 ≤ u` proof argument) so it can be reasoned
about as a monotone, measurable, finite-window-integrable function. -/
noncomputable def concreteCountReal (u : ℝ) : ℝ :=
  if h : 0 ≤ u then (zetaWeightedZeroCountUpToHeight u h : ℝ) else 0

/-- `concreteCountReal` is nonnegative (it is a `ℕ` cast, or `0`). -/
lemma concreteCountReal_nonneg (u : ℝ) : 0 ≤ concreteCountReal u := by
  unfold concreteCountReal
  by_cases h : 0 ≤ u
  · rw [dif_pos h]; exact Nat.cast_nonneg _
  · rw [dif_neg h]

/-- **The split identity.**  For every real `u`,
`concreteS u = concreteCountReal u − smoothMainTerm u`.  This holds on the
nose for both branches of `concreteS`'s `dite`: for `u ≥ 0`, both sides are
`count − smoothMainTerm`; for `u < 0`, `concreteS u = −smoothMainTerm u` and
`concreteCountReal u = 0`. -/
lemma concreteS_eq_countReal_sub_smoothMainTerm (u : ℝ) :
    concreteS u = concreteCountReal u - smoothMainTerm u := by
  unfold concreteS concreteCountReal
  by_cases h : 0 ≤ u
  · rw [dif_pos h, dif_pos h]
  · rw [dif_neg h, dif_neg h, zero_sub]

/-- 🌟 **PROVED — `concreteCountReal` is MONOTONE on `ℝ`.**  The genuine
weighted zero count is monotone in the height
(`zetaWeightedZeroCountUpToHeight_mono`) and nonnegative, so its total
real-valued extension is monotone across the `u < 0 ≤ u` seam as well. -/
lemma concreteCountReal_monotone : Monotone concreteCountReal := by
  intro a b hab
  by_cases ha : 0 ≤ a
  · -- 0 ≤ a ≤ b, so 0 ≤ b
    have hb : 0 ≤ b := le_trans ha hab
    unfold concreteCountReal
    rw [dif_pos ha, dif_pos hb]
    exact_mod_cast zetaWeightedZeroCountUpToHeight_mono ha hb hab
  · -- a < 0, LHS = 0 ≤ RHS (nonneg)
    have hla : concreteCountReal a = 0 := by
      unfold concreteCountReal; rw [dif_neg ha]
    rw [hla]
    exact concreteCountReal_nonneg b

/-- ⭐ **PROVED — `concreteCountReal` is `IntervalIntegrable` on any window.**
Direct from monotonicity. -/
lemma concreteCountReal_intervalIntegrable (T X : ℝ) :
    IntervalIntegrable concreteCountReal volume T X :=
  concreteCountReal_monotone.intervalIntegrable

-- =====================================================================
-- §2. `smoothMainTerm` is `ContinuousOn` / integrable on positive windows
-- =====================================================================

/-- ⭐ **PROVED — `smoothMainTerm` is `ContinuousOn [[T, X]]`** whenever both
endpoints are positive (so the whole interval lies in `(0, ∞)`, where
`continuousAt_smoothMainTerm` applies). -/
lemma smoothMainTerm_continuousOn_uIcc
    {T X : ℝ} (hT : 0 < T) (hX : 0 < X) :
    ContinuousOn smoothMainTerm (Set.uIcc T X) := by
  intro t ht
  have htpos : 0 < t := by
    rcases le_total T X with hle | hle
    · rw [Set.uIcc_of_le hle] at ht
      exact lt_of_lt_of_le hT ht.1
    · rw [Set.uIcc_of_ge hle] at ht
      exact lt_of_lt_of_le hX ht.1
  exact (continuousAt_smoothMainTerm htpos).continuousWithinAt

/-- ⭐ **PROVED — `smoothMainTerm` is `IntervalIntegrable` on positive
windows.** -/
lemma smoothMainTerm_intervalIntegrable
    {T X : ℝ} (hT : 0 < T) (hX : 0 < X) :
    IntervalIntegrable smoothMainTerm volume T X :=
  (smoothMainTerm_continuousOn_uIcc hT hX).intervalIntegrable

-- =====================================================================
-- §3. `concreteS` and `trueFluctuationPrimitive T0` are integrable
-- =====================================================================

/-- 🌟🌟 **PROVED — `concreteS` is `IntervalIntegrable` on positive windows.**
Rewrite via the split identity into (monotone, integrable) `concreteCountReal`
minus (continuous, integrable) `smoothMainTerm`. -/
lemma concreteS_intervalIntegrable
    {T X : ℝ} (hT : 0 < T) (hX : 0 < X) :
    IntervalIntegrable concreteS volume T X := by
  have hcongr :
      concreteS
        = (fun u => concreteCountReal u - smoothMainTerm u) := by
    funext u; exact concreteS_eq_countReal_sub_smoothMainTerm u
  rw [hcongr]
  exact (concreteCountReal_intervalIntegrable T X).sub
    (smoothMainTerm_intervalIntegrable hT hX)

/-- 🌟🌟 **PROVED — `trueFluctuationPrimitive T0` is `IntervalIntegrable` on
positive windows.**  It is `concreteS` minus the constant `concreteS T0`. -/
lemma trueFluctuationPrimitive_intervalIntegrable
    (T0 : ℝ) {T X : ℝ} (hT : 0 < T) (hX : 0 < X) :
    IntervalIntegrable (trueFluctuationPrimitive T0) volume T X := by
  have hcongr :
      trueFluctuationPrimitive T0
        = (fun u => concreteS u - concreteS T0) := by
    funext u; rfl
  rw [hcongr]
  exact (concreteS_intervalIntegrable hT hX).sub intervalIntegrable_const

-- =====================================================================
-- §4. The product against the continuous kernel derivative — DELIVERABLE
-- =====================================================================

/-- 🌟🌟🌟 **PROVED — `trueFluctuationPrimitive T0 · k'` is
`IntervalIntegrable` on every window** with positive endpoints and `z.im > 0`.
`trueFluctuationPrimitive T0` is `IntervalIntegrable` (§3); the kernel
derivative `pairedCauchyImKernelDeriv z.re z.im` is continuous
(`pairedCauchyImKernelDeriv_continuous`), hence `ContinuousOn [[T, X]]`;
`IntervalIntegrable.mul_continuousOn` combines them. -/
lemma trueFluctuationPrimitive_mul_kernelDeriv_intervalIntegrable
    (T0 : ℝ) {z : ℂ} {T X : ℝ}
    (hT : 0 < T) (hX : 0 < X) (hy : 0 < z.im) :
    IntervalIntegrable
      (fun u => trueFluctuationPrimitive T0 u
                  * pairedCauchyImKernelDeriv z.re z.im u)
      volume T X := by
  have hf : IntervalIntegrable (trueFluctuationPrimitive T0) volume T X :=
    trueFluctuationPrimitive_intervalIntegrable T0 hT hX
  have hg : ContinuousOn (fun u => pairedCauchyImKernelDeriv z.re z.im u)
      (Set.uIcc T X) :=
    (Phase1IBP.pairedCauchyImKernelDeriv_continuous hy z.re).continuousOn
  exact hf.mul_continuousOn hg

/-- 🌟🌟🌟🌟 **PROVED — `TrueFluctuationWindowIntegrable T0`** for every
architectural anchor `T0`.  This DISCHARGES the `Hint` obligation of the
de-vacuumed front door
(`ScratchTrueFluctuation.realIBPFamilyData_trueFluctuation`,
`xiPullbackAntiHerglotzTarget_trueFluctuation`).

The adaptive band gives `10 ≤ T ≤ 140` and `T ≤ X`, so both `T` and `X` are
`≥ 10 > 0`; `0 < z.im` is supplied directly.  All hypotheses of §4's product
integrability lemma are met. -/
theorem trueFluctuationWindowIntegrable (T0 : ℝ) :
    TrueFluctuationWindowIntegrable T0 := by
  intro z T X h10 _h140 hy _hregime hTX
  have hT : 0 < T := lt_of_lt_of_le (by norm_num) h10
  have hX : 0 < X := lt_of_lt_of_le hT hTX
  exact trueFluctuationPrimitive_mul_kernelDeriv_intervalIntegrable T0 hT hX hy

-- =====================================================================
-- §5. Axiom audit — NO sorryAx
-- =====================================================================
#print axioms concreteCountReal_monotone
#print axioms concreteS_eq_countReal_sub_smoothMainTerm
#print axioms concreteS_intervalIntegrable
#print axioms trueFluctuationPrimitive_mul_kernelDeriv_intervalIntegrable
#print axioms trueFluctuationWindowIntegrable

end OverflowResidueRH.BacklundTuring.ScratchWindowInt
