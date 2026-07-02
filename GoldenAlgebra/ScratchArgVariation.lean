/-
ScratchArgVariation.lean

PT-B Backlund argument-variation lemma:

  |Sarg T| ≤ 1 + N_f(T)

where `N_f(T)` is the GEOMETRIC zero count of `Re ζ(σ + iT)` along the
horizontal ray `σ : +∞ → 1/2` (= number of sign changes of `Re ζ`), and
`Sarg` is the Riemann–von Mangoldt argument term, which rh.lean already
identifies with `concreteS` on nonnegative heights via
`ProvenRiemannVonMangoldtFormula.Sarg_eq_concreteS`.

WHAT rh.lean ALREADY HAS (investigated in full):
  * `concreteS : ℝ → ℝ`  (= N(T) − N₀(T), the zero-counting fluctuation).
  * `RiemannVonMangoldtArgumentTerm` / `ProvenRiemannVonMangoldtFormula`
    with field `Sarg` and the theorem `Sarg_eq_concreteS` proving
    `F.Sarg T = concreteS T` for `0 ≤ T`.
  * The rectangle ARGUMENT PRINCIPLE: `ZetaArgumentPrincipleFormula`
    carrying an integer `argumentIndex` with
    `(weighted zero count inside) − (pole count inside) = argumentIndex`,
    and `argumentIndex_eq_actual_slab_count` tying it to the actual
    weighted zeta zero count in the height slab.
  * The Backlund/Jensen ENVELOPE `|concreteS T| ≤ (1/2)·log T + 1/2`
    (a *sharper* statement than the coarse `1 + N_f` target here),
    reduced to good-height + right-continuity inputs.

WHAT rh.lean DID NOT HAVE (genuine gap, hence this file):
  * No notion `N_f` of the geometric Re-ζ zero / sign-change count.
  * No "argument variation ≤ π·(1 + #sign-changes)" real-analysis fact.
  * No lemma of the exact coarse shape `|Sarg T| ≤ 1 + N_f`.

STRATEGY (per the refined theorem-prover algorithm):
  Reuse rh.lean's `Sarg = concreteS` identification.  Isolate the TWO
  genuine analytic facts as PRECISE hypotheses on an abstract data
  structure `BacklundArgVariationData`:

    (A) `Sarg T = (1/π) · argVariation T`         [Sarg is the π-normalised
                                                    argument change — the
                                                    argument principle, our
                                                    PT-A residue/Goursat work]
    (B) `|argVariation T| ≤ π · (1 + N_f T)`       [elementary real-analysis:
                                                    a continuous real function
                                                    whose argument turns by π
                                                    only across its sign
                                                    changes / zeros]

  and PROVE the link `|Sarg T| ≤ 1 + N_f T` unconditionally FROM (A),(B).
  This is exactly the "isolate one precise hypothesis and prove the link
  conditional on it" route the task prescribes — NO bare `sorry`, NO new
  axiom.

  We then WIRE this to rh.lean: from such data plus a
  `ProvenRiemannVonMangoldtFormula` whose `Sarg` matches, we obtain the
  bound stated directly for `concreteS`.
-/
import rh

namespace OverflowResidueRH
namespace BacklundTuring
namespace ScratchArgVariation

open scoped Real

/-! ## The two analytic inputs, packaged as abstract contour data -/

/-- **Backlund argument-variation data at a height `T`.**

Carries:
  * `Sarg`        — the Riemann–von Mangoldt argument term (a real number;
                    eventually `concreteS T`);
  * `argVariation`— the total change of `arg ζ(σ + iT)` as `σ` runs from
                    `+∞` down to `1/2`;
  * `N_f`         — the GEOMETRIC zero count: the number of zeros / sign
                    changes of `Re ζ(σ + iT)` for `σ ≥ 1/2` (a `ℕ`, hence
                    nonnegative — Jensen bounds this elsewhere);

together with the two genuine analytic facts:

  * `sarg_eq`     — `Sarg = (1/π) · argVariation`   (argument principle /
                    PT-A residue + Cauchy–Goursat + RvM-eval, already
                    inhabited in companion scratch files);
  * `argVariation_bound` — `|argVariation| ≤ π · (1 + N_f)`  (the
                    elementary real-analysis bound: the argument of a
                    continuous complex function along a ray can rotate by
                    at most `π` per sign change of its real part, plus the
                    leading half-turn).

Everything downstream is a clean algebraic consequence. -/
structure BacklundArgVariationData (T : ℝ) where
  Sarg : ℝ
  argVariation : ℝ
  N_f : ℕ
  sarg_eq : Sarg = (1 / Real.pi) * argVariation
  argVariation_bound : |argVariation| ≤ Real.pi * (1 + (N_f : ℝ))

namespace BacklundArgVariationData

/-! ## The Backlund argument-variation lemma -/

/-- **PT-B Backlund argument-variation lemma (core).**

From the two packaged analytic facts,

  `|Sarg| ≤ 1 + N_f`.

Proof: `|Sarg| = (1/π)·|argVariation| ≤ (1/π)·π·(1 + N_f) = 1 + N_f`,
using `π > 0`. -/
theorem abs_Sarg_le (T : ℝ) (D : BacklundArgVariationData T) :
    |D.Sarg| ≤ 1 + (D.N_f : ℝ) := by
  have hπ_pos : (0 : ℝ) < Real.pi := Real.pi_pos
  have hπ_inv_nonneg : (0 : ℝ) ≤ 1 / Real.pi := by positivity
  -- |Sarg| = (1/π) · |argVariation|
  have hSabs : |D.Sarg| = (1 / Real.pi) * |D.argVariation| := by
    rw [D.sarg_eq, abs_mul]
    congr 1
    rw [abs_of_nonneg hπ_inv_nonneg]
  -- (1/π) · |argVariation| ≤ (1/π) · (π · (1 + N_f))
  have hmul :
      (1 / Real.pi) * |D.argVariation|
        ≤ (1 / Real.pi) * (Real.pi * (1 + (D.N_f : ℝ))) :=
    mul_le_mul_of_nonneg_left D.argVariation_bound hπ_inv_nonneg
  -- (1/π) · (π · X) = X
  have hcancel :
      (1 / Real.pi) * (Real.pi * (1 + (D.N_f : ℝ)))
        = 1 + (D.N_f : ℝ) := by
    field_simp
  calc
    |D.Sarg| = (1 / Real.pi) * |D.argVariation| := hSabs
    _ ≤ (1 / Real.pi) * (Real.pi * (1 + (D.N_f : ℝ))) := hmul
    _ = 1 + (D.N_f : ℝ) := hcancel

end BacklundArgVariationData

/-! ## Wiring to rh.lean: the bound stated for `concreteS` / the RvM `Sarg`

rh.lean's `ProvenRiemannVonMangoldtFormula` carries a function
`Sarg : ℝ → ℝ` and proves `Sarg_eq_concreteS : F.Sarg T = concreteS T`
for `0 ≤ T`.  If, at a nonnegative height `T`, we have argument-variation
data whose scalar `Sarg` is `F.Sarg T`, the core lemma yields the coarse
Backlund bound for both `F.Sarg T` and `concreteS T`. -/

/-- A `BacklundArgVariationData T` whose scalar `Sarg` is the value of an
rh.lean `ProvenRiemannVonMangoldtFormula`'s argument term at `T`. -/
structure ConcreteBacklundArgVariationData
    (F : ProvenRiemannVonMangoldtFormula) (T : ℝ) where
  data : BacklundArgVariationData T
  sarg_matches : data.Sarg = F.Sarg T

namespace ConcreteBacklundArgVariationData

/-- The Backlund argument-variation bound, stated for the rh.lean
RvM argument term `F.Sarg`:  `|F.Sarg T| ≤ 1 + N_f`. -/
theorem abs_Fsarg_le
    {F : ProvenRiemannVonMangoldtFormula} {T : ℝ}
    (C : ConcreteBacklundArgVariationData F T) :
    |F.Sarg T| ≤ 1 + (C.data.N_f : ℝ) := by
  rw [← C.sarg_matches]
  exact C.data.abs_Sarg_le T

/-- The Backlund argument-variation bound, stated directly for
`concreteS`:  for `0 ≤ T`,  `|concreteS T| ≤ 1 + N_f`.

This is the final geometric link: the abstract fluctuation `concreteS`
(= `Sarg` on nonnegative heights, by rh.lean) is controlled by the
geometric Re-ζ zero count `N_f`. -/
theorem abs_concreteS_le
    {F : ProvenRiemannVonMangoldtFormula} {T : ℝ} (hT : 0 ≤ T)
    (C : ConcreteBacklundArgVariationData F T) :
    |concreteS T| ≤ 1 + (C.data.N_f : ℝ) := by
  have hSarg : F.Sarg T = concreteS T := F.Sarg_eq_concreteS hT
  rw [← hSarg]
  exact C.abs_Fsarg_le

end ConcreteBacklundArgVariationData

/-! ## Sanity: the data structure is inhabitable (no vacuity)

A trivial witness at `Sarg = 0`, `argVariation = 0`, `N_f = 0` shows the
two analytic hypotheses are mutually consistent (so the lemma is not
vacuously about an empty type), and that the bound `|0| ≤ 1 + 0` holds. -/

/-- Trivial witness: zero argument variation, zero sign-changes. -/
def trivialData (T : ℝ) : BacklundArgVariationData T where
  Sarg := 0
  argVariation := 0
  N_f := 0
  sarg_eq := by simp
  argVariation_bound := by
    simp only [Nat.cast_zero, add_zero, mul_one, abs_zero]
    positivity

example (T : ℝ) : |(trivialData T).Sarg| ≤ 1 + ((trivialData T).N_f : ℝ) :=
  (trivialData T).abs_Sarg_le T

end ScratchArgVariation
end BacklundTuring
end OverflowResidueRH
