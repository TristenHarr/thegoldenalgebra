import rh
import ScratchPositionEnvelope

/-!
# ScratchTraceFormula — the displacement *trace formula* / conservation-law interface

This file builds the **conservation-law** strengthening of the position-sensitive
energy certificate of `ScratchPositionEnvelope.lean`.  Where that file carries a
single bare RH-strength field (`energy = 0`), this file derives `energy = 0`
from a **trace identity** (an *equality* — the Killip–Simon-style sum rule):

```
        displacementEnergy  +  remainder  =  0,
        displacementEnergy  =  Σᶠ / ∫_{zeros} (ρ.im)² · W ρ,
        remainder ≥ 0,        W > 0  off the critical line.
```

Both summands are `≥ 0` and they sum to exactly `0`, so each is `0`; in
particular the displacement energy is `0`, which is *precisely* the
`PositionSensitiveEnergyCertificate.energy_zero` field.  Composing with the
already-proven `ScratchPositionEnvelope` bridge yields RH on the slab in the
codebase's headline form `∀ ρ, XiPullback ρ = 0 → ρ.im = 0`.

## Coordinate convention (inherited from `ScratchPositionEnvelope`)

`XiPullback z = ξ(½ + i·z)`.  A nontrivial zero of `ξ` at `s = β + iγ` pulls
back to `w = γ − i·(β − ½)`, so the **displacement** `η = β − ½` is (up to sign)
the imaginary part of the pulled-back zero.  An atom of the zero measure at
`(γ, η)` is a pulled-back zero `XiPullback ⟨γ, η⟩ = 0`, and RH ⟺ every atom has
`η = 0` ⟺ every zero `ρ` of `XiPullback` has `ρ.im = 0`.

## What is PROVEN here (no `sorry`, no `admit`)

* `DisplacementTraceFormula` — the conservation-law data structure.  It carries
  the genuine analytic *conservation witness* — the equality `trace_identity`
  and the positivity `remainder_nonneg` — as its only unproven fields, exactly
  as the task specifies (these two are the RH-strength core).
* `DisplacementTraceFormula.energy_zero` — **PROVED**: `0 ≤ remainder` and
  `0 ≤ displacementEnergy` (the latter forced by `W ≥ 0`) plus
  `displacementEnergy + remainder = 0` give `displacementEnergy = 0`.  This is
  the both-nonneg-summing-to-zero pinch.
* `DisplacementTraceFormula.toEnergyCertificate` — **PROVED**: every trace
  formula *is* a `PositionSensitiveEnergyCertificate` whose `energy_zero` field
  is supplied by the conservation pinch above.  The trace formula is the
  certificate PLUS the conservation-law witness for why the energy is zero.
* `RH_of_displacementTraceFormula` — **PROVED**: composing the bridge with
  `ScratchPositionEnvelope.RH_of_positionSensitiveEnergyCertificate` yields
  `∀ ρ, XiPullback ρ = 0 → ρ.im = 0`.

## Honesty: what is and isn't proved

`trace_identity` (the conservation equality) and `remainder_nonneg` (the
positivity of the prime/archimedean remainder) are **left UNPROVEN structure
fields**.  Together they are exactly RH-strength: realizing them unconditionally
is the open Weil-positivity / Killip–Simon sum-rule problem.  See the written
report accompanying this file for the brutally honest verdict — in short, the
remainder `R(Φ)` is the prime + archimedean side of the Weil explicit formula,
whose nonnegativity for the displacement test functions is *equivalent* to RH
(Bombieri), so `remainder_nonneg` cannot be made unconditional by any known
mechanism.  Nothing here assumes RH; the load-bearing direction proved here is
the trivial "sum rule ⟹ RH" pinch, not its converse.

`#print axioms` on the bridges: only `propext`, `Classical.choice`, `Quot.sound`
(no `sorryAx`).
-/

namespace OverflowResidueRH
namespace ScratchTraceFormula

open MeasureTheory
open OverflowResidueRH.ScratchPositionEnvelope

/-! ## §1. The displacement trace formula (conservation-law) data structure -/

/-- **Displacement trace formula** — the conservation-law witness.

`zeroMeasure` is the atomic measure on the `(γ, η)` plane (an atom at `(γ, η)`
is a pulled-back zero with ordinate `γ`, displacement `η`).  `W : ℂ → ℝ` is the
position-sensitive energy weight, strictly positive off the critical line.
`displacementEnergy = ∫ (η)² · W dμ` is the position-sensitive displacement
energy (the off-line zeros' second-moment energy).  `remainder` is the
prime + archimedean remainder `R(Φ)`.

The two unproven fields are the genuine RH-strength **conservation-law core**:

* `trace_identity` — the *equality* `displacementEnergy + remainder = 0`
  (the Killip–Simon-style sum rule);
* `remainder_nonneg` — `0 ≤ remainder` (positivity of the prime/archimedean
  side; = Weil positivity, see the report).

Everything else (`W_pos`, `W_nonneg`, integrability, `atoms_are_zeros`,
`energy_eq`) is honest bookkeeping. -/
structure DisplacementTraceFormula where
  /-- Atomic zero measure on the `(γ, η)` plane. -/
  zeroMeasure : Measure (ℝ × ℝ)
  /-- The position-sensitive energy weight (in the `ℂ` coordinate of the zero
  `ρ = γ + i·η`; evaluated at an atom `(γ, η)` as `W ⟨γ, η⟩`). -/
  W : ℂ → ℝ
  /-- The weight is strictly positive off the critical line (`η ≠ 0`). -/
  W_pos : ∀ ρ : ℂ, ρ.im ≠ 0 → 0 < W ρ
  /-- The weight is nonnegative everywhere (so the integrand `η²·W ≥ 0`). -/
  W_nonneg : ∀ ρ : ℂ, 0 ≤ W ρ
  /-- The position-sensitive displacement energy. -/
  displacementEnergy : ℝ
  /-- The displacement energy *is* `∫ η²·W dμ`, the position-sensitive
  second-moment energy over the zeros (the `ScratchPositionEnvelope`
  position-sensitive measure). -/
  energy_eq :
    displacementEnergy = ∫ p, p.2 ^ 2 * W ⟨p.1, p.2⟩ ∂zeroMeasure
  /-- The weighted integrand is `μ`-integrable. -/
  energy_integrable :
    Integrable (fun p : ℝ × ℝ => p.2 ^ 2 * W ⟨p.1, p.2⟩) zeroMeasure
  /-- **Atoms are zeros.** -/
  atoms_are_zeros : ∀ p : ℝ × ℝ,
    0 < zeroMeasure {p} → XiPullback ⟨p.1, p.2⟩ = 0
  /-- The prime + archimedean remainder `R(Φ)`. -/
  remainder : ℝ
  /-- **UNPROVEN RH-strength field (positivity of the remainder).** -/
  remainder_nonneg : 0 ≤ remainder
  /-- **UNPROVEN RH-strength field (the conservation-law equality / sum rule).** -/
  trace_identity : displacementEnergy + remainder = 0

/-! ## §2. The conservation pinch: both nonneg + sum zero ⟹ energy zero -/

/-- The displacement energy is nonnegative: it is `∫ η²·W dμ` with `η² ≥ 0` and
`W ≥ 0`, so the integrand is `≥ 0` and the integral is `≥ 0`. -/
theorem displacementEnergy_nonneg (F : DisplacementTraceFormula) :
    0 ≤ F.displacementEnergy := by
  rw [F.energy_eq]
  apply integral_nonneg
  intro p
  exact mul_nonneg (sq_nonneg p.2) (F.W_nonneg ⟨p.1, p.2⟩)

/-- **PROVED — the conservation pinch.**  `0 ≤ displacementEnergy`,
`0 ≤ remainder`, and `displacementEnergy + remainder = 0` force
`displacementEnergy = 0`.  This is the both-nonneg-summing-to-exactly-zero
mechanism: two nonnegative reals summing to `0` are each `0`. -/
theorem DisplacementTraceFormula.energy_zero (F : DisplacementTraceFormula) :
    F.displacementEnergy = 0 := by
  have hE : 0 ≤ F.displacementEnergy := displacementEnergy_nonneg F
  have hR : 0 ≤ F.remainder := F.remainder_nonneg
  have hsum : F.displacementEnergy + F.remainder = 0 := F.trace_identity
  linarith

/-! ## §3. The bridge: a trace formula IS an energy certificate

The trace formula carries everything a `PositionSensitiveEnergyCertificate`
needs — the same zero measure, the same integrand `η²·W` — and additionally a
*conservation-law witness* (`trace_identity` + `remainder_nonneg`) that supplies
the certificate's lone unproven field `energy_zero` via the pinch of §2.  So the
trace formula is the certificate PLUS a witness for why the energy is zero. -/

/-- **PROVED — every displacement trace formula is a position-sensitive energy
certificate.**  The weight is `fun p => W ⟨p.1, p.2⟩`; positivity/nonnegativity
transport directly from the `ℂ`-weight via `⟨p.1, p.2⟩.im = p.2`; the lone
`energy_zero` field is discharged by the conservation pinch
`DisplacementTraceFormula.energy_zero`. -/
noncomputable def DisplacementTraceFormula.toEnergyCertificate
    (F : DisplacementTraceFormula) : PositionSensitiveEnergyCertificate where
  zeroMeasure := F.zeroMeasure
  W := fun p => F.W ⟨p.1, p.2⟩
  W_pos := by
    intro p hp
    exact F.W_pos ⟨p.1, p.2⟩ (by simpa using hp)
  W_nonneg := fun p => F.W_nonneg ⟨p.1, p.2⟩
  energy := F.displacementEnergy
  energy_eq := F.energy_eq
  energy_integrable := F.energy_integrable
  atoms_are_zeros := F.atoms_are_zeros
  energy_zero := F.energy_zero

/-! ## §4. The capstone: trace formula ⟹ RH on the zeros

Compose the §3 bridge with the already-proven `ScratchPositionEnvelope`
energy-certificate bridge.  `completeness` says every pulled-back zero is an
atom of positive `μ`-mass; then `energy = 0` (from the conservation law) forces
`η = 0` for every such atom, i.e. `ρ.im = 0` for every zero. -/

/-- 🌟🌟🌟🌟🌟 **PROVED — the displacement trace formula yields RH.**

`completeness` records that every pulled-back zero is an atom of the zero
measure (positive mass).  Then the conservation law `displacementEnergy +
remainder = 0` with both terms `≥ 0` pins `displacementEnergy = 0`; the
position-sensitive bridge turns `∫ η²·W = 0` (`W > 0` off the line) into
`η = 0` `μ`-a.e., hence `ρ.im = 0` for every zero `ρ`.

This is the load-bearing "conservation law ⟹ RH" pinch.  It does NOT prove RH:
the *equality* `trace_identity` and the *positivity* `remainder_nonneg` are the
unproven RH-strength fields. -/
theorem RH_of_displacementTraceFormula
    (F : DisplacementTraceFormula)
    (completeness : ∀ ρ : ℂ, XiPullback ρ = 0 →
      0 < F.zeroMeasure {(ρ.re, ρ.im)}) :
    ∀ ρ : ℂ, XiPullback ρ = 0 → ρ.im = 0 :=
  RH_of_positionSensitiveEnergyCertificate
    F.toEnergyCertificate completeness

/-! ## §5. Axiom check — the bridges must be free of `sorryAx`. -/

#print axioms DisplacementTraceFormula.energy_zero
#print axioms DisplacementTraceFormula.toEnergyCertificate
#print axioms RH_of_displacementTraceFormula

end ScratchTraceFormula
end OverflowResidueRH
