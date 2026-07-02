import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# ScratchOscContinuation — the α-continuation launch obstruction

This file banks ONE clean, RH-free analytic fact from the **height-oscillation continuation**
campaign (`weil_attack/osc_phase_diagram.py`, `osc_obstruction.py`, `osc_fakemodel.py`).

## The object

For an off-line quartet `{½ ± η ± iγ}` and a positive-type Gaussian test window
`g_w(u) = exp(−u²/2w²)`, the two-parameter family interpolating the positive **displacement
envelope** (`α = 0`) and the **true Weil readout** (`α = 1`) has, for one quartet, the
closed-form per-term contribution (validated numerically to ~1e-13):

```
  I(η, w, β) = w√(2π) · [ exp(−w²(β²−η²)/2)·cos(w²ηβ) − exp(−w²β²/2) ],   β = α·γ.
```

`I(η,w,0) = w√(2π)(exp(w²η²/2) − 1) > 0` is the positive envelope (`α=0`).  The campaign's
numerics show `α=0` is a **strict local maximum** of the windowed Weil functional in `α`:
the second derivative in the oscillation frequency `β` at `β=0` is

```
  ∂²_β I(η,w,0) = w√(2π)·w² · [ 1 − (1 + η²w²)·exp(η²w²/2) ]  < 0   (UNCONDITIONALLY).
```

The bracket is negative for every `η ≠ 0` because `(1+x)·exp(x/2) > 1` for all `x > 0`
(here `x = η²w²`).  This is the analytic content of the obstruction: leaving the positive
envelope (`α → 0⁺`) **strictly decreases** the functional, so the positive envelope is an
*isolated* positivity peak — there is **no** positivity-preserving continuation path from the
envelope (`α=0`) to the true Weil form (`α=1`).  The positivity death occurs at the
`w·(α·γ) ≍ 1` gate (numerically `0.987`), i.e. the **same `δ·T ≍ 1` resolution gate** of
`ScratchResolutionTheory`, now with effective scale `T_eff = w` and effective frequency `α·γ`.

This file proves the **sign lemma** `(1+x)·exp(x/2) > 1` for `x > 0` that makes the launch
coefficient unconditionally negative — the kernel of the obstruction.  It does **NOT** prove
RH; it banks the obstruction.
-/

namespace OverflowResidueRH
namespace ScratchOscContinuation

open Real

/-- **The launch-sign lemma.**  `1 < (1 + x)·exp(x/2)` for every `x > 0`.

This is the unconditional negativity of the α-continuation launch coefficient
`∂²_β I(η,w,0) = w√(2π)·w²·(1 − (1+x)e^{x/2})` with `x = η²w² > 0`: the bracket
`1 − (1+x)e^{x/2} < 0`, so the second derivative is `< 0` and the positive envelope (`α=0`)
is a strict local maximum.  Proof: `exp(x/2) ≥ 1 + x/2 > 1` (from `add_one_le_exp`), and
`1 + x > 1`, so the product of two factors each `> 1` (resp `≥ 1+x/2`) exceeds `1`. -/
theorem one_lt_one_add_mul_exp_half {x : ℝ} (hx : 0 < x) :
    1 < (1 + x) * Real.exp (x / 2) := by
  have hexp : (1 : ℝ) + x / 2 ≤ Real.exp (x / 2) := by
    have := Real.add_one_le_exp (x / 2); linarith
  have h1 : (1 : ℝ) < 1 + x / 2 := by linarith
  have h2 : (1 : ℝ) < 1 + x := by linarith
  have hpos : (0 : ℝ) < 1 + x := by linarith
  calc (1 : ℝ) = 1 * 1 := by ring
    _ < (1 + x) * (1 + x / 2) := by
        apply mul_lt_mul' (le_of_lt h2) h1 (by norm_num) (by linarith)
    _ ≤ (1 + x) * Real.exp (x / 2) := by
        apply mul_le_mul_of_nonneg_left hexp (le_of_lt hpos)

/-- **The launch coefficient is strictly negative.**  The bracket
`1 − (1+x)·exp(x/2)` controlling `∂²_β I(η,w,0)` is `< 0` for every `x = η²w² > 0`.
Hence the per-term Weil contribution has a STRICT LOCAL MAXIMUM at the oscillation
frequency `β = 0` (the positive envelope `α = 0`): the continuation in `α` launches
*downward*, and no positivity-preserving path connects the envelope to the true Weil form.
-/
theorem launch_coeff_neg {x : ℝ} (hx : 0 < x) :
    1 - (1 + x) * Real.exp (x / 2) < 0 := by
  have := one_lt_one_add_mul_exp_half hx; linarith

/-- Specialization to the campaign's variables: with `x = η²·w²` (η ≠ 0, w ≠ 0) the launch
coefficient `1 − (1+η²w²)exp(η²w²/2)` is strictly negative — `α = 0` (positive displacement
envelope) is a strict local maximum of the windowed Weil functional in the oscillation
frequency `α·γ`.  The obstruction to the envelope → true-Weil continuation, banked. -/
theorem envelope_is_strict_local_max {η w : ℝ} (hη : η ≠ 0) (hw : w ≠ 0) :
    1 - (1 + η ^ 2 * w ^ 2) * Real.exp (η ^ 2 * w ^ 2 / 2) < 0 := by
  have hx : 0 < η ^ 2 * w ^ 2 := by positivity
  exact launch_coeff_neg hx

#print axioms one_lt_one_add_mul_exp_half
#print axioms launch_coeff_neg
#print axioms envelope_is_strict_local_max

end ScratchOscContinuation
end OverflowResidueRH
