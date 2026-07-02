import ScratchResolutionTheory

/-!
# ScratchSecondMoment — the SQUARED (second-moment) displacement detector

This file banks the one clean structural fact that emerges from the **second-moment**
route on the Weil off-line displacement readout (campaign report:
`weil_attack/SECMOM_*.py`, `SECMOM_FINDINGS.md`).

## The route

The first-moment off-line contribution of one zero `ρ = ½ + η_ρ + i γ_ρ` to the Weil sum,
for a positive-type test function `g` with `supp g ⊆ [−T,T]`, is (identity `(★)`,
`weil_attack/QUART_FINDINGS.md`)

```
  Δ_ρ(g) = 4 ∫_{−T}^{T} g(u) (cosh(η_ρ u) − 1) cos(γ_ρ u) du,
```

whose edge magnitude is governed by the resolution kernel `cosh(η_ρ T) − 1`
(`ScratchResolutionTheory.weilDetect`).  The **first** moment `Σ_ρ Δ_ρ(g)` is
sign-INDEFINITE through `cos(γ_ρ u)`.  The idea: **square** it.  The diagonal second
moment `M₂(g) = Σ_ρ |Δ_ρ(g)|²` is positive by construction; its per-zero detector is the
SQUARED kernel `(cosh(η_ρ T) − 1)²`.

## What this file PROVES (no `sorry`, axiom-clean: `propext`, `Classical.choice`, `Quot.sound`)

* `cosh_sub_one_sq_resolution` — **the squared uncertainty law**:
  `((cosh(δT) − 1)² ≤ (δT)⁴ · cosh(δT)²) ∧ (1 ≤ δT → ¼(δT)⁴ ≤ (cosh(δT) − 1)²)`.
  The first half is the `O((δT)⁴)` invisibility bound (exponent **4**, vs **2** for the
  first moment); the second is the `O(1)` visibility floor above the gate.  **Both proven**
  from the already-banked first-moment law `ScratchResolutionTheory.cosh_minus_one_resolution`
  by squaring nonnegative inequalities.
* `secondMomentProfile` — the squared detector `R₂(δ,T) = (cosh(δT) − 1)²` is a
  `ScratchResolutionTheory.DisplacementResolutionProfile` with leading invisibility exponent
  `p = 4`, SAME reciprocal gate `1` as the first-moment Weil profile.
* `secondMoment_same_gate` — the verdict fact: **squaring does NOT move the `δ·T ≍ 1` gate**;
  it only steepens the sub-gate invisibility from `p = 2` to `p = 4`.
* `secondMomentDetect_weight` — `R₂ ≥ 0` everywhere and `> 0` off the line: the squared
  detector is a valid (faithful) displacement energy weight.

## The honest verdict banked alongside (see `SECMOM_FINDINGS.md`)

The second moment **keeps** the displacement signal (faithful, `M₂ ∝ Σ η⁴ W`) but at FOURTH
order, with the SAME gate and a STEEPER (`p=4`) blindness below it — so it is a strictly
WORSE detector than the first moment for small displacement.  Pair-correlation
(Montgomery `F(α,T)`, unconditional only on `|α| ≤ 1`,
Baluyot–Goldston–Suriajaya–Turnage-Butterbaugh 2024) bounds the cross terms only ABOVE and
only to `O(T log T)` = diagonal-count order; an UPPER bound on a POSITIVE detector is the
WRONG direction for RH (never forces `η = 0`), and beating the diagonal needs `F(α) ≈ α`
for `α > 1` = Montgomery's CONJECTURE.  No unconditional `Σ η⁴ W ≤ [vanishing]` bound is
bankable.  This file banks only the rigorous *resolution-profile* fact (`p=4`, same gate).
-/

namespace OverflowResidueRH
namespace ScratchSecondMoment

open Real
open OverflowResidueRH.ScratchResolutionTheory

/-! ## §1. THE SQUARED UNCERTAINTY LAW

The second-moment per-zero detector is `R₂(δ,T) = (cosh(δT) − 1)²`.  We derive its exact
two-regime law by SQUARING the first-moment law `cosh_minus_one_resolution`.  Squaring a
nonnegative quantity preserves `≤`, so:

* `cosh(δT) − 1 ≤ (δT)²·cosh(δT)` (both sides `≥ 0`) `⟹` `(cosh(δT)−1)² ≤ (δT)⁴·cosh(δT)²`;
* `½(δT)² ≤ cosh(δT) − 1` for `δT ≥ 1` (both sides `≥ 0`) `⟹` `¼(δT)⁴ ≤ (cosh(δT)−1)²`.

The invisibility exponent is **`p = 4`** (vs `p = 2` for the first moment): the second
moment is steeper-blind below the gate, with the gate location UNCHANGED. -/

/-- `cosh x − 1 ≥ 0` for all `x` (the detector is a genuine nonnegative magnitude). -/
theorem cosh_sub_one_nonneg (x : ℝ) : 0 ≤ Real.cosh x - 1 := by
  have := Real.one_le_cosh x; linarith

/-- 🌟 **THE SQUARED UNCERTAINTY LAW.**  For the second-moment detector
`R₂(δ,T) = (cosh(δT) − 1)²` (per-zero square of the Weil off-line quartet readout):

```
  (cosh(δT) − 1)²  ≤  (δT)⁴ · cosh(δT)²          -- O((δT)⁴): INVISIBLE below the gate (p=4)
  1 ≤ δT   ⟹   ¼(δT)⁴  ≤  (cosh(δT) − 1)²        -- O(1):     VISIBLE  above the gate
```

Proven by squaring the first-moment law `cosh_minus_one_resolution`.  The exponent is now
`4`, not `2`: squaring keeps the `δ·T ≍ 1` gate but makes the sub-gate decay steeper. -/
theorem cosh_sub_one_sq_resolution (δ T : ℝ) (hδ : 0 ≤ δ) (hT : 0 ≤ T) :
    ((Real.cosh (δ * T) - 1) ^ 2 ≤ (δ * T) ^ 4 * Real.cosh (δ * T) ^ 2) ∧
      (1 ≤ δ * T → 1 / 4 * (δ * T) ^ 4 ≤ (Real.cosh (δ * T) - 1) ^ 2) := by
  obtain ⟨hsmall, hlarge⟩ := cosh_minus_one_resolution δ T hδ hT
  refine ⟨?_, fun hgate => ?_⟩
  · -- square `cosh(δT)−1 ≤ (δT)²·cosh(δT)`, both sides nonnegative
    have h0 : 0 ≤ Real.cosh (δ * T) - 1 := cosh_sub_one_nonneg _
    have hRHSnn : 0 ≤ (δ * T) ^ 2 * Real.cosh (δ * T) := by positivity
    have hsq := mul_le_mul hsmall hsmall h0 hRHSnn
    calc (Real.cosh (δ * T) - 1) ^ 2
          = (Real.cosh (δ * T) - 1) * (Real.cosh (δ * T) - 1) := by ring
      _ ≤ ((δ * T) ^ 2 * Real.cosh (δ * T)) * ((δ * T) ^ 2 * Real.cosh (δ * T)) := hsq
      _ = (δ * T) ^ 4 * Real.cosh (δ * T) ^ 2 := by ring
  · -- square `½(δT)² ≤ cosh(δT)−1`, both sides nonnegative
    have hlb := hlarge hgate
    have hLHSnn : 0 ≤ 1 / 2 * (δ * T) ^ 2 := by positivity
    have hsq := mul_le_mul hlb hlb hLHSnn (cosh_sub_one_nonneg _)
    calc 1 / 4 * (δ * T) ^ 4
          = (1 / 2 * (δ * T) ^ 2) * (1 / 2 * (δ * T) ^ 2) := by ring
      _ ≤ (Real.cosh (δ * T) - 1) * (Real.cosh (δ * T) - 1) := hsq
      _ = (Real.cosh (δ * T) - 1) ^ 2 := by ring

/-! ## §2. THE SECOND-MOMENT RESOLUTION PROFILE — exponent `p = 4`, SAME gate `1` -/

/-- The second-moment per-zero detector `R₂(δ,T) = (cosh(δT) − 1)²`. -/
noncomputable def secondMomentDetect (δ T : ℝ) : ℝ := (Real.cosh (δ * T) - 1) ^ 2

/-- **PROVED — the squared Weil detector fits the resolution profile** with leading
invisibility exponent `p = 4`, invisibility constant `C₁ = 4` (from
`(cosh(δT)−1)² ≤ (δT)⁴·cosh(δT)² ≤ 4(δT)⁴` for `δT < 1`, `cosh 1 ≤ 2 ⟹ cosh²1 ≤ 4`),
visibility floor `c₃ = ¼` at threshold `c₂ = 1`, and the SAME reciprocal gate `1` as the
first-moment `weilProfile`.  This is the formal statement that **squaring keeps the gate** and
only steepens the invisibility exponent (`2 → 4`). -/
noncomputable def secondMomentProfile : DisplacementResolutionProfile where
  detect := secondMomentDetect
  p := 4
  C₁ := 4
  c₂ := 1
  c₃ := 1 / 4
  gate := 1
  c₃_pos := by norm_num
  invisible_small := by
    intro δ T hδ hT hlt
    unfold secondMomentDetect
    have hbase := (cosh_sub_one_sq_resolution δ T hδ.le hT.le).1
    have hprod_nonneg : 0 ≤ δ * T := by positivity
    -- cosh(δT) ≤ cosh 1 ≤ 2  ⟹  cosh(δT)² ≤ 4
    have habs : |δ * T| ≤ 1 := by rw [abs_of_nonneg hprod_nonneg]; linarith
    have hmono : Real.cosh (δ * T) ≤ Real.cosh 1 := by
      rw [Real.cosh_le_cosh]; rwa [abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1)]
    have hcosh1 : Real.cosh 1 ≤ 2 := by
      rw [Real.cosh_eq]
      have h1 : Real.exp 1 ≤ 2.7182818286 := by have := Real.exp_one_lt_d9; linarith
      have h2 : Real.exp (-1) ≤ 1 := by
        rw [Real.exp_neg, inv_le_one_iff₀]; right; exact Real.one_le_exp (by norm_num)
      linarith
    have hcosh_le2 : Real.cosh (δ * T) ≤ 2 := le_trans hmono hcosh1
    have hcoshsq_le4 : Real.cosh (δ * T) ^ 2 ≤ 4 := by nlinarith [Real.one_le_cosh (δ * T)]
    have hpow4_nn : 0 ≤ (δ * T) ^ 4 := by positivity
    calc (Real.cosh (δ * T) - 1) ^ 2
          ≤ (δ * T) ^ 4 * Real.cosh (δ * T) ^ 2 := hbase
      _ ≤ (δ * T) ^ 4 * 4 := by apply mul_le_mul_of_nonneg_left hcoshsq_le4 hpow4_nn
      _ = 4 * (δ * T) ^ 4 := by ring
  visible_large := by
    intro δ T hlt
    unfold secondMomentDetect
    have h1le : (1 : ℝ) ≤ δ * T := le_of_lt hlt
    -- visibility floor: ½(δT)² ≤ cosh(δT)−1 (from one_add_half_sq_le_cosh, NO sign hyp needed)
    have hvis := one_add_half_sq_le_cosh (δ * T)
    have hpow2_ge1 : (1 : ℝ) ≤ (δ * T) ^ 2 := by nlinarith [h1le]
    have hpow4_ge1 : (1 : ℝ) ≤ (δ * T) ^ 4 := by nlinarith [hpow2_ge1, sq_nonneg ((δ*T)^2)]
    -- ½(δT)² ≤ cosh−1 and ½(δT)² ≥ ½ ⟹ cosh−1 ≥ ½ ⟹ (cosh−1)² ≥ ¼ ≥ ¼·1 ... need ¼(δT)⁴
    have hcm1 : 1 / 2 * (δ * T) ^ 2 ≤ Real.cosh (δ * T) - 1 := by linarith
    have hcm1_nn : 0 ≤ Real.cosh (δ * T) - 1 := cosh_sub_one_nonneg _
    have hhalf_nn : 0 ≤ 1 / 2 * (δ * T) ^ 2 := by positivity
    have hsq := mul_le_mul hcm1 hcm1 hhalf_nn hcm1_nn
    have : 1 / 4 * (δ * T) ^ 4 ≤ (Real.cosh (δ * T) - 1) ^ 2 := by nlinarith [hsq]
    nlinarith [this, hpow4_ge1]
  detect_zero_on_line := by intro T; unfold secondMomentDetect; simp

/-! ## §3. THE VERDICT FACTS -/

/-- 🌟🌟 **THE SECOND-MOMENT GATE IS THE FIRST-MOMENT GATE.**  Squaring the Weil off-line
readout does NOT move the `δ·T ≍ 1` displacement-visibility wall:
`secondMomentProfile.gate = weilProfile.gate = 1`.  Only the invisibility exponent changes
(`weilProfile.p = 2` `→` `secondMomentProfile.p = 4`).  The honest content: the second moment
is a STRICTLY steeper-blind detector below the gate (decays like `(δT)⁴`, not `(δT)²`), with
the gate UNCHANGED — squaring buys no resolution. -/
theorem secondMoment_same_gate :
    secondMomentProfile.gate = weilProfile.gate ∧
      secondMomentProfile.p = 4 ∧ weilProfile.p = 2 :=
  ⟨rfl, rfl, rfl⟩

/-- The second-moment detector is a valid (faithful) displacement energy weight: `≥ 0`
everywhere, and `> 0` off the line (`δ ≠ 0`).  This is the formal sense in which squaring
does NOT lose the displacement signal — `M₂(g) = Σ_ρ R₂(η_ρ,T)` vanishes iff every `η_ρ = 0`.
(The faithfulness is per-detector here; the collective height-band caveat — `R₂(γ,T)` small
for `γT ≳ 1` — is the numerical `SECMOM_weight.py` finding, not an obstruction to the weight
being `> 0` off the line.) -/
theorem secondMomentDetect_weight {T : ℝ} (hT : 0 < T) :
    (∀ δ : ℝ, 0 ≤ secondMomentDetect |δ| T) ∧
      (∀ δ : ℝ, δ ≠ 0 → 0 < secondMomentDetect |δ| T) := by
  refine ⟨fun δ => ?_, fun δ hδ => ?_⟩
  · unfold secondMomentDetect; positivity
  · unfold secondMomentDetect
    have hpos : 0 < |δ| := abs_pos.mpr hδ
    have hx : 0 < |δ| * T := mul_pos hpos hT
    have hgt1 : 1 < Real.cosh (|δ| * T) := by
      have := one_add_half_sq_le_cosh (|δ| * T)
      have hsq : 0 < (|δ| * T) ^ 2 := by positivity
      linarith
    have : 0 < Real.cosh (|δ| * T) - 1 := by linarith
    positivity

/-! ## §4. Axiom audit — only `propext`, `Classical.choice`, `Quot.sound`. -/

#print axioms cosh_sub_one_sq_resolution
#print axioms secondMomentProfile
#print axioms secondMoment_same_gate
#print axioms secondMomentDetect_weight

end ScratchSecondMoment
end OverflowResidueRH
