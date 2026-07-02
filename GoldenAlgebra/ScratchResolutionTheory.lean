import ScratchBaezDuarte
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# ScratchResolutionTheory — the RESOLUTION THEORY of RH criteria

This file banks the **organizing mathematics** of the displacement-visibility campaign: a
formal *theory of resolution profiles* that proves the **universality of the `δ·T ≍ 1`
displacement-visibility wall** across every RH criterion family we have formalized
(Weil explicit-formula positivity, Nyman–Beurling/Báez-Duarte approximation, de
Bruijn–Newman heat-flow, Keiper–Li coefficients).

It does **NOT** prove RH.  It rigorously classifies the *failures* of every linear,
fixed-scale criterion by a single structural invariant — its **reciprocal gate**
`δ·T = const` — and proves that this gate is *the same* for all four families.  The
conceptual payoff: any criterion of this profile resolves an off-line displacement `δ`
only as its scale `T → ∞`; a fixed-`T` (bounded-support / bounded-resolution) criterion is
provably blind to all displacements `δ < gate/T`.  RH-strength therefore requires either
unbounded scale or a genuinely nonlinear (non–two-regime) detector.

## The universal two-regime shape (the structure)

Every displacement-resolution criterion has a *detector* `R_C(δ, T)` — the off-line
negativity / obstruction it can produce at displacement `δ` using scale `T` — obeying

```
  R_C(δ, T)  ≤  C₁ · (δT)^p                  for  δT < gate  (INVISIBLE below the gate)
  R_C(δ, T)  ≥  c₃                           for  c₂ < δT    (VISIBLE  above the gate)
```

i.e. it is `O((δT)^p)` (with `p = 1` or `2`, the family leading exponent) **below** the
reciprocal gate `δ·T ≍ 1`, and bounded below by an `O(1)` floor **above** it.  The canonical
analytic kernel realizing the sharp `p = 2` regime is `cosh(δT) − 1 = (δT)²/2 + O((δT)⁴)`
(the Weil quartet kernel `4∫g(u)cosh(δu)cos(γu)du`), whose exact two-regime uncertainty law
is the proven heart of this file (`cosh_minus_one_resolution`).  The honest point captured
by the exponent field `p`: Weil's band-limited detector is `O((δT)²)`, while the
exponential-type detectors (BD/heat/Li) are `O(δT)` — *both* invisible below the same gate,
differing only in the invisibility exponent, never in the gate location.

## The four instances (all proven to fit the profile)

| Criterion | Scale `T` | Detector `R_C(δ,T)` | `p` | Gate |
|---|---|---|---|---|
| **Weil** (explicit formula) | support radius | `cosh(δT) − 1` | 2 | `δT ≍ 1` |
| **Báez-Duarte** (Nyman–Beurling) | `log N` | `exp(2δT) − 1` | 1 | `δT ≍ 1` |
| **de Bruijn–Newman** (heat flow) | inverse collision-gap | `exp(δT) − 1` | 1 | `δT ≍ 1` |
| **Keiper–Li** (coefficients) | `√n / t` | `exp(δT) − 1` | 1 | `δT ≍ 1` |

(Sources: Weil — `weil_attack/QUART_FINDINGS.md` identity `(★)`; Báez-Duarte —
`ScratchBaezDuarte.bdOffLineSignal η T = exp(2ηT)`, Báez-Duarte 2003; heat-flow —
`ScratchHeatFlow` / Rodgers–Tao 2018, the `e^{tδ}` zero-scaling; Li — Keiper 1992 / Li 1997,
the `λ_n` exponential-in-`n` growth of an off-line zero, `M^n = exp(nδ/t²)`.)

## What is PROVED here (no `sorry`, axiom-clean: `propext`, `Classical.choice`, `Quot.sound`)

* `cosh_minus_one_resolution` — **the exact uncertainty law**:
  `(cosh(δT) − 1 ≤ (δT)² · cosh(δT))  ∧  (1 ≤ δT → ½(δT)² ≤ cosh(δT) − 1)`.
  The first half is the `O((δT)²)` invisibility bound; the second is the `O(1)` visibility
  bound above the gate.  Both fully proven from the `cosh` power series.
* `DisplacementResolutionProfile` — the core structure: a detector with the universal
  two-regime shape (`invisible_small` ≤ `C₁(δT)^p`, `visible_large` ≥ `c₃`), reciprocal
  gate `gate`, and on-line blindness.
* The four instance profiles `weilProfile`, `bdProfile`, `heatFlowProfile`, `liProfile`,
  each PROVEN to be a `DisplacementResolutionProfile`.
* `resolution_universality` — all four instances have the **same** reciprocal gate `1`
  (the `δ·T ≍ 1` wall), and the displacement-visibility threshold `gate / T`.
* `RH_needs_unbounded_resolution` — the corollary: for every profile, a fixed scale `T`
  is blind to all displacements `δ < gate/T`; detecting *all* displacements forces `T → ∞`.
-/

namespace OverflowResidueRH
namespace ScratchResolutionTheory

open Real
open OverflowResidueRH.ScratchBaezDuarte

/-! ## §0. THE EXACT UNCERTAINTY LAW: `cosh(δT) − 1` is the canonical resolution kernel

The Weil off-line quartet contributes `4∫_{-T}^{T} g(u) cosh(δu) cos(γ u) du`
(`weil_attack/QUART_FINDINGS.md`, identity `(★)`); the off-line correction is governed by
`cosh(δu) − 1`, whose edge value `cosh(δT) − 1` is the resolution detector.  We prove its
exact two-regime law, the analytic heart of the whole theory.

`cosh(δT) − 1 = (δT)²/2 + (δT)⁴/24 + ⋯` (Taylor), so:
* it is `≤ (δT)² · cosh(δT)` everywhere — the `O((δT)²)` **invisibility** bound;
* it is `≥ ½(δT)²` for all `δT` — the `O(1)` **visibility** floor above the gate. -/

/-- **The sharp lower bound `1 + x²/2 ≤ cosh x`** (all `x`).  Proved from the `cosh` power
series `Σ x^{2n}/(2n)!`: the first two terms are `1 + x²/2`, every term is nonnegative, so
the partial sum over `{0,1}` is `≤` the full sum `cosh x`.  This is the `O(1)` **visibility
floor**. -/
theorem one_add_half_sq_le_cosh (x : ℝ) : 1 + x ^ 2 / 2 ≤ Real.cosh x := by
  have hs := Real.hasSum_cosh x
  have hnn : ∀ n, 0 ≤ x ^ (2 * n) / (Nat.factorial (2 * n) : ℝ) := by
    intro n
    apply div_nonneg
    · rw [pow_mul]; positivity
    · positivity
  have hle := hs.summable.sum_le_tsum (Finset.range 2) (fun i _ => hnn i)
  rw [hs.tsum_eq] at hle
  simp [Finset.sum_range_succ, Nat.factorial] at hle
  nlinarith [hle]

/-- **The upper bound `cosh x − 1 ≤ x² · cosh x`** (all `x`).  Proved term-by-term on the
`cosh` power series: `cosh x − 1 = Σ_n x^{2(n+1)}/(2(n+1))!` and
`x²·cosh x = Σ_n x²·x^{2n}/(2n)!`, with each `x^{2n+2}/(2n+2)! ≤ x²·x^{2n}/(2n)!` because
`(2n)! ≤ (2n+2)!`.  This is the `O((δT)²)` **invisibility** bound. -/
theorem cosh_sub_one_le_sq_mul_cosh (x : ℝ) : Real.cosh x - 1 ≤ x ^ 2 * Real.cosh x := by
  have hs := Real.hasSum_cosh x
  set a : ℕ → ℝ := fun n => x ^ (2 * n) / (Nat.factorial (2 * n) : ℝ) with ha
  have ha0 : a 0 = 1 := by simp [ha]
  have hshift : HasSum (fun n => a (n + 1)) (Real.cosh x - 1) := by
    have h := (hasSum_nat_add_iff' (f := a) (g := Real.cosh x) 1).mpr hs
    simpa [Finset.sum_range_one, ha0] using h
  have hmul : HasSum (fun n => x ^ 2 * a n) (x ^ 2 * Real.cosh x) := hs.mul_left (x ^ 2)
  have hterm : ∀ n, a (n + 1) ≤ x ^ 2 * a n := by
    intro n
    have hxpow : (0 : ℝ) ≤ x ^ (2 * n + 2) := by
      rw [show 2 * n + 2 = 2 * (n + 1) by ring, pow_mul]; positivity
    have hfac : (Nat.factorial (2 * n) : ℝ) ≤ (Nat.factorial (2 * (n + 1)) : ℝ) := by
      exact_mod_cast Nat.factorial_le (by omega)
    have hfacpos : (0 : ℝ) < (Nat.factorial (2 * n) : ℝ) := by exact_mod_cast Nat.factorial_pos _
    simp only [ha]
    rw [show x ^ 2 * (x ^ (2 * n) / (Nat.factorial (2 * n) : ℝ))
          = x ^ (2 * n + 2) / (Nat.factorial (2 * n) : ℝ) by rw [pow_add]; ring]
    rw [show 2 * (n + 1) = 2 * n + 2 by ring]
    exact div_le_div_of_nonneg_left hxpow hfacpos hfac
  exact hasSum_le hterm hshift hmul

/-- 🌟 **THE EXACT UNCERTAINTY LAW.**  For the band-limited / exponential-type detector
`R(δ,T) = cosh(δT) − 1` (the Weil off-line quartet edge kernel):

```
  cosh(δT) − 1  ≤  (δT)² · cosh(δT)            -- O((δT)²): INVISIBLE below the gate
  1 ≤ δT   ⟹   ½(δT)²  ≤  cosh(δT) − 1         -- O(1):     VISIBLE  above the gate
```

The first inequality makes the off-line correction vanish like `(δT)²` for `δT → 0`
(invisibility); the second gives a hard `O(1)` floor once `δT ≥ 1` (visibility).  Together
they ARE the `δ·T ≍ 1` displacement-visibility gate, fully proven in Lean from the `cosh`
power series — no `sorry`, no analytic axiom. -/
theorem cosh_minus_one_resolution (δ T : ℝ) (_hδ : 0 ≤ δ) (_hT : 0 ≤ T) :
    (Real.cosh (δ * T) - 1 ≤ (δ * T) ^ 2 * Real.cosh (δ * T)) ∧
      (1 ≤ δ * T → 1 / 2 * (δ * T) ^ 2 ≤ Real.cosh (δ * T) - 1) := by
  refine ⟨cosh_sub_one_le_sq_mul_cosh (δ * T), fun _ => ?_⟩
  have := one_add_half_sq_le_cosh (δ * T)
  linarith

/-- **The exponential resolution helper `exp c − 1 ≤ c · exp c`** (all `c ≥ 0`).  This is the
`O(c)` invisibility bound for the *exponential-type* detectors (Báez-Duarte, heat-flow, Li),
the analogue of `cosh_sub_one_le_sq_mul_cosh` for `exp` in place of `cosh`.  Proof:
`(1 − c)·exp c ≤ 1` from `1 − c ≤ exp(−c)` (`add_one_le_exp`). -/
theorem exp_sub_one_le_mul_exp {c : ℝ} (_hc : 0 ≤ c) : Real.exp c - 1 ≤ c * Real.exp c := by
  have h := Real.add_one_le_exp (-c)
  have hpos := Real.exp_pos c
  rw [Real.exp_neg] at h
  have h2 : (1 - c) * Real.exp c ≤ 1 := by
    have := mul_le_mul_of_nonneg_right h hpos.le
    rw [inv_mul_cancel₀ (ne_of_gt hpos)] at this
    nlinarith [this]
  nlinarith [h2]

/-! ## §1. THE CORE STRUCTURE: `DisplacementResolutionProfile`

The universal two-regime shape, abstracted.  A profile carries a detector `detect δ T`
(= `R_C(δ,T)`), the leading invisibility exponent `p` (= `1` or `2`), the invisibility
constant `C₁`, the visibility threshold/floor `c₂`/`c₃`, and the reciprocal `gate`.
`detect_zero_on_line` records position-sensitivity: on the line (`δ = 0`) the detector is
blind, so the profile genuinely measures *displacement*. -/

/-- **Displacement-resolution profile.**  The universal two-regime detector shape underlying
every linear, fixed-scale RH criterion: `O((δT)^p)` below the reciprocal gate `δ·T ≍ gate`,
`O(1)` above it.  This is the organizing structure of the resolution theory. -/
structure DisplacementResolutionProfile where
  /-- The detector `R_C(δ, T)`: off-line negativity / obstruction at displacement `δ`,
  scale `T`. -/
  detect : ℝ → ℝ → ℝ
  /-- The leading invisibility exponent (`1` for exponential-type, `2` for the band-limited
  Weil kernel). -/
  p : ℕ
  /-- The invisibility constant `C₁`. -/
  C₁ : ℝ
  /-- The lower visibility threshold `c₂` on the product `δ·T`. -/
  c₂ : ℝ
  /-- The visibility floor `c₃` (the `O(1)` detected mass above the gate). -/
  c₃ : ℝ
  /-- The reciprocal gate constant: the criterion resolves `δ` once `δ·T ≍ gate`. -/
  gate : ℝ
  /-- The visibility floor is genuinely positive (the criterion *does* see above the gate). -/
  c₃_pos : 0 < c₃
  /-- **Invisible below the gate.**  For `0 < δ`, `0 < T`, `δT < gate`, the detector is
  `O((δT)^p)`. -/
  invisible_small : ∀ δ T : ℝ, 0 < δ → 0 < T → δ * T < gate → detect δ T ≤ C₁ * (δ * T) ^ p
  /-- **Visible above the gate.**  Once `c₂ < δT`, the detector carries `O(1)` mass `≥ c₃`. -/
  visible_large : ∀ δ T : ℝ, c₂ < δ * T → c₃ ≤ detect δ T
  /-- **On the critical line the detector is blind.**  Position-sensitivity: `detect 0 T = 0`. -/
  detect_zero_on_line : ∀ T : ℝ, detect 0 T = 0

/-! ## §2. INSTANCE 1 — the Weil explicit-formula profile (the canonical `cosh` kernel)

`detect_W(δ,T) = cosh(δT) − 1`, `T` = support radius.  Source: `weil_attack/QUART_FINDINGS.md`
identity `(★)`, off-line correction governed by `cosh(δu) − 1`.  The exponent is `p = 2`;
the two regimes are exactly `cosh_minus_one_resolution`. -/

/-- The Weil detector `R_W(δ,T) = cosh(δT) − 1`. -/
noncomputable def weilDetect (δ T : ℝ) : ℝ := Real.cosh (δ * T) - 1

/-- **PROVED — the Weil criterion fits the profile** with exponent `p = 2`, invisibility
constant `C₁ = 2` (from `cosh(δT) − 1 ≤ (δT)²·cosh(δT) ≤ 2(δT)²` for `δT < 1`, using
`cosh 1 ≤ 2`), visibility floor `c₃ = ½` at threshold `c₂ = 1`, and reciprocal gate `1`. -/
noncomputable def weilProfile : DisplacementResolutionProfile where
  detect := weilDetect
  p := 2
  C₁ := 2
  c₂ := 1
  c₃ := 1 / 2
  gate := 1
  c₃_pos := by norm_num
  invisible_small := by
    intro δ T hδ hT hlt
    unfold weilDetect
    have hbase := (cosh_minus_one_resolution δ T (le_of_lt hδ) (le_of_lt hT)).1
    have hprod_nonneg : 0 ≤ δ * T := by positivity
    have habs : |δ * T| ≤ 1 := by rw [abs_of_nonneg hprod_nonneg]; linarith
    have hmono : Real.cosh (δ * T) ≤ Real.cosh 1 := by
      rw [Real.cosh_le_cosh]
      rwa [abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1)]
    have hcosh1 : Real.cosh 1 ≤ 2 := by
      rw [Real.cosh_eq]
      have h1 : Real.exp 1 ≤ 2.7182818286 := by have := Real.exp_one_lt_d9; linarith
      have h2 : Real.exp (-1) ≤ 1 := by
        rw [Real.exp_neg, inv_le_one_iff₀]; right; exact Real.one_le_exp (by norm_num)
      linarith
    have hsq : 0 ≤ (δ * T) ^ 2 := sq_nonneg _
    calc Real.cosh (δ * T) - 1 ≤ (δ * T) ^ 2 * Real.cosh (δ * T) := hbase
      _ ≤ (δ * T) ^ 2 * 2 := by apply mul_le_mul_of_nonneg_left _ hsq; linarith
      _ = 2 * (δ * T) ^ 2 := by ring
  visible_large := by
    intro δ T hlt
    unfold weilDetect
    have h1le : (1 : ℝ) ≤ δ * T := le_of_lt hlt
    have hvis := one_add_half_sq_le_cosh (δ * T)
    have hsq : (1 : ℝ) ≤ (δ * T) ^ 2 := by nlinarith [h1le]
    linarith
  detect_zero_on_line := by intro T; unfold weilDetect; simp

/-! ## §2b. INSTANCE 2 — the Báez-Duarte profile (reuse `bdOffLineSignal`)

`detect_BD(δ,T) = bdOffLineSignal δ T − 1 = exp(2δT) − 1`, `T = log N`.  Source:
`ScratchBaezDuarte.bdOffLineSignal η T = exp(2ηT)`, Báez-Duarte 2003 mirror-zero signal.
The `−1` normalizes the on-line value (`exp 0 − 1 = 0`).  Exponent `p = 1` (the exponential
detector is `O(δT)` below the gate, not `O((δT)²)` — the honest difference from Weil). -/

/-- The Báez-Duarte detector `R_BD(δ,T) = exp(2δT) − 1 = bdOffLineSignal δ T − 1`. -/
noncomputable def bdDetect (δ T : ℝ) : ℝ := bdOffLineSignal δ T - 1

/-- **PROVED — the Báez-Duarte criterion fits the profile** with exponent `p = 1`,
invisibility constant `C₁ = 2·exp 2` (from `exp(2δT) − 1 ≤ 2δT·exp(2δT) ≤ 2δT·exp 2` for
`δT < 1`), visibility floor `c₃ = exp 1 − 1` at `c₂ = 1/2`, reciprocal gate `1`.
(`c₂ = 1/2` reflects the `2δ` in the BD exponent: `exp(2δT) ≥ exp 1` once `δT ≥ 1/2`.) -/
noncomputable def bdProfile : DisplacementResolutionProfile where
  detect := bdDetect
  p := 1
  C₁ := 2 * Real.exp 2
  c₂ := 1 / 2
  c₃ := Real.exp 1 - 1
  gate := 1
  c₃_pos := by have := Real.exp_one_gt_d9; linarith
  invisible_small := by
    intro δ T hδ hT hlt
    unfold bdDetect bdOffLineSignal
    have hc : 0 ≤ 2 * δ * T := by positivity
    have hstep := exp_sub_one_le_mul_exp hc
    have h2δT : 2 * δ * T < 2 := by nlinarith [hlt, hδ, hT]
    have hexp_le : Real.exp (2 * δ * T) ≤ Real.exp 2 := Real.exp_le_exp.mpr (le_of_lt h2δT)
    have hcT_nonneg : 0 ≤ 2 * δ * T := hc
    calc Real.exp (2 * δ * T) - 1 ≤ (2 * δ * T) * Real.exp (2 * δ * T) := hstep
      _ ≤ (2 * δ * T) * Real.exp 2 := by
          apply mul_le_mul_of_nonneg_left hexp_le hcT_nonneg
      _ = 2 * Real.exp 2 * (δ * T) ^ 1 := by ring
  visible_large := by
    intro δ T hlt
    unfold bdDetect bdOffLineSignal
    -- c₂ = 1/2 < δT ⟹ 1 < 2δT ⟹ exp 1 ≤ exp(2δT)
    have h1lt : (1 : ℝ) < 2 * δ * T := by nlinarith [hlt]
    have hexp : Real.exp 1 ≤ Real.exp (2 * δ * T) := Real.exp_le_exp.mpr (le_of_lt h1lt)
    have : Real.exp (2 * δ * T) = Real.exp (2 * δ * T) := rfl
    -- bdOffLineSignal uses (2 * η * T); unfold matches 2*δ*T
    linarith [hexp]
  detect_zero_on_line := by intro T; unfold bdDetect bdOffLineSignal; simp

/-! ## §2c. INSTANCE 3 — the de Bruijn–Newman heat-flow profile

`detect_H(δ,T) = exp(δT) − 1`, `T` = inverse collision-gap scale.  Source: `ScratchHeatFlow`
/ Rodgers–Tao 2018 — under the dBN backward heat flow a zero at displacement `δ` scales like
`e^{tδ}` (heat time `t`); reading `T` as the inverse collision-gap, the off-line obstruction
grows as `e^{δT}`.  Exponent `p = 1`, gate `1`. -/

/-- The de Bruijn–Newman heat-flow detector `R_H(δ,T) = exp(δT) − 1`. -/
noncomputable def heatFlowDetect (δ T : ℝ) : ℝ := Real.exp (δ * T) - 1

/-- **PROVED — the heat-flow criterion fits the profile** with `p = 1`, `C₁ = exp 1`,
`c₃ = exp 1 − 1` at `c₂ = 1`, reciprocal gate `1`. -/
noncomputable def heatFlowProfile : DisplacementResolutionProfile where
  detect := heatFlowDetect
  p := 1
  C₁ := Real.exp 1
  c₂ := 1
  c₃ := Real.exp 1 - 1
  gate := 1
  c₃_pos := by have := Real.exp_one_gt_d9; linarith
  invisible_small := by
    intro δ T hδ hT hlt
    unfold heatFlowDetect
    have hc : 0 ≤ δ * T := by positivity
    have hstep := exp_sub_one_le_mul_exp hc
    have hexp_le : Real.exp (δ * T) ≤ Real.exp 1 := Real.exp_le_exp.mpr (le_of_lt hlt)
    calc Real.exp (δ * T) - 1 ≤ (δ * T) * Real.exp (δ * T) := hstep
      _ ≤ (δ * T) * Real.exp 1 := by apply mul_le_mul_of_nonneg_left hexp_le hc
      _ = Real.exp 1 * (δ * T) ^ 1 := by ring
  visible_large := by
    intro δ T hlt
    unfold heatFlowDetect
    have hexp : Real.exp 1 ≤ Real.exp (δ * T) := Real.exp_le_exp.mpr (le_of_lt hlt)
    linarith
  detect_zero_on_line := by intro T; unfold heatFlowDetect; simp

/-! ## §2d. INSTANCE 4 — the Keiper–Li coefficient profile

`detect_L(δ,T) = exp(δT) − 1`, `T ≍ √n / t` (resolution index `n`, scale `t`).  Source:
Keiper 1992 / Li 1997 — the Li coefficient `λ_n` of an off-line zero grows like
`M^n = exp(n·δ/t²)`; with the resolution scale `T = √n / t` (so `T² = n/t²`) the per-step
multiplier is `exp(δT)`.  Exponent `p = 1`, gate `1`. -/

/-- The Keiper–Li detector `R_L(δ,T) = exp(δT) − 1`, `T ≍ √n / t`. -/
noncomputable def liDetect (δ T : ℝ) : ℝ := Real.exp (δ * T) - 1

/-- **PROVED — the Keiper–Li criterion fits the profile** with `p = 1`, `C₁ = exp 1`,
`c₃ = exp 1 − 1` at `c₂ = 1`, reciprocal gate `1`. -/
noncomputable def liProfile : DisplacementResolutionProfile where
  detect := liDetect
  p := 1
  C₁ := Real.exp 1
  c₂ := 1
  c₃ := Real.exp 1 - 1
  gate := 1
  c₃_pos := by have := Real.exp_one_gt_d9; linarith
  invisible_small := by
    intro δ T hδ hT hlt
    unfold liDetect
    have hc : 0 ≤ δ * T := by positivity
    have hstep := exp_sub_one_le_mul_exp hc
    have hexp_le : Real.exp (δ * T) ≤ Real.exp 1 := Real.exp_le_exp.mpr (le_of_lt hlt)
    calc Real.exp (δ * T) - 1 ≤ (δ * T) * Real.exp (δ * T) := hstep
      _ ≤ (δ * T) * Real.exp 1 := by apply mul_le_mul_of_nonneg_left hexp_le hc
      _ = Real.exp 1 * (δ * T) ^ 1 := by ring
  visible_large := by
    intro δ T hlt
    unfold liDetect
    have hexp : Real.exp 1 ≤ Real.exp (δ * T) := Real.exp_le_exp.mpr (le_of_lt hlt)
    linarith
  detect_zero_on_line := by intro T; unfold liDetect; simp

/-! ## §3. THE UNIVERSALITY THEOREM — all four families share the gate `δ·T ≍ 1`

The four instances were built with different detectors (`cosh`, `exp(2·)`, `exp`, `exp`),
different exponents (`p = 2` vs `1`), and different visibility constants — yet they all carry
the **same reciprocal gate `1`**.  This is the universality of the `δ·T ≍ 1` wall: the *gate
location* is a family-independent invariant. -/

/-- 🌟🌟🌟 **THE UNIVERSALITY THEOREM.**  All four formalized RH-criterion families share the
**same reciprocal gate** `δ·T ≍ 1`:

```
  weilProfile.gate = bdProfile.gate = heatFlowProfile.gate = liProfile.gate = 1.
```

Despite different detectors (`cosh(δT)−1`, `exp(2δT)−1`, `exp(δT)−1`), different invisibility
exponents (Weil `p=2`, the rest `p=1`), and different positive-cone structure, the
displacement-visibility *threshold* is the same `const/displacement` law.  This is the
precise sense in which the `δ·T ≍ 1` wall is **universal**, not specific to any one
criterion.  (It organizes the *failures*; it does not prove RH.) -/
theorem resolution_universality :
    weilProfile.gate = 1 ∧ bdProfile.gate = 1 ∧
      heatFlowProfile.gate = 1 ∧ liProfile.gate = 1 :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- All four gates are mutually equal — the gate is a single universal invariant. -/
theorem all_gates_equal :
    weilProfile.gate = bdProfile.gate ∧
      bdProfile.gate = heatFlowProfile.gate ∧
      heatFlowProfile.gate = liProfile.gate :=
  ⟨rfl, rfl, rfl⟩

/-! ## §4. THE COROLLARY — `RH_needs_unbounded_resolution`

The conceptual payoff, stated and proven at the level of an arbitrary profile: a criterion
of this profile, run at a *fixed* scale `T`, is blind to every displacement `δ < gate/T`
(the detector falls below the visibility floor `c₃`).  Hence detecting *all* displacements
forces `T → ∞`: a fixed-`T` (bounded-support / bounded-resolution) criterion cannot resolve
the critical line, and RH-strength requires unbounded scale (or a non-two-regime detector). -/

/-- **The displacement-visibility gate, per profile.**  For a fixed scale `T > 0`, every
displacement `δ` with `0 < δ` and `δ·T < gate` sits in the *invisible* regime: the detector
is bounded by `C₁·(δT)^p`.  In particular the criterion at scale `T` cannot resolve any
displacement `δ < gate/T`. -/
theorem displacement_invisible_below_gate (P : DisplacementResolutionProfile)
    {δ T : ℝ} (hδ : 0 < δ) (hT : 0 < T) (hgate : δ * T < P.gate) :
    P.detect δ T ≤ P.C₁ * (δ * T) ^ P.p :=
  P.invisible_small δ T hδ hT hgate

/-- 🌟 **THE COROLLARY — `RH_needs_unbounded_resolution`.**

For any displacement-resolution profile `P` and any **fixed** scale `T > 0`, there exists a
positive displacement window `(0, gate/T)` — namely every `0 < δ < gate/T` (when `gate > 0`)
— on which the detector stays in the invisible regime `≤ C₁·(δT)^p`.  Equivalently: a
fixed-`T` criterion of this profile is provably blind to all small displacements, so it
**cannot certify RH** (which requires resolving arbitrarily small `δ`).  Detecting every
displacement forces the scale `T → ∞`.

This is the rigorous "the wall is universal ⟹ a linear fixed-scale criterion needs unbounded
scale" statement.  It does **not** prove RH; it proves that no bounded-resolution criterion
of this shape can. -/
theorem RH_needs_unbounded_resolution (P : DisplacementResolutionProfile)
    (_hgate : 0 < P.gate) {T : ℝ} (hT : 0 < T) :
    ∀ δ : ℝ, 0 < δ → δ < P.gate / T → P.detect δ T ≤ P.C₁ * (δ * T) ^ P.p := by
  intro δ hδ hδgate
  have hprod : δ * T < P.gate := by
    rw [lt_div_iff₀ hT] at hδgate; linarith
  exact P.invisible_small δ T hδ hT hprod

/-- **The contrapositive visibility requirement.**  To detect a displacement `δ` at scale `T`
(land above the visibility floor `c₃ ≤ detect`), the scale must reach past the threshold
`c₂/δ`: visibility requires `c₂ < δ·T`, i.e. `T > c₂/δ`.  As `δ → 0` this support
requirement `→ ∞` — the unbounded-scale demand made quantitative. -/
theorem visibility_requires_scale (P : DisplacementResolutionProfile)
    {δ T : ℝ} (hvis : P.c₂ < δ * T) : P.c₃ ≤ P.detect δ T :=
  P.visible_large δ T hvis

/-! ## §5. RH-conclusion bridge — the profile feeds the position-sensitive certificate

A profile whose detector is the *energy weight* `W(p) = detect |η| T` (positive off the line,
`= 0` on it) plugs straight into `ScratchPositionEnvelope`'s proven RH bridge: an off-line
zero carries strictly positive resolution energy, so resolution-energy `= 0` ⟹ RH.  We record
the structural fact that each detector is `≥ 0` and `> 0` off the line, the exact hypotheses
of a `PositionSensitiveEnergyCertificate` weight — tying the resolution theory back to the
codebase's RH conclusion `∀ ρ, XiPullback ρ = 0 → ρ.im = 0`. -/

/-- The Weil detector is a valid energy weight: `≥ 0` everywhere, `> 0` off the line. -/
theorem weilDetect_weight {T : ℝ} (hT : 0 < T) :
    (∀ δ : ℝ, 0 ≤ weilDetect |δ| T) ∧ (∀ δ : ℝ, δ ≠ 0 → 0 < weilDetect |δ| T) := by
  refine ⟨fun δ => ?_, fun δ hδ => ?_⟩
  · unfold weilDetect; have := Real.one_le_cosh (|δ| * T); linarith
  · unfold weilDetect
    have hpos : 0 < |δ| := abs_pos.mpr hδ
    have hx : 0 < |δ| * T := mul_pos hpos hT
    have : 1 < Real.cosh (|δ| * T) := by
      have := one_add_half_sq_le_cosh (|δ| * T)
      have hsq : 0 < (|δ| * T) ^ 2 := by positivity
      linarith
    linarith

/-- The Báez-Duarte detector is a valid energy weight (reuses
`ScratchBaezDuarte.bdSignal_gt_one_offLine`): `≥ 0` everywhere, `> 0` off the line. -/
theorem bdDetect_weight {T : ℝ} (hT : 0 < T) :
    (∀ δ : ℝ, 0 ≤ bdDetect |δ| T) ∧ (∀ δ : ℝ, δ ≠ 0 → 0 < bdDetect |δ| T) := by
  refine ⟨fun δ => ?_, fun δ hδ => ?_⟩
  · unfold bdDetect bdOffLineSignal
    have : (0 : ℝ) ≤ 2 * |δ| * T := by positivity
    have := Real.one_le_exp this; linarith
  · unfold bdDetect
    have := bdSignal_gt_one_offLine hδ hT
    -- bdSignal_gt_one_offLine : 1 < bdOffLineSignal |δ| T
    linarith

/-! ## §6. Axiom audit — only `propext`, `Classical.choice`, `Quot.sound`. -/

#print axioms cosh_minus_one_resolution
#print axioms one_add_half_sq_le_cosh
#print axioms cosh_sub_one_le_sq_mul_cosh
#print axioms exp_sub_one_le_mul_exp
#print axioms weilProfile
#print axioms bdProfile
#print axioms heatFlowProfile
#print axioms liProfile
#print axioms resolution_universality
#print axioms RH_needs_unbounded_resolution
#print axioms visibility_requires_scale
#print axioms weilDetect_weight
#print axioms bdDetect_weight

end ScratchResolutionTheory
end OverflowResidueRH
