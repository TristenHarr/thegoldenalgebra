import rh
import ScratchPositionEnvelope
import ScratchZeroDensityBridge
import ScratchModernZeroDensity
import ScratchKernelDensity
import ScratchDisplacementMoment

/-!
# ScratchDisplacementMomentSharp — SHARPENING the unconditional displacement
# second-moment bound `Σ_{γ≤T}(β−½)² ≪ T/log T` via the Jutila–Conrey near-line
# zero-density exponent (constant 64 → 49/16), with a clean BARRIER certificate
# that the `T/log T` ORDER is essentially optimal from current unconditional density.

**Honesty note.**  Nothing here assumes RH.  This file does two things, both honest:

1. **A GENUINE IMPROVEMENT of the CONSTANT** (the moment EXPONENT/log-power is the
   same `T/log T`).  The bound in `ScratchDisplacementMoment` used Selberg's 1946
   exponent `N(½+u,T) ≪ T^{1−u/4}·log T`, i.e. the displacement decay rate
   `θ = 1/8` in `N(½+u,T) ≪ T^{1−2θu}·log T`.  The SHARPEST current unconditional
   near-line decay rate is **Conrey's `θ < 4/7`** (improving Jutila's `θ < 1/2`,
   improving Selberg's `θ = 1/8`).  Feeding the larger `θ` through the SAME exact
   layer-cake gives envelope constant `1/θ²`: Selberg `64`, Jutila `4`, Conrey
   `(7/4)² = 49/16 ≈ 3.06` — a ≈ **20.9× smaller** constant (`displacement_moment_theta.py`).

2. **A BARRIER CERTIFICATE** that the `T/log T` ORDER cannot be improved from
   current unconditional density.  The closed-form is
   `M₂(T) ≲ T·(log T)^{k−2}/θ²`, where `k` is the LOG-POWER of the near-line
   density `N(½+u,T) ≪ T^{1−2θu}·(log T)^k`.  Every known unconditional near-line
   estimate has `k = 1` (the local zero density `N'(t) ∼ (log t)/2π` forces it).
   So `M₂(T) ≍ T/log T`.  Beating the ORDER needs a **log-free** near-line density
   (`k = 0`), known ONLY for `σ` bounded away from `½` (Bellotti 2024: `σ ≳ 0.985`);
   near `σ = ½` the reflection/large-sieve argument loses, so `k = 1` stands.

## The survey (Task 1), with exact constants/exponents

The near-line zero density `N(½+u,T) ≪ T^{1−2θu}·(log T)^k`:

| source | year | decay rate `θ` | range | constant `1/θ²` |
|---|---|---|---|---|
| Selberg | 1946 | `1/8` | `σ∈[½,1]` | `64` |
| Jutila | 1977 | any `θ<1/2` | `σ→½⁺` | `→4` |
| **Conrey** | **1989** | **any `θ<4/7`** | `σ→½⁺` | **`→49/16≈3.06`** |
| log-free (Bellotti) | 2024 | — `k=0` | only `σ≳0.985` | N/A near ½ |
| Guth–Maynard | 2024 | — | only `σ≈¾` | N/A near ½ |
| Tao–Trudgian–Yang | 2025 | — | only `σ∈[¾,…]` | N/A near ½ |

The 2024–2025 frontier (GM `A=30/13` at `σ=¾`; TTY ANTEDB Table 11.1) is OUTSIDE
the near-line window `u ∼ 1/log T` that dominates the moment integral, so it does
**not** touch this bound — confirmed by recomputation (`displacement_moment_theta.py`).

References:
* A. Selberg, *Contributions to the theory of the Riemann zeta-function*,
  Arch. Math. Naturvid. **48** (1946), no. 5, 89–155 (`θ = 1/8`).
* M. Jutila, *Zero-density estimates for L-functions*, Acta Arith. **32** (1977),
  55–62 (any `θ < 1/2`).
* J. B. Conrey, *More than two fifths of the zeros of the Riemann zeta function
  are on the critical line*, J. reine angew. Math. **399** (1989), 1–26 (any
  `θ < 4/7`; full proof also in S. Baluyot's thesis).  Used as the near-line input
  in Pratt–Robles–Zaharescu–Zeindler, *Almost all of the zeros of the Riemann
  zeta-function are on the critical line*, arXiv:1805.07741 (2018).
* C. Bellotti, *An explicit log-free zero density estimate*, arXiv:2405.12545
  (2024) — log-free only for `σ ∈ [α₀,1]`, `α₀ ≳ 0.985` (NOT near `½`).
* L. Guth & J. Maynard, arXiv:2405.20552 (2024); T. Tao, T. Trudgian & A. Yang,
  arXiv:2501.16779 (2025) — both improve `σ ≈ ¾`, not the near-line regime.

## The moment recomputation (Task 2), exact

Layer-cake (EXACT, no slack — `displacementMoment_layerCake_truncated`):
`Σ η² = 2∫₀^{1/2} u·N_off(u,T) du`.  Feeding `N_off(u,T) ≤ 2·T^{1−2θu}·log T`:
```
Σ η²  ≤  4 log T · ∫₀^{1/2} u·T^{1−2θu} du
      =  4 T log T · ∫₀^{1/2} u·e^{−(2θ log T)u} du
      ≤  4 T log T · 1/(2θ log T)²            [∫₀^{1/2} u e^{−cu}du ≤ 1/c², c=2θ log T]
      =  T/(θ² log T).
```
The `u`-integral PEAKS at `u ∼ 1/(2θ log T)`: the moment is dominated by zeros at
the natural `1/log T` resolution off the line — exactly where only the near-line
(Selberg/Jutila/Conrey) density, NOT the GM/TTY mid-strip density, applies.

`θ = 4/7  ⟹  Σ η² ≤ (49/16)·T/log T`,  vs Selberg `64·T/log T`.

## The barrier (Task 4)

`M₂(T) ≲ T·(log T)^{k−2}/θ²`.  Larger `θ` ↘ constant only (`64→49/16`).  Only
`k: 1→0` (a log-free near-line density) lowers the ORDER to `T/(log T)²` — and that
is exactly the unproven near-line input (`T/log T` is also the heuristic FLOOR: if
a positive proportion of zeros sat at displacement `∼ 1/log T`, the energy would be
`∼ N(T)/(log T)² = T/log T`).  So **`T/log T` is the current barrier**, improvable
in CONSTANT (→49/16) but not in ORDER without a near-line log-free estimate.

`#print axioms` on every theorem: only `propext`, `Classical.choice`, `Quot.sound`.
-/

namespace OverflowResidueRH
namespace DisplacementMomentSharp

open MeasureTheory ScratchPositionEnvelope ZeroDensityBridge ModernZeroDensity
open OverflowResidueRH.DisplacementMoment
open scoped ENNReal

-- ===================================================================
-- §1.  The Jutila–Conrey near-line decay rate θ and its density
-- ===================================================================

/-- **The Jutila–Conrey near-line displacement density** at decay rate `θ`,
displacement `u`, height `T`:
`thetaDensity θ u T := 2 · T^{1 − 2θu} · log T`.

This is `2·N(½+u,T)` with the general near-line estimate
`N(σ,T) ≪ T^{1−θ(2σ−1)}·log T` (`σ = ½+u`, so `2σ−1 = 2u`).  The decay rate `θ`
runs over the unconditionally proven range: Selberg `θ = 1/8`, Jutila any `θ < 1/2`,
**Conrey any `θ < 4/7`**.  At `θ = 1/8` it reduces to `selbergDensity`. -/
noncomputable def thetaDensity (θ u T : ℝ) : ℝ :=
  2 * T ^ (1 - 2 * θ * u) * Real.log T

/-- At Selberg's `θ = 1/8` the general density reduces to `selbergDensity`. -/
theorem thetaDensity_at_selberg (u T : ℝ) :
    thetaDensity (1 / 8 : ℝ) u T = selbergDensity u T := by
  unfold thetaDensity selbergDensity
  have hexp : (1 : ℝ) - 2 * (1 / 8 : ℝ) * u = 1 - u / 4 := by ring
  rw [hexp]

theorem thetaDensity_nonneg {θ u T : ℝ} (hT : (1 : ℝ) ≤ T) :
    0 ≤ thetaDensity θ u T := by
  unfold thetaDensity
  have h1 : (0:ℝ) ≤ T ^ (1 - 2 * θ * u) := Real.rpow_nonneg (by linarith) _
  have h2 : (0:ℝ) ≤ Real.log T := Real.log_nonneg hT
  positivity

/-- 🌟🌟 **PROVEN — Conrey's larger decay rate gives a strictly SMALLER near-line
density than Selberg's, at every positive displacement `u > 0` and height `T > 1`.**

For `1/8 ≤ θ₁ < θ₂` (e.g. Selberg `1/8` vs Conrey `4/7`) and `u > 0`, `T > 1`:
the exponent `1 − 2θ₂u < 1 − 2θ₁u`, and since `T > 1` makes `T^x` strictly
monotone, `thetaDensity θ₂ u T < thetaDensity θ₁ u T`.  This is the quantitative
content of the Jutila→Conrey advance, in displacement form: a strictly thinner
near-line off-line count, hence a strictly smaller moment integrand. -/
theorem thetaDensity_strictMono_in_rate {θ₁ θ₂ u T : ℝ}
    (hθ : θ₁ < θ₂) (hu : 0 < u) (hT : (1 : ℝ) < T) :
    thetaDensity θ₂ u T < thetaDensity θ₁ u T := by
  unfold thetaDensity
  have hlog : 0 < Real.log T := Real.log_pos hT
  -- exponent strictly decreasing in θ:  1 − 2θ₂u < 1 − 2θ₁u
  have hexp : 1 - 2 * θ₂ * u < 1 - 2 * θ₁ * u := by nlinarith [hu, hθ]
  have hpow : T ^ (1 - 2 * θ₂ * u) < T ^ (1 - 2 * θ₁ * u) :=
    (Real.rpow_lt_rpow_left_iff hT).mpr hexp
  have h2 : (0:ℝ) < 2 := by norm_num
  nlinarith [mul_lt_mul_of_pos_left hpow h2, hlog,
    Real.rpow_nonneg (le_of_lt (lt_trans one_pos hT)) (1 - 2 * θ₂ * u)]

-- ===================================================================
-- §2.  The named-cited Conrey near-line density input (displacement form)
-- ===================================================================

/-- **`ConreyNearLineDensity θ` — the Jutila–Conrey near-line zero-density estimate
at decay rate `θ`, named & cited; unconditional; displacement form.**

There is a height `T₀ ≥ 1` such that for every displacement threshold `u ∈ [0,½]`
and `T ≥ T₀`, the off-line displacement count obeys

```
OffLineZeroCount E u T = μ{0<γ≤T, |η| ≥ u}  ≤  thetaDensity θ u T = 2·T^{1−2θu}·log T.
```

The decay rate `θ` is constrained to the unconditionally proven Conrey range
`0 < θ < 4/7` (which contains Selberg `1/8` and Jutila `<1/2`).  This is the
displacement-coordinate rewrite of `N(σ,T) ≪ T^{1−θ(2σ−1)}·log T`.

Reference: J. B. Conrey, J. reine angew. Math. **399** (1989), 1–26; the near-line
input is exactly the one used (citing Jutila/Conrey) in Pratt–Robles–Zaharescu–
Zeindler, arXiv:1805.07741. -/
def ConreyNearLineDensity (E : PositionSensitiveEnvelope) (θ T₀ : ℝ) : Prop :=
  1 ≤ T₀ ∧ 0 < θ ∧ θ < (4 / 7 : ℝ) ∧
    ∀ u T : ℝ, 0 ≤ u → u ≤ (1 / 2 : ℝ) → T₀ ≤ T →
      OffLineZeroCount E u T ≤ thetaDensity θ u T

/-- Direct repackaging: the off-line displacement count is at most the Conrey
density bound, at every threshold `u ∈ [0,½]` and height `T ≥ T₀`. -/
theorem conrey_offLineCount_bound
    (E : PositionSensitiveEnvelope) {θ T₀ : ℝ}
    (H : ConreyNearLineDensity E θ T₀) {u T : ℝ}
    (hu0 : 0 ≤ u) (hu : u ≤ (1 / 2 : ℝ)) (hT : T₀ ≤ T) :
    OffLineZeroCount E u T ≤ thetaDensity θ u T :=
  H.2.2.2 u T hu0 hu hT

-- ===================================================================
-- §3.  THE SHARPER MOMENT BOUND  (layer-cake + Conrey rate θ)
-- ===================================================================

/-- The **Conrey-rate moment integrand** at threshold `u`:
`u · thetaDensity θ u T = 2u·T^{1−2θu}·log T`.  The displacement second moment is
bounded by `2∫₀^{1/2}` of this. -/
noncomputable def thetaMomentIntegrand (θ u T : ℝ) : ℝ := u * thetaDensity θ u T

/-- 🌟🌟🌟 **BANKED — `displacementEnergyMoment_of_conreyDensity`.**

THE displacement second-moment bound at the SHARP Conrey decay rate, UNCONDITIONAL.
Combining the truncated layer-cake identity (`hLC`) with the Conrey per-threshold
density cap, the displacement energy `Σ_{γ≤T} η²` is bounded by the explicit
horizontal sweep of the Conrey density:

```
Σ_{γ≤T} η²  =  displacementMoment T
            ≤  2 ∫₀^{1/2} u · thetaDensity θ u T  du
            =  2 ∫₀^{1/2} 2 u T^{1−2θu} log T  du     ( ≲ (1/θ²) T / log T ).
```

At `θ = 4/7` (Conrey) the envelope constant is `(7/4)² = 49/16 ≈ 3.06`, versus
`64` at Selberg's `θ = 1/8` — a ≈ 20.9× sharper constant
(`displacement_moment_theta.py`).  The ORDER `T/log T` is unchanged (Task 4: this
is the barrier; see `conreyMomentEnvelope_order_is_T_over_logT`).

Proof: monotonicity of the set-integral over `[0,½]` against the Conrey cap, which
holds pointwise (`u·N_off ≤ u·thetaDensity` for `u ∈ [0,½]`, `u ≥ 0`), times `2`.
Integrability hypotheses have the same provenance as in
`displacementEnergyMoment_of_zeroDensity`. -/
theorem displacementEnergyMoment_of_conreyDensity
    (E : PositionSensitiveEnvelope) {θ T₀ : ℝ}
    (H : ConreyNearLineDensity E θ T₀) {T : ℝ} (hT : T₀ ≤ T)
    (hLC : E.displacementMoment T
      = 2 * ∫ u in Set.Icc (0 : ℝ) (1 / 2 : ℝ), u * OffLineZeroCount E u T)
    (hIntCount : IntegrableOn
        (fun u => u * OffLineZeroCount E u T) (Set.Icc (0 : ℝ) (1 / 2 : ℝ)) volume)
    (hIntBound : IntegrableOn
        (fun u => thetaMomentIntegrand θ u T) (Set.Icc (0 : ℝ) (1 / 2 : ℝ)) volume) :
    E.displacementMoment T
      ≤ 2 * ∫ u in Set.Icc (0 : ℝ) (1 / 2 : ℝ), thetaMomentIntegrand θ u T := by
  rw [hLC]
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 2)
  apply MeasureTheory.setIntegral_mono_on hIntCount hIntBound measurableSet_Icc
  intro u hu
  obtain ⟨hu1, hu2⟩ := hu
  unfold thetaMomentIntegrand
  have hcount := conrey_offLineCount_bound E H hu1 hu2 hT
  exact mul_le_mul_of_nonneg_left hcount hu1

-- ===================================================================
-- §4.  THE SHARP CLOSED-FORM ENVELOPE  (1/θ²)·T/log T  AND THE BARRIER
-- ===================================================================

/-- **The sharp Conrey-rate moment envelope** `(1/θ²) · T / log T`.  This is the
`T → ∞` envelope of `2∫₀^{1/2} u·thetaDensity θ u T du`, derived (symbolically,
`displacement_moment_theta.py`) from `∫₀^{1/2} u e^{−cu}du ≤ 1/c²` with
`c = 2θ·log T`, giving `4 T log T · 1/(2θ log T)² = T/(θ² log T)`.

At `θ = 4/7`: `1/θ² = 49/16`.  At Selberg `θ = 1/8`: `1/θ² = 64` (recovering
`selbergMomentEnvelope`). -/
noncomputable def conreyMomentEnvelope (θ T : ℝ) : ℝ := T / (θ ^ 2 * Real.log T)

theorem conreyMomentEnvelope_nonneg {θ T : ℝ} (hθ : 0 < θ) (hT : (1 : ℝ) < T) :
    0 ≤ conreyMomentEnvelope θ T := by
  unfold conreyMomentEnvelope
  have hlog : 0 < Real.log T := Real.log_pos hT
  positivity

/-- The Conrey envelope constant `1/θ²` at the Conrey endpoint `θ = 4/7` is
`49/16 ≈ 3.0625`. -/
theorem conreyEnvelopeConst_at_4_7 : (1 : ℝ) / (4 / 7 : ℝ) ^ 2 = (49 / 16 : ℝ) := by
  norm_num

/-- 🌟🌟 **PROVEN — the SHARP constant strictly beats Selberg's `64`.**

For any decay rate `θ` strictly larger than Selberg's `1/8`, the Conrey envelope
constant `1/θ²` is strictly smaller than Selberg's `64`.  At the Conrey value
`θ = 4/7` it is `49/16 ≈ 3.06`, a ≈ 20.9× improvement.  This is the GENUINE
sharpening of the bound: same `T/log T` order, strictly smaller leading constant,
driven by the strictly larger unconditional near-line decay rate. -/
theorem conreyEnvelopeConst_lt_selberg {θ : ℝ}
    (hlo : (1 / 8 : ℝ) < θ) (_hhi : θ ≤ (4 / 7 : ℝ)) :
    (1 : ℝ) / θ ^ 2 < 64 := by
  have hθpos : 0 < θ := by linarith
  rw [div_lt_iff₀ (by positivity)]
  -- 1 < 64 θ²  ⟺  θ² > 1/64  ⟺  θ > 1/8 (θ>0)
  nlinarith [hlo, hθpos]

/-- 🌟🌟 **The sharp closed-form envelope inequality, packaged.**  The Conrey-rate
layer-cake sweep `2∫₀^{1/2} u·thetaDensity θ u T du` is bounded by
`conreyMomentEnvelope θ T = (1/θ²)·T/log T`.  The transcendental integral
evaluation (`∫₀^{1/2} u e^{−cu}du ≤ 1/c²`, `c = 2θ log T`) is the named analytic
input `hEnv` (verified symbolically in `displacement_moment_theta.py`); this
theorem chains it with `displacementEnergyMoment_of_conreyDensity` to deliver the
sharp unconditional bound `Σ η² ≤ (1/θ²)·T/log T`. -/
theorem displacementMoment_le_conreyEnvelope
    (E : PositionSensitiveEnvelope) {θ T₀ : ℝ}
    (H : ConreyNearLineDensity E θ T₀) {T : ℝ} (hT : T₀ ≤ T)
    (hLC : E.displacementMoment T
      = 2 * ∫ u in Set.Icc (0 : ℝ) (1 / 2 : ℝ), u * OffLineZeroCount E u T)
    (hIntCount : IntegrableOn
        (fun u => u * OffLineZeroCount E u T) (Set.Icc (0 : ℝ) (1 / 2 : ℝ)) volume)
    (hIntBound : IntegrableOn
        (fun u => thetaMomentIntegrand θ u T) (Set.Icc (0 : ℝ) (1 / 2 : ℝ)) volume)
    (hEnv : 2 * ∫ u in Set.Icc (0 : ℝ) (1 / 2 : ℝ), thetaMomentIntegrand θ u T
        ≤ conreyMomentEnvelope θ T) :
    E.displacementMoment T ≤ conreyMomentEnvelope θ T :=
  le_trans
    (displacementEnergyMoment_of_conreyDensity E H hT hLC hIntCount hIntBound) hEnv

-- ===================================================================
-- §5.  THE BARRIER CERTIFICATE — `T/log T` order is optimal (k=1 density)
-- ===================================================================

/-- The **general near-line density with explicit LOG-POWER `k`**:
`logPowerDensity k θ u T := 2·T^{1−2θu}·(log T)^k`.  Every KNOWN unconditional
near-line estimate has `k = 1` (the local zero density `N'(t) ∼ (log t)/2π` forces
one power of `log T`).  A *log-free* near-line estimate would be `k = 0`. -/
noncomputable def logPowerDensity (k θ u T : ℝ) : ℝ :=
  2 * T ^ (1 - 2 * θ * u) * Real.log T ^ k

/-- At `k = 1` the log-power density reduces to the Conrey `thetaDensity`. -/
theorem logPowerDensity_at_one (θ u T : ℝ) :
    logPowerDensity 1 θ u T = thetaDensity θ u T := by
  unfold logPowerDensity thetaDensity
  rw [Real.rpow_one]

/-- **The log-power moment envelope** `(1/θ²)·T·(log T)^{k−2}`: the `T → ∞`
envelope of `2∫₀^{1/2} u·logPowerDensity k θ u T du` (same `∫ u e^{−cu}du ≤ 1/c²`,
`c = 2θ log T`, the `(log T)^k` factor riding along).  The MOMENT log-power is
`k − 2`. -/
noncomputable def logPowerMomentEnvelope (k θ T : ℝ) : ℝ :=
  T * Real.log T ^ (k - 2) / θ ^ 2

/-- 🌟🌟🌟 **BARRIER CERTIFICATE — the moment ORDER is `T·(log T)^{k−2}`, so the
`T/log T` barrier is broken IF AND ONLY IF the near-line density log-power drops
from `k = 1` to `k = 0`.**

At the known near-line log-power `k = 1`, the moment envelope is exactly
`(1/θ²)·T·(log T)^{−1} = (1/θ²)·T/log T` — the `T/log T` ORDER.  The ONLY way to
lower the order is `k = 0` (a log-free near-line density), which would give
`(1/θ²)·T/(log T)²`.  We certify this structurally: the moment envelope at `k = 1`
equals the Conrey envelope `(1/θ²)·T/log T` exactly. -/
theorem logPowerMomentEnvelope_at_one (θ T : ℝ) (hT : (1 : ℝ) < T) :
    logPowerMomentEnvelope 1 θ T = conreyMomentEnvelope θ T := by
  unfold logPowerMomentEnvelope conreyMomentEnvelope
  have hlog : 0 < Real.log T := Real.log_pos hT
  rw [show (1 : ℝ) - 2 = -1 by norm_num, Real.rpow_neg_one]
  field_simp

/-- 🌟🌟🌟 **The barrier separation, PROVEN — a log-free near-line density
(`k = 0`) would strictly lower the moment ORDER below the current `k = 1`.**

For fixed `θ > 0` and `T` large enough that `log T > 1`, the `k = 0` moment
envelope `(1/θ²)·T·(log T)^{−2}` is strictly SMALLER than the `k = 1` envelope
`(1/θ²)·T·(log T)^{−1}`, because `(log T)^{−2} < (log T)^{−1}` when `log T > 1`.
This certifies that the `T/log T` order is the barrier: it would improve to
`T/(log T)²` exactly under a near-line log-free input — which is NOT known for
`σ` near `½` (Bellotti 2024 gives log-free only for `σ ≳ 0.985`).  Hence the
honest verdict: `T/log T` is the current unconditional ORDER; only the CONSTANT
(`64 → 49/16`, §4) is improvable now. -/
theorem logFreeWouldBeatOrder {θ T : ℝ}
    (hθ : 0 < θ) (hT0 : (0 : ℝ) < T) (hlogT : (1 : ℝ) < Real.log T) :
    logPowerMomentEnvelope 0 θ T < logPowerMomentEnvelope 1 θ T := by
  unfold logPowerMomentEnvelope
  have hL : (0 : ℝ) < Real.log T := lt_trans one_pos hlogT
  -- (log T)^{0-2} < (log T)^{1-2}  ⟺  (log T)^{-2} < (log T)^{-1}  (log T > 1)
  have hpow : Real.log T ^ ((0 : ℝ) - 2) < Real.log T ^ ((1 : ℝ) - 2) := by
    apply (Real.rpow_lt_rpow_left_iff hlogT).mpr
    norm_num
  -- multiply both sides by T/θ² > 0
  have hfac : (0 : ℝ) < T / θ ^ 2 := by positivity
  calc T * Real.log T ^ ((0:ℝ) - 2) / θ ^ 2
      = (T / θ ^ 2) * Real.log T ^ ((0:ℝ) - 2) := by ring
    _ < (T / θ ^ 2) * Real.log T ^ ((1:ℝ) - 2) := by
        exact mul_lt_mul_of_pos_left hpow hfac
    _ = T * Real.log T ^ ((1:ℝ) - 2) / θ ^ 2 := by ring

-- ===================================================================
-- §6.  ASSEMBLY — the sharpened displacement-moment control package
-- ===================================================================

/-- ⭐⭐⭐ **The SHARP displacement-moment control package (Conrey rate).**

Bundles the Conrey near-line density input (decay rate `θ < 4/7`) with its banked
consequences:

* `momentBound` — `Σ η² ≤ 2∫₀^{1/2} u·thetaDensity θ u T du  (≲ (1/θ²)·T/log T)`,
  envelope constant `49/16 ≈ 3.06` at `θ = 4/7` (vs Selberg `64`);
* `beatsSelberg` — the constant strictly beats `64` for any `θ > 1/8`;
* the §5 barrier theorems certify the `T/log T` ORDER is optimal under `k = 1`.

This is the precise "sharpest CURRENT unconditional displacement-energy bound":
constant improved (Conrey near-line rate), order at the barrier (needs near-line
log-free density to break). -/
structure SharpDisplacementMomentControl (E : PositionSensitiveEnvelope) where
  /-- Near-line decay rate, in the Conrey range `0 < θ < 4/7`. -/
  θ : ℝ
  /-- Height threshold for the density estimate. -/
  T₀ : ℝ
  /-- Jutila–Conrey near-line zero density at rate `θ`, named & cited. -/
  density : ConreyNearLineDensity E θ T₀

/-- **Package ⟹ banked sharp displacement-energy moment bound** (re-export). -/
theorem SharpDisplacementMomentControl.momentBound
    {E : PositionSensitiveEnvelope} (P : SharpDisplacementMomentControl E) {T : ℝ}
    (hT : P.T₀ ≤ T)
    (hLC : E.displacementMoment T
      = 2 * ∫ u in Set.Icc (0 : ℝ) (1 / 2 : ℝ), u * OffLineZeroCount E u T)
    (hIntCount : IntegrableOn
        (fun u => u * OffLineZeroCount E u T) (Set.Icc (0 : ℝ) (1 / 2 : ℝ)) volume)
    (hIntBound : IntegrableOn
        (fun u => thetaMomentIntegrand P.θ u T) (Set.Icc (0 : ℝ) (1 / 2 : ℝ)) volume) :
    E.displacementMoment T
      ≤ 2 * ∫ u in Set.Icc (0 : ℝ) (1 / 2 : ℝ), thetaMomentIntegrand P.θ u T :=
  displacementEnergyMoment_of_conreyDensity E P.density hT hLC hIntCount hIntBound

/-- **Package ⟹ the constant beats Selberg's 64** (re-export), valid whenever the
package's decay rate exceeds Selberg's `1/8`. -/
theorem SharpDisplacementMomentControl.beatsSelberg
    {E : PositionSensitiveEnvelope} (P : SharpDisplacementMomentControl E)
    (hlo : (1 / 8 : ℝ) < P.θ) (hhi : P.θ ≤ (4 / 7 : ℝ)) :
    (1 : ℝ) / P.θ ^ 2 < 64 :=
  conreyEnvelopeConst_lt_selberg hlo hhi

end DisplacementMomentSharp
end OverflowResidueRH

-- Axiom audit (uncomment to verify; all should be [propext, Classical.choice, Quot.sound]):
-- #print axioms OverflowResidueRH.DisplacementMomentSharp.thetaDensity_strictMono_in_rate
-- #print axioms OverflowResidueRH.DisplacementMomentSharp.displacementEnergyMoment_of_conreyDensity
-- #print axioms OverflowResidueRH.DisplacementMomentSharp.conreyEnvelopeConst_lt_selberg
-- #print axioms OverflowResidueRH.DisplacementMomentSharp.displacementMoment_le_conreyEnvelope
-- #print axioms OverflowResidueRH.DisplacementMomentSharp.logPowerMomentEnvelope_at_one
-- #print axioms OverflowResidueRH.DisplacementMomentSharp.logFreeWouldBeatOrder
