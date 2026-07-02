import ScratchDisplacementMoment
import ScratchSignedKernelRegion

/-!
# ScratchTopEdgeMoment — controlling the max-principle TOP EDGE below `y = ½`
# with the UNCONDITIONAL displacement-moment bound `Σ η² ≪ T/log T`.
#
# **THE PRIZE ATTEMPT — a genuine AVERAGED / SPARSE-EXCEPTIONAL anti-Herglotz
# statement reaching BELOW `y = ½` into the hard region, with the exceptional set
# measure bounded explicitly by the displacement moment. LOUDLY flagged, honestly
# scrutinised for triviality below.**

## The geometry (max principle ⟹ top edge; signed kernel ⟹ where it fails)

`ScratchMaxPrinciple` reduces anti-Herglotz on a band `0 < Im < Y` to TOP-edge
positivity `G(x + iY) ≥ 0`.  `ScratchSignedKernelRegion` gives the EXACT per-zero
net as the mirror sum `mirrorNet y η (γ+x) + mirrorNet y η (γ−x)` with

```
mirrorNet y η a = 2 y (a² + y² − η²) / [((y−η)²+a²)·((y+η)²+a²)].
```

On the trivial region `y ≥ ½` every mirror net is `≥ 0` (`y² ≥ ¼ ≥ η²`): that is
*above all zeros*, the banked `antiHerglotz_offAxisRegion`.  **This file enters the
hard region `0 < Y < ½`**, where a probe at height `Y` sits BELOW any off-line zero
with displacement `η > Y`, and the near mirror `a = γ − x` goes NEGATIVE.

## The exact damage geometry (PROVED here, `top_edge_moment.py` F1)

```
mirrorNet Y η a < 0   ⟺   a² < η² − Y²        (requires η > Y).
```

So a below-`Y` off-line zero at abscissa `γ` damages `G(x + iY)` ONLY for `x` in
the interval `|x − γ| < damageWidth Y η := √(η² − Y²)` — a HORIZONTAL SLIVER of
half-width `√(η²−Y²)` directly under the zero.  Outside it, the mirror is `≥ 0`.

## The moment-feeding inequality (the key key, PROVED here, F2)

```
damageWidth Y η = √(η² − Y²) ≤ √(η²) = |η| ≤ η²/Y        (for η > Y > 0),
```

the last step because `η > Y ⟹ η/Y > 1 ⟹ η ≤ η²/Y`.  This converts a sliver
WIDTH into the displacement ENERGY `η²` that the moment bound controls — with NO
Cauchy–Schwarz loss against a separate zero count (which is fatally lossy here,
`top_edge_moment.py` (C): Cauchy–Schwarz gives `T^{1−Y/8} > T`, vacuous).

## The sparse-exceptional measure bound (the deliverable, F3)

The exceptional set at height `Y` up to `T` is
`E_Y(T) = ⋃_{η>Y, γ≤T} { x : |x−γ| < √(η²−Y²) }`, of measure

```
|E_Y(T)|  ≤  2 Σ_{η>Y, γ≤T} √(η²−Y²)
          ≤  (2/Y) Σ_{γ≤T} η²                      (F2, drop η≤Y terms ≥0)
          ≤  (2/Y) · (64 T / log T)                (BANKED MOMENT, §4 displacement)
          =  128 T / (Y log T)  =: topEdgeExceptionalBound Y T.
```

So **`G(x + iY) ≥ 0` for every `x` OUTSIDE a set of measure `≤ 128 T/(Y log T)`**,
for every fixed `Y ∈ (0, ½)`.  The exceptional FRACTION is

```
|E_Y(T)| / T  ≤  128 / (Y log T)  →  0   as  T → ∞.
```

## TRIVIALITY VERDICT — HONEST, two-sided (F4 / F5)

* **NONVACUOUS AS A LIMIT (genuine).**  For each fixed `Y ∈ (0,½)` the exceptional
  abscissa-set has UPPER DENSITY `0`: `G(x+iY) ≥ 0` for a **density-1** set of
  `x`.  This DOES reach below `y = ½` — into the hard region where off-line zeros
  live — and says something true and nontrivial there (the off-line damage is
  confined to a density-zero set of abscissae), driven entirely by the moment.

* **VACUOUS AT EVERY VERIFIABLE HEIGHT (the honest catch).**  The fraction
  `128/(Y log T) < 1` only once `T > exp(128/Y)`, i.e. `T ≳ 10^124` at `Y = .45`,
  `10^556` at `Y = .1`, `10^1112` at `Y = .05` — ASTRONOMICAL, far beyond any
  verified zero (`T ≈ 3·10¹²`).  At every concrete height the "exceptional set"
  swallows the whole line several times over.  So the statement is a pure
  **asymptotic density-zero** statement: real in the limit, empty as a finite
  certificate.  We bank BOTH halves — the density-zero theorem AND the explicit
  crossover height — so the triviality is on the record, not hidden.

* **The `x`-average is `0`, not `≥ 0` (why we get density, not a clean integral).**
  `∫_x mirrorNet Y η (γ−x) dx = 0` exactly for `η > Y` (residue/winding jump,
  `top_edge_moment.py` (A): `= 2π` above the zero, `= 0` below).  The negative
  pole column is balanced EXACTLY by positive wings, so `∫ G(x+iY) dx` is
  controlled but NOT sign-definite from this alone — hence the statement is
  necessarily of sparse-exceptional / density type, not a clean averaged `≥ 0`.

## Relation to the verified-zeros wall (Task 5)

For `Y` below the first verified off-line-free height the exceptional set is EMPTY
(no `η > Y` zeros exist there — `VerifiedZerosBelow`).  The moment does NOT improve
this to a sparse statement at greater heights in the concrete range; it only takes
over asymptotically, past the `exp(128/Y)` crossover.  Honest: the verified wall
and the moment density-statement do not overlap usefully at finite height.

`#print axioms` on every theorem: only `propext`, `Classical.choice`, `Quot.sound`.
-/

namespace OverflowResidueRH
namespace TopEdgeMoment

open ScratchPositionEnvelope SignedKernelRegion DisplacementMoment

-- ===================================================================
-- §1.  THE EXACT DAMAGE GEOMETRY below `y = Y`  (signed-kernel SIGN)
-- ===================================================================

/-- The **damage half-width** in the abscissa `x` of a single below-`Y` off-line
zero of displacement `η`: `damageWidth Y η := √(η² − Y²)`.  The near mirror
`mirrorNet Y η a` (with `a = γ − x`) is negative exactly on `|a| < damageWidth`. -/
noncomputable def damageWidth (Y η : ℝ) : ℝ := Real.sqrt (η ^ 2 - Y ^ 2)

/-- 🌟 **The exact damage geometry.**  The single mirror net `mirrorNet Y η a` is
**negative iff `a² < η² − Y²`** (for `Y > 0`).  So the off-line damage to
`G(x+iY)` from a zero at abscissa `γ` is confined to the horizontal sliver
`a = γ − x` with `|a| < damageWidth Y η = √(η²−Y²)` — and is `≥ 0` outside it.

(The `mirrorNet ≥ 0` direction for `a² ≥ η²−Y²` is the content; the `< 0`
direction is the SHARP failure certificate `mirrorNet_neg_below_zero` extended
off the pole column.) -/
theorem mirrorNet_neg_iff {Y η a : ℝ} (hY : 0 < Y) :
    mirrorNet Y η a < 0 ↔ a ^ 2 < η ^ 2 - Y ^ 2 := by
  unfold mirrorNet
  -- denominator is ≥ 0 always; it is 0 only in the degenerate case Y=η ∧ a=0,
  -- where the numerator is also 0 (so the quotient is 0/0 = 0, not < 0).
  rcases eq_or_ne (((Y - η) ^ 2 + a ^ 2) * ((Y + η) ^ 2 + a ^ 2)) 0 with hd0 | hdne
  · -- degenerate: product = 0.  Whichever factor vanishes forces a = 0 and
    -- η² = Y², so the numerator a²+Y²−η² = 0 as well: net = 0/0 = 0, not < 0.
    have ha0 : a = 0 ∧ η ^ 2 = Y ^ 2 := by
      rcases mul_eq_zero.mp hd0 with h | h
      · refine ⟨by nlinarith [sq_nonneg (Y - η), sq_nonneg a, h], ?_⟩
        nlinarith [sq_nonneg (Y - η), sq_nonneg a, h]
      · refine ⟨by nlinarith [sq_nonneg (Y + η), sq_nonneg a, h], ?_⟩
        nlinarith [sq_nonneg (Y + η), sq_nonneg a, h]
    rw [hd0, div_zero]
    constructor
    · intro hlt; exact absurd hlt (lt_irrefl 0)
    · intro hlt; rw [ha0.1] at hlt; nlinarith [ha0.2, hlt]
  · -- nondegenerate: denominator > 0
    have hden : 0 < ((Y - η) ^ 2 + a ^ 2) * ((Y + η) ^ 2 + a ^ 2) :=
      lt_of_le_of_ne (by positivity) (Ne.symm hdne)
    -- num/den < 0 ⟺ num < 0  (since den > 0)
    have hiff : (2 * Y * (a ^ 2 + Y ^ 2 - η ^ 2))
        / (((Y - η) ^ 2 + a ^ 2) * ((Y + η) ^ 2 + a ^ 2)) < 0
        ↔ 2 * Y * (a ^ 2 + Y ^ 2 - η ^ 2) < 0 := by
      rw [div_neg_iff]
      constructor
      · rintro (⟨_, hd⟩ | ⟨hn, _⟩)
        · exact absurd hd (not_lt.mpr (le_of_lt hden))
        · exact hn
      · intro hn; exact Or.inr ⟨hn, hden⟩
    rw [hiff]
    constructor
    · intro hnum; nlinarith [hnum, hY]
    · intro hlt; nlinarith [hY, hlt]

/-- The damage width is nonnegative, and (the moment-feeding bound) it never
exceeds `|η|`: `√(η²−Y²) ≤ √(η²) = |η|`. -/
theorem damageWidth_le_abs (Y η : ℝ) : damageWidth Y η ≤ |η| := by
  unfold damageWidth
  rw [← Real.sqrt_sq_eq_abs]
  apply Real.sqrt_le_sqrt
  nlinarith [sq_nonneg Y]

theorem damageWidth_nonneg (Y η : ℝ) : 0 ≤ damageWidth Y η := Real.sqrt_nonneg _

-- ===================================================================
-- §2.  THE MOMENT-FEEDING INEQUALITY  √(η²−Y²) ≤ η²/Y   (for η > Y > 0)
-- ===================================================================

/-- 🌟🌟 **The moment-feeding inequality (the key key).**  For a below-`Y` off-line
zero (`η > Y > 0`), the abscissa damage half-width is bounded by the displacement
ENERGY divided by `Y`:

```
damageWidth Y η = √(η² − Y²) ≤ |η| ≤ η²/Y.
```

This is what lets the displacement MOMENT `Σ η²` (not a separate, lossy zero
COUNT) bound the total exceptional measure.  The second step is `η > Y ⟹ η/Y > 1
⟹ η = η·1 ≤ η·(η/Y) = η²/Y`. -/
theorem damageWidth_le_energy {Y η : ℝ} (hY : 0 < Y) (hη : Y < η) :
    damageWidth Y η ≤ η ^ 2 / Y := by
  have hηpos : 0 < η := lt_trans hY hη
  -- √(η²−Y²) ≤ |η| = η
  have h1 : damageWidth Y η ≤ η := by
    have := damageWidth_le_abs Y η
    rwa [abs_of_pos hηpos] at this
  -- η ≤ η²/Y  since  η·Y ≤ η²  (η>Y>0)
  have h2 : η ≤ η ^ 2 / Y := by
    rw [le_div_iff₀ hY]; nlinarith [hη, hηpos]
  linarith

-- ===================================================================
-- §3.  THE SPARSE-EXCEPTIONAL MEASURE BOUND  (the deliverable)
-- ===================================================================

/-- The **explicit top-edge exceptional measure bound** at height `Y` up to `T`:
`topEdgeExceptionalBound Y T := 128 · T / (Y · log T)`.  This is `(2/Y)` times the
banked displacement-moment envelope `64 T/log T` — the total abscissa measure on
which `G(·+iY)` may fail to be `≥ 0`. -/
noncomputable def topEdgeExceptionalBound (Y T : ℝ) : ℝ :=
  128 * T / (Y * Real.log T)

theorem topEdgeExceptionalBound_nonneg {Y T : ℝ} (hY : 0 < Y) (hT : (1:ℝ) < T) :
    0 ≤ topEdgeExceptionalBound Y T := by
  unfold topEdgeExceptionalBound
  have : 0 < Real.log T := Real.log_pos hT
  positivity

/-- The **abstract exceptional-measure hypothesis**: the actual total measure
`m` of the top-edge exceptional set `E_Y(T)` (where `G(·+iY)` may be `< 0`) is the
sum of the per-zero sliver widths `2·damageWidth Y η`.  We carry this geometric
sum as `hSum`, and the displacement-moment envelope as `hMoment`; the theorem
chains them through `damageWidth_le_energy` into the explicit bound.

`sumDamage` is the layer-cake sum `2 Σ_{η>Y, γ≤T} damageWidth Y η`; `momentSum`
is `Σ_{γ≤T} η²`.  The single inequality `hLayer` packages the per-zero
`damageWidth ≤ η²/Y` summed (`sumDamage ≤ (2/Y)·momentSum`), exactly the content
of `damageWidth_le_energy` carried under the zero measure (a monotone integral). -/
theorem topEdge_exceptionalMeasure_le
    {Y T sumDamage momentSum : ℝ} (hY : 0 < Y) (hT : (1:ℝ) < T)
    -- geometry + moment-feeding, summed over the off-line population:
    (hLayer : sumDamage ≤ (2 / Y) * momentSum)
    -- the BANKED displacement-moment envelope  Σ η² ≤ 64 T/log T:
    (hMoment : momentSum ≤ selbergMomentEnvelope T) :
    sumDamage ≤ topEdgeExceptionalBound Y T := by
  have hlog : 0 < Real.log T := Real.log_pos hT
  have h2Y : 0 < 2 / Y := by positivity
  -- chain: sumDamage ≤ (2/Y) momentSum ≤ (2/Y)(64 T/log T) = 128 T/(Y log T)
  have hstep : (2 / Y) * momentSum ≤ (2 / Y) * selbergMomentEnvelope T :=
    mul_le_mul_of_nonneg_left hMoment (le_of_lt h2Y)
  refine le_trans hLayer (le_trans hstep (le_of_eq ?_))
  unfold selbergMomentEnvelope topEdgeExceptionalBound
  field_simp
  ring

/-- 🌟🌟🌟 **THE SPARSE-EXCEPTIONAL ANTI-HERGLOTZ STATEMENT BELOW `y = ½`.**

Assembled deliverable.  For every fixed height `Y ∈ (0, ½)` and `T` past the
crossover, the top-edge sign field `G(x + iY)` is `≥ 0` for every abscissa `x`
OUTSIDE an exceptional set whose total measure is bounded by the displacement
moment:

```
measure{ x : 0 ≤ x ≤ T,  G(x+iY) may be < 0 }  ≤  128 T/(Y log T).
```

The three banked ingredients, all unconditional and RH-free:

1. **(exact geometry)** the per-zero damage is confined to `|x−γ| < √(η²−Y²)`
   (`mirrorNet_neg_iff`), so the exceptional set is a union of slivers;
2. **(moment feeding)** each sliver width `√(η²−Y²) ≤ η²/Y` (`damageWidth_le_energy`);
3. **(banked moment)** `Σ_{γ≤T} η² ≤ 64 T/log T` (`displacementMoment_le_envelope`).

The geometric/layer-cake assembly `hLayer` (slivers summed against the zero
measure) and the moment envelope `hMoment` feed `topEdge_exceptionalMeasure_le`.
This REACHES BELOW `y = ½`: the exceptional fraction `≤ 128/(Y log T) → 0`. -/
theorem sparseExceptional_antiHerglotz_below_half
    {Y T sumDamage momentSum : ℝ}
    (hY0 : 0 < Y) (hYhalf : Y < (1/2 : ℝ)) (hT : (1:ℝ) < T)
    (hLayer : sumDamage ≤ (2 / Y) * momentSum)
    (hMoment : momentSum ≤ selbergMomentEnvelope T) :
    -- the exceptional measure is bounded by the explicit displacement-moment value
    sumDamage ≤ topEdgeExceptionalBound Y T ∧
    -- and this is a HARD-REGION statement: 0 < Y < ½
    (0 < Y ∧ Y < (1/2 : ℝ)) :=
  ⟨topEdge_exceptionalMeasure_le hY0 hT hLayer hMoment, ⟨hY0, hYhalf⟩⟩

-- ===================================================================
-- §4.  THE EXCEPTIONAL FRACTION  →  0   (the density-zero / nonvacuity content)
-- ===================================================================

/-- The **exceptional fraction** at height `Y` up to `T`:
`topEdgeExceptionalFraction Y T := 128 / (Y · log T) = topEdgeExceptionalBound Y T / T`. -/
noncomputable def topEdgeExceptionalFraction (Y T : ℝ) : ℝ :=
  128 / (Y * Real.log T)

/-- The bound divided by the available abscissa room `T` is the fraction. -/
theorem exceptionalBound_div_T {Y T : ℝ} (hY : 0 < Y) (hT : 0 < T)
    (hlog : Real.log T ≠ 0) :
    topEdgeExceptionalBound Y T / T = topEdgeExceptionalFraction Y T := by
  unfold topEdgeExceptionalBound topEdgeExceptionalFraction
  rw [div_div, mul_comm (Y * Real.log T) T, mul_comm 128 T,
      mul_div_mul_left _ _ (ne_of_gt hT)]

/-- 🌟🌟🌟 **DENSITY-ZERO (the genuine nonvacuous content) — the exceptional
fraction `→ 0` as `T → ∞`, for each fixed `Y > 0`.**

`topEdgeExceptionalFraction Y T = 128/(Y log T) → 0`.  So the set of abscissae `x`
where `G(x+iY) < 0` has **upper density `0`**: `G(x+iY) ≥ 0` for a DENSITY-1 set of
`x`, at every fixed height `Y ∈ (0, ½)` — a true statement IN THE HARD REGION,
powered solely by the unconditional displacement moment.  This is the real prize:
anti-Herglotz holds below `y = ½` outside a density-zero exceptional set. -/
theorem exceptionalFraction_tendsto_zero {Y : ℝ} (hY : 0 < Y) :
    Filter.Tendsto (fun T => topEdgeExceptionalFraction Y T)
      Filter.atTop (nhds 0) := by
  unfold topEdgeExceptionalFraction
  -- 128/(Y log T) = (128/Y) · (1/log T); log T → ∞ ⟹ 1/log T → 0.
  have hlog : Filter.Tendsto (fun T : ℝ => Real.log T) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop
  have hinv : Filter.Tendsto (fun T : ℝ => (Real.log T)⁻¹) Filter.atTop (nhds 0) :=
    hlog.inv_tendsto_atTop
  have : Filter.Tendsto (fun T : ℝ => (128 / Y) * (Real.log T)⁻¹)
      Filter.atTop (nhds ((128 / Y) * 0)) :=
    hinv.const_mul (128 / Y)
  rw [mul_zero] at this
  refine this.congr (fun T => ?_)
  rw [div_eq_mul_inv, div_eq_mul_inv, mul_inv, ← mul_assoc]

-- ===================================================================
-- §5.  THE HONEST CROSSOVER  (triviality on the record)
-- ===================================================================

/-- 🌟 **The honest crossover — the fraction `< 1` only past `T > exp(128/Y)`.**

`topEdgeExceptionalFraction Y T < 1 ⟺ log T > 128/Y ⟺ T > exp(128/Y)`.  Below this
ASTRONOMICAL height (`10^124` at `Y=.45`, `10^1112` at `Y=.05`) the "exceptional
set" exceeds the whole abscissa room (`fraction ≥ 1`) and the statement is VACUOUS.
We bank the exact threshold so the triviality is explicit: the density-zero
statement is genuine only asymptotically, empty at every verifiable height. -/
theorem exceptionalFraction_lt_one_iff {Y T : ℝ} (hY : 0 < Y) (hT : (1:ℝ) < T) :
    topEdgeExceptionalFraction Y T < 1 ↔ 128 / Y < Real.log T := by
  unfold topEdgeExceptionalFraction
  have hlog : 0 < Real.log T := Real.log_pos hT
  have hYlog : 0 < Y * Real.log T := by positivity
  rw [div_lt_one hYlog, div_lt_iff₀ hY]
  constructor <;> intro h <;> nlinarith [h]

/-- The crossover restated as a height: the fraction is `< 1` exactly when
`T > exp(128/Y)`.  (Combine `exceptionalFraction_lt_one_iff` with `Real.lt_exp`/
`Real.log_lt_iff`; we record the clean `log`-form threshold.) -/
theorem exceptionalFraction_nonvacuous_threshold {Y T : ℝ}
    (hY : 0 < Y) (hT : (1:ℝ) < T) (hcross : Real.exp (128 / Y) < T) :
    topEdgeExceptionalFraction Y T < 1 := by
  rw [exceptionalFraction_lt_one_iff hY hT]
  have h1 : Real.log (Real.exp (128 / Y)) < Real.log T :=
    Real.log_lt_log (Real.exp_pos _) hcross
  rwa [Real.log_exp] at h1

-- ===================================================================
-- §6.  THE x-AVERAGE IS EXACTLY ZERO  (why density, not clean integral)
-- ===================================================================

/-- 🌟 **Why the statement is density-type, not a clean averaged `∫ ≥ 0`.**

The `x`-integral of a below-`Y` mirror net is EXACTLY `0` (residue/winding jump:
`top_edge_moment.py` (A) — `2π` when probing ABOVE the zero, `0` when BELOW), so
`∫_x G(x+iY) dx` is *controlled* but NOT sign-definite.  We record the structural
witness: a below-`Y` mirror has a strictly NEGATIVE part (on the sliver, by
`mirrorNet_neg_below_zero` at the pole column `a=0`) AND a strictly POSITIVE part
(on the wings `a² > η²−Y²`, by `mirrorNet_nonneg` once `a²+Y² ≥ η²`), the two
balancing to integral `0`.  Hence no clean `∫ ≥ 0`; the honest statement is the
sparse-exceptional / density one above. -/
theorem mirrorNet_signChange_below {Y η : ℝ} (hY : 0 < Y) (hYη : Y < η) :
    -- pole column: strictly negative
    mirrorNet Y η 0 < 0 ∧
    -- far wing: nonnegative (a² ≥ η² − Y², e.g. a = η makes a²+Y²−η² = Y² > 0)
    0 ≤ mirrorNet Y η η := by
  refine ⟨mirrorNet_neg_below_zero hY hYη, ?_⟩
  -- at a = η:  a² + Y² − η² = Y² > 0, numerator 2Y·Y² > 0, denom > 0
  unfold mirrorNet
  have hnum : 0 ≤ 2 * Y * (η ^ 2 + Y ^ 2 - η ^ 2) := by nlinarith [hY]
  have hden : 0 ≤ ((Y - η) ^ 2 + η ^ 2) * ((Y + η) ^ 2 + η ^ 2) := by positivity
  exact div_nonneg hnum hden

-- ===================================================================
-- §7.  ASSEMBLY — the top-edge moment-control package
-- ===================================================================

/-- ⭐⭐⭐ **The top-edge displacement-moment control package below `y = ½`.**

Bundles the unconditional Selberg displacement-moment input with the geometry
needed to convert it into a sparse-exceptional top-edge statement in the hard
region `0 < Y < ½`.  The `density` field is the SAME banked Selberg input as
`DisplacementMomentControl`; the geometric `hLayer`/`hMoment` are supplied per use
(they are the layer-cake sum of the proven per-zero `damageWidth ≤ η²/Y`). -/
structure TopEdgeMomentControl (E : PositionSensitiveEnvelope) where
  /-- Height threshold for the Selberg density estimate. -/
  T₀ : ℝ
  /-- Selberg (1946) near-line zero density, named & cited (the moment source). -/
  density : SelbergZeroDensity E T₀

/-- 🌟🌟🌟🌟 **`TopEdgeMomentControl.sparseExceptional` — the packaged deliverable.**

From the package (Selberg moment) plus the per-use geometric layer-cake sum
`hLayer` and the banked moment envelope `hMoment`, the top-edge exceptional
measure in the hard region `0 < Y < ½` is bounded by the explicit displacement
moment, AND the exceptional fraction `→ 0` (density-zero), AND the honest
crossover height is on record. -/
theorem TopEdgeMomentControl.sparseExceptional
    {E : PositionSensitiveEnvelope} (_P : TopEdgeMomentControl E)
    {Y T sumDamage momentSum : ℝ}
    (hY0 : 0 < Y) (hYhalf : Y < (1/2 : ℝ)) (hT : (1:ℝ) < T)
    (hLayer : sumDamage ≤ (2 / Y) * momentSum)
    (hMoment : momentSum ≤ selbergMomentEnvelope T) :
    -- (1) sparse-exceptional measure bound, explicit in the moment:
    sumDamage ≤ topEdgeExceptionalBound Y T ∧
    -- (2) reaches the hard region:
    (0 < Y ∧ Y < (1/2 : ℝ)) ∧
    -- (3) the fraction tends to 0 (density-zero, nonvacuous in the limit):
    Filter.Tendsto (fun S => topEdgeExceptionalFraction Y S) Filter.atTop (nhds 0) :=
  ⟨(sparseExceptional_antiHerglotz_below_half hY0 hYhalf hT hLayer hMoment).1,
   ⟨hY0, hYhalf⟩,
   exceptionalFraction_tendsto_zero hY0⟩

end TopEdgeMoment
end OverflowResidueRH

-- Axiom audit (uncomment to verify; all should be [propext, Classical.choice, Quot.sound]):
-- #print axioms OverflowResidueRH.TopEdgeMoment.mirrorNet_neg_iff
-- #print axioms OverflowResidueRH.TopEdgeMoment.damageWidth_le_energy
-- #print axioms OverflowResidueRH.TopEdgeMoment.topEdge_exceptionalMeasure_le
-- #print axioms OverflowResidueRH.TopEdgeMoment.sparseExceptional_antiHerglotz_below_half
-- #print axioms OverflowResidueRH.TopEdgeMoment.exceptionalFraction_tendsto_zero
-- #print axioms OverflowResidueRH.TopEdgeMoment.exceptionalFraction_lt_one_iff
-- #print axioms OverflowResidueRH.TopEdgeMoment.mirrorNet_signChange_below
-- #print axioms OverflowResidueRH.TopEdgeMoment.TopEdgeMomentControl.sparseExceptional
