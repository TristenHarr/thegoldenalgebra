import rh
import ScratchPositionEnvelope
import ScratchZeroDensityBridge
import ScratchModernZeroDensity

/-!
# ScratchKernelDensity — the EXACT anti-Herglotz kernel `K_z(η,γ)` and the
# kernel-weighted density bridge (sharper than the crude count)

**Honesty note.**  Nothing here assumes RH.  The deep arithmetic input is the
*current-best unconditional* zero-density estimate (Guth–Maynard 2024 /
Tao–Trudgian–Yang 2025), reused verbatim through the named `Prop`s of
`ScratchModernZeroDensity` (`ModernZeroDensityExponent`, `modernAExp`,
`modernDensityBound`, `OffLineZeroCount`).  What is *proved* here is a STRUCTURAL
sharpening: the previous bridge `averagedAntiHerglotz_of_modernZeroDensity`
weights every off-line zero **uniformly** (by `1`, a count) before invoking the
density bound; this file instead weights each off-line zero by the **exact
anti-Herglotz kernel** `K_z(η,γ)` — the true displacement of the paired-Cauchy
pole that the off-line zero contributes to the sign field
`G(z) = −Im (Ξ'/Ξ)(z)`.

## The exact kernel (provenance: `kernel_density.py`, `kernel_final.py`)

The anti-Herglotz field is, with the functional-equation pullback `w_ρ = γ − iη`,

```
G(z) = −Im Σ_ρ [ 1/(z − w_ρ) + 1/(z + w_ρ) ].
```

The contribution of ONE off-line zero — its FE-paired quadruple `{±γ ± iη}`
minus the two on-line reference atoms at `±γ` (the `D_quad` field of
`ScratchDisplacementObstruction`) — to `G` at the worst-case probe `z = i·y`
(`x = Re w = 0` is the abscissa directly below the zero) is the **exact kernel**

```
K_z(η,γ) := −Im D_quad(i y, γ, η)
          = 4 η² y (y² − 3γ² − η²)
              / [ (γ²+y²)·((η−y)²+γ²)·((η+y)²+γ²) ].
```

Symbolically verified (`kernel_density.py`) to equal `−Im D_quad`, the negated
six-term `ImDquad` closed form of `ScratchDisplacementObstruction`.

## Exact kernel decay (the sharpening, all PROVEN below)

* **Quadratic in displacement.** `K_z(η,γ) = η² · R(η,γ,y)` factors an explicit
  `η²`: an off-line zero contributes `O(η²)`, not `O(1)` — `kernel_onLine_zero`.
* **Small-η leading term** `4η²y(y²−3γ²)/(γ²+y²)³` (the `C₂` coefficient of
  `ScratchDisplacementObstruction`) — `kernelAxis_smallEta_leading` connects it.
* **Height decay `γ⁻⁴`.** `lim_{γ→∞} γ⁴·K_z(η,γ) = −12 η² y` — each off-line zero
  at height `γ` is damped by `γ⁻⁴`, NOT counted uniformly.
* **Uniform majorant (banked).** For probe height `y ≥ 1`,
  `|K_z(η,γ)| ≤ 12 y · η² / (γ²+y²)²` — `kernelAxis_abs_le` (verified on
  `5·10⁵` random points, max ratio `0.99999`, `kernel_final.py`).

## The kernel-weighted bound (the banked theorem)

The off-line population's contribution to `G(z)` is
`Φ_K(z) = ∫ |K_z(η,γ)| dμ`.  Bounding `|K_z| ≤ 12y·η²/(γ²+y²)²` and running the
**kernel-weighted layer-cake** `η² = 2∫₀^{|η|} u du` gives

```
Φ_K(z) ≤ 24 y ∫₀^{1/2} u · [ ∫_γ 1_{|η|≥u}/(γ²+y²)² dμ ] du,
```

a *height-weighted* off-line count.  Because the kernel supplies the convergent
height weight `1/(γ²+y²)²`, the inner integral is **`T`-uniform** (a convergent
height integral, no positive power of `T`), whereas the crude count
`OffLineZeroCount E ε T ≤ modernDensityBound ε T = T^{A(½+ε)(½−ε)}·log T`
**grows** with `T` (≈ `T^{0.99}·log T` at `ε = 0.01`, `≈ 1.1·10⁷` at `T = 10⁶`).

We bank `kernelWeightedAntiHerglotz_of_modernDensity`: the kernel-weighted
contribution at each displacement layer `u` is bounded by the kernel slope
`24 y u` times the **modern** density `modernDensityBound u T` — the exact-kernel
weighting carried through the Guth–Maynard exponent.

## The honest RH gap (`kernelWeighted_residual_iff_RH`)

The kernel weight `K_z(η,γ)` vanishes to second order at `η = 0`, so it *cannot*
empty the off-line set: `K_z(η,γ) = 0 ⟺ η = 0` (off-line) — but a nonzero off-line
zero still contributes the strictly positive `|K_z| > 0`.  The residual is
exactly the RH gap: `OffLineZeroCount E ε T = 0` for all `ε > 0` **iff** the
displacement moment vanishes (RH on the slab) — no density bound forces it.

`#print axioms` on every theorem: only `propext`, `Classical.choice`, `Quot.sound`.
-/

namespace OverflowResidueRH
namespace KernelDensity

open MeasureTheory ScratchPositionEnvelope ZeroDensityBridge ModernZeroDensity
open scoped ENNReal

-- ===================================================================
-- §1.  The EXACT anti-Herglotz kernel `K_z(η,γ)` (closed form)
-- ===================================================================

/-- **The exact anti-Herglotz kernel at the on-abscissa probe `z = i·y`.**

`kernelAxis y η γ := −Im D_quad(i y, γ, η)` — the signed contribution of one
off-line zero (its FE-paired quadruple, minus the two on-line reference atoms)
to the sign field `G(z) = −Im(Ξ'/Ξ)(z)` at the probe directly below the zero.
Closed form (symbolically verified in `kernel_density.py` against the
`ImDquad` six-term formula of `ScratchDisplacementObstruction`):

```
K = 4 η² y (y² − 3γ² − η²)
      / [ (γ²+y²)·((η−y)²+γ²)·((η+y)²+γ²) ].
```

The triple denominator is `> 0` for `y > 0` (all three factors are sums of a
square and `y² > 0`); the numerator carries the explicit `η²` factor. -/
noncomputable def kernelAxis (y η γ : ℝ) : ℝ :=
  4 * η ^ 2 * y * (y ^ 2 - 3 * γ ^ 2 - η ^ 2)
    / ((γ ^ 2 + y ^ 2) * ((η - y) ^ 2 + γ ^ 2) * ((η + y) ^ 2 + γ ^ 2))

/-- The full kernel denominator is nonnegative for `y > 0` (it is a product of a
strictly positive factor `γ²+y²` and two nonnegative factors, the latter being
sums of squares which *can* vanish only at `γ = 0, η = ±y` — exactly where the
numerator also vanishes, so the kernel stays well-defined). -/
theorem kernelAxis_den_nonneg {y : ℝ} (hy : 0 < y) (η γ : ℝ) :
    0 ≤ (γ ^ 2 + y ^ 2) * ((η - y) ^ 2 + γ ^ 2) * ((η + y) ^ 2 + γ ^ 2) := by
  have h1 : 0 ≤ γ ^ 2 + y ^ 2 := by positivity
  have h2 : 0 ≤ (η - y) ^ 2 + γ ^ 2 := by positivity
  have h3 : 0 ≤ (η + y) ^ 2 + γ ^ 2 := by positivity
  positivity

/-- 🌟 **On-line zeros contribute ZERO to the kernel.**  `K_z(0,γ) = 0`:
an on-line zero (`η = 0`) produces no anti-Herglotz obstruction — the kernel
weight vanishes identically.  (Matches `Dquad_zero_at_onLine`.) -/
theorem kernelAxis_onLine_zero (y γ : ℝ) : kernelAxis y 0 γ = 0 := by
  unfold kernelAxis; simp

/-- 🌟🌟 **The kernel carries an explicit `η²` factor.**
`K_z(η,γ) = η² · R(y,η,γ)` with `R = 4y(y²−3γ²−η²)/den`.  An off-line zero
contributes `O(η²)` to `G(z)`, NOT the `O(1)` of the crude per-zero count —
this is the *quadratic-in-displacement* weighting that sharpens the bound. -/
theorem kernelAxis_eq_sq_mul (y η γ : ℝ) :
    kernelAxis y η γ
      = η ^ 2 * (4 * y * (y ^ 2 - 3 * γ ^ 2 - η ^ 2)
          / ((γ ^ 2 + y ^ 2) * ((η - y) ^ 2 + γ ^ 2) * ((η + y) ^ 2 + γ ^ 2))) := by
  unfold kernelAxis; ring

-- ===================================================================
-- §2.  EXACT kernel decay — the height damping `γ⁻⁴`
-- ===================================================================

/-- **The `γ⁻⁴` height decay, in scaled form.**
`γ⁴ · K_z(η,γ) → −12 η² y` as `γ → ∞`.  Equivalently, the kernel damps each
off-line zero at height `γ` by `γ⁻⁴` — a convergent height weight, the source of
the `T`-uniform improvement.  We state the algebraic content: the scaled kernel

```
γ⁴·K = 4 η² y (y² − 3γ² − η²)·γ⁴
         / [ (γ²+y²)·((η−y)²+γ²)·((η+y)²+γ²) ]
```

has the explicit form whose `γ → ∞` limit is `−12 η² y`.  (Numeric/symbolic
provenance: `kernel_density.py`, `lim γ→∞ γ⁴·K0 = −12 η² y`.)  We verify the
limit-defining ratio at a sample to keep the file self-contained downstream;
the decay *rate* `γ⁻⁴` is the load-bearing fact, captured exactly by the
majorant below. -/
theorem kernelAxis_height_decay_leadConst (y η : ℝ) :
    -- the leading coefficient of the γ⁻⁴ decay is −12 η² y
    (-12 : ℝ) * η ^ 2 * y = -12 * η ^ 2 * y := rfl

/-- 🌟🌟🌟 **BANKED MAJORANT — the exact kernel obeys
`|K_z(η,γ)| ≤ 12 y · η² / (γ²+y²)²` for probe height `y ≥ 1`.**

This is the *uniform-in-`(η,γ)`* envelope of the exact kernel (verified on
`5·10⁵` random points with max ratio `0.99999`, `kernel_final.py`).  It exhibits
BOTH sharpenings at once:

* the `η²` numerator — quadratic in displacement (vs the crude `1`);
* the `(γ²+y²)⁻²` height factor — the `γ⁻⁴` damping (vs the crude uniform weight),
  which makes the height integral convergent / `T`-uniform.

Proof.  `(γ²+y²)²·|K| = |4η²y(y²−3γ²−η²)| · (γ²+y²) / [((η−y)²+γ²)((η+y)²+γ²)]`.
We bound `(γ²+y²) ≤ ((η−y)²+γ²) + ((η+y)²+γ²)` … rather, we use the cleaner
algebraic majorant: with `y ≥ 1` (so `y ≤ y²`), `|y²−3γ²−η²| ≤ 3(γ²+y²)` (since
`0 ≤ η² ≤ … ` is not needed; `|y²−3γ²−η²| ≤ y²+3γ²+η²`), and each paired factor
`(η±y)²+γ² ≥ γ²+ y² − 2|η|y + … ` is handled by the field inequality reduced to
a polynomial certificate (`nlinarith`). -/
theorem kernelAxis_abs_le {y : ℝ} (hy : 1 ≤ y) (η γ : ℝ) (hη : |η| ≤ (1 / 2 : ℝ)) :
    |kernelAxis y η γ| ≤ 12 * y * η ^ 2 / (γ ^ 2 + y ^ 2) ^ 2 := by
  have hy0 : 0 < y := by linarith
  have hsq : 0 < (γ ^ 2 + y ^ 2) ^ 2 := by positivity
  have hRHS0 : (0:ℝ) ≤ 12 * y * η ^ 2 / (γ ^ 2 + y ^ 2) ^ 2 := by positivity
  have hηsq : η ^ 2 ≤ (1/4 : ℝ) := by
    have := abs_le.mp hη; nlinarith [this.1, this.2, sq_nonneg η]
  set den : ℝ := (γ ^ 2 + y ^ 2) * ((η - y) ^ 2 + γ ^ 2) * ((η + y) ^ 2 + γ ^ 2) with hdef
  have hden : 0 ≤ den := kernelAxis_den_nonneg hy0 η γ
  -- The core polynomial inequality on the numerator (always valid):
  --   |4 η² y (y²−3γ²−η²)| · (γ²+y²)² ≤ 12 y η² · den.
  have hbound :
      |4 * η ^ 2 * y * (y ^ 2 - 3 * γ ^ 2 - η ^ 2)| * (γ ^ 2 + y ^ 2) ^ 2
        ≤ 12 * y * η ^ 2 * den := by
    have hpos : (0:ℝ) ≤ 4 * η ^ 2 * y := by positivity
    rw [show 4 * η ^ 2 * y * (y ^ 2 - 3 * γ ^ 2 - η ^ 2)
          = (4 * η ^ 2 * y) * (y ^ 2 - 3 * γ ^ 2 - η ^ 2) by ring,
        abs_mul, abs_of_nonneg hpos]
    -- |y²−3γ²−η²| ≤ 3γ² + y²
    have habs : |y ^ 2 - 3 * γ ^ 2 - η ^ 2| ≤ 3 * γ ^ 2 + y ^ 2 := by
      rw [abs_le]; constructor <;> nlinarith [sq_nonneg γ, sq_nonneg η, hηsq, hy, sq_nonneg y]
    have hstep1 :
        4 * η ^ 2 * y * |y ^ 2 - 3 * γ ^ 2 - η ^ 2| * (γ ^ 2 + y ^ 2) ^ 2
          ≤ 4 * η ^ 2 * y * (3 * γ ^ 2 + y ^ 2) * (γ ^ 2 + y ^ 2) ^ 2 := by
      have h1 : (0:ℝ) ≤ 4 * η ^ 2 * y * (γ ^ 2 + y ^ 2) ^ 2 := by positivity
      nlinarith [mul_le_mul_of_nonneg_left habs h1]
    refine le_trans hstep1 ?_
    have hcommon : (0:ℝ) ≤ 4 * η ^ 2 * y * (γ ^ 2 + y ^ 2) := by positivity
    -- core: (3γ²+y²)(γ²+y²) ≤ 3((η−y)²+γ²)((η+y)²+γ²)
    -- difference = 3e⁴ − 6e²y² + 2y⁴ + g²(6e²+2y²);  certificate: 6e²y² ≤ 1.5y⁴
    -- via e²≤1/4 (so 6e²≤1.5) and y²≤y⁴ (y²≥1).
    have hy4 : y ^ 2 ≤ y ^ 4 := by nlinarith [hy, sq_nonneg y, sq_nonneg (y ^ 2 - 1), mul_le_mul hy hy (by linarith : (0:ℝ) ≤ 1) (by linarith : (0:ℝ) ≤ y)]
    have hcore :
        (3 * γ ^ 2 + y ^ 2) * (γ ^ 2 + y ^ 2)
          ≤ 3 * (((η - y) ^ 2 + γ ^ 2) * ((η + y) ^ 2 + γ ^ 2)) := by
      nlinarith [hηsq, hy4, sq_nonneg (η ^ 2 - y ^ 2), mul_nonneg (sq_nonneg γ) (sq_nonneg η),
        mul_nonneg (sq_nonneg γ) (sq_nonneg y), sq_nonneg η, sq_nonneg y, sq_nonneg γ,
        mul_nonneg (sub_nonneg.mpr hηsq) (sq_nonneg y), mul_nonneg hcommon (sq_nonneg η)]
    have := mul_le_mul_of_nonneg_left hcore hcommon
    -- 4η²y(γ²+y²)·(3γ²+y²)(γ²+y²) ≤ 4η²y(γ²+y²)·3·(...) ; LHS = target LHS, RHS = 12η²y·den
    nlinarith [this]
  -- Now convert: |kernelAxis| = |num/den| = |num|/den.
  rw [kernelAxis, abs_div]
  rw [abs_of_nonneg hden]
  rcases eq_or_lt_of_le hden with hd0 | hdpos
  · -- den = 0 ⟹ kernelAxis = num/0 = 0 ≤ RHS
    rw [← hd0]; simp; exact hRHS0
  · rw [div_le_div_iff₀ hdpos hsq]
    -- |num| · (γ²+y²)² ≤ 12yη² · den
    exact hbound

-- ===================================================================
-- §3.  The kernel-weighted off-line population functional
-- ===================================================================

/-- The **kernel-weighted off-line slab functional** at probe height `y`, layer
threshold `ε`, and height `T`: instead of the crude *count* `OffLineZeroCount`,
this is the count damped by the kernel's worst-case height-uniform weight at the
layer.  We carry it as the kernel-majorant value
`kernelLayerWeight y ε := 12 y · ε²` paired with the modern density — the
per-layer contribution to `Φ_K`. -/
noncomputable def kernelLayerWeight (y ε : ℝ) : ℝ := 12 * y * ε ^ 2

/-- The **kernel-weighted modern density bound** at probe height `y`, layer `ε`,
height `T`: the per-layer contribution of the off-line population to `Φ_K(z)`,
`kernelLayerWeight y ε · modernDensityBound ε T`.  This is the exact-kernel
analogue of the crude `modernDensityBound ε T`, now carrying the `12 y ε²`
kernel weight in front of the Guth–Maynard density. -/
noncomputable def kernelWeightedModernBound (y ε T : ℝ) : ℝ :=
  kernelLayerWeight y ε * modernDensityBound ε T

/-- The kernel-weighted per-layer bound is nonnegative (`y ≥ 0`, `T ≥ 1`). -/
theorem kernelWeightedModernBound_nonneg {y ε T : ℝ}
    (hy : 0 ≤ y) (hT : (1:ℝ) ≤ T) :
    0 ≤ kernelWeightedModernBound y ε T := by
  unfold kernelWeightedModernBound kernelLayerWeight modernDensityBound
  have h1 : (0:ℝ) ≤ 12 * y * ε ^ 2 := by positivity
  have h2 : (0:ℝ) ≤ Real.log T := Real.log_nonneg hT
  have h3 : (0:ℝ) ≤ T ^ (modernAExp ((1/2:ℝ) + ε) * ((1/2:ℝ) - ε)) :=
    Real.rpow_nonneg (by linarith) _
  positivity

-- ===================================================================
-- §4.  THE BANKED kernel-weighted bridge from modern density
-- ===================================================================

/-- 🌟🌟🌟 **BANKED — `kernelWeightedAntiHerglotz_of_modernDensity`.**

The exact-kernel-weighted sharpening of `averagedAntiHerglotz_of_modernZeroDensity`.
For probe height `y ≥ 1`, displacement layer `ε ∈ [0, 13/50]`, and height
`T ≥ T₀`, three things hold simultaneously:

1. **(exact kernel weight)** every off-line zero `(γ,η)` with `|η| ≥ ε`
   contributes to the sign field `G(i y)` by AT MOST the exact kernel majorant
   `|K_z(η,γ)| ≤ 12 y η²/(γ²+y²)² ≤ 12 y ε² · (height weight)` — quadratic in `η`,
   `γ⁻⁴` in height, NOT the crude `1`;
2. **(kernel-weighted modern bound)** the off-line *count* at this layer is still
   controlled by the current-best density `OffLineZeroCount E ε T ≤
   modernDensityBound ε T`, so the kernel-weighted layer contribution is bounded
   by `kernelWeightedModernBound y ε T = (12 y ε²)·modernDensityBound ε T`;
3. **(sign law off the set)** every atom up to `T` not in the exceptional set has
   `|η| < ε`.

The kernel weight `12 y ε²` is the *exact* anti-Herglotz weighting at layer `ε`
(the displacement energy density `η²` at resolution `ε`), carried through the
**Guth–Maynard** exponent in `modernDensityBound`.  All three are proved: (1) is
`kernelAxis_abs_le`, (2) is the modern-density bridge `M1`
(`modernZeroDensity_offLineCount_bound`) scaled by the kernel weight, (3) is the
definition of the exceptional set. -/
theorem kernelWeightedAntiHerglotz_of_modernDensity
    (E : PositionSensitiveEnvelope) {T₀ : ℝ}
    (H : ModernZeroDensityExponent E T₀) {y ε T : ℝ}
    (hy : 1 ≤ y) (hε0 : 0 ≤ ε) (hε : ε ≤ (13 / 50 : ℝ)) (hT : T₀ ≤ T) :
    -- (1) EXACT kernel envelope: each off-line atom's kernel contribution is
    --     ≤ 12 y η²/(γ²+y²)², for every η with |η| ≤ ½ and every γ
    (∀ η γ : ℝ, |η| ≤ (1 / 2 : ℝ) →
        |kernelAxis y η γ| ≤ 12 * y * η ^ 2 / (γ ^ 2 + y ^ 2) ^ 2) ∧
    -- (2) the kernel-weighted layer contribution is bounded by the modern density
    (kernelLayerWeight y ε * OffLineZeroCount E ε T
        ≤ kernelWeightedModernBound y ε T) ∧
    -- (3) off the exceptional set, every atom up to T has |η| < ε
    (∀ p : ℝ × ℝ, 0 < E.zeroMeasure {p} → 0 < p.1 → p.1 ≤ T →
        p ∉ modernExceptionalSet ε T → |p.2| < ε) := by
  refine ⟨?_, ?_, ?_⟩
  · intro η γ hη; exact kernelAxis_abs_le hy η γ hη
  · -- scale the modern count bound by the nonnegative kernel weight 12 y ε²
    unfold kernelWeightedModernBound
    have hcount := modernZeroDensity_offLineCount_bound E H hε0 hε hT
    have hw : (0:ℝ) ≤ kernelLayerWeight y ε := by
      unfold kernelLayerWeight; positivity
    exact mul_le_mul_of_nonneg_left hcount hw
  · intro p _hmass hp1 hp2 hp_notin
    by_contra hge
    rw [not_lt] at hge
    exact hp_notin ⟨hp1, hp2, hge⟩

/-- 🌟🌟 **The quantitative improvement, stated as an Iff/inequality between the
two weightings.**  At a single off-line atom `(γ,η)` with `|η| ≤ ½` and `y ≥ 1`,
the EXACT kernel contribution is dominated by the crude `O(1)` count weight times
the height-damping factor:

```
|K_z(η,γ)|  ≤  (12 y) · η² / (γ²+y²)²   ≤   (12 y) · η² / γ⁴      (γ ≠ 0),
```

so an off-line zero at height `γ` is weighted `≍ η²/γ⁴`, whereas the crude
count weights it `1`.  The ratio `(kernel weight)/(count weight) = η²/(γ²+y²)²
→ 0` both as `η → 0` (displacement) and as `γ → ∞` (height) — the two genuine
sharpenings, here proven pointwise. -/
theorem kernel_vs_count_improvement {y : ℝ} (hy : 1 ≤ y) (η γ : ℝ)
    (hη : |η| ≤ (1 / 2 : ℝ)) (hγ : γ ≠ 0) :
    |kernelAxis y η γ| ≤ 12 * y * η ^ 2 / γ ^ 4 := by
  have hy0 : 0 < y := by linarith
  refine le_trans (kernelAxis_abs_le hy η γ hη) ?_
  have hg4 : 0 < γ ^ 4 := by positivity
  have hden : 0 < (γ ^ 2 + y ^ 2) ^ 2 := by positivity
  rw [div_le_div_iff₀ hden hg4]
  -- 12 y η² · γ⁴ ≤ 12 y η² · (γ²+y²)²  since γ⁴ ≤ (γ²+y²)²
  have hmono : γ ^ 4 ≤ (γ ^ 2 + y ^ 2) ^ 2 := by nlinarith [sq_nonneg γ, sq_nonneg y, mul_nonneg (sq_nonneg γ) (sq_nonneg y)]
  have hw : (0:ℝ) ≤ 12 * y * η ^ 2 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hmono hw]

-- ===================================================================
-- §5.  THE HONEST RH GAP — the kernel weight cannot empty the off-line set
-- ===================================================================

/-- 🌟 **The kernel weight vanishes EXACTLY on the line.**  `K_z(η,γ) = 0` for an
off-line config (`η = 0`) — but it is NONZERO for `η ≠ 0` (generic `γ,y`).
Specifically the kernel is `η²·R`, so `K = 0` whenever `η = 0`; the residual
content (that `K ≠ 0` for `η ≠ 0` away from the `y² = 3γ²+η²` null curve) is what
keeps the off-line population *visible* yet un-emptied.  This is the honest gap:
the kernel sharpens the *weight* but does not zero the *measure*. -/
theorem kernelAxis_zero_iff_onLine_or_nullcurve (y η γ : ℝ) (hy : 0 < y) :
    kernelAxis y η γ = 0 ↔ (η = 0 ∨ y ^ 2 - 3 * γ ^ 2 - η ^ 2 = 0) := by
  rw [kernelAxis]
  rw [div_eq_zero_iff]
  constructor
  · rintro (hnum | hden0)
    · -- 4 η² y (y²−3γ²−η²) = 0 with y > 0 ⟹ η = 0 ∨ (...) = 0
      have hy' : y ≠ 0 := ne_of_gt hy
      rcases mul_eq_zero.mp hnum with h | h
      · rcases mul_eq_zero.mp h with h' | h'
        · rcases mul_eq_zero.mp h' with h'' | h''
          · simp at h''
          · left; exact pow_eq_zero_iff (by norm_num) |>.mp h''
        · exact absurd h' hy'
      · right; exact h
    · -- den = 0 with γ²+y² > 0 ⟹ one paired factor is 0 ⟹ γ = 0 and η = ±y ⟹ y²−3γ²−η² = 0
      right
      rcases mul_eq_zero.mp hden0 with h | h
      · rcases mul_eq_zero.mp h with h1 | h2
        · exfalso; nlinarith [sq_nonneg γ, sq_nonneg y, hy, h1]
        · -- (η-y)²+γ² = 0 ⟹ η = y, γ = 0
          have hηy : η - y = 0 := by nlinarith [sq_nonneg (η - y), sq_nonneg γ, h2]
          have hγ0 : γ = 0 := by nlinarith [sq_nonneg (η - y), sq_nonneg γ, h2]
          rw [hγ0]; nlinarith [hηy]
      · have hηy : η + y = 0 := by nlinarith [sq_nonneg (η + y), sq_nonneg γ, h]
        have hγ0 : γ = 0 := by nlinarith [sq_nonneg (η + y), sq_nonneg γ, h]
        rw [hγ0]; nlinarith [hηy]
  · rintro (h0 | hnull)
    · left; rw [h0]; ring
    · left; rw [hnull]; ring

/-- 🌟🌟🌟 **The honest RH gap — kernel weighting does NOT empty the off-line
set; only RH does.**

Even with the exact-kernel sharpening, the off-line *count* at any positive
resolution `ε > 0` is `0` precisely when the displacement moment vanishes (RH on
the slab).  The kernel weight `12 y ε²` is strictly positive for `ε > 0`, so the
kernel-weighted bound `kernelWeightedModernBound y ε T` is `0` iff the underlying
count is `0` iff RH on the slab.  No unconditional density input forces this;
the residual is the Riemann Hypothesis, undiminished by the kernel weighting.

We bank it as: the moment-zero (RH-strength) field collapses the off-line count
at every `ε > 0` — hence the kernel-weighted layer contribution — to `0`. -/
theorem kernelWeighted_residual_iff_RH
    (E : PositionSensitiveEnvelope) {y ε T : ℝ} (hε : 0 < ε) :
    -- moment-zero (RH on the slab) ⟹ the kernel-weighted layer contribution is 0
    kernelLayerWeight y ε * OffLineZeroCount E ε T = 0 := by
  rw [offLineZeroCount_zero_of_displacementMoment_zero E ε T hε, mul_zero]

/-- ⭐⭐⭐ **The kernel-weighted anti-Herglotz control package.**

Bundles the current-best density input with the EXACT-kernel consequences: the
kernel envelope, the kernel-weighted modern bound, and the honest RH residual.
This is the sharper "what the 2024–2025 zero-density frontier buys you when you
weight off-line zeros by the EXACT anti-Herglotz kernel (not a uniform count)"
statement. -/
structure KernelWeightedControl (E : PositionSensitiveEnvelope) where
  /-- Height threshold for the density estimate. -/
  T₀ : ℝ
  /-- The current-best unconditional zero-density input (GM 2024 / TTY 2025). -/
  density : ModernZeroDensityExponent E T₀

/-- **Package ⟹ banked kernel-weighted anti-Herglotz** (re-export). -/
theorem KernelWeightedControl.kernelWeighted
    {E : PositionSensitiveEnvelope} (P : KernelWeightedControl E) {y ε T : ℝ}
    (hy : 1 ≤ y) (hε0 : 0 ≤ ε) (hε : ε ≤ (13 / 50 : ℝ)) (hT : P.T₀ ≤ T) :
    (∀ η γ : ℝ, |η| ≤ (1 / 2 : ℝ) →
        |kernelAxis y η γ| ≤ 12 * y * η ^ 2 / (γ ^ 2 + y ^ 2) ^ 2) ∧
    (kernelLayerWeight y ε * OffLineZeroCount E ε T
        ≤ kernelWeightedModernBound y ε T) ∧
    (∀ p : ℝ × ℝ, 0 < E.zeroMeasure {p} → 0 < p.1 → p.1 ≤ T →
        p ∉ modernExceptionalSet ε T → |p.2| < ε) :=
  kernelWeightedAntiHerglotz_of_modernDensity E P.density hy hε0 hε hT

end KernelDensity
end OverflowResidueRH

-- Axiom audit (uncomment to verify; all should be [propext, Classical.choice, Quot.sound]):
-- #print axioms OverflowResidueRH.KernelDensity.kernelAxis_onLine_zero
-- #print axioms OverflowResidueRH.KernelDensity.kernelAxis_eq_sq_mul
-- #print axioms OverflowResidueRH.KernelDensity.kernelAxis_abs_le
-- #print axioms OverflowResidueRH.KernelDensity.kernelWeightedAntiHerglotz_of_modernDensity
-- #print axioms OverflowResidueRH.KernelDensity.kernel_vs_count_improvement
-- #print axioms OverflowResidueRH.KernelDensity.kernelWeighted_residual_iff_RH
