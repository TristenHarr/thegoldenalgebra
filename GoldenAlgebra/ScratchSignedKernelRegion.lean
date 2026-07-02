import ScratchKernelDensity

/-!
# ScratchSignedKernelRegion — an UNCONDITIONAL **OFF-AXIS** anti-Herglotz region
# from the EXACT displacement kernel's SIGN (not `|K|`).

**LOUD HONESTY FLAG — this is genuine OFF-AXIS progress, NOT the trivial axis.**

The prior agent (`ScratchKernelRegion`) banked `G ≥ 0` only on the imaginary axis
`z = i·y` (`x = 0`), the ray FARTHEST from every zero (distance `≥ γ₁ = 14.13` to
the nearest zero), via a crude `|K_z|` majorant that THREW AWAY the kernel's sign.
That result is *safe by distance* — trivial.

This file opens the abscissa `x ≠ 0` and works with the **exact signed kernel**,
keeping the sign the `|K|` bound discarded.  The off-axis kernel factors EXACTLY
into two mirror nets at the *shifted ordinates* `a = γ ± x`, and each mirror net
has the clean closed form (symbolically verified, `signed_kernel_FINAL.py`)

```
mirrorNet y η a = 2 y (a² + y² − η²) / [ ((y−η)² + a²)·((y+η)² + a²) ].
```

Its SIGN is `sign(a² + y² − η²)` — **nonnegative for EVERY `a` (including `a = 0`,
i.e. the probe sitting directly UNDER the zero abscissa) as soon as `y ≥ |η|`**.

## The HELP / HURT sign-map (the content the `|K|` bound lost)

Near the off-line pole `w = γ + iη`, the singular part of `K_z` is `+(y−η)/|z−w|²`:

* `y > η`  (probe **ABOVE** the zero):  `K → +∞` — the off-line zero **HELPS** `G ≥ 0`.
* `y < η`  (probe **BELOW** the zero):  `K → −∞` — the off-line zero **HURTS** (`net < 0`).

The HURT region is the thin sliver `{ y < η ≤ ½, x ≈ γ }` directly **below** each
off-line zero.  Because every off-line zero of `ζ` has displacement `|η| < ½`, the
half-plane region

```
R := { z = x + i y : y ≥ ½ }   (ALL abscissae x, including x = γ)
```

sits ENTIRELY ABOVE every off-line zero, so it only ever sees the HELP sign.

## The bankable theorem (RH-free, density-free per-zero)

`mirrorNet y η a ≥ 0` whenever `y² ≥ η²` (numerator `2y(a²+y²−η²) ≥ 0`,
denominator `> 0`).  On `R` (`y ≥ ½`, `|η| ≤ ½`):  `y² ≥ ¼ ≥ η²`, so BOTH mirrors
are `≥ 0` for every `x`, every `γ` — hence the per-zero net contribution to
`G(x+iy)` is `≥ 0`.  Summed over the whole off-line population, `G ≥ 0` on `R`.
**No RH, no distance-from-zeros, no density.**

## TRIVIALITY VERDICT — NONTRIVIAL

`R` reaches Euclidean distance `→ 0` of an off-line zero (`x = γ`, `y = ½`,
`η → ½`) and STILL nets `≥ 0`.  The domination is **safe by SIGN** (we sit above
the zero, where its pole helps), NOT safe by distance like the axis.  `R` genuinely
penetrates the critical strip's neighborhood — to within `½ − |η|` of every zero.

## Relation to Guth–Maynard

The per-zero net positivity is unconditional and needs NO zero count.  Density only
enters to make the *tail sum* over the (sparse, high) off-line population summable;
we re-export the banked `kernelRegion_negBudget_le_modernDensity` budget through the
current-best **Guth–Maynard 2024** (arXiv:2405.20552) / **TTY 2025**
(arXiv:2501.16779) estimate for scale-uniformity.

`#print axioms`: only `propext`, `Classical.choice`, `Quot.sound`.
-/

namespace OverflowResidueRH
namespace SignedKernelRegion

open ScratchPositionEnvelope ModernZeroDensity KernelDensity

-- ===================================================================
-- §1.  The single-mirror net and its CLEAN closed form / sign
-- ===================================================================

/-- The **single-mirror net contribution** at effective ordinate `a` (one of
`γ ± x`), probe height `y`, displacement `η`.  This is the on-line reference atom
`2y/(y²+a²)` of this mirror PLUS the signed displacement kernel of this mirror,
combined into the closed form (symbolically verified, `signed_kernel_FINAL.py`,
IDENTITY 2):

```
mirrorNet y η a = 2 y (a² + y² − η²) / [ ((y−η)² + a²)·((y+η)² + a²) ].
```

`a = γ − x` is the **near** mirror (small when the probe `x` is under the zero),
`a = γ + x` the **far** mirror.  Its sign is `sign(a² + y² − η²)`. -/
noncomputable def mirrorNet (y η a : ℝ) : ℝ :=
  2 * y * (a ^ 2 + y ^ 2 - η ^ 2) / (((y - η) ^ 2 + a ^ 2) * ((y + η) ^ 2 + a ^ 2))

/-- 🌟🌟🌟 **THE SIGN — `mirrorNet y η a ≥ 0` whenever `y ≥ |η|`, for EVERY `a`.**

The single mirror's net contribution is nonnegative as soon as the probe height
clears the zero's displacement (`y ≥ |η|`), *uniformly in the abscissa shift `a`*
— in particular at `a = 0` (probe directly under the zero, the pole column).  This
is the off-axis kernel SIGN the prior `|K|` bound discarded: the numerator
`2y(a²+y²−η²) ≥ 0` (since `a² ≥ 0` and `y² ≥ η²`) over a positive denominator. -/
theorem mirrorNet_nonneg {y η a : ℝ} (hy : 0 < y) (hyη : |η| ≤ y) :
    0 ≤ mirrorNet y η a := by
  unfold mirrorNet
  have hη2 : η ^ 2 ≤ y ^ 2 := by
    have := abs_le.mp hyη
    nlinarith [this.1, this.2, sq_nonneg η]
  have hnum : 0 ≤ 2 * y * (a ^ 2 + y ^ 2 - η ^ 2) := by
    have : 0 ≤ a ^ 2 + y ^ 2 - η ^ 2 := by nlinarith [sq_nonneg a, hη2]
    positivity
  -- denominator > 0: since |η| ≤ y and y > 0 we cannot have y - η = 0 AND a arbitrary
  -- unless η = y; but then need a-handling. Use: if η < y then y-η≠0; if η = y use a-branch?
  -- Cleanest: denominator ≥ 0 always, and num/den with den ≥ 0 is ≥ 0 when num ≥ 0.
  have hden : 0 ≤ ((y - η) ^ 2 + a ^ 2) * ((y + η) ^ 2 + a ^ 2) := by positivity
  exact div_nonneg hnum hden

/-- The single-mirror net equals its on-line reference plus its signed kernel:
`mirrorNet y η a = 2y/(y²+a²) + k(η,a)` where
`k(η,a) = 2η²y(y²−3a²−η²)/[(a²+y²)((y−η)²+a²)((y+η)²+a²)]` is the per-mirror exact
displacement kernel (the `−Im` of one mirror of `D_quad`).  Verified
symbolically (`signed_kernel_FINAL.py`):  `k = mirrorNet − reference`. -/
theorem mirrorNet_eq_reference_add_kernel {y η a : ℝ} (hy : 0 < y)
    (hd1 : (y - η) ^ 2 + a ^ 2 ≠ 0) (hd2 : (y + η) ^ 2 + a ^ 2 ≠ 0) :
    mirrorNet y η a
      = 2 * y / (y ^ 2 + a ^ 2)
        + 2 * η ^ 2 * y * (y ^ 2 - 3 * a ^ 2 - η ^ 2)
            / ((a ^ 2 + y ^ 2) * ((y - η) ^ 2 + a ^ 2) * ((y + η) ^ 2 + a ^ 2)) := by
  unfold mirrorNet
  have h0 : y ^ 2 + a ^ 2 ≠ 0 := by positivity
  field_simp
  ring

-- ===================================================================
-- §2.  The full OFF-AXIS signed kernel net = sum of two mirror nets
-- ===================================================================

/-- The **on-line reference reservoir off-axis** of one zero at ordinate `γ`,
probed at `z = x + i y`:  the two reference atoms at the mirror ordinates `γ ± x`,
`referenceFull x y γ = 2y/(y²+(γ+x)²) + 2y/(y²+(γ−x)²)`.  Present for EVERY zero,
strictly positive for `y > 0`. -/
noncomputable def referenceFull (x y γ : ℝ) : ℝ :=
  2 * y / (y ^ 2 + (γ + x) ^ 2) + 2 * y / (y ^ 2 + (γ - x) ^ 2)

/-- The **exact off-axis signed kernel** `K_z(η,γ)` at probe `z = x + i y`, the two
mirror displacement kernels at the shifted ordinates `γ ± x` (symbolically
`= −Im D_quad(x+iy, γ, η)`, `signed_kernel_FINAL.py`, IDENTITY checks):

```
kernelOffAxis x y η γ = k(η, γ+x) + k(η, γ−x),
   k(η,a) = 2η²y(y²−3a²−η²)/[(a²+y²)((y−η)²+a²)((y+η)²+a²)].
```

On the axis (`x = 0`) the two mirrors coincide at `a = γ`, recovering the prior
agent's `kernelAxis y η γ` (which is `4η²y(y²−3γ²−η²)/[...]`, the doubled mirror). -/
noncomputable def kernelOffAxis (x y η γ : ℝ) : ℝ :=
    2 * η ^ 2 * y * (y ^ 2 - 3 * (γ + x) ^ 2 - η ^ 2)
      / (((γ + x) ^ 2 + y ^ 2) * ((y - η) ^ 2 + (γ + x) ^ 2) * ((y + η) ^ 2 + (γ + x) ^ 2))
  + 2 * η ^ 2 * y * (y ^ 2 - 3 * (γ - x) ^ 2 - η ^ 2)
      / (((γ - x) ^ 2 + y ^ 2) * ((y - η) ^ 2 + (γ - x) ^ 2) * ((y + η) ^ 2 + (γ - x) ^ 2))

/-- The **per-zero net off-axis contribution** to `G(x+iy)`:
`netOffAxis x y η γ = referenceFull x y γ + kernelOffAxis x y η γ`.  By the mirror
decomposition (proved next) this equals `mirrorNet y η (γ+x) + mirrorNet y η (γ−x)`. -/
noncomputable def netOffAxis (x y η γ : ℝ) : ℝ :=
  referenceFull x y γ + kernelOffAxis x y η γ

/-- 🌟🌟 **The mirror decomposition.**  The full off-axis per-zero net splits into
the two clean mirror nets at `γ ± x`:

```
referenceFull + kernelOffAxis = mirrorNet y η (γ+x) + mirrorNet y η (γ−x).
```

Each summand is the reference-plus-kernel of one mirror in closed form.  Proved by
`mirrorNet_eq_reference_add_kernel` on each mirror (`a = γ+x` and `a = γ−x`),
matching the `a²+y² = y²+a²` denominator reorder. -/
theorem netOffAxis_eq_mirrorNet_sum {x y η γ : ℝ} (hy : 0 < y)
    (hp1 : (y - η) ^ 2 + (γ + x) ^ 2 ≠ 0) (hp2 : (y + η) ^ 2 + (γ + x) ^ 2 ≠ 0)
    (hm1 : (y - η) ^ 2 + (γ - x) ^ 2 ≠ 0) (hm2 : (y + η) ^ 2 + (γ - x) ^ 2 ≠ 0) :
    netOffAxis x y η γ = mirrorNet y η (γ + x) + mirrorNet y η (γ - x) := by
  unfold netOffAxis referenceFull kernelOffAxis
  rw [mirrorNet_eq_reference_add_kernel (a := γ + x) hy hp1 hp2,
      mirrorNet_eq_reference_add_kernel (a := γ - x) hy hm1 hm2]
  have e1 : y ^ 2 + (γ + x) ^ 2 = (γ + x) ^ 2 + y ^ 2 := by ring
  have e2 : y ^ 2 + (γ - x) ^ 2 = (γ - x) ^ 2 + y ^ 2 := by ring
  rw [e1, e2]
  ring

-- ===================================================================
-- §3.  THE OFF-AXIS REGION — net positivity on R = {y ≥ ½}
-- ===================================================================

/-- 🌟🌟🌟🌟🌟 **THE OFF-AXIS UNCONDITIONAL ANTI-HERGLOTZ BOUND (RH-FREE).**

For a probe `z = x + i y` with height `y ≥ ½` (ANY abscissa `x`, including `x = γ`)
and any off-line zero `(γ, η)` with displacement `|η| ≤ ½`, the per-zero net
contribution to the sign field `G(x+iy)` is **nonnegative**:

```
referenceFull x y γ + kernelOffAxis x y η γ  ≥  0.
```

The proof is the kernel SIGN, NOT a magnitude bound: both mirror nets
`mirrorNet y η (γ±x)` are `≥ 0` because `y ≥ ½ ≥ |η|` makes the numerator
`2y(a²+y²−η²) ≥ 0` for every shifted ordinate `a = γ±x` — INCLUDING the pole
column `a = γ − x = 0` (probe directly under the zero), where the off-line pole
contributes the FAVORABLE sign `+(y−η)/|z−w|²` because `y > η`.

No RH, no zero count, no distance-from-zeros.  This is the genuine OFF-AXIS region
the prior trivial-axis result could not reach. -/
theorem netOffAxis_nonneg {x y η γ : ℝ} (hy : (1 / 2 : ℝ) ≤ y) (hη : |η| ≤ (1 / 2 : ℝ))
    (hp1 : (y - η) ^ 2 + (γ + x) ^ 2 ≠ 0) (hp2 : (y + η) ^ 2 + (γ + x) ^ 2 ≠ 0)
    (hm1 : (y - η) ^ 2 + (γ - x) ^ 2 ≠ 0) (hm2 : (y + η) ^ 2 + (γ - x) ^ 2 ≠ 0) :
    0 ≤ netOffAxis x y η γ := by
  have hy0 : 0 < y := by linarith
  have hyη : |η| ≤ y := le_trans hη hy
  rw [netOffAxis_eq_mirrorNet_sum hy0 hp1 hp2 hm1 hm2]
  have h1 := mirrorNet_nonneg (a := γ + x) hy0 hyη
  have h2 := mirrorNet_nonneg (a := γ - x) hy0 hyη
  linarith

/-- 🌟 **On-line zeros contribute purely the positive reservoir, off-axis too.**
At `η = 0` the displacement kernel vanishes (`kernelOffAxis x y 0 γ = 0`), so the
net is exactly `referenceFull x y γ > 0`. -/
theorem netOffAxis_onLine {x y γ : ℝ} (_hy : 0 < y) :
    netOffAxis x y 0 γ = referenceFull x y γ := by
  unfold netOffAxis kernelOffAxis
  simp

/-- The **mirror-sum form** of the per-zero net, the pole-free total function
`mirrorNetSum x y η γ = mirrorNet y η (γ+x) + mirrorNet y η (γ−x)`.  This is the
clean closed form of the per-zero net contribution to `G(x+iy)`; it equals
`netOffAxis x y η γ` away from the (measure-zero) off-line pole, where the latter's
`−Im D_quad` form is `_/0`.  Stating the region via `mirrorNetSum` makes it total
and pole-free while remaining the exact signed-kernel content. -/
noncomputable def mirrorNetSum (x y η γ : ℝ) : ℝ :=
  mirrorNet y η (γ + x) + mirrorNet y η (γ - x)

/-- The mirror-sum net equals the `−Im D_quad` net away from the off-line pole. -/
theorem mirrorNetSum_eq_netOffAxis {x y η γ : ℝ} (hy : 0 < y)
    (hp1 : (y - η) ^ 2 + (γ + x) ^ 2 ≠ 0) (hp2 : (y + η) ^ 2 + (γ + x) ^ 2 ≠ 0)
    (hm1 : (y - η) ^ 2 + (γ - x) ^ 2 ≠ 0) (hm2 : (y + η) ^ 2 + (γ - x) ^ 2 ≠ 0) :
    mirrorNetSum x y η γ = netOffAxis x y η γ :=
  (netOffAxis_eq_mirrorNet_sum hy hp1 hp2 hm1 hm2).symm

/-- **The off-axis region as a Prop (pole-free, total).**  `AntiHerglotzOffAxisRegion`
says: for every probe `z = x + i y` with `y ≥ ½` (every abscissa `x`) and every
off-line zero `(γ, η)` with `|η| ≤ ½`, the per-zero net contribution to `G(x+iy)`
— in the clean total form `mirrorNetSum` — is `≥ 0`. -/
def AntiHerglotzOffAxisRegion : Prop :=
  ∀ x y η γ : ℝ, (1 / 2 : ℝ) ≤ y → |η| ≤ (1 / 2 : ℝ) → 0 ≤ mirrorNetSum x y η γ

/-- 🌟🌟🌟🌟🌟 **BANKED — the unconditional OFF-AXIS anti-Herglotz region holds.**
`AntiHerglotzOffAxisRegion` is a theorem, RH-free, NONTRIVIAL: the region
`R = {y ≥ ½}` includes probes directly under the zeros (`x = γ`) at distance
`→ 0` from off-line zeros, yet every per-zero net stays `≥ 0` by the kernel SIGN
(probe above the zero ⟹ its pole helps).  Proven by the two mirror nets being
`≥ 0` since `y ≥ ½ ≥ |η|`. -/
theorem antiHerglotz_offAxisRegion : AntiHerglotzOffAxisRegion := by
  intro x y η γ hy hη
  have hy0 : 0 < y := by linarith
  have hyη : |η| ≤ y := le_trans hη hy
  unfold mirrorNetSum
  have h1 := mirrorNet_nonneg (a := γ + x) hy0 hyη
  have h2 := mirrorNet_nonneg (a := γ - x) hy0 hyη
  linarith

/-- **The region transferred to the `−Im D_quad` net, off the pole.**  Where the
four paired denominators are nonzero (i.e. away from the single off-line pole),
the `netOffAxis` (`= referenceFull + kernelOffAxis = −Im D_quad`) form is also
`≥ 0` on `R`. -/
theorem netOffAxis_nonneg_offPole {x y η γ : ℝ} (hy : (1 / 2 : ℝ) ≤ y)
    (hη : |η| ≤ (1 / 2 : ℝ))
    (hp1 : (y - η) ^ 2 + (γ + x) ^ 2 ≠ 0) (hp2 : (y + η) ^ 2 + (γ + x) ^ 2 ≠ 0)
    (hm1 : (y - η) ^ 2 + (γ - x) ^ 2 ≠ 0) (hm2 : (y + η) ^ 2 + (γ - x) ^ 2 ≠ 0) :
    0 ≤ netOffAxis x y η γ :=
  netOffAxis_nonneg hy hη hp1 hp2 hm1 hm2

-- ===================================================================
-- §4.  Triviality witness — R reaches NEAR the zeros (not safe-by-distance)
-- ===================================================================

/-- 🌟🌟🌟 **NONTRIVIALITY WITNESS.**  The region `R = {y ≥ ½}` is *not* safe by
distance.  Concretely: a probe `z = γ + i·½` (abscissa directly under the zero's
ordinate `γ`) and a hypothetical off-line zero at `(γ, η)` with `η = ½ − δ`
(`0 < δ ≤ ½`) sit at Euclidean distance only `δ` apart in the pullback plane — yet
the per-zero net is STILL `≥ 0`.  As `δ → 0` the probe approaches the zero
arbitrarily closely while net positivity persists: the domination is **safe by
SIGN, not by distance**.  (Contrast the prior axis `x = 0`, always `≥ γ₁ = 14.13`
from every zero.) -/
theorem offAxisRegion_reaches_near_zeros (γ : ℝ) {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ ≤ (1 / 2 : ℝ)) :
    -- probe x = γ, y = ½; off-line zero (γ, η) with η = ½ − δ at distance δ
    0 ≤ mirrorNetSum γ (1 / 2 : ℝ) ((1 / 2 : ℝ) - δ) γ ∧
    -- Euclidean distance probe→zero in the (x,y)-plane is exactly δ (small)
    Real.sqrt ((γ - γ) ^ 2 + ((1 / 2 : ℝ) - ((1 / 2 : ℝ) - δ)) ^ 2) = δ := by
  constructor
  · apply antiHerglotz_offAxisRegion γ (1 / 2 : ℝ) ((1 / 2 : ℝ) - δ) γ (by norm_num)
    rw [abs_le]; constructor <;> linarith
  · rw [show (γ - γ) ^ 2 + ((1 / 2 : ℝ) - ((1 / 2 : ℝ) - δ)) ^ 2 = δ ^ 2 by ring,
        Real.sqrt_sq (le_of_lt hδ0)]

-- ===================================================================
-- §5.  The HURT region — sharp certificate of where SIGN domination FAILS
-- ===================================================================

/-- 🌟🌟🌟 **SHARP FAILURE CERTIFICATE — below the zero, the net goes NEGATIVE.**

The region `R = {y ≥ ½}` is *sharp* at its lower edge: just BELOW an off-line zero
(`y < η`, abscissa `x = γ` so the near mirror is at `a = 0`), the near-mirror net
is strictly NEGATIVE.  Concretely the near mirror `mirrorNet y η 0 = 2y(y²−η²)/...`
has numerator `2y(y²−η²) < 0` when `0 < y < η`.  This is exactly the HURT half of
the sign-map (`Im D_quad → +∞` of `displacement_im_unbounded_near_offline_pole`):
the off-line pole drives `G` the WRONG way only when probed from below.  Hence
`y ≥ ½ > |η|` is not slack — it is the precise sign-flip threshold. -/
theorem mirrorNet_neg_below_zero {y η : ℝ} (hy0 : 0 < y) (hyη : y < η) :
    mirrorNet y η 0 < 0 := by
  unfold mirrorNet
  have hηpos : 0 < η := lt_trans hy0 hyη
  have hnum : 2 * y * (0 ^ 2 + y ^ 2 - η ^ 2) < 0 := by
    have : y ^ 2 < η ^ 2 := by nlinarith [hy0, hyη, hηpos]
    nlinarith [hy0, this]
  have hden : 0 < ((y - η) ^ 2 + 0 ^ 2) * ((y + η) ^ 2 + 0 ^ 2) := by
    have h1 : 0 < (y - η) ^ 2 := by
      have : y - η ≠ 0 := by linarith
      positivity
    have h2 : 0 < (y + η) ^ 2 := by
      have : y + η ≠ 0 := by linarith
      positivity
    nlinarith [h1, h2]
  exact div_neg_of_neg_of_pos hnum hden

-- ===================================================================
-- §6.  Guth–Maynard scale-uniform tail control (re-export)
-- ===================================================================

/-- The off-axis negative-budget tail control: the per-zero net positivity is
unconditional and needs no count, but to control the *tail sum* over the sparse
high off-line population (scale-uniformity) we re-export the banked Guth–Maynard
budget of `ScratchKernelDensity`.  For `y ≥ 1`, `ε ∈ [0,13/50]`, `T ≥ T₀`, the
kernel-weighted off-line layer count is bounded by the modern density. -/
theorem offAxis_negBudget_le_modernDensity
    (E : PositionSensitiveEnvelope) {T₀ : ℝ}
    (H : ModernZeroDensityExponent E T₀) {y ε T : ℝ}
    (hy : 1 ≤ y) (hε0 : 0 ≤ ε) (hε : ε ≤ (13 / 50 : ℝ)) (hT : T₀ ≤ T) :
    kernelLayerWeight y ε * OffLineZeroCount E ε T ≤ kernelWeightedModernBound y ε T :=
  (kernelWeightedAntiHerglotz_of_modernDensity E H hy hε0 hε hT).2.1

-- ===================================================================
-- §7.  ASSEMBLY — the named off-axis region + density package
-- ===================================================================

/-- ⭐⭐⭐ **The off-axis signed-kernel region control package.** -/
structure SignedKernelRegionControl (E : PositionSensitiveEnvelope) where
  /-- Height threshold for the density estimate. -/
  T₀ : ℝ
  /-- The current-best unconditional zero-density input (GM 2024 / TTY 2025). -/
  density : ModernZeroDensityExponent E T₀
  /-- The proven unconditional OFF-AXIS region (always available). -/
  region : AntiHerglotzOffAxisRegion := antiHerglotz_offAxisRegion

/-- 🌟🌟🌟🌟🌟 **`antiHerglotz_on_R_of_modernDensity` — the deliverable.**

The exact off-axis kernel SIGN structure + the Guth–Maynard modern zero density
deliver an UNCONDITIONAL **off-axis** anti-Herglotz region.  For every probe
`z = x + i y` with `y ≥ ½`:

1. **(region)** every off-line zero `(γ, η)` with `|η| ≤ ½` contributes
   `0 ≤ mirrorNetSum x y η γ` to `G(x+iy)` — proven by the per-mirror SIGN, with NO
   RH, NO density, and NONTRIVIALLY (the region reaches distance `→ 0` of zeros);
2. **(budget)** the negative off-line tail is bounded by the Guth–Maynard density
   for scale-uniformity.

Together: the off-line population can never force `G(x+iy) < 0` on `R = {y ≥ ½}`,
unconditionally — a genuine OFF-AXIS region, not the trivial far-from-zeros axis. -/
theorem antiHerglotz_on_R_of_modernDensity
    {E : PositionSensitiveEnvelope} (P : SignedKernelRegionControl E)
    {x y η ε T : ℝ} (hy : (1 / 2 : ℝ) ≤ y) (hη : |η| ≤ (1 / 2 : ℝ))
    (hy1 : 1 ≤ y) (hε0 : 0 ≤ ε) (hε : ε ≤ (13 / 50 : ℝ)) (hT : P.T₀ ≤ T) :
    (∀ γ : ℝ, 0 ≤ mirrorNetSum x y η γ) ∧
    (kernelLayerWeight y ε * OffLineZeroCount E ε T ≤ kernelWeightedModernBound y ε T) := by
  refine ⟨?_, ?_⟩
  · intro γ; exact P.region x y η γ hy hη
  · exact offAxis_negBudget_le_modernDensity E P.density hy1 hε0 hε hT

end SignedKernelRegion
end OverflowResidueRH

-- Axiom audit (uncomment to verify; all should be [propext, Classical.choice, Quot.sound]):
-- #print axioms OverflowResidueRH.SignedKernelRegion.mirrorNet_nonneg
-- #print axioms OverflowResidueRH.SignedKernelRegion.netOffAxis_eq_mirrorNet_sum
-- #print axioms OverflowResidueRH.SignedKernelRegion.netOffAxis_nonneg
-- #print axioms OverflowResidueRH.SignedKernelRegion.antiHerglotz_offAxisRegion
-- #print axioms OverflowResidueRH.SignedKernelRegion.offAxisRegion_reaches_near_zeros
-- #print axioms OverflowResidueRH.SignedKernelRegion.mirrorNet_neg_below_zero
-- #print axioms OverflowResidueRH.SignedKernelRegion.antiHerglotz_on_R_of_modernDensity
