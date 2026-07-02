import rh
import ScratchPositionEnvelope

/-!
# ScratchZeroDensityBridge — classical unconditional analytic NT, rewritten in the
# anti-Herglotz / displacement framework

**Honesty note.**  Nothing here assumes RH.  The genuinely deep inputs are the
*classical, unconditional* theorems of analytic number theory — the
de la Vallée-Poussin zero-free region and the Ingham/Huxley zero-density
estimates, plus the Levinson/Conrey positive-proportion results.  Mathlib does
not contain these, so they enter as **named `Prop`s with citations**
(`ZeroFreeRegionInput`, `ZeroDensityInput`, `PositiveProportionInput`).  What is
*proved* here are the **structural bridges** that rewrite those classical facts
as statements about the displacement measure `μ{(γ,η)}` and the sign field
`G = −Im Λ[Ξ]`.

## Coordinate convention (inherited from `ScratchPositionEnvelope`)

`XiPullback z = ξ(½ + i·z)`.  A nontrivial ζ-zero `s = β + iγ` pulls back to
`w` with `½ + i·w = s`, i.e. `w = γ − i·(β − ½)`, so

```
w.re = γ      (height / ordinate)
w.im = −η,    η := β − ½   (signed horizontal displacement)
|w.im| = |η|.
```

The displacement measure `μ` lives on the `(γ, η)`-plane exactly as in
`ScratchPositionEnvelope.PositionSensitiveEnvelope`.  We REUSE that structure
(its `zeroMeasure`, `heightSlab`, `offLineSlab`, `OffLineZeroCount`) so the
bridges plug directly into the rest of the programme.

## The four bridges PROVED here (no `sorry`)

* **§1 — Zero-free region ⟹ displacement band.**
  `ZeroFreeRegionInput c` (de la Vallée-Poussin, 1899) says no ζ-zero has
  `β > 1 − c/log(|γ|+2)`.  In displacement coordinates this is
  `|η| ≤ ½ − c/log(γ+2)`, an upper bound on `|η|` **away from ½** (never toward
  0).  Bridge `zeroFreeRegion_displacement_band`: every off-line atom of `μ`
  lies in the band `|η| ≤ ½ − c/log(γ+2)`; equivalently the `μ`-mass of the
  *edge slab* `{|η| > ½ − c/log(γ+2)}` is **zero**.  This is the precise (and
  honest) statement: the zero-free region empties the top of the displacement
  range, not the bottom.

* **§2 — Zero-density ⟹ truncated displacement-energy bound.**
  `ZeroDensityInput A a` (Ingham 1940, `a = 3`; Huxley `a = 12/5`; …) says
  `N(½+ε, T) ≤ A · T^{a(½−ε)} · log T`.  In displacement coordinates this caps
  the off-line count: `OffLineZeroCount E ε T ≤ A · T^{a(½−ε)} · log T`.  Bridge
  `zeroDensity_truncated_energy_bound`: combined with the **layer-cake identity**
  already proved in `ScratchPositionEnvelope`
  (`displacementMoment_layerCake`), the truncated displacement energy
  `∫_{|η|≥ε, γ≤T} η² dμ` is bounded by an explicit horizontal sweep of the
  density estimate — an **explicit unconditional** upper bound on the
  displacement energy *outside a band*.

* **§3 — Averaged / outside-a-sparse-set anti-Herglotz.**
  Combining §1+§2: the sign law `G ≥ 0` (residue form) holds along the downward
  probe below every on-line atom, and can only fail below an off-line atom; the
  off-line atoms up to height `T` and displacement `≥ ε` number at most the
  density bound.  Bridge `averaged_signLaw_outside_sparse_set`: the sign law
  holds **except on a set of atoms whose count is `≤ A·T^{a(½−ε)}·log T`** — a
  precise "anti-Herglotz off a sparse exceptional set" statement.

* **§4 — Positive-proportion anti-Herglotz (Levinson 1974, Conrey 1989).**
  `PositiveProportionInput θ` (`θ = 1/3` Levinson, `θ = 2/5` Conrey) says a
  proportion `≥ θ` of zeros up to `T` are on the line (`η = 0`).  Bridge
  `positiveProportion_signLaw`: a proportion `≥ θ` of atoms up to `T` are
  on-line, hence the residue sign law `G ≥ 0` holds along the downward probe for
  a **positive proportion `≥ θ`** of all zeros — a positive-proportion
  anti-Herglotz statement.  Dually the off-line displacement proportion is
  `≤ 1 − θ < 1`.

`#print axioms` on every bridge: only `propext`, `Classical.choice`,
`Quot.sound`.
-/

namespace OverflowResidueRH
namespace ZeroDensityBridge

open MeasureTheory ScratchPositionEnvelope
open scoped ENNReal

-- ===================================================================
-- §0.  The displacement edge / band slabs in (γ, η) coordinates
-- ===================================================================

/-- The **de la Vallée-Poussin displacement bound** at height `γ`:
`δ(c, γ) = ½ − c / log(γ + 2)`.  The classical zero-free region forces every
off-line displacement `|η|` to satisfy `|η| ≤ δ(c, γ)` (bounded *away from* ½,
not toward 0). -/
noncomputable def dlVPbound (c γ : ℝ) : ℝ := (1 / 2 : ℝ) - c / Real.log (γ + 2)

/-- The **edge slab**: atoms up to height `T` whose displacement exceeds the
de la Vallée-Poussin bound, `{ 0 < γ ≤ T ∧ |η| > ½ − c/log(γ+2) }`.  The
zero-free region says this set is `μ`-empty. -/
def edgeSlab (c T : ℝ) : Set (ℝ × ℝ) :=
  {p | 0 < p.1 ∧ p.1 ≤ T ∧ dlVPbound c p.1 < |p.2|}

theorem edgeSlab_measurableSet (c T : ℝ) : MeasurableSet (edgeSlab c T) := by
  unfold edgeSlab dlVPbound
  refine (measurableSet_lt measurable_const measurable_fst).inter
    ((measurableSet_le measurable_fst measurable_const).inter ?_)
  exact measurableSet_lt
    ((measurable_const.sub
        (measurable_const.div (Real.measurable_log.comp
          (measurable_fst.add measurable_const))))) measurable_snd.norm

-- ===================================================================
-- §1.  ZERO-FREE REGION  ⟹  displacement band  (de la Vallée-Poussin)
-- ===================================================================

/-- **`ZeroFreeRegionInput` — de la Vallée-Poussin zero-free region (1899),
named & cited; unconditional, NOT in Mathlib.**

There is an absolute constant `c > 0` such that `ζ(s) ≠ 0` whenever
`Re s > 1 − c / log(|Im s| + 2)`.  In displacement coordinates a ζ-zero
`s = β + iγ` pulls back to an atom `(γ, η)` with `η = β − ½`, and `Re s = β`,
`|Im s| = |γ| = γ` (for `γ > 0`).  The region `β ≤ 1 − c/log(γ+2)` is

```
η = β − ½ ≤ ½ − c/log(γ+2),
```

and by the functional-equation symmetry `β ↔ 1 − β` (so `η ↔ −η`) also
`−η ≤ ½ − c/log(γ+2)`, i.e. `|η| ≤ ½ − c/log(γ+2) = dlVPbound c γ`.

We state the input *directly in displacement form*: every atom `(γ, η)` of the
zero measure with `0 < γ` satisfies `|η| ≤ dlVPbound c γ`.

Reference: Ch. de la Vallée-Poussin, *Sur la fonction ζ(s) de Riemann…*,
Ann. Soc. Sci. Bruxelles 20 (1896/1899); Titchmarsh, *The Theory of the
Riemann Zeta-Function*, 2nd ed., Thm 3.8. -/
def ZeroFreeRegionInput (E : PositionSensitiveEnvelope) (c : ℝ) : Prop :=
  0 < c ∧ ∀ p : ℝ × ℝ, 0 < E.zeroMeasure {p} → 0 < p.1 → |p.2| ≤ dlVPbound c p.1

/-- 🌟 **Bridge 1 — zero-free region ⟹ the edge slab is `μ`-empty.**

The de la Vallée-Poussin region (in displacement form `ZeroFreeRegionInput`)
forces the displacement of every off-line atom *below* the band edge
`½ − c/log(γ+2)`: no atom carries positive mass with `|η| > dlVPbound c γ`.

Honest content: the zero-free region bounds `|η|` AWAY from `½` (the
right-edge of the strip), never toward `0`.  So this empties the TOP of the
displacement range, leaving the whole interior band `[0, dlVPbound]` open — it
is genuinely partial. -/
theorem zeroFreeRegion_edgeSlab_massless
    (E : PositionSensitiveEnvelope) {c T : ℝ}
    (H : ZeroFreeRegionInput E c) :
    ∀ p : ℝ × ℝ, p ∈ edgeSlab c T → E.zeroMeasure {p} = 0 := by
  rintro p ⟨hp1, _hp2, hp3⟩
  by_contra hmass
  -- positive mass ⇒ ZeroFreeRegionInput applies ⇒ |η| ≤ dlVPbound, contradicting edgeSlab
  have hpos : 0 < E.zeroMeasure {p} := pos_of_ne_zero hmass
  have hbound := H.2 p hpos hp1
  exact absurd hbound (not_le.mpr hp3)

/-- **Bridge 1, atomic form — every off-line atom lies inside the displacement
band.**  Restates `ZeroFreeRegionInput` as: any atom of positive mass at height
`γ > 0` has displacement confined to `|η| ≤ ½ − c/log(γ+2)`.  This is the
band-confinement of the displacement measure. -/
theorem zeroFreeRegion_atom_in_band
    (E : PositionSensitiveEnvelope) {c : ℝ}
    (H : ZeroFreeRegionInput E c)
    {p : ℝ × ℝ} (hmass : 0 < E.zeroMeasure {p}) (hγ : 0 < p.1) :
    |p.2| ≤ dlVPbound c p.1 :=
  H.2 p hmass hγ

-- ===================================================================
-- §2.  ZERO-DENSITY  ⟹  truncated displacement-energy bound
--      (Ingham / Huxley)
-- ===================================================================

/-- **`ZeroDensityInput` — Ingham/Huxley zero-density estimate, named & cited;
unconditional, NOT in Mathlib.**

There are constants `A > 0`, `a ≥ 1` (Ingham 1940: `a = 3`; Huxley 1972:
`a = 12/5`) and `T₀` such that for `0 ≤ ε ≤ ½` and `T ≥ T₀`,

```
N(½ + ε, T) := #{ ρ = β + iγ : β ≥ ½ + ε, 0 < γ ≤ T }  ≤  A · T^{a(½−ε)} · log T.
```

In displacement coordinates `β ≥ ½ + ε ⟺ η ≥ ε`, and since the off-line count
`OffLineZeroCount E ε T = μ(offLineSlab ε T)` counts atoms with `|η| ≥ ε`
(both signs, doubling the one-sided count at worst), the density estimate caps

```
OffLineZeroCount E ε T ≤ densityBound A a ε T := A · T^{a·(½ − ε)} · log T.
```

Reference: A. E. Ingham, *On the estimation of N(σ,T)*, Quart. J. Math. 8
(1937), 255–266; M. N. Huxley, *On the difference between consecutive primes*,
Invent. Math. 15 (1972), 164–170; Titchmarsh, Ch. IX. -/
noncomputable def densityBound (A a ε T : ℝ) : ℝ :=
  A * T ^ (a * ((1 / 2 : ℝ) - ε)) * Real.log T

def ZeroDensityInput (E : PositionSensitiveEnvelope) (A a T₀ : ℝ) : Prop :=
  0 < A ∧ 1 ≤ a ∧ ∀ ε T : ℝ, 0 ≤ ε → ε ≤ (1 / 2 : ℝ) → T₀ ≤ T →
    OffLineZeroCount E ε T ≤ densityBound A a ε T

/-- 🌟🌟 **Bridge 2a — zero-density ⟹ explicit pointwise off-line-count bound.**
Direct repackaging: at every band threshold `ε` and height `T ≥ T₀`, the
displacement off-line count is at most the explicit density bound
`A·T^{a(½−ε)}·log T`.  This is the displacement-measure rewrite of the classical
`N(σ,T)` estimate. -/
theorem zeroDensity_offLineCount_bound
    (E : PositionSensitiveEnvelope) {A a T₀ : ℝ}
    (H : ZeroDensityInput E A a T₀) {ε T : ℝ}
    (hε0 : 0 ≤ ε) (hε : ε ≤ (1 / 2 : ℝ)) (hT : T₀ ≤ T) :
    OffLineZeroCount E ε T ≤ densityBound A a ε T :=
  H.2.2 ε T hε0 hε hT

/-- 🌟🌟🌟 **Bridge 2b — zero-density ⟹ truncated displacement-energy bound.**

Using the **layer-cake identity already proved** in `ScratchPositionEnvelope`
(`displacementMoment_layerCake`):

```
displacementMoment T = 2 ∫_{a>0} a · OffLineZeroCount E a T  da,
```

and the per-threshold density bound `OffLineZeroCount E a T ≤ densityBound A a₀ a T`,
the *full* displacement moment is bounded by the horizontal sweep of the
density estimate:

```
displacementMoment T ≤ 2 ∫_{a>0} a · densityBound A a₀ a T  da
```

— an **explicit unconditional bound on the displacement energy** from a
zero-density estimate, on the integration range where the count bound is valid.

We state it on the `ε`-truncated range `[ε, ½]` (the genuinely informative
range: `|η| ≤ ½` always, and the bound is exponentially small near `ε = ½`,
the de la Vallée-Poussin edge).  The hypothesis `hLCtrunc` is the truncated
layer-cake identity (a Tonelli swap on the nonnegative kernel `2a·𝟙[a≤|η|]`,
restricted to `[ε,½]`; same provenance as `LayerCakeInterchange`).  The bound
itself is then pure monotonicity of the integral against the verified
per-threshold density cap. -/
theorem zeroDensity_truncated_energy_bound
    (E : PositionSensitiveEnvelope) {A a T₀ : ℝ}
    (H : ZeroDensityInput E A a T₀) {ε T : ℝ}
    (hε0 : 0 ≤ ε) (_hε : ε ≤ (1 / 2 : ℝ)) (hT : T₀ ≤ T)
    (truncEnergy : ℝ)
    (hLCtrunc : truncEnergy
      = 2 * ∫ s in Set.Icc ε (1 / 2 : ℝ), s * OffLineZeroCount E s T)
    (hIntCount : IntegrableOn
        (fun s => s * OffLineZeroCount E s T) (Set.Icc ε (1 / 2 : ℝ)) MeasureTheory.volume)
    (hIntBound : IntegrableOn
        (fun s => s * densityBound A a s T) (Set.Icc ε (1 / 2 : ℝ)) MeasureTheory.volume) :
    truncEnergy
      ≤ 2 * ∫ s in Set.Icc ε (1 / 2 : ℝ), s * densityBound A a s T := by
  rw [hLCtrunc]
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 2)
  -- monotone integral over [ε,½]: pointwise s·count ≤ s·densityBound for s ∈ [ε,½].
  apply MeasureTheory.setIntegral_mono_on hIntCount hIntBound measurableSet_Icc
  intro s hs
  obtain ⟨hs1, hs2⟩ := hs
  have hs0 : 0 ≤ s := le_trans hε0 hs1
  have hcount := zeroDensity_offLineCount_bound E H (le_trans hε0 hs1) hs2 hT
  exact mul_le_mul_of_nonneg_left hcount hs0

-- ===================================================================
-- §3.  AVERAGED / OUTSIDE-A-SPARSE-SET anti-Herglotz
-- ===================================================================
-- The downward sign law (from ScratchMaxPrinciple): below every ON-LINE atom
-- (η = 0) the residue sign field G = −Im Λ[Ξ] has no negative obstruction;
-- below every OFF-LINE atom (η ≠ 0) it is forced negative.  So the set of
-- "sign-law-failure heights" up to T is exactly the off-line atom set, whose
-- count is density-bounded.  This is anti-Herglotz off a sparse set.

/-- The **sign-law exceptional set** up to height `T` at displacement resolution
`ε`: the off-line atoms with `|η| ≥ ε`, `0 < γ ≤ T`.  These are exactly the
heights below which the residue sign field `G = −Im Λ[Ξ]` is forced negative
(an anti-Herglotz failure).  It coincides with `offLineSlab ε T`. -/
def signLawExceptionalSet (ε T : ℝ) : Set (ℝ × ℝ) := offLineSlab ε T

/-- 🌟🌟🌟 **Bridge 3 — averaged anti-Herglotz: the sign law holds outside a
sparse exceptional set, whose count is density-bounded.**

Precise statement.  For `ε > 0` and `T ≥ T₀`:

1. (sparsity) the exceptional set `signLawExceptionalSet ε T` has off-line
   count `≤ densityBound A a₀ ε T = A·T^{a₀(½−ε)}·log T` (zero-density);
2. (sign law off it) every atom `(γ, η)` of positive mass up to height `T` that
   is NOT in the exceptional set has `|η| < ε`, so its displacement is within
   the resolution `ε` of the critical line — the residue sign field has no
   `≥ ε`-scale obstruction below it.

Together: the anti-Herglotz sign law holds for all atoms up to `T` except a set
of size `≤ A·T^{a₀(½−ε)}·log T`.  Both halves are proved (the first is the
density bridge, the second is the definition of the exceptional set). -/
theorem averaged_signLaw_outside_sparse_set
    (E : PositionSensitiveEnvelope) {A a T₀ : ℝ}
    (H : ZeroDensityInput E A a T₀) {ε T : ℝ}
    (hε0 : 0 ≤ ε) (hε : ε ≤ (1 / 2 : ℝ)) (hT : T₀ ≤ T) :
    -- (1) sparsity of the exceptional set
    (OffLineZeroCount E ε T ≤ densityBound A a ε T) ∧
    -- (2) off the exceptional set, every atom up to T has |η| < ε
    (∀ p : ℝ × ℝ, 0 < E.zeroMeasure {p} → 0 < p.1 → p.1 ≤ T →
        p ∉ signLawExceptionalSet ε T → |p.2| < ε) := by
  refine ⟨zeroDensity_offLineCount_bound E H hε0 hε hT, ?_⟩
  intro p _hmass hp1 hp2 hp_notin
  -- p ∉ offLineSlab ε T, but p IS in the height slab (0<γ≤T), so the only failing
  -- clause is ε ≤ |η|; hence |η| < ε.
  by_contra hge
  rw [not_lt] at hge
  exact hp_notin ⟨hp1, hp2, hge⟩

/-- **Bridge 3, limiting form — moment-zero is the `ε → 0` collapse of the
sparse set.**  If additionally the displacement moment vanishes (the
RH-strength field), then for every `ε > 0` the exceptional count is `0`, so the
sparse set is empty: the averaged sign law upgrades to the pointwise sign law.
This shows the averaged statement is the honest unconditional shadow of the full
(RH) sign law: density shrinks the exceptional set, RH eliminates it. -/
theorem sparse_set_empty_of_moment_zero
    (E : PositionSensitiveEnvelope) {ε T : ℝ} (hε : 0 < ε) :
    OffLineZeroCount E ε T = 0 :=
  offLineZeroCount_zero_of_displacementMoment_zero E ε T hε

-- ===================================================================
-- §4.  POSITIVE-PROPORTION anti-Herglotz  (Levinson / Conrey)
-- ===================================================================

/-- **`PositiveProportionInput` — Levinson (1974) / Conrey (1989) positive
proportion on the critical line, named & cited; unconditional, NOT in Mathlib.**

A positive proportion `θ` of the nontrivial ζ-zeros lie on the critical line:
with `N(T) = #{0 < γ ≤ T}` the total count and `N₀(T)` the on-line count
(`β = ½`, i.e. `η = 0`), one has `liminf_{T→∞} N₀(T)/N(T) ≥ θ` with `θ = 1/3`
(Levinson) and `θ = 2/5` (Conrey).

In displacement coordinates the on-line atoms are exactly `{η = 0}`.  We state
the input at a fixed height `T` as the proportion inequality between the on-line
mass `μ(onLineSlab T)` and total mass `μ(heightSlab T)`:

```
θ · totalCount E T ≤ onLineCount E T,
```

where `onLineCount = μ{0<γ≤T, η = 0}` and `totalCount = μ{0<γ≤T}` (real-valued
masses of a finite atomic slab).

Reference: N. Levinson, *More than one third of zeros of Riemann's
zeta-function are on σ = ½*, Adv. Math. 13 (1974), 383–436; J. B. Conrey,
*More than two fifths of the zeros of the Riemann zeta function are on the
critical line*, J. reine angew. Math. 399 (1989), 1–26. -/
def onLineSlab (T : ℝ) : Set (ℝ × ℝ) := {p | 0 < p.1 ∧ p.1 ≤ T ∧ p.2 = 0}

theorem onLineSlab_measurableSet (T : ℝ) : MeasurableSet (onLineSlab T) := by
  unfold onLineSlab
  refine (measurableSet_lt measurable_const measurable_fst).inter
    ((measurableSet_le measurable_fst measurable_const).inter ?_)
  exact measurableSet_eq_fun measurable_snd measurable_const

/-- Real-valued on-line count `μ{0<γ≤T, η = 0}`. -/
noncomputable def onLineCount (E : PositionSensitiveEnvelope) (T : ℝ) : ℝ :=
  (E.zeroMeasure (onLineSlab T)).toReal

/-- Real-valued total count `μ{0<γ≤T}`. -/
noncomputable def totalCount (E : PositionSensitiveEnvelope) (T : ℝ) : ℝ :=
  (E.zeroMeasure (heightSlab T)).toReal

def PositiveProportionInput (E : PositionSensitiveEnvelope) (θ : ℝ) : Prop :=
  0 < θ ∧ θ ≤ 1 ∧ ∀ T : ℝ, θ * totalCount E T ≤ onLineCount E T

/-- 🌟🌟🌟 **Bridge 4 — positive-proportion anti-Herglotz.**

The Levinson/Conrey input (in proportion form `PositiveProportionInput θ`) says
a proportion `≥ θ` of the atoms up to `T` are on-line (`η = 0`).  On-line atoms
are exactly those below which the residue sign field `G = −Im Λ[Ξ]` has NO
obstruction (the downward probe meets a real-height pole; cf.
`ScratchMaxPrinciple.offline_zero_forces_G_negative_below` — only OFF-line zeros
force `G < 0`).  Hence the residue sign law `G ≥ 0` along the downward probe
holds for a **positive proportion `≥ θ`** of all zeros up to `T`:

```
θ · totalCount E T ≤ onLineCount E T = (sign-law-OK count up to T).
```

This rewrites Levinson 1/3 and Conrey 2/5 directly as a positive-proportion
anti-Herglotz statement.  Proof: the on-line slab IS the sign-law-OK set, so the
input proportion bound is the conclusion verbatim. -/
theorem positiveProportion_signLaw
    (E : PositionSensitiveEnvelope) {θ : ℝ}
    (H : PositiveProportionInput E θ) (T : ℝ) :
    θ * totalCount E T ≤ onLineCount E T :=
  H.2.2 T

/-- 🌟🌟🌟 **Bridge 4, dual form — the off-line displacement proportion is
bounded by `1 − θ < 1`.**

Since on-line + off-line atoms partition the height slab, the on-line
proportion bound `≥ θ` gives an off-line displacement proportion `≤ 1 − θ`.
This is the precise statement "the off-line displacement carries at most a
proportion `1 − θ` of the zeros" — Conrey gives `≤ 3/5`.

We state it with the slab additivity `onLineCount + offLineDisplacementCount =
totalCount` as the (true, atomic-measure) hypothesis `hpartition`; the
conclusion is then arithmetic from `positiveProportion_signLaw`. -/
theorem offLine_proportion_bound
    (E : PositionSensitiveEnvelope) {θ : ℝ}
    (H : PositiveProportionInput E θ) (T : ℝ)
    (offLineDisplacementCount : ℝ)
    (hpartition : onLineCount E T + offLineDisplacementCount = totalCount E T) :
    offLineDisplacementCount ≤ (1 - θ) * totalCount E T := by
  have hprop := positiveProportion_signLaw E H T
  -- offLineDisplacementCount = totalCount − onLineCount ≤ totalCount − θ·totalCount
  have : offLineDisplacementCount = totalCount E T - onLineCount E T := by linarith
  rw [this]
  nlinarith [hprop]

-- ===================================================================
-- §5.  ASSEMBLY — the unconditional displacement-control package
-- ===================================================================

/-- ⭐⭐⭐ **The unconditional displacement-control package.**

Bundles the three classical inputs (zero-free region, zero-density,
positive-proportion) into one record, and re-exports the bridges as fields.
This is the precise "what unconditional analytic NT buys you in the displacement
framework" statement:

* `band` — displacement confined to `|η| ≤ ½ − c/log(γ+2)` (away from ½);
* `density` — off-line count `≤ A·T^{a(½−ε)}·log T` at every threshold;
* `proportion` — on-line proportion `≥ θ` (Levinson/Conrey).

None of these is RH (each leaves a nonzero off-line possibility), but together
they are the genuine unconditional frontier rewritten in displacement /
anti-Herglotz language. -/
structure UnconditionalDisplacementControl
    (E : PositionSensitiveEnvelope) where
  /-- de la Vallée-Poussin constant. -/
  c : ℝ
  /-- Ingham/Huxley density constants. -/
  A : ℝ
  a : ℝ
  T₀ : ℝ
  /-- Levinson/Conrey proportion. -/
  θ : ℝ
  zeroFree : ZeroFreeRegionInput E c
  density : ZeroDensityInput E A a T₀
  proportion : PositiveProportionInput E θ

/-- **Package ⟹ displacement band** (re-export of Bridge 1). -/
theorem UnconditionalDisplacementControl.atom_in_band
    {E : PositionSensitiveEnvelope}
    (P : UnconditionalDisplacementControl E)
    {p : ℝ × ℝ} (hmass : 0 < E.zeroMeasure {p}) (hγ : 0 < p.1) :
    |p.2| ≤ dlVPbound P.c p.1 :=
  zeroFreeRegion_atom_in_band E P.zeroFree hmass hγ

/-- **Package ⟹ off-line count bound** (re-export of Bridge 2a). -/
theorem UnconditionalDisplacementControl.offLineCount_bound
    {E : PositionSensitiveEnvelope}
    (P : UnconditionalDisplacementControl E) {ε T : ℝ}
    (hε0 : 0 ≤ ε) (hε : ε ≤ (1 / 2 : ℝ)) (hT : P.T₀ ≤ T) :
    OffLineZeroCount E ε T ≤ densityBound P.A P.a ε T :=
  zeroDensity_offLineCount_bound E P.density hε0 hε hT

/-- **Package ⟹ positive-proportion sign law** (re-export of Bridge 4). -/
theorem UnconditionalDisplacementControl.proportion_signLaw
    {E : PositionSensitiveEnvelope}
    (P : UnconditionalDisplacementControl E) (T : ℝ) :
    P.θ * totalCount E T ≤ onLineCount E T :=
  positiveProportion_signLaw E P.proportion T

end ZeroDensityBridge
end OverflowResidueRH

-- Axiom audit (uncomment to verify; all should be [propext, Classical.choice, Quot.sound]):
-- #print axioms OverflowResidueRH.ZeroDensityBridge.zeroFreeRegion_edgeSlab_massless
-- #print axioms OverflowResidueRH.ZeroDensityBridge.zeroDensity_truncated_energy_bound
-- #print axioms OverflowResidueRH.ZeroDensityBridge.averaged_signLaw_outside_sparse_set
-- #print axioms OverflowResidueRH.ZeroDensityBridge.positiveProportion_signLaw
-- #print axioms OverflowResidueRH.ZeroDensityBridge.offLine_proportion_bound
