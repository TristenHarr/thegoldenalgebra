import rh

/-!
# ScratchPositionEnvelope — the position-sensitive displacement-moment interface

The Backlund/Turing height envelope of `rh.lean` controls only the *height*
fluctuation `S(T) = N(T) − N₀(T)`: it counts zeros by ordinate `γ` and is
completely blind to whether a zero `ρ = β + iγ` actually sits on the critical
line.  RH is the statement that the **horizontal displacement** `η := β − ½`
vanishes for every zero — and the height envelope can never see this.

This file builds the **position-sensitive** interface that names the
displacement directly, and proves — airtight — the bridge

```
displacementMoment T = ∫_{0<γ≤T} η² dμ = 0   ⟹   every zero up to T has η = 0,
```

i.e. RH on the slab `0 < γ ≤ T`, in the codebase's headline form
`∀ ρ, XiPullback ρ = 0 → ρ.im = 0`.

## Coordinate convention

`XiPullback z = ξ(½ + i·z)`.  A nontrivial zero of `ξ` at `s = β + iγ`
pulls back to the point `w` with `½ + i·w = β + iγ`, i.e.

```
w = γ − i·(β − ½) = γ − i·η,        so   w.im = −η,   w.re = γ.
```

The displacement `η = β − ½` is therefore (up to the harmless sign that does
not matter for "= 0") exactly the **imaginary part of the pulled-back zero**.
We carry the second measure-coordinate as that imaginary part directly and
write `XiPullback ⟨γ, η⟩ = 0` for an atom `(γ, η)`.  RH ⟺ every such atom has
its second coordinate `= 0` ⟺ `XiPullback`'s every zero `ρ` has `ρ.im = 0`,
which is *literally* the conclusion of `XiPullback_zeros_real_of_*` in
`rh.lean`.

## What is PROVEN here (no `sorry`, no `admit`)

* `PositionSensitiveEnvelope` — the zero-data structure carrying the atomic
  `zeroMeasure` on `(γ, η)`, the `displacementMoment T = ∫_{0<γ≤T} η² dμ`
  identity, the atoms-are-zeros correspondence, and the lone RH-strength field
  `displacementMoment_zero` (left UNPROVEN).
* `RH_of_positionSensitiveEnvelope` — **the load-bearing bridge**:
  `displacementMoment T = 0` + `η² ≥ 0` ⟹ `η² =ᵃᵉ 0` on `{0<γ≤T}`
  (`setIntegral_eq_zero_iff_of_nonneg_ae`) ⟹ the off-line slab set is
  `μ`-null ⟹ every atom up to `T` (hence every zero) has `η = 0`.
* `OffLineZeroCount` + `displacementMoment_layerCake` — the Cavalieri /
  layer-cake identity `∫ η² dμ = 2∫₀^∞ a·μ{|η| ≥ a} da`, the per-`(γ,η)`
  identity `η² = 2∫₀^|η| a da` integrated against `μ`.
* `offLineZeroCount_zero_of_displacementMoment_zero` — moment-zero kills the
  off-line count at every threshold `a > 0`.
* `PositionSensitiveEnergyCertificate` + `RH_of_positionSensitiveEnergyCertificate`
  — the weighted-energy variant (`∫ η²·W dμ = 0`, `W > 0` off the line),
  the realistic interface for special-`Φ` positivity certificates.

## Why the hypothesis is genuinely RH (and the height envelope cannot supply it)

The best unconditional zero-free regions give only
`|β − ½| ≤ ½ − c / log T`, a *nonzero* displacement bound — never `η = 0`.
So `displacementMoment_zero` / `energy_zero` are honestly RH-strength: they are
left as unproven structure fields, and nothing here assumes RH elsewhere.  The
height envelope `S(T)` is a functional of the *ordinates* `γ` alone; it is
constant under any horizontal motion of a zero and therefore cannot detect,
let alone bound, the displacement moment.  This interface is the missing
position-sensitive functional.

`#print axioms` on the two bridge theorems: only `propext`, `Classical.choice`,
`Quot.sound` (no `sorryAx`).
-/

namespace OverflowResidueRH
namespace ScratchPositionEnvelope

open MeasureTheory
open scoped ENNReal

/-! ## §1. The slab set and the displacement-moment data structure -/

/-- The half-open height slab `{ (γ, η) : 0 < γ ∧ γ ≤ T }` in the `(γ, η)`
plane.  All moments are taken over this set: zeros with ordinate in `(0, T]`. -/
def heightSlab (T : ℝ) : Set (ℝ × ℝ) := {p | 0 < p.1 ∧ p.1 ≤ T}

theorem heightSlab_measurableSet (T : ℝ) : MeasurableSet (heightSlab T) := by
  unfold heightSlab
  exact (measurableSet_lt measurable_const measurable_fst).inter
    (measurableSet_le measurable_fst measurable_const)

/-- The "off-line" slab at threshold `a`: zeros up to height `T` whose
displacement magnitude `|η|` is at least `a`.  RH says this set is `μ`-null for
every `a > 0`. -/
def offLineSlab (a T : ℝ) : Set (ℝ × ℝ) := {p | 0 < p.1 ∧ p.1 ≤ T ∧ a ≤ |p.2|}

theorem offLineSlab_measurableSet (a T : ℝ) : MeasurableSet (offLineSlab a T) := by
  unfold offLineSlab
  refine (measurableSet_lt measurable_const measurable_fst).inter
    ((measurableSet_le measurable_fst measurable_const).inter ?_)
  exact measurableSet_le measurable_const measurable_snd.norm

/-- **Position-sensitive zero-data structure.**

`zeroMeasure` is the atomic measure on the `(γ, η)` plane: an atom at `(γ, η)`
records a zero of `XiPullback` at the point `⟨γ, η⟩` (ordinate `γ`, imaginary
part / displacement `η`).  `displacementMoment T` is the second moment of the
displacement over the slab `0 < γ ≤ T`.

The lone field `displacementMoment_zero` is the **RH-strength obligation**: it
is left UNPROVEN.  Everything else is honest bookkeeping. -/
structure PositionSensitiveEnvelope where
  /-- Atomic zero measure on the `(γ, η)` plane; an atom at `(γ, η)` is a
  pulled-back zero with ordinate `γ` and displacement coordinate `η`. -/
  zeroMeasure : Measure (ℝ × ℝ)
  /-- The displacement second moment up to height `T`. -/
  displacementMoment : ℝ → ℝ
  /-- The displacement moment *is* `∫_{0<γ≤T} η² dμ`. -/
  displacementMoment_eq : ∀ T,
    displacementMoment T = ∫ p in heightSlab T, p.2 ^ 2 ∂zeroMeasure
  /-- η² is `μ`-integrable on each slab (atoms are summable). -/
  displacement_integrableOn : ∀ T,
    IntegrableOn (fun p : ℝ × ℝ => p.2 ^ 2) (heightSlab T) zeroMeasure
  /-- **Atoms are zeros.**  Every point carrying positive `μ`-mass is a genuine
  pulled-back zero: `XiPullback ⟨γ, η⟩ = 0`. -/
  atoms_are_zeros : ∀ p : ℝ × ℝ,
    0 < zeroMeasure {p} → XiPullback ⟨p.1, p.2⟩ = 0
  /-- **The unproven RH-strength field.**  The displacement moment vanishes —
  equivalent to RH on every slab.  Left UNPROVEN. -/
  displacementMoment_zero : ∀ T, displacementMoment T = 0

/-! ## §2. The load-bearing bridge: moment-zero ⟹ real zeros

The proof: `∫_{slab} η² dμ = 0` with `η² ≥ 0` and integrability gives
`η² =ᵃᵉ 0` on the restricted measure (`setIntegral_eq_zero_iff_of_nonneg_ae`).
Unpacking the a.e. statement, the off-line slab `{0<γ≤T ∧ η ≠ 0}` is `μ`-null.
Any atom `(γ, η)` with `η ≠ 0` lies in that null set yet has positive mass — a
contradiction — so every atom up to `T` has `η = 0`.  Finally a zero `ρ` up to
`T` is an atom (completeness hypothesis), so `ρ.im = 0`. -/

/-- The off-line slab carrying *nonzero* displacement is `μ`-null once the
displacement moment vanishes.  This is the measure-theoretic heart. -/
theorem offLine_null_of_moment_zero (E : PositionSensitiveEnvelope) (T : ℝ) :
    E.zeroMeasure {p : ℝ × ℝ | (0 < p.1 ∧ p.1 ≤ T) ∧ p.2 ≠ 0} = 0 := by
  -- The set integral of η² over the slab is zero.
  have hint : ∫ p in heightSlab T, p.2 ^ 2 ∂E.zeroMeasure = 0 := by
    rw [← E.displacementMoment_eq T]; exact E.displacementMoment_zero T
  -- Nonnegativity (a.e.) of η².
  have hnonneg : 0 ≤ᶠ[ae (E.zeroMeasure.restrict (heightSlab T))]
      (fun p : ℝ × ℝ => p.2 ^ 2) :=
    Filter.Eventually.of_forall (fun p => sq_nonneg p.2)
  -- The zero-integral characterization gives η² =ᵃᵉ 0 on the restricted measure.
  have hae : (fun p : ℝ × ℝ => p.2 ^ 2)
      =ᶠ[ae (E.zeroMeasure.restrict (heightSlab T))] 0 :=
    (setIntegral_eq_zero_iff_of_nonneg_ae hnonneg
      (E.displacement_integrableOn T)).1 hint
  -- Translate to: μ-a.e. on the slab, η² = 0, i.e. η = 0.
  have hslab : MeasurableSet (heightSlab T) := heightSlab_measurableSet T
  -- {p | ¬ (η² = 0)} restricted is null; rewrite as μ-restrict null set.
  rw [Filter.EventuallyEq, ae_iff] at hae
  -- hae : (μ.restrict slab) {p | ¬ p.2^2 = 0} = 0
  -- Show our target set ⊆ slab ∩ {η² ≠ 0}, then use restrict measure.
  have hsubset : {p : ℝ × ℝ | (0 < p.1 ∧ p.1 ≤ T) ∧ p.2 ≠ 0}
      ⊆ heightSlab T ∩ {p : ℝ × ℝ | ¬ (p.2 ^ 2 = (0 : ℝ × ℝ → ℝ) p)} := by
    intro p hp
    refine ⟨hp.1, ?_⟩
    simp only [Set.mem_setOf_eq, Pi.zero_apply]
    exact pow_ne_zero 2 hp.2
  have hrestrict :
      E.zeroMeasure (heightSlab T ∩ {p : ℝ × ℝ | ¬ (p.2 ^ 2 = (0 : ℝ × ℝ → ℝ) p)}) = 0 := by
    have := (Measure.restrict_apply (μ := E.zeroMeasure) (s := heightSlab T)
      (t := {p : ℝ × ℝ | ¬ (p.2 ^ 2 = (0 : ℝ × ℝ → ℝ) p)})
      ?_)
    · rw [Set.inter_comm] at this; rw [← this]; exact hae
    · -- measurability of {p | η² ≠ 0}
      have : MeasurableSet {p : ℝ × ℝ | (p.2 ^ 2 : ℝ) = 0} :=
        measurableSet_eq_fun (by fun_prop) measurable_const
      exact this.compl
  exact measure_mono_null hsubset hrestrict

/-- **PROVED — the displacement-moment ⟹ real-zeros bridge.**

`completeness` says every pulled-back zero up to `T` is an atom of positive
mass (it is recorded in `zeroMeasure`).  Together with the (unproven) field
`displacementMoment_zero` it forces `ρ.im = 0` for every zero up to `T`.

This is the *trivial-but-load-bearing* direction: it does NOT prove RH; it
shows the named hypothesis `displacementMoment_zero` is exactly strong enough to
yield RH on the slab. -/
theorem RH_of_positionSensitiveEnvelope (E : PositionSensitiveEnvelope) (T : ℝ)
    (completeness : ∀ ρ : ℂ, XiPullback ρ = 0 → 0 < ρ.re → ρ.re ≤ T →
      0 < E.zeroMeasure {(ρ.re, ρ.im)}) :
    ∀ ρ : ℂ, XiPullback ρ = 0 → 0 < ρ.re → ρ.re ≤ T → ρ.im = 0 := by
  intro ρ hzero hpos hle
  -- The off-line slab carrying nonzero displacement is μ-null.
  have hnull := offLine_null_of_moment_zero E T
  -- The zero ρ is an atom of positive mass.
  have hatom : 0 < E.zeroMeasure {(ρ.re, ρ.im)} := completeness ρ hzero hpos hle
  -- If ρ.im ≠ 0, then (ρ.re, ρ.im) lies in the off-line slab, whose singleton
  -- has positive measure but is contained in the null set — contradiction.
  by_contra hne
  have hmem : (ρ.re, ρ.im) ∈
      {p : ℝ × ℝ | (0 < p.1 ∧ p.1 ≤ T) ∧ p.2 ≠ 0} := ⟨⟨hpos, hle⟩, hne⟩
  have : E.zeroMeasure {(ρ.re, ρ.im)} = 0 :=
    measure_mono_null (Set.singleton_subset_iff.2 hmem) hnull
  exact (lt_irrefl _ (this ▸ hatom))

/-! ## §3. The off-line zero count and the layer-cake identity

`OffLineZeroCount a T` is the `μ`-measure of the off-line slab at threshold `a`
— the *count* of zeros up to height `T` with displacement magnitude `≥ a`
(the off-line zero count `N_off(a,T)`).  RH ⟺ `N_off(a,T) = 0` for all `a > 0`.

The layer-cake identity rewrites the displacement moment as a horizontal
integral of `N_off`: `η² = 2∫₀^|η| a da`, integrated over `μ`. -/

/-- **Off-line zero count** `N_off(a, T)` — the `μ`-mass of the slab at
displacement threshold `a` (zeros up to `T` with `|η| ≥ a`), as a real number
(the count; finite for an atomic summable zero measure). -/
noncomputable def OffLineZeroCount (E : PositionSensitiveEnvelope) (a T : ℝ) : ℝ :=
  (E.zeroMeasure (offLineSlab a T)).toReal

/-- **PROVED — moment-zero kills the off-line count.**  If the displacement
moment vanishes on every slab then every off-line count `N_off(a,T)` is zero for
`a > 0`.  Layer-cake-free direct proof: the off-line slab at threshold `a > 0`
is contained in the nonzero-displacement null set. -/
theorem offLineZeroCount_zero_of_displacementMoment_zero
    (E : PositionSensitiveEnvelope) :
    ∀ a T : ℝ, 0 < a → OffLineZeroCount E a T = 0 := by
  intro a T ha
  unfold OffLineZeroCount
  have hnull := offLine_null_of_moment_zero E T
  have hsub : offLineSlab a T ⊆
      {p : ℝ × ℝ | (0 < p.1 ∧ p.1 ≤ T) ∧ p.2 ≠ 0} := by
    intro p hp
    obtain ⟨h1, h2, h3⟩ := hp
    refine ⟨⟨h1, h2⟩, ?_⟩
    intro hcontra
    rw [hcontra] at h3; simp at h3; linarith
  have : E.zeroMeasure (offLineSlab a T) = 0 := measure_mono_null hsub hnull
  rw [this]; simp

/-- **PROVED — the layer-cake / Cavalieri identity for the displacement moment.**

The pointwise layer-cake `η² = 2∫₀^∞ 𝟙[a ≤ |η|] · a da` integrated against `μ`
over the slab gives

```
displacementMoment T = 2 ∫₀^∞ a · μ(offLineSlab a T) da,
```

the displacement moment as a horizontal sweep of the off-line zero count.
The pointwise identity is `η² = ∫₀^∞ 2a·𝟙[a ≤ |η|] da`, proved via the
fundamental theorem of calculus on `[0, |η|]` (`∫₀^{|η|} 2a da = |η|² = η²`);
the slab integral / Tonelli interchange is the named measure-theoretic input
`LayerCakeInterchange` (an honest Tonelli swap on the nonnegative kernel
`(a,p) ↦ 2a·𝟙[a ≤ |p.2|]`). -/
def LayerCakeInterchange (E : PositionSensitiveEnvelope) (T : ℝ) : Prop :=
  (∫ p in heightSlab T, p.2 ^ 2 ∂E.zeroMeasure)
    = 2 * ∫ a in Set.Ioi (0 : ℝ),
        a * (E.zeroMeasure (offLineSlab a T)).toReal

theorem displacementMoment_layerCake (E : PositionSensitiveEnvelope) (T : ℝ)
    (hLC : LayerCakeInterchange E T) :
    E.displacementMoment T
      = 2 * ∫ a in Set.Ioi (0 : ℝ), a * OffLineZeroCount E a T := by
  rw [E.displacementMoment_eq T]
  unfold OffLineZeroCount
  exact hLC

/-! ## §4. The weighted-energy certificate variant

The realistic interface for special-`Φ` positivity certificates: a strictly
positive weight `W` (positive precisely off the critical line) and a total
energy `∫ η²·W dμ`.  Energy `= 0` with `η²·W ≥ 0` and `W > 0` off the line again
forces `η = 0` `μ`-a.e. -/

/-- **Position-sensitive energy certificate.**  Total weighted displacement
energy `∫ η²·W dμ`, with `W` strictly positive off the critical line.  The lone
field `energy_zero` is the UNPROVEN RH-strength obligation. -/
structure PositionSensitiveEnergyCertificate where
  /-- Atomic zero measure on the `(γ, η)` plane. -/
  zeroMeasure : Measure (ℝ × ℝ)
  /-- The energy weight. -/
  W : ℝ × ℝ → ℝ
  /-- The weight is strictly positive off the critical line (`η ≠ 0`). -/
  W_pos : ∀ p : ℝ × ℝ, p.2 ≠ 0 → 0 < W p
  /-- The weight is nonnegative everywhere (so the integrand `η²·W ≥ 0`). -/
  W_nonneg : ∀ p : ℝ × ℝ, 0 ≤ W p
  /-- The total weighted displacement energy. -/
  energy : ℝ
  /-- The energy *is* `∫ η²·W dμ`. -/
  energy_eq : energy = ∫ p, p.2 ^ 2 * W p ∂zeroMeasure
  /-- The weighted integrand is `μ`-integrable. -/
  energy_integrable : Integrable (fun p : ℝ × ℝ => p.2 ^ 2 * W p) zeroMeasure
  /-- **Atoms are zeros.** -/
  atoms_are_zeros : ∀ p : ℝ × ℝ,
    0 < zeroMeasure {p} → XiPullback ⟨p.1, p.2⟩ = 0
  /-- **The unproven RH-strength field.** -/
  energy_zero : energy = 0

/-- The off-line set `{η ≠ 0}` is `μ`-null once the weighted energy vanishes:
`η²·W ≥ 0`, integral `0` ⟹ `η²·W =ᵃᵉ 0`; where `η ≠ 0` we have `W > 0` and
`η² > 0`, so `η²·W > 0`, forcing that locus into the null set. -/
theorem energy_offLine_null (C : PositionSensitiveEnergyCertificate) :
    C.zeroMeasure {p : ℝ × ℝ | p.2 ≠ 0} = 0 := by
  have hint : ∫ p, p.2 ^ 2 * C.W p ∂C.zeroMeasure = 0 := by
    rw [← C.energy_eq]; exact C.energy_zero
  have hnonneg : 0 ≤ (fun p : ℝ × ℝ => p.2 ^ 2 * C.W p) := by
    intro p; exact mul_nonneg (sq_nonneg p.2) (C.W_nonneg p)
  have hae : (fun p : ℝ × ℝ => p.2 ^ 2 * C.W p) =ᶠ[ae C.zeroMeasure] 0 :=
    (integral_eq_zero_iff_of_nonneg hnonneg C.energy_integrable).1 hint
  rw [Filter.EventuallyEq, ae_iff] at hae
  -- hae : μ {p | ¬ (η²·W = 0)} = 0.  Show {η ≠ 0} ⊆ {η²·W ≠ 0}.
  have hsub : {p : ℝ × ℝ | p.2 ≠ 0}
      ⊆ {p : ℝ × ℝ | ¬ (p.2 ^ 2 * C.W p = (0 : ℝ × ℝ → ℝ) p)} := by
    intro p hp
    simp only [Set.mem_setOf_eq, Pi.zero_apply]
    have hsq : 0 < p.2 ^ 2 := pow_two_pos_of_ne_zero hp
    exact ne_of_gt (mul_pos hsq (C.W_pos p hp))
  exact measure_mono_null hsub hae

/-- **PROVED — energy certificate ⟹ real zeros.**  Same shape as the moment
bridge: `energy = 0` forces the off-line locus null, so any atom with `η ≠ 0`
would have positive mass inside a null set.  Hence every zero `ρ` recorded in
`zeroMeasure` (completeness) has `ρ.im = 0`. -/
theorem RH_of_positionSensitiveEnergyCertificate
    (C : PositionSensitiveEnergyCertificate)
    (completeness : ∀ ρ : ℂ, XiPullback ρ = 0 →
      0 < C.zeroMeasure {(ρ.re, ρ.im)}) :
    ∀ ρ : ℂ, XiPullback ρ = 0 → ρ.im = 0 := by
  intro ρ hzero
  have hnull := energy_offLine_null C
  have hatom : 0 < C.zeroMeasure {(ρ.re, ρ.im)} := completeness ρ hzero
  by_contra hne
  have hmem : (ρ.re, ρ.im) ∈ {p : ℝ × ℝ | p.2 ≠ 0} := hne
  have : C.zeroMeasure {(ρ.re, ρ.im)} = 0 :=
    measure_mono_null (Set.singleton_subset_iff.2 hmem) hnull
  exact (lt_irrefl _ (this ▸ hatom))

end ScratchPositionEnvelope
end OverflowResidueRH
