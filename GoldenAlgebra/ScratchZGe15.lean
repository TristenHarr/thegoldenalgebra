import rh

/-!
# Investigation: is `h_Z_ge_15` dischargeable or external?

`h_Z_ge_15 : ∀ i:ℕ, 15 ≤ Dzero.toFluctuationMeasureData.Z i`

This scratch file records the *honest* verdict on whether the hypothesis
`h_Z_ge_15` that appears throughout the Path B publication theorems
(`XiPullbackAntiHerglotzTarget_of_..._Z_ge_15_*`,
`XiPullbackAntiHerglotzTarget_of_entireHadamard_and_classicalStieltjes`,
`...classicalStieltjes`, etc.) can be closed inside Lean.

## Structures (from `rh.lean`)

```
structure FluctuationMeasureData where            -- rh:48918
  Z    : ℕ → ℝ      -- zero ordinates  (FREE field)
  mult : ℕ → ℕ      -- multiplicities  (FREE field)
  n    : ℕ          -- window size     (FREE field)
  N₀   : ℝ → ℝ
  S    : ℝ → ℝ
  S_eq : ∀ u, S u = concreteFluctuation Z mult n N₀ u

structure OrderedFluctuationMeasureData extends    -- rh:55517
    FluctuationMeasureData where
  mono_Z : Monotone Z                              -- the ONLY extra law
```

So at the *atom level*, `Z : ℕ → ℝ` is a completely free field; the only
constraint `OrderedFluctuationMeasureData` adds is `Monotone Z`. There is
**no global/canonical `Dzero` defined anywhere in `rh.lean`** — every
occurrence of `Dzero` is a bound parameter of a theorem (verified by
grep: 0 `def`/`where` instantiations of `OrderedFluctuationMeasureData`).

## Constraint analysis

In every Path B theorem `Dzero` is universally quantified together with
a bundle of *other* hypotheses that pin its meaning to the real ξ-zeros:

* `Hst : ClassicalStieltjesExplicitFormulaInputs Dzero 10 (pullbackZeroContribution …) …`
  whose `mid`/`high` fields (`StieltjesMidTailEqualityAFZ`, rh:75990) read
  ```
  ZC z = cloudModel zeros100ceil z
         + zeroDensitySmoothTailModel (2π) … z
         + L,   where  L = XiFluctuationTailValue Dzero T0 … z L
  ```
  i.e. the genuine ξ zero-contribution `ZC` equals the *finite cloud over
  `zeros100ceil`* plus the *smooth tail* plus the **tail of THIS Dzero's
  fluctuation primitive**.  This forces `Dzero`'s atoms to be the real
  zero ordinates (low ones already hard-coded as `zeros100ceil`).

* `hTuring`/`hHighLog` (a.k.a. `PathBTuringEnvelopeInputs Dzero`) bound
  `|finiteFluctuationPrimitive Dzero 10 u|` by `½·log u + c`.  Such an
  RvM/Backlund–Turing envelope only holds when `Dzero`'s discrete zero
  count tracks the genuine ζ-zero density.

Therefore `h_Z_ge_15` is NOT a free knob that trivializes the theorem:
it is one assertion about the *same* real-zero data that the Stieltjes
and Turing inputs constrain.  Picking a degenerate `Dzero` to satisfy
`h_Z_ge_15` would make `Hst`/`hTuring` *unsatisfiable*, not the theorem
vacuous.

## Verdict

The atom-level statement `∀ i, 15 ≤ Z i` is, in isolation, **purely
arithmetic and trivially dischargeable for any concrete `Z` whose entries
are ≥ 15** — e.g. the intended `zeros100ceil` list (every entry ∈ [15,237],
first entry 15 = ⌈14.13⌉).  The two demonstrations below build concrete
`OrderedFluctuationMeasureData` values and close `h_Z_ge_15` with `axiom`-free
proofs (`#print axioms` shows no `sorryAx`).

BUT the *mathematically meaningful* discharge — exhibiting the `Dzero`
that simultaneously satisfies `Hst` and `hTuring` (the real-ξ measure)
and then proving its `Z ≥ 15` — is **external** to what is currently in
`rh.lean`: that requires the verified-zeros input (the first ζ zero is
14.134… < 15, so a `Z ≥ 15` normalization is the choice to *start the
analysis above height 15* and handle `[0,15)` via the hard-coded finite
`zeros100ceil` cloud).  `rh.lean` contains no construction that ties a
concrete `Z ≥ 15` sequence to the `Hst`/`hTuring` obligations, so for the
*intended* `Dzero` the bound is supplied as external verified-zero data,
not derived.

Bottom line:
* `h_Z_ge_15` **as a standalone hypothesis is dischargeable** (arithmetic)
  for a concrete `Dzero` — proven below.
* For the `Dzero` that makes the surrounding theorem *non-vacuous*
  (constrained by `Hst`/`hTuring` to the real ξ-zeros), the `Z ≥ 15`
  normalization is an **external** verified-zero fact; `rh.lean` does not
  build that `Dzero`, so there is no in-file discharge that is
  simultaneously meaningful.
-/

namespace OverflowResidueRH.BacklundTuring.ScratchZGe15

open Phase1IBP

/-- A concrete `OrderedFluctuationMeasureData` with the **constant** zero
sequence `Z ≡ 15`.  Monotone trivially; every atom is exactly `15`.
This is the minimal witness that `h_Z_ge_15` is arithmetically
dischargeable for a concrete `Dzero`. -/
noncomputable def Dzero15 : OrderedFluctuationMeasureData where
  toFluctuationMeasureData := FluctuationMeasureData.ofXiSmooth (fun _ => 15) (fun _ => 1) 0
  mono_Z := by
    intro a b _hab
    simp [FluctuationMeasureData.ofXiSmooth]

/-- ✅ `h_Z_ge_15` for `Dzero15`: every atom is `15`, so `15 ≤ Z i`. -/
theorem Dzero15_Z_ge_15 :
    ∀ i : ℕ, (15 : ℝ) ≤ Dzero15.toFluctuationMeasureData.Z i := by
  intro i
  -- `Dzero15.Z i = 15` definitionally
  show (15 : ℝ) ≤ 15
  exact le_refl _

/-- The concrete `Dzero15` *can be fed* to the publication front door:
`h_Z_ge_15` is discharged with no remaining `Z`-bound obligation. -/
example :
    DzeroStartsAfter Dzero15 14 :=
  DzeroStartsAfter_of_Z_ge_15 Dzero15 Dzero15_Z_ge_15

/-!
### A faithful-shape witness drawn from `zeros100ceil`

The intended `Dzero` uses `zeros100ceil = [15, 22, …, 237]` for its low
atoms.  We can realize a monotone `Z : ℕ → ℝ` that *agrees with the
intended low cloud's lower bound* by clamping the list lookup from below
at `15`: `Z i = max 15 (zeros100ceil.getD i 15)`.  Every entry of
`zeros100ceil` is ≥ 15, so this equals the list on `[0,100)` and is
`15` beyond, and is `≥ 15` everywhere by construction.  Monotonicity of
the raw `getD` over the 100-entry sorted list is the only nontrivial
obligation; we sidestep it here by using the `max 15`-clamp form's
*lower bound* only (which is all `h_Z_ge_15` needs), pairing it with a
constant carrier to keep `Monotone` cheap. -/

/-- A second concrete witness: `Z i = 15 + (i : ℝ)` — strictly the real
zeros are *not* this, but it is monotone and ≥ 15, again showing the
atom bound is arithmetic.  (Illustrative; not the real measure.) -/
noncomputable def DzeroRamp : OrderedFluctuationMeasureData where
  toFluctuationMeasureData :=
    FluctuationMeasureData.ofXiSmooth (fun i => 15 + (i : ℝ)) (fun _ => 1) 0
  mono_Z := by
    intro a b hab
    simp only [FluctuationMeasureData.ofXiSmooth]
    have : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
    linarith

theorem DzeroRamp_Z_ge_15 :
    ∀ i : ℕ, (15 : ℝ) ≤ DzeroRamp.toFluctuationMeasureData.Z i := by
  intro i
  show (15 : ℝ) ≤ 15 + (i : ℝ)
  have : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
  linarith

#print axioms Dzero15_Z_ge_15
#print axioms DzeroRamp_Z_ge_15

end OverflowResidueRH.BacklundTuring.ScratchZGe15
