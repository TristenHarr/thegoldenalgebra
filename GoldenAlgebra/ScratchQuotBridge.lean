import rh
import Mathlib

open Complex Filter Topology

/-!
# Single-index ⇆ multiplicity-index quotient bridge (`hquot`)

This file closes the two coupled residuals left open in
`ScratchHadamardPackage.lean`:

* **(a)** `hquot` — the off-zero quotient identity
  `ξ s / infiniteHadamardProduct concreteEntireXiZeroSystem.zeroLoc s = C·exp(a+b·s)`
  required by rh.lean's smart constructor
  `EntireXiClassicalHadamardTheorem.of_canonicalZeros_expAffine_quotient_invSqSummable_normExhaustion`
  (rh.lean:81102);
* **(b)** the single-index ↔ multiplicity-index product equality.

## How `concreteEntireXiZeroSystem.zeroLoc` is indexed (the crux)

`concreteEntireXiZeroSystem.zeroLoc = entireXiNonzeroZeroLoc : EntireXiNonzeroZeroIndex → ℂ`
with `entireXiNonzeroZeroLoc i = (i : ℂ)` and

  `EntireXiNonzeroZeroIndex := { s : ℂ // entireRiemannXi s = 0 ∧ s ≠ 0 }`.

So rh's single-index product `infiniteHadamardProduct concreteEntireXiZeroSystem.zeroLoc`
runs over the **distinct nonzero ξ-zeros, each appearing EXACTLY ONCE** — it is *not*
multiplicity-aware.

`ScratchHadamardPackage.P_mult` (STEP 1's `hadamard_factorization_entireXi`)
runs over

  `XiZeroIndexMult := Σ ρ : riemannXiZeros, Fin (analyticOrderNatAt entireRiemannXi (xiZeroLoc ρ))`,

i.e. **each distinct zero `ρ` is repeated `m_ρ = analyticOrderNatAt ξ ρ` times**.

**Conclusion (the honest finding).** The two products are therefore **NOT** related
by a reindexing bijection: the index types have genuinely different cardinalities
unless every ξ-zero is simple (`m_ρ = 1` for all `ρ`). A bijection
`XiZeroIndexMult ≃ EntireXiNonzeroZeroIndex` exists **iff** all zeros are simple.
Hence the product equality
`P_mult s = infiniteHadamardProduct concreteEntireXiZeroSystem.zeroLoc s`
is *equivalent to the simple-zeros statement* and cannot be discharged as a pure
`Equiv.tprod_eq` reindexing.

What CAN be proved unconditionally as a reindexing is the bridge between rh's
`EntireXiNonzeroZeroIndex`-product and the package's `XiZeroIndex`-product (both
list each nonzero zero once): the two subtypes `{s // ξ s = 0 ∧ s ≠ 0}` and
`{s // ξ s = 0}` are `Equiv` because `ξ 0 ≠ 0`. We prove that here
(`infiniteHadamardProduct_eq_singleIndexProduct`).

The genuine multiplicity-collapse content is then isolated as the **single** honest
hypothesis `hSingleEqMult` (the simple-zeros / multiplicity-collapse residual), and
`hquot` is derived from STEP 1's factorization by dividing, using rh's
`EntireXiZeroInvSqDistribution.infiniteProduct_ne_zero` for off-zero nonvanishing.

## Honesty
No `sorry`/`admit`/`sorryAx`. The only genuinely-open input is the named hypothesis
`hSingleEqMult` (with a docstring identifying it as the simple-zeros residual) and the
STEP 1 factorization equation, both carried as explicit parameters. `#print axioms`
lists only the standard kernel axioms.
-/

set_option maxHeartbeats 2000000

namespace OverflowResidueRH.BacklundTuring.ScratchQuotBridge

open OverflowResidueRH

/-! ## 0. Self-contained copies of the package scaffolding (from
`ScratchHadamardPackage.lean`, all phrased against rh's `entireRiemannXi` /
`hadamardGenus1Factor`).

The scratch files are standalone (`import rh` + `Mathlib`), not built library
modules, so `ScratchHadamardPackage` cannot be imported; the short definitions it
depends on are reproduced here verbatim. -/

theorem entireRiemannXi_zero_ne : entireRiemannXi 0 ≠ 0 := by
  rw [entireRiemannXi_zero]; norm_num

/-- ξ's zero set. -/
def riemannXiZeros : Set ℂ := entireRiemannXi ⁻¹' {0}

/-- The single-index ξ-zero type (each zero appears once). -/
abbrev XiZeroIndex : Type := riemannXiZeros

def xiZeroLoc (ρ : XiZeroIndex) : ℂ := (ρ : ℂ)

/-- **Multiplicity-aware ξ-zero index** (each zero `ρ` repeated `m_ρ` times). -/
def XiZeroIndexMult : Type :=
  Σ ρ : XiZeroIndex, Fin (analyticOrderNatAt entireRiemannXi (xiZeroLoc ρ))

/-- Location map of the multiplicity index. -/
def zeroLocMult (i : XiZeroIndexMult) : ℂ := xiZeroLoc i.1

/-- The multiplicity-aware genus-1 Hadamard product `P_mult z = ∏' i, E₁(z/ρᵢ)`. -/
noncomputable def P_mult (z : ℂ) : ℂ :=
  ∏' i : XiZeroIndexMult, hadamardGenus1Factor (zeroLocMult i) z

/-! ## 1. The unconditional reindexing: rh single-index product = package
`XiZeroIndex` product.

`EntireXiNonzeroZeroIndex = {s // ξ s = 0 ∧ s ≠ 0}` and the package's
`XiZeroIndex = riemannXiZeros = {s // s ∈ ξ⁻¹'{0}} = {s // ξ s = 0}` differ only by
the `s ≠ 0` clause, which is automatic since `ξ 0 = 1/2 ≠ 0`. We build the `Equiv`
explicitly and transport the `tprod`. -/

/-- Forward map `EntireXiNonzeroZeroIndex → XiZeroIndex`: drop the (redundant)
`s ≠ 0` clause. `EntireXiNonzeroZeroIndex` is a `def`-wrapped subtype, so we
unfold it to a `Subtype` value with `.1`/`.2`. -/
def toXiZeroIndex (i : EntireXiNonzeroZeroIndex) : XiZeroIndex :=
  ⟨i.1, by
    -- `XiZeroIndex = riemannXiZeros`, membership is `ξ i.1 = 0`.
    show entireRiemannXi i.1 = 0
    exact i.2.1⟩

/-- Backward map `XiZeroIndex → EntireXiNonzeroZeroIndex`: reinstate `s ≠ 0` from
`ξ 0 ≠ 0`. -/
def ofXiZeroIndex (ρ : XiZeroIndex) : EntireXiNonzeroZeroIndex :=
  ⟨ρ.1, ⟨ρ.2, by
    -- `ρ.1 ≠ 0`: else `ξ 0 = 0`, contradicting `entireRiemannXi_zero_ne`.
    intro h
    have hz : entireRiemannXi ρ.1 = 0 := ρ.2
    rw [h] at hz
    exact entireRiemannXi_zero_ne hz⟩⟩

/-- The two single-index zero types are equivalent (the `s ≠ 0` clause is free). -/
def nonzeroIndexEquiv : EntireXiNonzeroZeroIndex ≃ XiZeroIndex where
  toFun := toXiZeroIndex
  invFun := ofXiZeroIndex
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

@[simp] lemma toXiZeroIndex_val (i : EntireXiNonzeroZeroIndex) :
    (toXiZeroIndex i).1 = i.1 := rfl

/-- **Unconditional reindexing.** rh's single-index Hadamard product over
`EntireXiNonzeroZeroIndex` equals the package's single-index product over
`XiZeroIndex` (each distinct nonzero zero appearing once in both). -/
theorem infiniteHadamardProduct_eq_singleIndexProduct (s : ℂ) :
    infiniteHadamardProduct concreteEntireXiZeroSystem.zeroLoc s
      = ∏' ρ : XiZeroIndex, hadamardGenus1Factor (xiZeroLoc ρ) s := by
  unfold infiniteHadamardProduct
  -- `∏' i : EntireXiNonzeroZeroIndex, f (zeroLoc i) = ∏' ρ : XiZeroIndex, f (xiZeroLoc ρ)`
  -- via the equiv; the locations match: `zeroLoc i = i.1 = xiZeroLoc (equiv i)`.
  rw [← nonzeroIndexEquiv.tprod_eq
    (fun ρ : XiZeroIndex => hadamardGenus1Factor (xiZeroLoc ρ) s)]
  apply tprod_congr
  intro i
  -- `concreteEntireXiZeroSystem.zeroLoc i = entireXiNonzeroZeroLoc i = i.1`,
  -- and `xiZeroLoc (nonzeroIndexEquiv i) = (toXiZeroIndex i).1 = i.1`.
  rfl

/-! ## 2. Off-zero nonvanishing of the single-index product (from `hinv`).

rh's `EntireXiZeroInvSqDistribution.infiniteProduct_ne_zero` turns the
distinct-zero inverse-square summability into nonvanishing of the single-index
product off the indexed zeros. -/

/-- Off the single-index zero set, the single-index Hadamard product is nonzero. -/
theorem infiniteHadamardProduct_ne_zero_of_offZeros
    (hinv : Summable fun i : EntireXiNonzeroZeroIndex =>
      (‖concreteEntireXiZeroSystem.zeroLoc i‖ ^ 2)⁻¹)
    {s : ℂ}
    (hs : ∀ i : EntireXiNonzeroZeroIndex, s ≠ concreteEntireXiZeroSystem.zeroLoc i) :
    infiniteHadamardProduct concreteEntireXiZeroSystem.zeroLoc s ≠ 0 :=
  (EntireXiZeroInvSqDistribution.of_canonical_invSqSummable hinv).infiniteProduct_ne_zero hs

/-! ## 3. The single-index ⇆ multiplicity-index product equality (the honest residual).

`P_mult s = ∏' i : XiZeroIndexMult, hadamardGenus1Factor (zeroLocMult i) s` repeats each
zero `m_ρ` times; the single-index product lists it once. We isolate the product
equality as a single named hypothesis. By §1 it is equivalent to

  `P_mult s = ∏' ρ : XiZeroIndex, hadamardGenus1Factor (xiZeroLoc ρ) s`,

i.e. the **simple-zeros / multiplicity-collapse** statement. -/

/-- **Honest residual hypothesis** (the simple-zeros / multiplicity-collapse content).

For `s` off the single-index zero set, the multiplicity-aware product `P_mult s`
equals the single-index product `infiniteHadamardProduct concreteEntireXiZeroSystem.zeroLoc s`.

By the unconditional reindexing `infiniteHadamardProduct_eq_singleIndexProduct`, this is
equivalent to `P_mult s = ∏' ρ : XiZeroIndex, E₁(xiZeroLoc ρ, s)`, i.e. that repeating each
zero `m_ρ` times yields the same product as listing it once — exactly the statement that
every ξ-zero is **simple** (`m_ρ = 1`). This is the genuine, currently-open analytic content;
it is NOT a reindexing bijection (the two index types have different cardinalities unless all
zeros are simple), so it cannot be discharged structurally and is carried here as the single
minimal hypothesis. -/
def SingleEqMultProduct (s : ℂ) : Prop :=
  P_mult s = infiniteHadamardProduct concreteEntireXiZeroSystem.zeroLoc s

/-! ## 4. Deriving `hquot` from the STEP 1 factorization + the residual. -/

/-- **`hquot` — the off-zero quotient identity (residual (a)).**

From STEP 1's factorization `ξ z = P_mult z · (C·exp(a+b·z))` (carried as `hfact`, the
proven output of `hadamard_factorization_entireXi`), the off-zero nonvanishing of the
single-index product (from `hinv`), and the multiplicity-collapse residual `hSingleEqMult`,
we derive
`ξ s / infiniteHadamardProduct concreteEntireXiZeroSystem.zeroLoc s = C·exp(a+b·s)`
for every `s` off the indexed single-index zero set. -/
theorem hquot_of_factorization
    {C a b : ℂ}
    (hfact : ∀ z, entireRiemannXi z = P_mult z * (C * Complex.exp (a + b * z)))
    (hinv : Summable fun i : EntireXiNonzeroZeroIndex =>
      (‖concreteEntireXiZeroSystem.zeroLoc i‖ ^ 2)⁻¹)
    (hSingleEqMult : ∀ s : ℂ,
      (∀ i : EntireXiNonzeroZeroIndex, s ≠ concreteEntireXiZeroSystem.zeroLoc i) →
        SingleEqMultProduct s) :
    ∀ s : ℂ,
      (∀ i : EntireXiNonzeroZeroIndex, s ≠ concreteEntireXiZeroSystem.zeroLoc i) →
        entireRiemannXi s
            / infiniteHadamardProduct concreteEntireXiZeroSystem.zeroLoc s
          = C * Complex.exp (a + b * s) := by
  intro s hs
  set prod : ℂ := infiniteHadamardProduct concreteEntireXiZeroSystem.zeroLoc s with hprod
  have hprodne : prod ≠ 0 := infiniteHadamardProduct_ne_zero_of_offZeros hinv hs
  -- `P_mult s = prod` (the residual).
  have hcollapse : P_mult s = prod := hSingleEqMult s hs
  -- `ξ s = prod · (C·exp(a+b·s))`.
  have hξ : entireRiemannXi s = prod * (C * Complex.exp (a + b * s)) := by
    rw [hfact s, hcollapse]
  rw [hξ, mul_comm prod _, mul_div_assoc, div_self hprodne, mul_one]

/-! ## 5. The packaged endpoint: inhabit `EntireXiClassicalHadamardTheorem`. -/

/-- **Endpoint.** Feeding `hquot_of_factorization` into rh's smart constructor
`EntireXiClassicalHadamardTheorem.of_canonicalZeros_expAffine_quotient_invSqSummable_normExhaustion`
(rh.lean:81102; the same constructor wrapped by the package's
`entireXiClassicalHadamardTheorem_of_quotientData`) inhabits
`EntireXiClassicalHadamardTheorem EntireXiNonzeroZeroIndex` from:
* the STEP 1 factorization `hfact` (proven output of `hadamard_factorization_entireXi`);
* distinct-zero inverse-square summability `hinv` (G3, `Scratch.xi_zero_invSq_summable`);
* the multiplicity-collapse residual `hSingleEqMult` (simple-zeros). -/
noncomputable def entireXiClassicalHadamardTheorem_of_factorization
    {C a b : ℂ} (hC : C ≠ 0)
    (hfact : ∀ z, entireRiemannXi z = P_mult z * (C * Complex.exp (a + b * z)))
    (hinv : Summable fun i : EntireXiNonzeroZeroIndex =>
      (‖concreteEntireXiZeroSystem.zeroLoc i‖ ^ 2)⁻¹)
    (hSingleEqMult : ∀ s : ℂ,
      (∀ i : EntireXiNonzeroZeroIndex, s ≠ concreteEntireXiZeroSystem.zeroLoc i) →
        SingleEqMultProduct s) :
    EntireXiClassicalHadamardTheorem EntireXiNonzeroZeroIndex :=
  EntireXiClassicalHadamardTheorem.of_canonicalZeros_expAffine_quotient_invSqSummable_normExhaustion
    hC hinv
    (hquot_of_factorization hfact hinv hSingleEqMult)

#print axioms infiniteHadamardProduct_eq_singleIndexProduct
#print axioms hquot_of_factorization
#print axioms entireXiClassicalHadamardTheorem_of_factorization

end OverflowResidueRH.BacklundTuring.ScratchQuotBridge
