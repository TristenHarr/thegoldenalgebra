import rh
import Mathlib

open Complex Filter Topology

/-!
# Multiplicity-index inhabitant of `EntireXiClassicalHadamardTheorem` — NO simplicity

This file eliminates the **simplicity-of-zeros residual** left open by
`ScratchQuotBridge.lean`.

`ScratchQuotBridge` inhabits `EntireXiClassicalHadamardTheorem EntireXiNonzeroZeroIndex`
through rh's canonical-zeros smart constructor, whose index runs over the **distinct**
nonzero ξ-zeros (each once); matching that single-index product to the genuine
multiplicity-aware product `P_mult` requires the (open) statement that every ξ-zero is
simple — carried there as `hSingleEqMult`.

Here we BYPASS the distinct-zero route entirely. `EntireXiClassicalHadamardTheorem (ι)`
(rh:80264) is **generic over `ι`**, and so are its `of_*` smart constructors that take a
generic `HZ : ConcreteEntireXiZeroSystem ι` (notably
`EntireXiClassicalHadamardTheorem.of_invSq_mono_exhaustive`, rh:80498). We instantiate
`ι := XiZeroIndexMult` (each zero `ρ` repeated `m_ρ = analyticOrderNatAt ξ ρ` times),
`zeroLoc := zeroLocMult`. Then

  `infiniteHadamardProduct zeroLocMult s = ∏' i, hadamardGenus1Factor (zeroLocMult i) s = P_mult s`

DEFINITIONALLY, so the off-zero quotient `ξ s / infiniteHadamardProduct zeroLocMult s
= C·exp(a+b·s)` is EXACTLY the proven multiplicity-factorization
`ScratchHadamardPackage.hadamard_factorization_entireXi` divided through — **no simplicity
assumption appears**.

## The 7 structure fields of `EntireXiClassicalHadamardTheorem ι`
(rh:80264), all generic over `ι`:
1. `zeroSystem  : ConcreteEntireXiZeroSystem ι`           — filled with the mult index
2. `prefactor   : ℂ → ℂ`                                  — `fun s => C·exp(a+b·s)`
3. `zeroDistribution : EntireXiZeroInvSqDistribution zeroSystem` — from mult inv-sq summability
4. `luc         : HadamardProductLUCLogDerivData zeroLoc`  — built INTERNALLY by the constructor
5. `region      : ∀ s, ξ s ≠ 0 → s ∈ luc.region`          — built INTERNALLY
6. `factorization : EntireXiHadamardFactorization …`      — from the mult-factorization quotient
7. `prefactorData : EntireXiHadamardPrefactor prefactor`  — `exp_affine hC`, INTERNAL

Fields 4 and 5 (the locally-uniform-convergence / log-derivative-interchange data and the
region cover) are discharged **internally** by `of_invSq_mono_exhaustive` from the inverse-
square zero distribution and a monotone exhaustive Finset sequence. Fields 1,3,6 are filled
from the mult index + named residuals. Fields 2,7 are the exp-affine prefactor.

## Residuals (already named upstream; NOT new)
* `hMult`  : `WithMultInvSqSummable` — with-multiplicity inverse-square summability over the
             distinct zeros (`ScratchMultIndex.WithMultInvSqSummable`, deep residual: the
             multiplicity-weighted RvM/divisor count). Gives mult inv-sq summability
             **and** (via discreteness) norm-properness.
* `hNormProper` : `HadamardZeroNormProper zeroLocMult` — finitely many mult-indices per disk.
             This is the classical local finiteness of the ξ-zero set counted with
             multiplicity; supplied here as a named hypothesis (it is the discreteness datum,
             the same content already used upstream).
* `hfact`  : the proven multiplicity-factorization
             `ξ z = P_mult z · (C·exp(a+b·z))` — the output of
             `ScratchHadamardPackage.hadamard_factorization_entireXi` (residuals hLU/hOrder/hMinMod).

**Crucially, NONE of these is the simplicity-of-zeros statement.** The simplicity residual is
GONE: the product here is the multiplicity-aware product, so the factorization is the
unconditional genus-1 Hadamard factorization.

## Honesty
No `sorry`/`admit`/`sorryAx`. Genuinely-open inputs are explicit, docstring'd parameters.
`#print axioms` lists only the standard kernel axioms.
-/

set_option maxHeartbeats 2000000

namespace OverflowResidueRH.BacklundTuring.ScratchMultHadamard

open OverflowResidueRH

/-! ## 0. The multiplicity index over rh's `entireRiemannXi` (verbatim from the package). -/

theorem entireRiemannXi_zero_ne : entireRiemannXi 0 ≠ 0 := by
  rw [entireRiemannXi_zero]; norm_num

theorem analyticOnNhd_entireRiemannXi :
    AnalyticOnNhd ℂ entireRiemannXi Set.univ :=
  fun z _ => entireRiemannXi_differentiable.analyticAt z

/-- ξ has finite analytic order at every point (it is not identically zero). -/
theorem analyticOrderAt_entireRiemannXi_ne_top (z : ℂ) :
    analyticOrderAt entireRiemannXi z ≠ ⊤ := by
  have h₀ : analyticOrderAt entireRiemannXi 0 ≠ ⊤ := by
    rw [(analyticOnNhd_entireRiemannXi 0 (Set.mem_univ _)).analyticOrderAt_eq_zero.2
      entireRiemannXi_zero_ne]
    exact (by simp : (0 : ℕ∞) ≠ ⊤)
  exact analyticOnNhd_entireRiemannXi.analyticOrderAt_ne_top_of_isPreconnected
    isPreconnected_univ (Set.mem_univ 0) (Set.mem_univ z) h₀

/-- ξ's zero set. -/
def riemannXiZeros : Set ℂ := entireRiemannXi ⁻¹' {0}

/-- The single-index ξ-zero type (each zero appears once). -/
abbrev XiZeroIndex : Type := riemannXiZeros

def xiZeroLoc (ρ : XiZeroIndex) : ℂ := (ρ : ℂ)

lemma entireRiemannXi_xiZeroLoc (ρ : XiZeroIndex) :
    entireRiemannXi (xiZeroLoc ρ) = 0 := ρ.2

lemma xiZeroLoc_ne_zero (ρ : XiZeroIndex) : xiZeroLoc ρ ≠ 0 := by
  intro h
  have hz := entireRiemannXi_xiZeroLoc ρ
  rw [h] at hz
  exact entireRiemannXi_zero_ne hz

/-- **Multiplicity-aware ξ-zero index**: each zero `ρ` is repeated
`m_ρ = analyticOrderNatAt ξ ρ` times. -/
def XiZeroIndexMult : Type :=
  Σ ρ : XiZeroIndex, Fin (analyticOrderNatAt entireRiemannXi (xiZeroLoc ρ))

/-- Location map of the multiplicity index. -/
def zeroLocMult (i : XiZeroIndexMult) : ℂ := xiZeroLoc i.1

lemma zeroLocMult_ne_zero (i : XiZeroIndexMult) : zeroLocMult i ≠ 0 :=
  xiZeroLoc_ne_zero i.1

lemma entireRiemannXi_zeroLocMult (i : XiZeroIndexMult) :
    entireRiemannXi (zeroLocMult i) = 0 :=
  entireRiemannXi_xiZeroLoc i.1

/-- The multiplicity-aware genus-1 Hadamard product `P_mult z = ∏' i, E₁(z/ρᵢ)`. -/
noncomputable def P_mult (z : ℂ) : ℂ :=
  ∏' i : XiZeroIndexMult, hadamardGenus1Factor (zeroLocMult i) z

/-- `P_mult` is **definitionally** `infiniteHadamardProduct zeroLocMult`. -/
theorem P_mult_eq_infiniteHadamardProduct (z : ℂ) :
    P_mult z = infiniteHadamardProduct zeroLocMult z := rfl

/-! ## 1. The multiplicity multiplicity is positive at every ξ-zero ⇒ surjectivity. -/

/-- At a ξ-zero `ρ`, the multiplicity `m_ρ = analyticOrderNatAt ξ ρ` is positive. -/
theorem analyticOrderNatAt_pos_of_zero (ρ : XiZeroIndex) :
    0 < analyticOrderNatAt entireRiemannXi (xiZeroLoc ρ) := by
  have hne_top := analyticOrderAt_entireRiemannXi_ne_top (xiZeroLoc ρ)
  have hzero : entireRiemannXi (xiZeroLoc ρ) = 0 := entireRiemannXi_xiZeroLoc ρ
  -- order ≠ 0 because ξ vanishes there
  have hane : analyticOrderAt entireRiemannXi (xiZeroLoc ρ) ≠ 0 := by
    intro hcontra
    have := ((analyticOnNhd_entireRiemannXi (xiZeroLoc ρ)
      (Set.mem_univ _)).analyticOrderAt_eq_zero).1 hcontra
    exact this hzero
  -- push to ℕ
  have hcast : (analyticOrderNatAt entireRiemannXi (xiZeroLoc ρ) : ℕ∞)
      = analyticOrderAt entireRiemannXi (xiZeroLoc ρ) :=
    Nat.cast_analyticOrderNatAt hne_top
  rcases Nat.eq_zero_or_pos (analyticOrderNatAt entireRiemannXi (xiZeroLoc ρ)) with h0 | hpos
  · exfalso
    rw [h0] at hcast
    exact hane hcast.symm
  · exact hpos

/-! ## 2. The concrete entire-ξ zero system over the MULTIPLICITY index.

This is the field 1 (`zeroSystem`) of `EntireXiClassicalHadamardTheorem`, instantiated
with `ι := XiZeroIndexMult`, `zeroLoc := zeroLocMult`. The surjectivity field
`all_nonzero_entireXi_zeros` is the only nontrivial one: given a nonzero ξ-zero `s`, the base
zero `ρ = ⟨s, _⟩` has positive multiplicity, so `Fin m_ρ` is inhabited (by `⟨0, hpos⟩`) and
the index `⟨ρ, ⟨0, hpos⟩⟩` maps to `s`. -/

/-- **Field 1 — the multiplicity-index concrete zero system.** Generic over `ι`; built here
with `ι = XiZeroIndexMult`, NO simplicity assumption. -/
def concreteEntireXiZeroSystemMult :
    ConcreteEntireXiZeroSystem XiZeroIndexMult where
  zeroLoc := zeroLocMult
  zeroLoc_ne_zero := zeroLocMult_ne_zero
  zeroLoc_is_zero := entireRiemannXi_zeroLocMult
  all_nonzero_entireXi_zeros := by
    intro s hs _hs0
    -- `s` is a ξ-zero, so it is a base index `ρ`; its multiplicity is positive.
    refine ⟨⟨⟨s, hs⟩, ⟨0, analyticOrderNatAt_pos_of_zero ⟨s, hs⟩⟩⟩, ?_⟩
    rfl

@[simp] lemma concreteEntireXiZeroSystemMult_zeroLoc :
    concreteEntireXiZeroSystemMult.zeroLoc = zeroLocMult := rfl

/-! ## 3. Field 3 — the inverse-square zero distribution over the multiplicity index.

`EntireXiZeroInvSqDistribution concreteEntireXiZeroSystemMult` needs:
* `inv_sq_summable` : `Summable fun i => (‖zeroLocMult i‖²)⁻¹`  ← `hinvMult` (mult inv-sq);
* `eventually_large`                                             ← from `hNormProper`.

Both are supplied via rh's `of_invSqSummable_normProper`, fed the named residuals. -/

/-- **Field 3 — mult-index inverse-square zero distribution.** Generic constructor; no
simplicity. -/
def entireXiZeroInvSqDistributionMult
    (hinvMult : Summable fun i : XiZeroIndexMult => (‖zeroLocMult i‖ ^ 2)⁻¹)
    (hNormProper : HadamardZeroNormProper zeroLocMult) :
    EntireXiZeroInvSqDistribution concreteEntireXiZeroSystemMult :=
  EntireXiZeroInvSqDistribution.of_invSqSummable_normProper
    (HZ := concreteEntireXiZeroSystemMult) hinvMult hNormProper

/-! ## 4. Field 6 — the entire-ξ Hadamard factorization over the multiplicity index.

The off-zero quotient `ξ s / infiniteHadamardProduct zeroLocMult s = C·exp(a+b·s)` is the
proven multiplicity-factorization `hfact : ξ z = P_mult z · (C·exp(a+b·z))` divided through,
using `P_mult = infiniteHadamardProduct zeroLocMult` (definitional) and product nonvanishing
off the zero set (from the inverse-square distribution). NO simplicity is used: the product is
the genuine multiplicity-aware one. -/

/-- The off-zero quotient identity over the mult index, from the mult-factorization. -/
theorem hquotMult_of_factorization
    {C a b : ℂ}
    (hfact : ∀ z, entireRiemannXi z = P_mult z * (C * Complex.exp (a + b * z)))
    (Hdist : EntireXiZeroInvSqDistribution concreteEntireXiZeroSystemMult) :
    ∀ s : ℂ,
      (∀ i : XiZeroIndexMult, s ≠ concreteEntireXiZeroSystemMult.zeroLoc i) →
        entireRiemannXi s
            / infiniteHadamardProduct concreteEntireXiZeroSystemMult.zeroLoc s
          = C * Complex.exp (a + b * s) := by
  intro s hs
  have hprodne : infiniteHadamardProduct zeroLocMult s ≠ 0 :=
    Hdist.infiniteProduct_ne_zero hs
  -- `ξ s = P_mult s · (C·exp …) = infiniteHadamardProduct zeroLocMult s · (C·exp …)`.
  have hξ : entireRiemannXi s
      = infiniteHadamardProduct zeroLocMult s * (C * Complex.exp (a + b * s)) := by
    rw [hfact s]; rfl
  show entireRiemannXi s / infiniteHadamardProduct zeroLocMult s = C * Complex.exp (a + b * s)
  rw [hξ, mul_comm _ (C * Complex.exp (a + b * s)), mul_div_assoc, div_self hprodne, mul_one]

/-- **Field 6 — mult-index entire-ξ Hadamard factorization** (exp-affine prefactor), from the
off-zero quotient + the inverse-square distribution. NO simplicity. -/
def entireXiHadamardFactorizationMult
    {C a b : ℂ}
    (hfact : ∀ z, entireRiemannXi z = P_mult z * (C * Complex.exp (a + b * z)))
    (Hdist : EntireXiZeroInvSqDistribution concreteEntireXiZeroSystemMult) :
    EntireXiHadamardFactorization concreteEntireXiZeroSystemMult
      (fun s : ℂ => C * Complex.exp (a + b * s)) :=
  EntireXiHadamardFactorization.exp_affine_of_offZeroQuotient_invSq
    Hdist (hquotMult_of_factorization hfact Hdist)

/-! ## 5. THE ENDPOINT — inhabit `EntireXiClassicalHadamardTheorem XiZeroIndexMult`
directly, via the GENERIC constructor `of_invSq_mono_exhaustive` (rh:80498), which fills
fields 4 (`luc`), 5 (`region`), and the LUC/log-derivative interchange INTERNALLY. NO
simplicity hypothesis. -/

/-- **Multiplicity-index inhabitant of `EntireXiClassicalHadamardTheorem`** — eliminates the
simplicity residual.

Inputs (all already-named residuals; none is simplicity):
* `hC`          : `C ≠ 0`;
* `hfact`       : the proven multiplicity-factorization `ξ z = P_mult z · (C·exp(a+b·z))`
                  (= `ScratchHadamardPackage.hadamard_factorization_entireXi`);
* `hinvMult`    : with-multiplicity inverse-square summability;
* `hNormProper` : finitely many mult-indices per disk (ξ-zero discreteness with multiplicity).

The exhaustion is the norm-ball exhaustion of `hNormProper`; the genus-1 product
convergence, log-derivative interchange (fields 4/5) and the prefactor data (field 7) are
discharged INTERNALLY by `of_invSq_mono_exhaustive` / the exp-affine prefactor lemma. -/
noncomputable def entireXiClassicalHadamardTheoremMult
    {C a b : ℂ} (hC : C ≠ 0)
    (hfact : ∀ z, entireRiemannXi z = P_mult z * (C * Complex.exp (a + b * z)))
    (hinvMult : Summable fun i : XiZeroIndexMult => (‖zeroLocMult i‖ ^ 2)⁻¹)
    (hNormProper : HadamardZeroNormProper zeroLocMult) :
    EntireXiClassicalHadamardTheorem XiZeroIndexMult :=
  let Hdist : EntireXiZeroInvSqDistribution concreteEntireXiZeroSystemMult :=
    entireXiZeroInvSqDistributionMult hinvMult hNormProper
  EntireXiClassicalHadamardTheorem.of_invSq_mono_exhaustive
    concreteEntireXiZeroSystemMult
    (fun s : ℂ => C * Complex.exp (a + b * s))
    Hdist
    hNormProper.normExhaustion
    hNormProper.normExhaustion_mono
    hNormProper.normExhaustion_exhaustive
    (entireXiHadamardFactorizationMult hfact Hdist)
    (EntireXiHadamardPrefactor.exp_affine hC)

/-! ## 6. Capstone compatibility check.

The final capstone `XiPullbackAntiHerglotzTarget_of_entireHadamard_and_classicalStieltjes`
(rh:99546) takes `Hhad : EntireXiClassicalHadamardTheorem ι` with `ι` fully generic, and the
log-derivative source map `Hhad.toCompletedXiSourceAFZ_canonical` (rh:86994) is defined for
ANY `ι`. So the multiplicity-index inhabitant feeds the capstone with `ι := XiZeroIndexMult`.

We verify both facts by COMPILATION below:
* `toCompletedXiSourceAFZ_canonical` is defined for the mult inhabitant;
* the capstone accepts it (partially-applied here through the Hhad slot). -/

/-- The canonical AFZ log-derivative source for the multiplicity inhabitant is well-typed. -/
noncomputable def multHadamard_toSourceAFZ_canonical
    {C a b : ℂ} (hC : C ≠ 0)
    (hfact : ∀ z, entireRiemannXi z = P_mult z * (C * Complex.exp (a + b * z)))
    (hinvMult : Summable fun i : XiZeroIndexMult => (‖zeroLocMult i‖ ^ 2)⁻¹)
    (hNormProper : HadamardZeroNormProper zeroLocMult) :
    CompletedXiLogDerivativeSourceAFZ :=
  (entireXiClassicalHadamardTheoremMult hC hfact hinvMult hNormProper).toCompletedXiSourceAFZ_canonical

/-- **Capstone accepts the multiplicity inhabitant.** This is the full
`XiPullbackAntiHerglotzTarget_of_entireHadamard_and_classicalStieltjes` (rh:99546) with the
`Hhad` slot filled by `entireXiClassicalHadamardTheoremMult` (`ι = XiZeroIndexMult`). The
remaining hypotheses (Dzero/Turing/Stieltjes data) are carried as parameters — they are the
analysis-side inputs of the capstone, unrelated to the Hadamard index choice. The very fact
that this type-checks confirms `ι = XiZeroIndexMult` is accepted with NO simplicity. -/
theorem capstone_accepts_multHadamard
    (Dzero : Phase1IBP.OrderedFluctuationMeasureData)
    (h_Z_ge_15 : ∀ i : ℕ, (15 : ℝ) ≤ Dzero.toFluctuationMeasureData.Z i)
    (hTuring :
      ∀ {z : ℂ} {T u : ℝ},
        10 ≤ T → T ≤ 140 → 0 < z.im →
        2 * (1 + |z.re| + z.im) ≤ T → T ≤ u →
        |Phase1IBP.finiteFluctuationPrimitive Dzero 10 u|
          ≤ (slabCD T).1 * Real.log u + (slabCD T).2)
    (hHighLog :
      ∀ {z : ℂ} {T u : ℝ},
        140 ≤ T → 0 < z.im →
        2 * (1 + |z.re| + z.im) ≤ T → T ≤ u →
        |Phase1IBP.finiteFluctuationPrimitive Dzero 10 u|
          ≤ (1 / 2 : ℝ) * Real.log u + (49 / 20 : ℝ))
    {C a b : ℂ} (hC : C ≠ 0)
    (hfact : ∀ z, entireRiemannXi z = P_mult z * (C * Complex.exp (a + b * z)))
    (hinvMult : Summable fun i : XiZeroIndexMult => (‖zeroLocMult i‖ ^ 2)⁻¹)
    (hNormProper : HadamardZeroNormProper zeroLocMult)
    {finiteCloud tail : ℂ → ℂ}
    (Hst :
      ClassicalStieltjesExplicitFormulaInputs
        Dzero 10
        (pullbackZeroContribution
          (entireXiClassicalHadamardTheoremMult hC hfact hinvMult hNormProper).toCompletedXiSourceAFZ_canonical)
        finiteCloud tail) :
    XiPullbackAntiHerglotzTarget :=
  XiPullbackAntiHerglotzTarget_of_entireHadamard_and_classicalStieltjes
    Dzero h_Z_ge_15 hTuring hHighLog
    (entireXiClassicalHadamardTheoremMult hC hfact hinvMult hNormProper) Hst

#print axioms analyticOrderNatAt_pos_of_zero
#print axioms concreteEntireXiZeroSystemMult
#print axioms hquotMult_of_factorization
#print axioms entireXiClassicalHadamardTheoremMult
#print axioms multHadamard_toSourceAFZ_canonical
#print axioms capstone_accepts_multHadamard

end OverflowResidueRH.BacklundTuring.ScratchMultHadamard
