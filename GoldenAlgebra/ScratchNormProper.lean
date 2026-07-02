import rh
import Mathlib

open Complex Filter Topology

/-!
# Closing `hNormProper : HadamardZeroNormProper zeroLocMult`

`ScratchMultHadamard.lean` carries, as a named hypothesis, the classical local
finiteness / properness of the ξ-zero locations counted **with multiplicity**:

    `hNormProper : HadamardZeroNormProper zeroLocMult`

where `HadamardZeroNormProper` (rh:74787) is the single-field structure

    `finite_norm_le : ∀ R : ℝ, { i | ‖zeroLoc i‖ ≤ R }.Finite`

(every closed norm disk contains only finitely many indexed zeros), and
`zeroLocMult : XiZeroIndexMult → ℂ` is the multiplicity-aware ξ-zero location map.

This file **proves** that hypothesis. The scaffolding (`riemannXiZeros`,
`XiZeroIndex`, `xiZeroLoc`, `XiZeroIndexMult`, `zeroLocMult`) is the verbatim copy
used by `ScratchMultIndex.lean` / `ScratchMultHadamard.lean` (the scratch files are
standalone and each re-states these short definitions over rh's `entireRiemannXi`,
since they cannot `import` one another).

The content is exactly the cocompact escape
`Tendsto zeroLocMult cofinite (cocompact ℂ)` already established (for the analogous
multiplicity index) in `ScratchMultIndex.tendsto_zeroLocMult_cofinite_cocompact`,
re-derived here. Cofinite → cocompact says precisely that the preimage of every
compact set is finite; the closed disk `‖·‖ ≤ R = closedBall 0 R` is compact in `ℂ`,
so `{ i | ‖zeroLocMult i‖ ≤ R }` is finite — which is the structure field.

The escape itself is structural:
* `zeroLocMult = (↑) ∘ Sigma.fst`;
* `Sigma.fst` is cofinite→cofinite because each fiber `Fin m_ρ` is finite;
* the inclusion `riemannXiZeros ↪ ℂ` is cofinite→cocompact because the zero set is
  closed and discrete (`IsClosed.tendsto_coe_cofinite_of_isDiscrete`), and ξ's zero
  set is closed+discrete since ξ is analytic and `ξ 0 = ½ ≠ 0`
  (`AnalyticOnNhd.preimage_zero_mem_codiscrete`).

No `sorry`/`admit`. The ONLY mathematical inputs are rh's `entireRiemannXi`
analyticity (`entireRiemannXi_differentiable`) and `ξ 0 ≠ 0`, both already in rh.
-/

set_option maxHeartbeats 2000000

namespace OverflowResidueRH.BacklundTuring.ScratchNormProper

open OverflowResidueRH

/-! ## 0. Self-contained ξ-Hadamard scaffolding (verbatim, over rh's `entireRiemannXi`). -/

theorem entireRiemannXi_zero_ne : entireRiemannXi 0 ≠ 0 := by
  rw [entireRiemannXi_zero]; norm_num

theorem analyticOnNhd_entireRiemannXi :
    AnalyticOnNhd ℂ entireRiemannXi Set.univ :=
  fun z _ => entireRiemannXi_differentiable.analyticAt z

/-- ξ's zero set. -/
def riemannXiZeros : Set ℂ := entireRiemannXi ⁻¹' {0}

/-- The single-index ξ-zero type (each zero appears once). -/
abbrev XiZeroIndex : Type := riemannXiZeros

def xiZeroLoc (ρ : XiZeroIndex) : ℂ := (ρ : ℂ)

lemma entireRiemannXi_xiZeroLoc (ρ : XiZeroIndex) :
    entireRiemannXi (xiZeroLoc ρ) = 0 := ρ.2

/-- **Multiplicity-aware ξ-zero index**: each zero `ρ` is repeated
`m_ρ = analyticOrderNatAt ξ ρ` times. -/
def XiZeroIndexMult : Type :=
  Σ ρ : XiZeroIndex, Fin (analyticOrderNatAt entireRiemannXi (xiZeroLoc ρ))

/-- Location map of the multiplicity index. -/
def zeroLocMult (i : XiZeroIndexMult) : ℂ := xiZeroLoc i.1

/-! ## 1. ξ-zero-set discreteness. -/

theorem compl_riemannXiZeros_mem_codiscrete :
    (riemannXiZeros : Set ℂ)ᶜ ∈ codiscrete ℂ :=
  analyticOnNhd_entireRiemannXi.preimage_zero_mem_codiscrete entireRiemannXi_zero_ne

theorem isClosed_riemannXiZeros : IsClosed (riemannXiZeros : Set ℂ) := by
  simpa using (mem_codiscrete'.mp compl_riemannXiZeros_mem_codiscrete).1

theorem isDiscrete_riemannXiZeros : IsDiscrete (riemannXiZeros : Set ℂ) := by
  simpa using (mem_codiscrete'.mp compl_riemannXiZeros_mem_codiscrete).2

/-- Inclusion of the (closed, discrete) ξ-zero set into `ℂ` is cofinite→cocompact. -/
theorem tendsto_riemannXiZeros_cofinite_cocompact :
    Tendsto ((↑) : riemannXiZeros → ℂ) cofinite (cocompact ℂ) :=
  isClosed_riemannXiZeros.tendsto_coe_cofinite_of_isDiscrete isDiscrete_riemannXiZeros

/-! ## 2. The multiplicity index escapes to ∞ along the cofinite filter. -/

/-- `zeroLocMult = (↑) ∘ Sigma.fst` escapes every compact set along `cofinite`. -/
theorem tendsto_zeroLocMult_cofinite_cocompact :
    Tendsto (zeroLocMult : XiZeroIndexMult → ℂ) cofinite (cocompact ℂ) := by
  -- `Sigma.fst` is cofinite→cofinite: each fiber `Fin m_ρ` is finite.
  have hfst : Tendsto (Sigma.fst : XiZeroIndexMult → XiZeroIndex) cofinite cofinite := by
    refine Tendsto.cofinite_of_finite_preimage_singleton (fun ρ => ?_)
    apply Set.Finite.subset (Set.finite_range
      (fun k : Fin (analyticOrderNatAt entireRiemannXi (xiZeroLoc ρ)) =>
        (⟨ρ, k⟩ : XiZeroIndexMult)))
    rintro ⟨b, k⟩ hb
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hb
    subst hb
    exact ⟨k, rfl⟩
  exact tendsto_riemannXiZeros_cofinite_cocompact.comp hfst

/-! ## 3. THE DELIVERABLE — norm-properness from cocompact escape. -/

/-- **PROVED — `HadamardZeroNormProper zeroLocMult`.**
Every closed norm disk `{ i | ‖zeroLocMult i‖ ≤ R }` is finite, because it is the
preimage under `zeroLocMult` of the compact closed ball `closedBall 0 R`, and the
cofinite→cocompact escape of `zeroLocMult` makes preimages of compacts finite. -/
theorem hadamardZeroNormProper_zeroLocMult :
    HadamardZeroNormProper (zeroLocMult : XiZeroIndexMult → ℂ) where
  finite_norm_le := by
    intro R
    have hcompact : IsCompact (Metric.closedBall (0 : ℂ) R) := isCompact_closedBall _ _
    have hco : (Metric.closedBall (0 : ℂ) R)ᶜ ∈ cocompact ℂ :=
      hcompact.compl_mem_cocompact
    have hpre : (zeroLocMult ⁻¹' (Metric.closedBall (0 : ℂ) R)ᶜ) ∈ cofinite :=
      tendsto_zeroLocMult_cofinite_cocompact hco
    rw [Filter.mem_cofinite] at hpre
    -- `(zeroLocMult ⁻¹' Sᶜ)ᶜ = zeroLocMult ⁻¹' S = { i | ‖zeroLocMult i‖ ≤ R }`
    have hset : { i : XiZeroIndexMult | ‖zeroLocMult i‖ ≤ R }
        = (zeroLocMult ⁻¹' (Metric.closedBall (0 : ℂ) R)ᶜ)ᶜ := by
      ext i
      simp only [Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_preimage,
        Metric.mem_closedBall, dist_zero_right, not_lt, not_le]
    rw [hset]
    exact hpre

#print axioms hadamardZeroNormProper_zeroLocMult

end OverflowResidueRH.BacklundTuring.ScratchNormProper
