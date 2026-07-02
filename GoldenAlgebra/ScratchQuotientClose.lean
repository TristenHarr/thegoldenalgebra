import Mathlib

open Complex Filter Topology

/-!
# TASK #3 — the Hadamard quotient `Q = ξ/∏` is ENTIRE and ZERO-FREE

This file closes the structural Hadamard-quotient step: combining

* **B45** (`entire_quotient_of_analyticOrderAt_eq`, the structural heart of Hadamard
  factorization — two entire functions vanishing to the same order at *every* point have a
  zero-free entire quotient), copied verbatim from `Scratch.lean`/`ScratchQuotient.lean`; with

* the multiplicity-aware genus-1 product `P_mult z = ∏' i : XiZeroIndexMult, genus1Factor
  (zeroLocMult i) z` of `ScratchMultIndex.lean`, whose two DEEP outputs are carried here as
  honestly-named hypotheses matching `ScratchMultIndex`'s proven signatures:

  - `hLU` : `MultipliableLocallyUniformlyOn (fun i s => genus1Factor (zeroLocMult i) s) univ`
    — this is the proven `ScratchMultIndex.xiMult_genus1Product_LU hMult`
    (locally-uniform convergence of the genus-1 Hadamard product over the multiplicity index);

  - `hOrder` : `∀ z, analyticOrderAt P_mult z = analyticOrderAt entireRiemannXi z`
    — this is the proven *deliverable* `ScratchMultIndex.xiMult_genus1Product_analyticOrderAt`
    (unconditional, given its own structural `htail` input).

to produce the **Hadamard quotient**:

  `∃ Q : ℂ → ℂ, Differentiable ℂ Q ∧ (∀ z, Q z ≠ 0) ∧ ∀ z, entireRiemannXi z = P_mult z · Q z`.

## What is COPIED verbatim vs CARRIED as hypothesis

Because the sibling scratch files cannot be imported (they are standalone `import Mathlib`
scratch files, not built library modules), the following are **copied verbatim**:

* `genus1Factor` and `analyticAt_genus1Factor` (`ScratchMultIndex` §0);
* `entireRiemannXi`, `differentiable_entireRiemannXi`, `entireRiemannXi_zero`,
  `entireRiemannXi_zero_ne` (`ScratchMultIndex` §0);
* the multiplicity-aware index scaffolding `riemannXiZeros`, `XiZeroIndex`, `xiZeroLoc`,
  `XiZeroIndexMult`, `zeroLocMult`, and the order-finiteness facts needed to *state* it
  (`ScratchMultIndex` §0–§1);
* **B45** `entire_quotient_of_analyticOrderAt_eq` (`Scratch.lean`/`ScratchQuotient.lean`).

The two DEEP inputs — the locally-uniform multipliability and the everywhere `analyticOrderAt`
match — are **carried as hypotheses** `hLU`, `hOrder` of the headline theorem
`hadamard_quotient_entire_zeroFree`, exactly matching `ScratchMultIndex`'s proven outputs. The
self-contained corollary `hadamard_quotient_of_multIndex_data` packages the only genuinely-new
local work: deriving `Differentiable ℂ P_mult` from `hLU` (via Mathlib's
`HasProdLocallyUniformlyOn` ⇒ `TendstoLocallyUniformlyOn` of finite products ⇒
`TendstoLocallyUniformlyOn.differentiableOn`), then feeding B45.

No `sorry`/`admit`; `#print axioms` at the end shows only the standard kernel axioms.
-/

set_option maxHeartbeats 2000000

namespace OverflowResidueRH.BacklundTuring.ScratchQuotientClose

/-! ## 0. Copied scaffolding from `ScratchMultIndex.lean` (verbatim). -/

/-- Genus-1 Weierstrass factor `E₁(s/ρ) = (1 - s/ρ)·exp(s/ρ)`. -/
noncomputable def genus1Factor (ρ s : ℂ) : ℂ := (1 - s / ρ) * Complex.exp (s / ρ)

theorem analyticAt_genus1Factor (ρ : ℂ) (z : ℂ) : AnalyticAt ℂ (genus1Factor ρ) z := by
  unfold genus1Factor; fun_prop

/-- Each genus-1 factor is differentiable everywhere (used for the finite-product approximants). -/
theorem differentiable_genus1Factor (ρ : ℂ) : Differentiable ℂ (genus1Factor ρ) := by
  unfold genus1Factor; fun_prop

/-- The entire completion of ξ: `½·(s·(s−1)·Λ₀(s) + 1)` (manifestly entire). -/
noncomputable def entireRiemannXi (s : ℂ) : ℂ :=
  (1 / 2) * (s * (s - 1) * completedRiemannZeta₀ s + 1)

theorem differentiable_entireRiemannXi : Differentiable ℂ entireRiemannXi := by
  unfold entireRiemannXi
  exact (((differentiable_id.mul (differentiable_id.sub_const 1)).mul
    differentiable_completedZeta₀).add_const 1).const_mul _

theorem analyticOnNhd_entireRiemannXi :
    AnalyticOnNhd ℂ entireRiemannXi Set.univ :=
  differentiable_entireRiemannXi.differentiableOn.analyticOnNhd isOpen_univ

theorem entireRiemannXi_zero : entireRiemannXi 0 = 1 / 2 := by simp [entireRiemannXi]

theorem entireRiemannXi_zero_ne : entireRiemannXi 0 ≠ 0 := by
  rw [entireRiemannXi_zero]; norm_num

/-- ξ's zero set. -/
def riemannXiZeros : Set ℂ := entireRiemannXi ⁻¹' {0}

@[simp] lemma mem_riemannXiZeros {z : ℂ} :
    z ∈ riemannXiZeros ↔ entireRiemannXi z = 0 := Iff.rfl

lemma compl_riemannXiZeros_mem_codiscrete :
    riemannXiZerosᶜ ∈ codiscrete ℂ :=
  analyticOnNhd_entireRiemannXi.preimage_zero_mem_codiscrete entireRiemannXi_zero_ne

lemma isClosed_riemannXiZeros : IsClosed riemannXiZeros := by
  simpa using (mem_codiscrete'.mp compl_riemannXiZeros_mem_codiscrete).1

/-- The single-index ξ-zero type (each zero appears ONCE). -/
abbrev XiZeroIndex : Type := riemannXiZeros

def xiZeroLoc (ρ : XiZeroIndex) : ℂ := (ρ : ℂ)

lemma entireRiemannXi_xiZeroLoc (ρ : XiZeroIndex) :
    entireRiemannXi (xiZeroLoc ρ) = 0 := ρ.2

/-- ξ has finite analytic order at every point (it is not identically zero). -/
theorem analyticOrderAt_entireRiemannXi_ne_top (z : ℂ) :
    analyticOrderAt entireRiemannXi z ≠ ⊤ := by
  have h₀ : analyticOrderAt entireRiemannXi 0 ≠ ⊤ := by
    rw [(analyticOnNhd_entireRiemannXi 0 (Set.mem_univ _)).analyticOrderAt_eq_zero.2
      entireRiemannXi_zero_ne]
    exact (by simp : (0 : ℕ∞) ≠ ⊤)
  exact analyticOnNhd_entireRiemannXi.analyticOrderAt_ne_top_of_isPreconnected
    isPreconnected_univ (Set.mem_univ 0) (Set.mem_univ z) h₀

/-- **Multiplicity-aware ξ-zero index**: each zero `ρ` is repeated `m_ρ = analyticOrderNatAt ξ ρ`
times via the dependent sum over `Fin m_ρ`. -/
def XiZeroIndexMult : Type :=
  Σ ρ : XiZeroIndex, Fin (analyticOrderNatAt entireRiemannXi (xiZeroLoc ρ))

/-- Location map of the multiplicity index: every copy of `ρ` maps to `(ρ : ℂ)`. -/
def zeroLocMult (i : XiZeroIndexMult) : ℂ := xiZeroLoc i.1

/-- The multiplicity-aware genus-1 Hadamard product `P_mult z = ∏' i, E₁(z/ρᵢ)`. -/
noncomputable def P_mult (z : ℂ) : ℂ :=
  ∏' i : XiZeroIndexMult, genus1Factor (zeroLocMult i) z

theorem P_mult_zero_ne : P_mult 0 ≠ 0 := by
  -- At `z = 0` every factor is `(1 - 0) * exp 0 = 1`, so the tprod is `∏' 1 = 1 ≠ 0`.
  have hone : ∀ i : XiZeroIndexMult, genus1Factor (zeroLocMult i) 0 = 1 := by
    intro i; simp [genus1Factor]
  have : P_mult 0 = ∏' _i : XiZeroIndexMult, (1 : ℂ) := by
    unfold P_mult; exact tprod_congr hone
  rw [this, tprod_one]; exact one_ne_zero

/-! ## 1. B45 — entire quotient with matching zero-orders (copied verbatim from `Scratch.lean`). -/

/-- **Bridge 45.** Structural heart of Hadamard factorization: if two entire functions vanish to the
same order at every point, their quotient extends to a zero-free entire function. -/
theorem entire_quotient_of_analyticOrderAt_eq
    {f P : ℂ → ℂ} (hf : Differentiable ℂ f) (hP : Differentiable ℂ P)
    (hP0 : ∃ z₀, P z₀ ≠ 0)
    (horder : ∀ z, analyticOrderAt f z = analyticOrderAt P z) :
    ∃ Q : ℂ → ℂ, Differentiable ℂ Q ∧ (∀ z, Q z ≠ 0) ∧ ∀ z, f z = P z * Q z := by
  -- Analyticity of `f` and `P` at every point.
  have hfa : ∀ z, AnalyticAt ℂ f z := hf.analyticAt
  have hPa : ∀ z, AnalyticAt ℂ P z := hP.analyticAt
  -- The quotient `f / P` is meromorphic at every point.
  have hmero : ∀ z, MeromorphicAt (f / P) z := fun z =>
    (hfa z).meromorphicAt.div (hPa z).meromorphicAt
  -- `P` is not identically zero, so it never vanishes to infinite order (identity principle).
  have hPonNhd : AnalyticOnNhd ℂ P Set.univ := fun z _ => hPa z
  have hPnotTop : ∀ z, analyticOrderAt P z ≠ ⊤ := by
    intro z htop
    obtain ⟨z₀, hz₀⟩ := hP0
    have hev : P =ᶠ[𝓝 z] 0 := analyticOrderAt_eq_top.mp htop
    have : Set.EqOn P 0 Set.univ :=
      hPonNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero
        isPreconnected_univ (Set.mem_univ z) hev
    exact hz₀ (this (Set.mem_univ z₀))
  -- Its meromorphic order is `0` everywhere (orders cancel by `horder`).
  have horder0 : ∀ z, meromorphicOrderAt (f / P) z = 0 := by
    intro z
    rw [meromorphicOrderAt_div (hfa z).meromorphicAt (hPa z).meromorphicAt,
      (hfa z).meromorphicOrderAt_eq, (hPa z).meromorphicOrderAt_eq, horder z]
    exact LinearOrderedAddCommGroupWithTop.sub_self_eq_zero_of_ne_top
      (by rw [Ne, ENat.map_eq_top_iff]; exact hPnotTop z)
  -- Define `Q` as the meromorphic normal form of `f / P` on the whole plane.
  set Q : ℂ → ℂ := toMeromorphicNFOn (f / P) Set.univ with hQdef
  have hmeroOn : MeromorphicOn (f / P) Set.univ := fun z _ => hmero z
  -- `Q` agrees with `f / P` outside a discrete set; in particular its order is `0`.
  have hQorder : ∀ z, meromorphicOrderAt Q z = 0 := by
    intro z
    rw [hQdef, meromorphicOrderAt_toMeromorphicNFOn hmeroOn (Set.mem_univ z), horder0 z]
  -- `Q` is in normal form at every point, hence (order `0 ≥ 0`) analytic everywhere.
  have hQnf : ∀ z, MeromorphicNFAt Q z := fun z =>
    meromorphicNFOn_toMeromorphicNFOn (f / P) Set.univ (Set.mem_univ z)
  have hQa : ∀ z, AnalyticAt ℂ Q z := by
    intro z
    exact (hQnf z).meromorphicOrderAt_nonneg_iff_analyticAt.mp (by rw [hQorder z])
  -- `Q` is differentiable everywhere.
  have hQdiff : Differentiable ℂ Q := fun z => (hQa z).differentiableAt
  -- `Q` is zero-free: analytic with meromorphic order `0` means nonzero value.
  have hQne : ∀ z, Q z ≠ 0 := by
    intro z
    have hAorder : analyticOrderAt Q z = 0 := by
      have hmap := (hQa z).meromorphicOrderAt_eq
      rw [hQorder z] at hmap
      rw [eq_comm, ENat.map_natCast_eq_zero] at hmap
      exact hmap
    exact ((hQa z).analyticOrderAt_eq_zero).mp hAorder
  refine ⟨Q, hQdiff, hQne, ?_⟩
  -- Pointwise identity `f z = P z * Q z`.
  intro z
  by_cases hPz : P z = 0
  · -- At a zero of `P`: matching order forces `f z = 0`, and `P z * Q z = 0`.
    have hPorderne : analyticOrderAt P z ≠ 0 := (hPa z).analyticOrderAt_ne_zero.mpr hPz
    have hforderne : analyticOrderAt f z ≠ 0 := by rw [horder z]; exact hPorderne
    have hfz : f z = 0 := apply_eq_zero_of_analyticOrderAt_ne_zero hforderne
    rw [hfz, hPz, zero_mul]
  · -- Away from zeros of `P`: `Q =ᶠ f/P` on a punctured nbhd, so `P*Q =ᶠ f`; conclude by continuity.
    have hQeq : Q =ᶠ[𝓝[≠] z] (f / P) :=
      hmeroOn.toMeromorphicNFOn_eq_self_on_nhdsNE (Set.mem_univ z)
    have hPne_nhds : ∀ᶠ w in 𝓝 z, P w ≠ 0 :=
      (hPa z).continuousAt.eventually_ne hPz
    have hkey : (fun w => P w * Q w) =ᶠ[𝓝[≠] z] f := by
      filter_upwards [hQeq, hPne_nhds.filter_mono nhdsWithin_le_nhds] with w hw hPw
      rw [hw, Pi.div_apply, mul_div_cancel₀ _ hPw]
    have hcontPQ : ContinuousAt (fun w => P w * Q w) z :=
      ((hPa z).continuousAt).mul ((hQa z).continuousAt)
    have htends_val : Tendsto (fun w => P w * Q w) (𝓝[≠] z) (𝓝 (P z * Q z)) :=
      hcontPQ.continuousWithinAt.tendsto
    have htends_f : Tendsto (fun w => P w * Q w) (𝓝[≠] z) (𝓝 (f z)) :=
      ((hfa z).continuousAt.continuousWithinAt.tendsto).congr' hkey.symm
    exact (tendsto_nhds_unique htends_val htends_f).symm

/-! ## 2. `P_mult` is entire, from local-uniform multipliability of the genus-1 product.

`HasProdLocallyUniformlyOn f g univ` is *definitionally* `TendstoLocallyUniformlyOn (∏ i ∈ ·, f i ·)
g atTop univ` — the locally-uniform limit (along the `atTop` filter on `Finset XiZeroIndexMult`) of
the finite partial products. Those finite products are differentiable (finite product of entire
`genus1Factor`s), and `atTop` on a finset filter is `NeBot`, so Mathlib's
`TendstoLocallyUniformlyOn.differentiableOn` (locally-uniform limit of holomorphic functions is
holomorphic) gives `DifferentiableOn ℂ (∏' i, ·) univ`, i.e. `Differentiable ℂ P_mult`. -/

/-- From the locally-uniform multipliability of the genus-1 product over the multiplicity index,
`P_mult` is entire. -/
theorem differentiable_P_mult
    (hLU : MultipliableLocallyUniformlyOn
      (fun i : XiZeroIndexMult => fun s => genus1Factor (zeroLocMult i) s) Set.univ) :
    Differentiable ℂ P_mult := by
  -- The locally-uniform product equals `∏' i, ·`, as a `TendstoLocallyUniformlyOn` of finite
  -- partial products along `atTop`.
  have hHP : HasProdLocallyUniformlyOn
      (fun i : XiZeroIndexMult => fun s => genus1Factor (zeroLocMult i) s)
      (fun s => ∏' i, genus1Factor (zeroLocMult i) s) Set.univ :=
    hLU.hasProdLocallyUniformlyOn
  have hTLU : TendstoLocallyUniformlyOn
      (fun (t : Finset XiZeroIndexMult) (s : ℂ) => ∏ i ∈ t, genus1Factor (zeroLocMult i) s)
      (fun s => ∏' i, genus1Factor (zeroLocMult i) s) atTop Set.univ :=
    (hasProdLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn).mp hHP
  -- Each finite partial product is differentiable on `univ`.
  have hdiffOn : ∀ᶠ (t : Finset XiZeroIndexMult) in atTop,
      DifferentiableOn ℂ (fun s => ∏ i ∈ t, genus1Factor (zeroLocMult i) s) Set.univ := by
    refine Filter.Eventually.of_forall (fun t => ?_)
    exact DifferentiableOn.fun_finsetProd
      (fun i _ => (differentiable_genus1Factor (zeroLocMult i)).differentiableOn)
  -- Locally-uniform limit of holomorphic functions is holomorphic.
  have hP_mult_diffOn : DifferentiableOn ℂ
      (fun s => ∏' i, genus1Factor (zeroLocMult i) s) Set.univ :=
    hTLU.differentiableOn hdiffOn isOpen_univ
  rw [← differentiableOn_univ]
  exact hP_mult_diffOn

/-! ## 3. THE DELIVERABLE — the Hadamard quotient. -/

/-- **The Hadamard quotient (headline deliverable).**

Given the two proven structural outputs of `ScratchMultIndex.lean`, carried here as honest
hypotheses:

* `hLU` — local-uniform multipliability of the genus-1 product over the multiplicity index
  (`ScratchMultIndex.xiMult_genus1Product_LU`);
* `hOrder` — the everywhere `analyticOrderAt` match `P_mult ↔ ξ`
  (`ScratchMultIndex.xiMult_genus1Product_analyticOrderAt`);

there is an entire, zero-free `Q` with `ξ = P_mult · Q`. This is the Hadamard quotient: combined
with the quotient GROWTH (TASK #4/`ScratchQGrowth`) it yields `Q = C·exp(a+bs)`, hence the Hadamard
factorization. -/
theorem hadamard_quotient_entire_zeroFree
    (hLU : MultipliableLocallyUniformlyOn
      (fun i : XiZeroIndexMult => fun s => genus1Factor (zeroLocMult i) s) Set.univ)
    (hOrder : ∀ z, analyticOrderAt P_mult z = analyticOrderAt entireRiemannXi z) :
    ∃ Q : ℂ → ℂ, Differentiable ℂ Q ∧ (∀ z, Q z ≠ 0) ∧
      ∀ z, entireRiemannXi z = P_mult z * Q z := by
  -- Apply B45 with `f := ξ`, `P := P_mult`.
  refine entire_quotient_of_analyticOrderAt_eq
    (f := entireRiemannXi) (P := P_mult)
    differentiable_entireRiemannXi (differentiable_P_mult hLU)
    ⟨0, P_mult_zero_ne⟩ (fun z => ?_)
  -- B45 wants `analyticOrderAt ξ z = analyticOrderAt P_mult z`; `hOrder` is the symmetric form.
  exact (hOrder z).symm

/-- **Self-contained packaging.** Same deliverable, but the two structural inputs are stated in the
exact shapes produced by `ScratchMultIndex.lean`:

* `hLU` : `xiMult_genus1Product_LU` (local-uniform multipliability over the multiplicity index);
* `hMatch` : `xiMult_genus1Product_analyticOrderAt`, the order match written with the explicit
  `∏' i, genus1Factor (zeroLocMult i) s` (definitionally `P_mult`).

This corollary exists to make the wiring to `ScratchMultIndex` literally typecheck:
`hMatch` is `ScratchMultIndex.xiMult_genus1Product_analyticOrderAt htail` and `hLU` is
`ScratchMultIndex.xiMult_genus1Product_LU hMult` (modulo the verbatim re-copy of the defs). -/
theorem hadamard_quotient_of_multIndex_data
    (hLU : MultipliableLocallyUniformlyOn
      (fun i : XiZeroIndexMult => fun s => genus1Factor (zeroLocMult i) s) Set.univ)
    (hMatch : ∀ z : ℂ,
      analyticOrderAt (fun s => ∏' i : XiZeroIndexMult, genus1Factor (zeroLocMult i) s) z
        = analyticOrderAt entireRiemannXi z) :
    ∃ Q : ℂ → ℂ, Differentiable ℂ Q ∧ (∀ z, Q z ≠ 0) ∧
      ∀ z, entireRiemannXi z = P_mult z * Q z :=
  -- `P_mult` is definitionally `fun s => ∏' i, genus1Factor (zeroLocMult i) s`, so `hMatch`
  -- is exactly `hOrder`.
  hadamard_quotient_entire_zeroFree hLU hMatch

#print axioms hadamard_quotient_entire_zeroFree
#print axioms hadamard_quotient_of_multIndex_data
#print axioms differentiable_P_mult

end OverflowResidueRH.BacklundTuring.ScratchQuotientClose
