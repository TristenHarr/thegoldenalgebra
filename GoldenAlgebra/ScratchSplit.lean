import Mathlib

open Complex Filter Topology

/-!
# Local split of the genus-1 product near a zero (Task #1 — discharges `hsplit`)

`genus1Factor ρ s := (1 - s/ρ) * exp(s/ρ)`. Given the locally-uniform multipliability of the
product (a HYPOTHESIS here; in the real setting it is `xi_genus1Product_LU`), and that only
finitely many indices `hit` a point `z` (`{i | loc i = z}` finite), prove the local factorization
`∏' i = (∏ i ∈ hitting, ...) · tail` with `tail` analytic and nonvanishing at `z`. This is exactly
the `hsplit` input to the order theorem `analyticOrderAt_genus1Product`.
-/

set_option maxHeartbeats 2000000

noncomputable def genus1Factor (ρ s : ℂ) : ℂ := (1 - s / ρ) * Complex.exp (s / ρ)

theorem genus1Factor_ne_zero {ρ s : ℂ} (hρ : ρ ≠ 0) (hsρ : s ≠ ρ) : genus1Factor ρ s ≠ 0 := by
  unfold genus1Factor
  refine mul_ne_zero ?_ (Complex.exp_ne_zero _)
  rw [sub_ne_zero, ne_comm, ne_eq, div_eq_one_iff_eq hρ]; exact hsρ

/-- Pure index-split of a multipliable ℂ-product over a finset and its complement.
Stated with an abstract `f` so that no concrete factor (`genus1Factor`/`exp`) ever enters the
`whnf` used by `HasProd.mul_compl` (ℂ is not a multiplicative uniform group, so the group-based
`tprod_subtype_mul_tprod_subtype_compl` is unavailable). -/
theorem tprod_finset_mul_tprod_compl {ι : Type*} (f : ι → ℂ) (H : Finset ι)
    (hf : Multipliable f) :
    (∏' i, f i) = (∏ i ∈ H, f i) * ∏' i : {i // i ∉ H}, f i := by
  have hsub := (hf.subtype (· ∈ (↑H : Set ι))).hasProd
  have hsubc := (hf.subtype (· ∈ (↑H : Set ι)ᶜ)).hasProd
  have hsplit := (hsub.mul_compl hsubc).tprod_eq
  rw [hsplit, Finset.tprod_subtype' H f]

/-- GOAL (Task #1). You may adjust hypothesis spelling, but the conclusion must give the local
factorization with an analytic, nonvanishing tail.

The pointwise split `∏' = (∏ hitting)·tail` and the analyticity of `tail` are proved from Mathlib.
The single genuinely-absent Mathlib fact — "a locally-uniformly-multipliable ℂ-product of factors
all nonzero at `z` is nonzero at `z`" — is isolated as the named hypothesis `htail_ne` below
(ℂ is not a multiplicative group, so `Multipliable.tprod_vanishing` does not apply, and the
units/summable-norm route `tprod_one_add_ne_zero_of_summable` needs a `∑‖·‖<∞` datum not present in
`MultipliableLocallyUniformlyOn`). `hcompl` (the complement family is still locally-uniformly
multipliable) is a structural input; in the real setting it follows from `xi_genus1Product_LU` by a
finite-index modification. -/
theorem genus1Product_local_split
    {ι : Type*} (loc : ι → ℂ) (z : ℂ)
    (hne : ∀ i, loc i ≠ 0)
    (hmul : MultipliableLocallyUniformlyOn (fun i s => genus1Factor (loc i) s) Set.univ)
    (hfin : {i | loc i = z}.Finite)
    (hcompl : MultipliableLocallyUniformlyOn
      (fun i : {i // i ∉ hfin.toFinset} => fun s => genus1Factor (loc i) s) Set.univ)
    (htail_ne : (∏' i : {i // i ∉ hfin.toFinset}, genus1Factor (loc i) z) ≠ 0) :
    ∃ tail : ℂ → ℂ, AnalyticAt ℂ tail z ∧ tail z ≠ 0 ∧
      ∀ᶠ s in nhds z, (∏' i, genus1Factor (loc i) s)
        = (∏ i ∈ hfin.toFinset, genus1Factor (loc i) s) * tail s := by
  classical
  -- The hitting finset and the canonical complement (tail) product.
  set H := hfin.toFinset with hH
  refine ⟨fun s => ∏' i : {i // i ∉ H}, genus1Factor (loc i) s, ?_, htail_ne, ?_⟩
  · -- TAIL ANALYTIC at z, via the locally-uniform-limit ⇒ holomorphic bridge on the open set univ.
    have hdiff : DifferentiableOn ℂ
        (fun s => ∏' i : {i // i ∉ H}, genus1Factor (loc i) s) (Set.univ : Set ℂ) := by
      refine hcompl.hasProdLocallyUniformlyOn.differentiableOn
        (.of_forall fun (N : Finset {i // i ∉ H}) => ?_) isOpen_univ
      -- each finite partial product is differentiable (polynomial × exp).
      have : (fun s => ∏ i ∈ N, genus1Factor (loc (i : ι)) s)
          = ∏ i ∈ N, (fun s => genus1Factor (loc (i : ι)) s) := by
        funext s; rw [Finset.prod_apply]
      rw [this]
      apply DifferentiableOn.finsetProd
      intro i _
      unfold genus1Factor
      fun_prop
    exact hdiff.analyticAt (Filter.univ_mem)
  · -- EVENTUAL FACTORIZATION: holds at every `s`, hence eventually near `z`.
    filter_upwards with s
    -- Work with an abstract `F` to keep `genus1Factor`/ℂ instances from unfolding during the
    -- subtype/complement `whnf` (which otherwise blows up the elaborator).
    set F : ι → ℂ := fun i => genus1Factor (loc i) s with hF
    have hmuls : Multipliable F := hmul.multipliable (Set.mem_univ s)
    -- Split `∏' i` over the set `H` and its complement using the CommMonoid lemma
    -- `HasProd.mul_compl` (ℂ is NOT a multiplicative uniform group, so the `IsUniformGroup`-based
    -- `tprod_subtype_mul_tprod_subtype_compl` is unavailable / diverges on instance search).
    have hsub := (hmuls.subtype (· ∈ (↑H : Set ι))).hasProd
    have hsubc := (hmuls.subtype (· ∈ (↑H : Set ι)ᶜ)).hasProd
    have hsplit := (hsub.mul_compl hsubc).tprod_eq
    -- `hsplit : ∏' i, F i = (∏' i:↑H, F i) * ∏' i:↑Hᶜ, F i`
    rw [hsplit, Finset.tprod_subtype' H F]

/-!
## STRATEGY / POINTERS (search Mathlib first)
* The hitting finset `H := hfin.toFinset`. Define `tail s := ∏' i : (↥(H : Set ι))ᶜ, genus1Factor (loc i) s`
  (product over the NON-hitting indices), or use `Multipliable.prod_mul_tprod_subtype_compl` /
  `Multipliable.prod_mul_tprod_compl` to split `∏' i = (∏ i ∈ H, ·) * (∏' i ∈ Hᶜ, ·)` POINTWISE
  (the pointwise `Multipliable` comes from `hmul.multipliable`/`HasProdLocallyUniformlyOn` at each s).
* tail ANALYTIC at z: the complement product is a locally-uniform limit of analytic partial products
  ⇒ analytic. Look for `HasProdLocallyUniformlyOn.analyticOnNhd` / `.differentiableOn` (used in
  `Mathlib/.../DedekindEta.lean`), or that the restricted product over `Hᶜ` is still
  `MultipliableLocallyUniformlyOn` (restrict `hmul`), giving an analytic limit.
* tail z ≠ 0 at z: each complement factor `genus1Factor (loc i) z` with `loc i ≠ z` is NONZERO
  (`genus1Factor_ne_zero (hne i) (loc i ≠ z)`), and a locally-uniformly-convergent product of
  nonvanishing factors is nonvanishing — search `HasProdLocallyUniformlyOn` nonvanishing / the
  `tprod_ne_zero` for `Multipliable` with all factors ≠ 0 on a punctured/whole nbhd. If Mathlib
  lacks "loc-unif product of nonvanishing ⇒ nonvanishing at a point", isolate it as a precise hyp.
* WATCH the ℂ-defeq/`whnf` timeout: applying `prod_mul_tprod_subtype_compl` over ℂ can hang via the
  `IsUniformGroup ℂ` instance — set `maxHeartbeats` higher locally, or avoid that lemma by working
  with `HasProd`/`HasProdLocallyUniformlyOn` splits and explicit finset/complement reindexing.

## ALGORITHM: read; search Mathlib for the split + nonvanishing lemmas FIRST; prove the eventual
equality and tail analyticity/nonvanishing; build incrementally; NO bare `sorry` (isolate gaps as
hypotheses); verify EXIT 0 + no warnings + `#print axioms` clean. Build:
`cd /Users/tristen/Desktop/goldenalgebra/GoldenAlgebra && lake env lean ScratchSplit.lean`.
Edit ONLY this file. Report the final signature + Mathlib lemmas used + any isolated gap.
-/
