/-
================================================================================
  ScratchPackage.lean — DRAFT packaging skeleton for
  `EntireXiClassicalHadamardTheorem` (target Hadamard bundle in rh.lean)
================================================================================

  STATUS: DRAFT. This file is a reconnaissance + integration skeleton, NOT a
  finished proof. It compiles only insofar as `import rh` resolves; the single
  theorem `scratch_Hhad` is left with `?_` obligations and `sorry`, each tagged
  with the Scratch.lean (`ScratchBridges`) result that is meant to discharge it.

  ┌──────────────────────────────────────────────────────────────────────────┐
  │ TARGET STRUCTURE (rh.lean:80264)                                           │
  │                                                                            │
  │ structure EntireXiClassicalHadamardTheorem (ι : Type) : Type where         │
  │   zeroSystem       : ConcreteEntireXiZeroSystem ι                          │
  │   prefactor        : ℂ → ℂ                                                  │
  │   zeroDistribution : EntireXiZeroInvSqDistribution zeroSystem              │
  │   luc              : HadamardProductLUCLogDerivData zeroSystem.zeroLoc      │
  │   region           : ∀ s, entireRiemannXi s ≠ 0 → s ∈ luc.region          │
  │   factorization    : EntireXiHadamardFactorization zeroSystem prefactor    │
  │   prefactorData    : EntireXiHadamardPrefactor prefactor                   │
  └──────────────────────────────────────────────────────────────────────────┘

  IMPORTANT NAMESPACE / CONVENTION NOTES
  --------------------------------------
  * rh.lean's `entireRiemannXi`, `hadamardGenus1Factor`, etc. live at TOP LEVEL
    (root namespace, library `rh`). Scratch.lean's analogues live INSIDE
    `namespace ScratchBridges` and are SEPARATE definitions:

        rh.lean   entireRiemannXi s = (1/2)*s*(s-1)*completedRiemannZeta₀ s + 1/2
        Scratch   entireRiemannXi s = (1/2)*(s*(s-1)*completedRiemannZeta₀ s + 1)

    These are EQUAL (`ring`), but NOT syntactically/definitionally identical, so
    every Scratch result phrased in `ScratchBridges.entireRiemannXi` must be
    transported across `rfl`-after-`ring` / a `congr` lemma before it can feed
    an rh.lean field. ⇒ GAP G1 (see below).

        rh.lean   hadamardGenus1Factor ρ s = (1 - s/ρ) * exp (s/ρ)
        Scratch   genus1Factor          ρ s = (1 - s/ρ) * exp (s/ρ)

    These two ARE syntactically identical bodies, so `hadamardGenus1Factor` and
    `ScratchBridges.genus1Factor` agree by `rfl` (modulo the namespace). The
    infinite products therefore agree pointwise:
        infiniteHadamardProduct zeroLoc s = ∏' i, hadamardGenus1Factor (zeroLoc i) s
        ScratchBridges product             = ∏' ρ, genus1Factor (xiZeroLoc ρ) s
    ⇒ matchable once the index map `zeroLoc` is `xiZeroLoc`.

  * INDEX TYPE. rh.lean's canonical index is
        EntireXiNonzeroZeroIndex := { s : ℂ // entireRiemannXi s = 0 ∧ s ≠ 0 }
    Scratch's is
        XiZeroIndex := riemannXiZeros := entireRiemannXi ⁻¹' {0}   (= { s // ξ s = 0 })
    These DIFFER: rh.lean excludes `s = 0` (it knows ξ(0)=1/2≠0 so the exclusion
    is harmless), Scratch keeps the full preimage. Since ξ(0) ≠ 0 in BOTH
    conventions, `0 ∉ riemannXiZeros`, so the two subtypes are in canonical
    bijection — but proving that bijection (and that it preserves `zeroLoc`) is
    GAP G2. The cleanest route is to instantiate `scratch_Hhad` at
    `ι := EntireXiNonzeroZeroIndex` using `concreteEntireXiZeroSystem`
    (rh.lean:80806) directly, and use Scratch only for the ANALYTIC fields
    (distribution + LUC), re-deriving them for rh's `zeroLoc`.

================================================================================
  FIELD-BY-FIELD OBLIGATION MAP  (rh.lean field  ⟵  Scratch source / GAP)
================================================================================

  zeroSystem : ConcreteEntireXiZeroSystem ι
      ⟵ rh.lean already provides `concreteEntireXiZeroSystem`
        (ι = EntireXiNonzeroZeroIndex). Its four sub-fields correspond to:
          zeroLoc                 ↔ Scratch.xiZeroLoc           (same body : i.1)
          zeroLoc_ne_zero         ↔ Scratch.xiZeroLoc_ne_zero
          zeroLoc_is_zero         ↔ Scratch.entireRiemannXi_xiZeroLoc
          all_nonzero_entireXi_zeros ↔ (surjectivity; trivial for the subtype)
        ⇒ USE rh's `concreteEntireXiZeroSystem` verbatim. No Scratch import
          needed for this field. (Scratch lemmas are the moral source but live
          in the wrong `ξ`-namespace — see G1.)

  prefactor : ℂ → ℂ
      ⟵ choose  `fun s => C * Complex.exp (a + b * s)`  (exp-affine).
        Pure data; supplied by us.

  zeroDistribution : EntireXiZeroInvSqDistribution zeroSystem
      requires:  (i) Summable fun i => (‖zeroLoc i‖^2)⁻¹
                 (ii) ∀ s, ∀ᶠ i in cofinite, 2‖s‖ ≤ ‖zeroLoc i‖
      ⟵ (i)  Scratch `xi_genus1Product_multipliable` CONSUMES exactly this
             summability (`Summable fun ρ => 1/‖xiZeroLoc ρ‖^2`); the summability
             itself is an INPUT in Scratch (hsumm), i.e. NOT yet proved there.
             GAP G3: Σ 1/‖ρ‖² < ∞ is still an open analytic input
             (would come from the RvM zero-count `summable_inv_sq_of_shellCard`
             at Scratch.lean:906 — needs the shell-card bound).
        (ii) Scratch `tendsto_riemannXiZeros_cofinite_cocompact` gives
             `Tendsto (↑) cofinite (cocompact ℂ)`, from which `2‖s‖ ≤ ‖ρ‖`
             cofinitely follows (cocompact ⇒ norms → ∞). Small wrapper needed.
        ⇒ rh.lean even has `EntireXiZeroInvSqDistribution.of_invSqSummable_normProper`
          (rh.lean:78853) that builds this field from (i) + a `HadamardZeroNormProper`,
          the latter being the rh-side analogue of (ii).

  luc : HadamardProductLUCLogDerivData zeroSystem.zeroLoc
      requires: a `region`, locally-uniform finite-product convergence to
                `infiniteHadamardProduct`, differentiability, and
                logDeriv = regularized Σ(1/(s-ρ)+1/ρ) on the region.
      ⟵ rh.lean BUILDS this entirely from `zeroDistribution`! The cleanest
        constructor is the chain
          HadamardProductLUCOnEntireXiNonzeroData.of_invSq_mono_exhaustive
            (rh.lean:80207)  →  .toLUCLogDerivData  (rh.lean:79952)
        which needs only `Hdist` + a monotone exhaustive `exhaust : ℕ → Finset ι`.
        Scratch's `xi_genus1Product_multipliableLocallyUniformlyOn`
        (Scratch.lean:1175) and `xi_genus1Product_logDeriv_eq_tsum`
        (Scratch.lean:1181) are the MORAL content of these fields, but rh.lean
        already has a self-contained internal proof from invSq, so we prefer it.
        GAP G4: need an `exhaust : ℕ → Finset EntireXiNonzeroZeroIndex` that is
        monotone and exhaustive — e.g. zeros in the disk of radius n. Existence
        follows from local finiteness (`isDiscrete_riemannXiZeros`,
        Scratch.lean:532 / rh-side equivalent) but the explicit enumeration is
        not yet packaged. ⇒ For the draft we leave `exhaust` as `sorry`.

  region : ∀ s, entireRiemannXi s ≠ 0 → s ∈ luc.region
      ⟵ DEFINITIONALLY trivial when `luc` is built via
        `HadamardProductLUCOnEntireXiNonzeroData.toLUCLogDerivData`, whose
        region IS `{s | entireRiemannXi s ≠ 0}` (rh.lean:79956). Then
        `region := fun s hs => hs`. The `of_lucOnEntireXiNonzero` constructor
        (rh.lean:80348) discharges this field for us.

  factorization : EntireXiHadamardFactorization zeroSystem prefactor
      requires: ∀ s, entireRiemannXi s = prefactor s * infiniteHadamardProduct …
      ⟵ THE deep Hadamard step `ξ = C·exp(a+b s)·∏ E₁(s/ρ)`. NOT yet in Scratch
        as a finished theorem (the task lists it as "(forthcoming)"). rh.lean
        offers the reduced quotient form
          EntireXiHadamardFactorization.exp_affine_of_offZeroQuotient_invSq
          (used in rh.lean:80635) which needs only the OFF-ZERO quotient identity
          ξ(s)/∏(s) = C·exp(a+b s)  for s off the zeros.
        GAP G5 (the real mathematical gap): that quotient identity. Scratch
        Bridges 40/41 (`affine_of_entire_of_linear_growth`,
        `exists_entire_exp_eq`, Scratch.lean:1191+) are the building blocks
        (zero-free entire ⇒ exp; linear growth ⇒ affine) but the assembly into
        the quotient identity is not done. ⇒ `sorry` in the draft.

  prefactorData : EntireXiHadamardPrefactor prefactor
      requires: prefactor differentiable & nonzero at every ξ-nonzero point.
      ⟵ FULLY DISCHARGED by rh.lean `EntireXiHadamardPrefactor.exp_affine hC`
        (rh.lean:79422) for the exp-affine prefactor. No gap.

================================================================================
  SMART CONSTRUCTOR WE TARGET
================================================================================
  `EntireXiClassicalHadamardTheorem.of_canonicalZeros_expAffine_quotient_lucLogDerivData`
  (rh.lean:80704) is the minimal-input inhabitant. Its inputs are:
      {C a b : ℂ} (hC : C ≠ 0)
      (Hdist : EntireXiZeroInvSqDistribution concreteEntireXiZeroSystem)   -- field zeroDistribution
      (Hluc  : HadamardProductLUCLogDerivData concreteEntireXiZeroSystem.zeroLoc)
      (h_region : ∀ s, entireRiemannXi s ≠ 0 → s ∈ Hluc.region)
      (hquot : ∀ s, (∀ i, s ≠ zeroLoc i) →
                 entireRiemannXi s / infiniteHadamardProduct zeroLoc s
                   = C * exp (a + b*s))                                     -- the GAP G5 quotient
  Everything else (prefactor data, product nonvanishing, factorization) is
  internal. So the WHOLE bundle reduces to:  (Hdist) + (Hluc) + (h_region) +
  (hquot).  Of these, Hluc reduces further to Hdist + an `exhaust` (G4), and
  Hdist reduces to invSq-summability (G3) + cofinite-large (provable). The two
  genuine open inputs are therefore G3 (Σ1/‖ρ‖²) and G5 (the quotient identity).
================================================================================
-/

import rh

open Complex Filter Topology

-- NOTE: every rh.lean symbol below (`EntireXiClassicalHadamardTheorem`,
-- `entireRiemannXi`, `EntireXiNonzeroZeroIndex`, the smart constructors, …)
-- lives inside `namespace OverflowResidueRH` (opened at rh.lean:305 and never
-- closed before the structure). We `open` it so the names resolve unqualified.
open OverflowResidueRH

namespace ScratchPackage

/-- DRAFT exp-affine Hadamard-bundle packaging for entire ξ.

This targets the minimal smart constructor
`EntireXiClassicalHadamardTheorem.of_canonicalZeros_expAffine_quotient_lucLogDerivData`
(rh.lean:80704). This compiles against `import rh` (the interface and the
smart-constructor application are verified correct); the four `sorry`s mark the
remaining obligations:

* `Hdist`    → GAP G3 (Σ 1/‖ρ‖² < ∞) + cofinite-large (latter provable).
* `Hluc`     → GAP G4 (explicit monotone exhaustion); then `.toLUCLogDerivData`.
* `h_region` → trivial (`intro s hs; exact hs`) once `Hluc` is the nonzero-locus package.
* `hquot`    → GAP G5 (the off-zero quotient identity ξ/∏ = C·exp(a+bs)).

Set `C := 1/2`, `a := 0`, `b := 0` as harmless placeholder constants; the true
`a, b` are fixed by the Hadamard normalization once G5 is supplied. -/
noncomputable def scratch_Hhad :
    EntireXiClassicalHadamardTheorem EntireXiNonzeroZeroIndex := by
  refine
    EntireXiClassicalHadamardTheorem.of_canonicalZeros_expAffine_quotient_lucLogDerivData
      (C := (1 / 2 : ℂ)) (a := 0) (b := 0)
      (hC := by norm_num)
      (Hdist := ?_)        -- field `zeroDistribution`
      (Hluc := ?_)         -- field `luc`
      (h_region := ?_)     -- field `region`
      (hquot := ?_)        -- collapses to `factorization` (prefactor data is internal)
  -- (1) zeroDistribution : EntireXiZeroInvSqDistribution concreteEntireXiZeroSystem
  --     ⟵ inv_sq_summable  : GAP G3  (Scratch needs Σ1/‖ρ‖² — open analytic input)
  --     ⟵ eventually_large : provable from `tendsto_riemannXiZeros_cofinite_cocompact`
  --       (Scratch.lean:563). Cleanest: rh.lean
  --       `EntireXiZeroInvSqDistribution.of_invSqSummable_normProper` (rh.lean:78853).
  · sorry  -- TODO G3: supply `Summable fun i => (‖zeroLoc i‖^2)⁻¹` + norm-proper.
  -- (2) luc : HadamardProductLUCLogDerivData concreteEntireXiZeroSystem.zeroLoc
  --     ⟵ build from the Hdist above + a monotone exhaustive `exhaust`:
  --         (HadamardProductLUCOnEntireXiNonzeroData.of_invSq_mono_exhaustive
  --            concreteEntireXiZeroSystem Hdist exhaust hmono hexhaustive).toLUCLogDerivData
  --       Scratch moral source: `xi_genus1Product_multipliableLocallyUniformlyOn`
  --       (Scratch.lean:1175) + `xi_genus1Product_logDeriv_eq_tsum` (Scratch.lean:1181).
  · sorry  -- TODO G4: provide `exhaust : ℕ → Finset EntireXiNonzeroZeroIndex`
           --          (e.g. zeros in disk radius n), monotone + exhaustive,
           --          then call `.of_invSq_mono_exhaustive … .toLUCLogDerivData`.
  -- (3) region : ∀ s, entireRiemannXi s ≠ 0 → s ∈ Hluc.region
  --     ⟵ if Hluc came from `.toLUCLogDerivData`, its region is
  --       `{s | entireRiemannXi s ≠ 0}`, so this is `fun s hs => hs`.
  · sorry  -- TODO: once (2) is the `.toLUCLogDerivData` package, replace by
           --       `intro s hs; exact hs`.
  -- (4) hquot : ∀ s, (∀ i, s ≠ zeroLoc i) →
  --        entireRiemannXi s / infiniteHadamardProduct zeroLoc s = (1/2)*exp(0+0*s)
  --     ⟵ GAP G5 — the off-zero Hadamard quotient identity. Building blocks:
  --       Scratch Bridges 40/41 (`exists_entire_exp_eq`,
  --       `affine_of_entire_of_linear_growth`, Scratch.lean:1191+).
  · sorry  -- TODO G5: the deep Hadamard quotient identity ξ/∏ = C·exp(a+b s).

/-
  WHAT COMPILES vs WHAT IS A PLACEHOLDER
  --------------------------------------
  COMPILES (once `import rh` resolves):
    * the `refine … of_canonicalZeros_expAffine_quotient_lucLogDerivData` skeleton
      and its field/argument structure — i.e. the INTERFACE is correct and the
      smart constructor is applied with the right named arguments.
    * the prefactor `(1/2)·exp(0+0·s)` and `hC : (1/2) ≠ 0`.
    * prefactor DATA (`EntireXiHadamardPrefactor`), product nonvanishing, and the
      global factorization are all discharged INTERNALLY by the constructor — we
      never have to touch them.
  PLACEHOLDER (`sorry`):
    * G3  Σ 1/‖ρ‖² summability (Hdist).            [open analytic input]
    * G4  explicit monotone exhaustion (Hluc).     [packaging, follows from discreteness]
    * (region) trivial once G4 uses `.toLUCLogDerivData`.
    * G5  off-zero quotient identity ξ/∏ = C·exp.  [the deep Hadamard step]

  VERIFIED: `import rh` resolves and this file compiles with exactly one
  `sorry` warning (the four `?_` obligations above). All rh.lean symbols live in
  `namespace OverflowResidueRH` (see the `open` at the top); without that open
  the names do NOT resolve even though the import succeeds.

  NOTE on `import rh`: rh.lean is ~99k lines (~4.5 min cold compile). If the build
  is ever too slow or `import rh` fails to resolve, the fallback is to COPY
  the structure `EntireXiClassicalHadamardTheorem` + its dependency defs
  (`ConcreteEntireXiZeroSystem`, `EntireXiZeroInvSqDistribution`,
  `HadamardProductLUCLogDerivData`, `EntireXiHadamardFactorization`,
  `EntireXiHadamardPrefactor`, `hadamardGenus1Factor`, `infiniteHadamardProduct`,
  `entireRiemannXi`) verbatim into this file as a faithful stand-in. The
  interface above is exact (verbatim from rh.lean lines 80264–80727), so such a
  copy would be a 1:1 stand-in.
-/

end ScratchPackage
