import rh

/-!
# ScratchAP_GlobalFactor: closing the `GlobalOrderFactorization` gap from AP1

`ScratchAP_SingleZero.lean` proves the single-zero residue identity

    `∮_{∂R} f'/f = 2πi·m`

*conditional* on a structure `GlobalOrderFactorization R f g a m` asserting a
**global** factorization `f = (· - a)^m · g` on a neighborhood of the closed
rectangle, with `g` analytic and non-vanishing on the closed rectangle, and `a`
strictly interior.

This file **constructs** that structure from the natural local hypotheses:

* `f` is analytic at every point of the closed rectangle
  (`hf_an : ∀ z ∈ closedRect, AnalyticAt ℂ f z`);
* `a` is strictly interior (`ha : R.ContainsOpen a`);
* `f` has an order-`m` zero at `a`
  (`horder : analyticOrderAt f a = (m : ℕ∞)`);
* `f` has **no other** zeros on the closed rectangle
  (`hf_ne : ∀ z ∈ closedRect, z ≠ a → f z ≠ 0`).

## Construction

Mathlib's `AnalyticAt.analyticOrderAt_eq_natCast` gives a **local** cofactor `h`
analytic at `a` with `h a ≠ 0` and `f =ᶠ[𝓝 a] fun z => (z - a)^m • h z`.

Define the **global** cofactor by

    `g z := if z = a then h a else f z / (z - a)^m`.

* **Analytic at `a`** (removable singularity): whenever `f z = (z - a)^m • h z`
  we have `g z = h z` (for `z = a` directly by definition; for `z ≠ a` because
  `f z / (z - a)^m = (z - a)^m * h z / (z - a)^m = h z`).  So `g =ᶠ[𝓝 a] h` and
  `g` is analytic at `a` by `AnalyticAt.congr`.
* **Analytic away from `a`** (on the rectangle): near such `z`, `w ≠ a`
  (open condition), so `g =ᶠ[𝓝 z] f / (· - a)^m`, which is analytic since `f` is
  analytic and `(· - a)^m` is analytic and nonzero at `z`.
* **Non-vanishing:** at `a`, `g a = h a ≠ 0`; away from `a` on the rectangle,
  `g z = f z / (z - a)^m` with `f z ≠ 0` (no other zeros) and `(z - a)^m ≠ 0`.
* **Global factorization `f = (· - a)^m * g`:** for `z ≠ a`,
  `(z - a)^m * (f z / (z - a)^m) = f z` algebraically; at `z = a`, the local
  `eventuallyEq` evaluated at `a` gives `f a = (a - a)^m • h a = (a - a)^m * g a`.

No genuine gap remains: every step is discharged from Mathlib + `rh.lean`.  The
only structural caveat is that `GlobalOrderFactorization` lives in the scratch
file `ScratchAP_SingleZero.lean`, which is **not** a library target and cannot be
imported.  We therefore **re-declare** an identical structure locally
(`GlobalOrderFactorization`, same four fields) and target it; the field
signatures match `ScratchAP_SingleZero.GlobalOrderFactorization` verbatim, so the
constructed term plugs directly into AP1 once that file imports this one.
-/

open Complex
open scoped Real Topology

namespace OverflowResidueRH
namespace BacklundTuring
namespace ScratchAPGlobalFactor

open ZetaRectangle

/-! ## The target structure (re-declared identically to the one in
`ScratchAP_SingleZero.lean`, which is not importable). -/

/-- **Global order-`m` factorization on the closed rectangle.**  Identical to the
structure `OverflowResidueRH.BacklundTuring.ScratchAPSingleZero.GlobalOrderFactorization`;
re-declared here because that scratch file is not a library target. -/
structure GlobalOrderFactorization
    (R : ZetaRectangle) (f g : ℂ → ℂ) (a : ℂ) (m : ℕ) : Prop where
  /-- `a` lies strictly inside the rectangle. -/
  interior : R.ContainsOpen a
  /-- The global factorization `f = (· - a)^m · g`. -/
  factor : f = fun z => (z - a) ^ m * g z
  /-- `g` is analytic at every point of the closed rectangle. -/
  g_analytic : ∀ z ∈ {z : ℂ | R.ContainsClosed z}, AnalyticAt ℂ g z
  /-- `g` does not vanish on the closed rectangle. -/
  g_ne_zero : ∀ z ∈ {z : ℂ | R.ContainsClosed z}, g z ≠ 0

/-! ## A small geometric fact: the interior point is in the closed rectangle. -/

/-- A strictly-interior point lies in the closed rectangle. -/
theorem containsClosed_of_containsOpen {R : ZetaRectangle} {a : ℂ}
    (ha : R.ContainsOpen a) : R.ContainsClosed a :=
  ⟨le_of_lt ha.1, le_of_lt ha.2.1, le_of_lt ha.2.2.1, le_of_lt ha.2.2.2⟩

/-! ## The construction. -/

/-- **The global cofactor**, defined from the local Mathlib cofactor `h` at the
zero by `g z = if z = a then h a else f z / (z - a)^m`.  This is the analytic
continuation of `f / (· - a)^m` across the removable singularity at `a`. -/
noncomputable def globalCofactor (f : ℂ → ℂ) (a : ℂ) (m : ℕ) (h : ℂ → ℂ) : ℂ → ℂ :=
  fun z => if z = a then h a else f z / (z - a) ^ m

/-- **Main construction.**  From an interior order-`m` zero at `a` with no other
zeros on the closed rectangle (and `f` analytic on the closed rectangle), build
the global order-`m` factorization with cofactor `globalCofactor f a m h`, where
`h` is Mathlib's local cofactor at the zero. -/
noncomputable def globalOrderFactorization_of_isolatedZero
    (R : ZetaRectangle) (f : ℂ → ℂ) (a : ℂ) (m : ℕ)
    (ha : R.ContainsOpen a)
    (hf_an : ∀ z ∈ {z : ℂ | R.ContainsClosed z}, AnalyticAt ℂ f z)
    (horder : analyticOrderAt f a = (m : ℕ∞))
    (hf_ne : ∀ z ∈ {z : ℂ | R.ContainsClosed z}, z ≠ a → f z ≠ 0) :
    GlobalOrderFactorization R f
      (globalCofactor f a m
        (((hf_an a (containsClosed_of_containsOpen ha)).analyticOrderAt_eq_natCast).mp
          horder).choose)
      a m := by
  classical
  -- `a` is in the closed rectangle.
  have haClosed : a ∈ {z : ℂ | R.ContainsClosed z} := containsClosed_of_containsOpen ha
  have hfa : AnalyticAt ℂ f a := hf_an a haClosed
  -- Mathlib local factorization at the zero: `f =ᶠ[𝓝 a] (· - a)^m • h`, `h a ≠ 0`.
  set spec := (hfa.analyticOrderAt_eq_natCast.mp horder) with hspec
  set h : ℂ → ℂ := spec.choose with hh
  obtain ⟨hh_an, hh_ne, hh_eq⟩ := spec.choose_spec
  -- The global cofactor.
  set g : ℂ → ℂ := globalCofactor f a m h with hg
  -- `g a = h a`.
  have hg_at_a : g a = h a := by simp [hg, globalCofactor]
  -- KEY removable-singularity fact: wherever `f z = (z - a)^m • h z`, `g z = h z`.
  have hg_eq_h_of : ∀ z, f z = (z - a) ^ m • h z → g z = h z := by
    intro z hz
    by_cases hza : z = a
    · simp [hg, globalCofactor, hza]
    · have hsub : z - a ≠ 0 := sub_ne_zero.mpr hza
      have hpow : (z - a) ^ m ≠ 0 := pow_ne_zero m hsub
      simp only [hg, globalCofactor, if_neg hza]
      rw [hz, smul_eq_mul, mul_comm, mul_div_assoc, div_self hpow, mul_one]
  -- Near `a`, `g` agrees with `h` (removable singularity), hence analytic at `a`.
  have hg_eqOn_a : g =ᶠ[𝓝 a] h := hh_eq.mono hg_eq_h_of
  have hg_an_a : AnalyticAt ℂ g a := hh_an.congr hg_eqOn_a.symm
  -- Global factorization `f = (· - a)^m * g`.
  have hfactor : f = fun z => (z - a) ^ m * g z := by
    funext z
    by_cases hza : z = a
    · -- At `a`: use the local eventuallyEq at the point.
      rw [hza]
      have hfa_val : f a = (a - a) ^ m • h a := hh_eq.self_of_nhds
      rw [hfa_val, hg_at_a, smul_eq_mul]
    · -- Away from `a`: `g z = f z / (z - a)^m`, multiply back.
      have hsub : z - a ≠ 0 := sub_ne_zero.mpr hza
      have hpow : (z - a) ^ m ≠ 0 := pow_ne_zero m hsub
      simp only [hg, globalCofactor, if_neg hza]
      rw [mul_div_assoc', mul_comm, mul_div_assoc, div_self hpow, mul_one]
  -- `g` analytic on the closed rectangle.
  have hg_an : ∀ z ∈ {z : ℂ | R.ContainsClosed z}, AnalyticAt ℂ g z := by
    intro z hz
    by_cases hza : z = a
    · subst hza; exact hg_an_a
    · -- Away from `a`: `g =ᶠ[𝓝 z] f / (· - a)^m`, analytic.
      have hfz : AnalyticAt ℂ f z := hf_an z hz
      have hsub : z - a ≠ 0 := sub_ne_zero.mpr hza
      have hden_an : AnalyticAt ℂ (fun w => (w - a) ^ m) z := by fun_prop
      have hden_ne : (fun w => (w - a) ^ m) z ≠ 0 := pow_ne_zero m hsub
      have hquot_an : AnalyticAt ℂ (fun w => f w / (w - a) ^ m) z :=
        hfz.div hden_an hden_ne
      -- `g` agrees with the quotient near `z` (since `w ≠ a` there).
      have hne_nhds : ∀ᶠ w in 𝓝 z, w ≠ a := eventually_ne_nhds hza
      have hg_eq_quot : g =ᶠ[𝓝 z] fun w => f w / (w - a) ^ m := by
        refine hne_nhds.mono (fun w hw => ?_)
        simp only [hg, globalCofactor, if_neg hw]
      exact hquot_an.congr hg_eq_quot.symm
  -- `g` non-vanishing on the closed rectangle.
  have hg_ne : ∀ z ∈ {z : ℂ | R.ContainsClosed z}, g z ≠ 0 := by
    intro z hz
    by_cases hza : z = a
    · subst hza; rw [hg_at_a]; exact hh_ne
    · have hsub : z - a ≠ 0 := sub_ne_zero.mpr hza
      have hpow : (z - a) ^ m ≠ 0 := pow_ne_zero m hsub
      have hfz_ne : f z ≠ 0 := hf_ne z hz hza
      simp only [hg, globalCofactor, if_neg hza]
      exact div_ne_zero hfz_ne hpow
  exact ⟨ha, hfactor, hg_an, hg_ne⟩

end ScratchAPGlobalFactor
end BacklundTuring
end OverflowResidueRH

/-! ## Axiom audit

Must show only the standard classical/quotient axioms (`propext`,
`Classical.choice`, `Quot.sound`) and NO `sorryAx`. -/

#print axioms
  OverflowResidueRH.BacklundTuring.ScratchAPGlobalFactor.globalOrderFactorization_of_isolatedZero
