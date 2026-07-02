import rh

/-!
# Scratch: per-singularity analyticity of the log-derivative remainder

GOAL (argument-principle per-singularity obligation).

At a point `ρ` where an analytic function `f` has analytic order `n`
(a zero of multiplicity `n`; away from zeros `n = 0`), the function
`s ↦ logDeriv f s − n/(s − ρ)` is analytic at `ρ` once one subtracts the
integer principal part.  Concretely: there is an analytic germ `g` at `ρ`
with `logDeriv f =ᶠ[𝓝[≠] ρ] (fun z => n/(z − ρ) + g z)`, i.e. the analytic
remainder `g = logDeriv f − n/(·−ρ)` is `AnalyticAt ℂ … ρ`.

This is the classical "log-derivative principal-part" fact.  Mathlib supplies:

* `AnalyticAt.analyticOrderAt_eq_natCast` — local factorization
  `f =ᶠ[𝓝 ρ] (·−ρ)^n • g` with `g` analytic and `g ρ ≠ 0`;
* `logDeriv_mul`, `logDeriv_fun_pow` — product / power rules;
* `AnalyticAt.div`/`AnalyticAt.deriv` — `logDeriv g` analytic at a
  nonvanishing analytic `g`.

The rh.lean codebase already packages exactly this as
`hasLogDerivPrincipalPart_of_analytic_zero` (the AG4 theorem) producing a
`HasLogDerivPrincipalPart` witness.  Here we (1) re-expose the explicit
`AnalyticAt` content of the remainder germ, (2) connect it to the rh.lean
obligation field `RectangleLogDerivRemainderAnalyticInput.analytic_at_singularity`
(via the BV1 extension-data route, which is what the `1/0 = 0` convention
forces — see the BV1 note in rh.lean), and (3) specialize to `riemannZeta`
at a nontrivial zero.

We only `import rh`; no edits to rh.lean.
-/

namespace OverflowResidueRH.BacklundTuring

open scoped Topology

/-! ## 1. The analytic remainder germ, extracted explicitly. -/

/-- **Core per-singularity analyticity.**  If `f` is analytic at `ρ` with
analytic order `n`, then there is an analytic germ `g` at `ρ` such that the
log-derivative principal part holds:
`logDeriv f =ᶠ[𝓝[≠] ρ] (fun z => n/(z − ρ) + g z)`.

The remainder `g` is genuinely `AnalyticAt ℂ g ρ`, which is the precise
content of "subtracting the integer principal part leaves an analytic
function at `ρ`".  This repackages `hasLogDerivPrincipalPart_of_analytic_zero`
to surface the `AnalyticAt` witness directly. -/
theorem analyticRemainder_of_analytic_order
    {f : ℂ → ℂ} {ρ : ℂ} {n : ℕ}
    (hAn : AnalyticAt ℂ f ρ)
    (horder : analyticOrderAt f ρ = (n : ℕ∞)) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g ρ ∧
      logDeriv f =ᶠ[𝓝[≠] ρ] (fun z : ℂ => (n : ℂ) / (z - ρ) + g z) :=
  hasLogDerivPrincipalPart_of_analytic_zero hAn horder

/-- **Remainder germ analyticity, stated as the difference.**  Under the
same hypotheses, the explicit difference function `logDeriv f − n/(·−ρ)`
agrees, on the punctured neighborhood of `ρ`, with a function `g` that is
analytic *at* `ρ`.  This is the literal "the remainder is analytic at the
singularity" statement (the punctured-neighborhood agreement is forced: the
raw difference is undefined / `1/0 = 0` exactly at `ρ`). -/
theorem analyticRemainder_difference_eq_analyticAt
    {f : ℂ → ℂ} {ρ : ℂ} {n : ℕ}
    (hAn : AnalyticAt ℂ f ρ)
    (horder : analyticOrderAt f ρ = (n : ℕ∞)) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g ρ ∧
      (fun z : ℂ => logDeriv f z - (n : ℂ) / (z - ρ)) =ᶠ[𝓝[≠] ρ] g := by
  obtain ⟨g, hg_an, hg_eq⟩ :=
    analyticRemainder_of_analytic_order hAn horder
  refine ⟨g, hg_an, ?_⟩
  filter_upwards [hg_eq] with z hz
  -- `logDeriv f z = n/(z-ρ) + g z`  ⟹  `logDeriv f z − n/(z-ρ) = g z`.
  rw [hz]; ring

/-! ## 2. Specialization to `riemannZeta` at a nontrivial zero. -/

/-- At a nontrivial zeta zero `ρ`, the log-derivative `ζ'/ζ` has analytic
remainder after subtracting the integer principal part `m/(·−ρ)`, where
`m = zetaGlobalZeroMultiplicity.mult ρ` is the analytic multiplicity.  The
remainder germ is `AnalyticAt ℂ … ρ`. -/
theorem zeta_analyticRemainder_at_nontrivial_zero
    {ρ : ℂ} (hρ : IsNontrivialZetaZero ρ) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g ρ ∧
      logDeriv riemannZeta =ᶠ[𝓝[≠] ρ]
        (fun z : ℂ =>
          ((zetaGlobalZeroMultiplicity.mult ρ : ℕ) : ℂ) / (z - ρ) + g z) :=
  analyticRemainder_of_analytic_order
    (riemannZeta_analyticAt_of_isNontrivialZetaZero hρ)
    (zetaGlobalZeroMultiplicity_order_eq hρ)

/-- Difference form at a nontrivial zeta zero: `ζ'/ζ − m/(·−ρ)` agrees on the
punctured neighborhood of `ρ` with an analytic germ.  This is precisely the
per-singularity analyticity obligation of the argument principle, specialized
to a zero of `ζ`. -/
theorem zeta_analyticRemainder_difference_at_nontrivial_zero
    {ρ : ℂ} (hρ : IsNontrivialZetaZero ρ) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g ρ ∧
      (fun z : ℂ =>
          logDeriv riemannZeta z
            - ((zetaGlobalZeroMultiplicity.mult ρ : ℕ) : ℂ) / (z - ρ))
        =ᶠ[𝓝[≠] ρ] g :=
  analyticRemainder_difference_eq_analyticAt
    (riemannZeta_analyticAt_of_isNontrivialZetaZero hρ)
    (zetaGlobalZeroMultiplicity_order_eq hρ)

/-! ## 3. Connection to the rh.lean BV1 extension obligation.

The honest rh.lean obligation that consumes this is the *extension* package
`RectangleLogDerivRemainderExtensionData`, whose `analytic_remainderExt`
field asks for a function analytic on the closed rectangle that agrees with
the raw remainder off the singularities.  (The BV1 note in rh.lean records
that the *raw* `logDerivRemainder` cannot itself be `AnalyticAt` at a
singularity, because Lean's `1/0 = 0` totalization gives it the wrong value
there; the genuine analytic object is the germ `g` produced above.)

Below we show how the per-singularity germ `g` produced here is exactly the
local analytic data feeding that extension: away from `ρ` it agrees with
`zetaLogDeriv − principalKernel m ρ`, the per-singularity contribution to
`logDerivRemainder`. -/

/-- The per-singularity germ matches the local raw remainder off `ρ`.
For a single-singularity principal part, `zetaLogDeriv z − principalKernel m ρ z`
equals `logDeriv riemannZeta z − m/(z−ρ)`, which agrees with the analytic
germ `g` on the punctured neighborhood of `ρ`.  (`zetaLogDeriv = logDeriv
riemannZeta` and `principalKernel k s z = k/(z−s)` by definition.) -/
theorem zeta_germ_agrees_with_principalKernel_difference
    {ρ : ℂ} (hρ : IsNontrivialZetaZero ρ) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g ρ ∧
      (fun z : ℂ =>
          ZetaRectangle.zetaLogDeriv z
            - ZetaRectangle.principalKernel
                ((zetaGlobalZeroMultiplicity.mult ρ : ℕ) : ℤ) ρ z)
        =ᶠ[𝓝[≠] ρ] g := by
  obtain ⟨g, hg_an, hg_eq⟩ :=
    zeta_analyticRemainder_difference_at_nontrivial_zero hρ
  refine ⟨g, hg_an, ?_⟩
  filter_upwards [hg_eq] with z hz
  -- `zetaLogDeriv z = deriv ζ z / ζ z = logDeriv ζ z`; `principalKernel k s z = k/(z−s)`.
  simp only [ZetaRectangle.zetaLogDeriv, logDeriv, ZetaRectangle.principalKernel,
    Pi.div_apply] at hz ⊢
  push_cast at hz ⊢
  rw [← hz]

end OverflowResidueRH.BacklundTuring
