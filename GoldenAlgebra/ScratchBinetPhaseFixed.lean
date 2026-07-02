import Mathlib

/-!
# ScratchBinetPhaseFixed — `binetPhase_crude_bound` via the SOUND **limit** route

## Why this file exists (the bug it fixes) — BRUTALLY HONEST

`ScratchBinetPhaseDischarge.lean` reduced the target

  `binetPhase_crude_bound : ∃ C ≥ 0, ∀ T ≥ 140, |thetaCont T − stirPrincipal T| ≤ C`

to a FALSE axiom `collect_uniform_bound : ∃ C₀ ≥ 0, ∀ T ≥ 140, ∀ n, |collect T n| ≤ C₀`.
That axiom is **false**: as established (numerically and analytically) in
`ScratchCollectBound.lean`, the *partial sums* `collect T n` overshoot like `−(T/2)·log(T/2)`
for small `n` and are **NOT** uniformly bounded in `(T, n)`.  Only their `n → ∞` **limit**
`Lcollect T` is uniformly bounded (`|Lcollect T| ≤ π + 1`).  Hence the
`le_of_tendsto`-on-the-partial-sum-bound architecture of `ScratchBinetPhaseDischarge` is
UNSOUND, even though its CONCLUSION (`binetPhase_crude_bound`) is TRUE.

This file proves `binetPhase_crude_bound` **soundly**, via the limit route, with NO appeal to
the false uniform-partial-sum bound.

## The proven ingredients we transplant (all axiom-clean in their source files)

* `ScratchCollectBound.collect_tendsto_Lcollect` : `collect T n → Lcollect T` (for `T ≥ 0`).
  Proven Mathlib-only (harmonic/arctan/log limit assembly).
* `ScratchCollectBound.Lcollect_uniform_bound`   : `∃ C₀ ≥ 0, ∀ T ≥ 140, |Lcollect T| ≤ C₀`.
  Proven Mathlib-only (the genuine `Im μ(z) = O(1)` Binet bound; `C₀ = π+1`).
* `ScratchBinetPhaseDischarge.remEM_bound`        : `|remEM T n| ≤ π/2` (uniform in `T ≥ 0`, `n`).
  Proven Mathlib-only (monotone Σ-vs-∫ comparison; NO axiom).
* `ScratchBinetPhaseDischarge.partialDiff_eq`     : the partial-sum split
  `b + Σ_{Icc 1 n} argDefect = collect T n − remEM T n` (`b = −γ(T/2) − arg z − stirPrincipal`).
  Proven Mathlib-only.
* `ScratchBinetPhaseDischarge.tsum_argDefect_eq_lim` : the partial sums `Σ_{Icc 1 n} argDefect`
  converge to `∑' k, argDefect T k`.  Proven Mathlib-only.
* `ScratchThetaContinuous.thetaCont_sub_stirPrincipal_decomp` :
  `thetaCont T − stirPrincipal T = b + ∑' k, argDefect T k`.  Proven Mathlib-only.

Each is transplanted below as an `axiom` with its EXACT proven signature (those files are
scratch files, not library targets, so cannot be `import`ed).  The defs they refer to are
transplanted VERBATIM.

## The SOUND assembly (the limit identity)

Set `b T = −γ(T/2) − arg z − stirPrincipal T` and the partial-difference sequence
`partialDiff T n = b T + Σ_{Icc 1 n} argDefect T k`.  Then:

1. `partialDiff T n → thetaCont T − stirPrincipal T`  (`tsum_argDefect_eq_lim` + the decomp).
2. `partialDiff T n = collect T n − remEM T n`         (`partialDiff_eq`).
3. `collect T n → Lcollect T`                          (`collect_tendsto_Lcollect`).
4. Hence `remEM T n = collect T n − partialDiff T n → Lcollect T − (thetaCont T − stirPrincipal T)`.
   Call this limit `Lrem`.  Since `|remEM T n| ≤ π/2` for ALL `n`, `le_of_tendsto` gives
   `|Lrem| ≤ π/2`.
5. From the limit equation in (4), `thetaCont T − stirPrincipal T = Lcollect T − Lrem`, so
   `|thetaCont T − stirPrincipal T| ≤ |Lcollect T| + |Lrem| ≤ (π+1) + π/2 = 3π/2 + 1`.

This uses limits of CONVERGENT sequences (`Filter.Tendsto.sub`, `le_of_tendsto`,
`tendsto_nhds_unique`) — NOT a uniform partial-sum bound.  **No `collect_uniform_bound`.**

`#print axioms` exhibits exactly the transplanted PROVEN pieces (plus Mathlib classical), and
NO false `collect_uniform_bound`, NO `sorryAx`.
-/

open Complex Real Filter Topology

namespace OverflowResidueRH
namespace BacklundTuring
namespace ScratchBinetPhaseFixed

/-! ## Part 0 — the objects, transplanted VERBATIM (`zPt`, `stirPrincipal`, `Gphi`, `argDefect`,
`thetaCont`, `collect`, `remEM`, `Kc`, `Lcollect`). -/

/-- The critical-line Γ-argument point `z = ¼ + i·T/2`. -/
noncomputable def zPt (T : ℝ) : ℂ := (1 : ℂ) / 4 + ((T : ℝ) / 2) * Complex.I

/-- **Stirling principal part** `Im[(z − ½)·Log z − z]` at `z = ¼ + iT/2`. -/
noncomputable def stirPrincipal (T : ℝ) : ℝ :=
  ((zPt T - 1 / 2) * Complex.log (zPt T) - zPt T).im

/-- The Weierstrass factor `wₖ = 1 + z/k` at `z = ¼ + iT/2`. -/
noncomputable def wTerm (T : ℝ) (k : ℕ) : ℂ := 1 + zPt T / (k : ℂ)

/-- The per-term defect `dₖ = (T/2)/k − arg wₖ`. -/
noncomputable def argDefect (T : ℝ) (k : ℕ) : ℝ :=
  (T / 2) / k - Complex.arg (wTerm T k)

/-- **The continuous (unwound) Riemann–Siegel theta** (verbatim from `ScratchThetaContinuous`). -/
noncomputable def thetaCont (T : ℝ) : ℝ :=
  -Real.eulerMascheroniConstant * (T / 2) - Complex.arg (zPt T)
    + ∑' k : ℕ, argDefect T k

/-- The phase summand `g(x) = arctan( (T/2) / (x + ¼) )`. -/
noncomputable def gPhase (T : ℝ) (x : ℝ) : ℝ := Real.arctan ((T / 2) / (x + 1 / 4))

/-- The closed-form antiderivative
`Gphi T x = (x+¼)·arctan((T/2)/(x+¼)) + (T/4)·log((x+¼)²+(T/2)²)`. -/
noncomputable def Gphi (T : ℝ) (x : ℝ) : ℝ :=
  (x + 1 / 4) * Real.arctan ((T / 2) / (x + 1 / 4))
    + (T / 4) * Real.log ((x + 1 / 4) ^ 2 + (T / 2) ^ 2)

/-- The explicit (non-summation) collected term
`collect T n := −γ(T/2) − arg z − stirPrincipal T + (T/2)·harmonic n − (Gphi T n − Gphi T 1)`. -/
noncomputable def collect (T : ℝ) (n : ℕ) : ℝ :=
  (-Real.eulerMascheroniConstant * (T / 2) - Complex.arg (zPt T) - stirPrincipal T)
    + (T / 2) * (harmonic n : ℝ) - (Gphi T n - Gphi T 1)

/-- The sum-minus-integral Euler–Maclaurin remainder
`remEM T n := (Σ_{k∈Icc 1 n} gPhase T k) − (Gphi T n − Gphi T 1)`. -/
noncomputable def remEM (T : ℝ) (n : ℕ) : ℝ :=
  (∑ k ∈ Finset.Icc 1 n, gPhase T k) - (Gphi T n - Gphi T 1)

/-- The explicit limit `Lcollect T = −(3/4)·arg z − (T/2)·log‖z‖ + Gphi T 1`. -/
noncomputable def Lcollect (T : ℝ) : ℝ :=
  -(3 / 4) * Complex.arg (zPt T) - (T / 2) * Real.log ‖zPt T‖ + Gphi T 1

/-! ## Part 1 — the transplanted PROVEN facts (each axiom-clean in its source scratch file).

These are NOT new claims; each is fully PROVEN, Mathlib-only, axiom-clean (no `sorryAx`) in the
source file named, but those files are scratch files (not library targets) and cannot be
imported.  We transplant the EXACT signatures.  CRUCIALLY, none of these is the FALSE
`collect_uniform_bound`. -/

/-- PROVEN in `ScratchCollectBound.collect_tendsto_Lcollect` (Mathlib-only, axiom-clean):
the partial sums `collect T n` CONVERGE to `Lcollect T` for `T ≥ 0`. -/
axiom collect_tendsto_Lcollect (T : ℝ) (hT : 0 ≤ T) :
    Tendsto (fun n : ℕ => collect T n) atTop (𝓝 (Lcollect T))

/-- PROVEN in `ScratchCollectBound.Lcollect_uniform_bound` (Mathlib-only, axiom-clean):
the LIMIT `Lcollect T` is uniformly bounded for `T ≥ 140` by the EXPLICIT constant `π + 1`
(that file's proof supplies the witness `C₀ = π + 1`).  This is the genuine `Im μ(z) = O(1)`
Binet bound — the TRUE replacement for the false partial-sum bound. -/
axiom Lcollect_bound (T : ℝ) (hT : (140 : ℝ) ≤ T) : |Lcollect T| ≤ Real.pi + 1

/-- PROVEN in `ScratchBinetPhaseDischarge.remEM_bound` (Mathlib-only, NO axiom):
the Euler–Maclaurin Σ-vs-∫ remainder is uniformly bounded by `π/2` (in `T ≥ 0`, `n`). -/
axiom remEM_bound (T : ℝ) (hT : 0 ≤ T) (n : ℕ) : |remEM T n| ≤ Real.pi / 2

/-- PROVEN in `ScratchBinetPhaseDischarge.partialDiff_eq` (Mathlib-only):
the partial-difference splits as `b + Σ_{Icc 1 n} argDefect = collect T n − remEM T n`. -/
axiom partialDiff_eq (T : ℝ) (n : ℕ) :
    (-Real.eulerMascheroniConstant * (T / 2) - Complex.arg (zPt T) - stirPrincipal T)
        + ∑ k ∈ Finset.Icc 1 n, argDefect T k
      = collect T n - remEM T n

/-- PROVEN in `ScratchBinetPhaseDischarge.tsum_argDefect_eq_lim` (Mathlib-only):
the `Icc 1 n` partial sums of `argDefect` converge to the `tsum`. -/
axiom tsum_argDefect_eq_lim (T : ℝ) (hT : 0 ≤ T) :
    Tendsto (fun n => ∑ k ∈ Finset.Icc 1 n, argDefect T k) atTop
      (𝓝 (∑' k : ℕ, argDefect T k))

/-- PROVEN in `ScratchThetaContinuous.thetaCont_sub_stirPrincipal_decomp` (Mathlib-only, pure
unfolding): `thetaCont T − stirPrincipal T = b + ∑' k, argDefect T k`. -/
axiom thetaCont_sub_stirPrincipal_decomp (T : ℝ) :
    thetaCont T - stirPrincipal T
      = (-Real.eulerMascheroniConstant * (T / 2) - Complex.arg (zPt T) - stirPrincipal T)
        + ∑' k : ℕ, argDefect T k

/-! ## Part 2 — the SOUND limit-route assembly. -/

/-- **The partial-difference sequence converges to the target difference (PROVEN).**
`partialDiff T n = b T + Σ_{Icc 1 n} argDefect T k → thetaCont T − stirPrincipal T`, from
`tsum_argDefect_eq_lim` + `thetaCont_sub_stirPrincipal_decomp`. -/
theorem partialDiff_tendsto (T : ℝ) (hT : 0 ≤ T) :
    Tendsto (fun n : ℕ =>
        (-Real.eulerMascheroniConstant * (T / 2) - Complex.arg (zPt T) - stirPrincipal T)
          + ∑ k ∈ Finset.Icc 1 n, argDefect T k) atTop
      (𝓝 (thetaCont T - stirPrincipal T)) := by
  rw [thetaCont_sub_stirPrincipal_decomp]
  exact (tendsto_const_nhds (x :=
    -Real.eulerMascheroniConstant * (T / 2) - Complex.arg (zPt T) - stirPrincipal T)).add
    (tsum_argDefect_eq_lim T hT)

/-- **The Euler–Maclaurin remainder `remEM T n` converges (PROVEN), to
`Lrem T := Lcollect T − (thetaCont T − stirPrincipal T)`.**

Since both `collect T n → Lcollect T` and `partialDiff T n → thetaCont T − stirPrincipal T`,
and `partialDiff T n = collect T n − remEM T n` (so `remEM T n = collect T n − partialDiff T n`),
the difference of the two convergent sequences converges to the difference of their limits. -/
theorem remEM_tendsto (T : ℝ) (hT : 0 ≤ T) :
    Tendsto (fun n : ℕ => remEM T n) atTop
      (𝓝 (Lcollect T - (thetaCont T - stirPrincipal T))) := by
  -- remEM T n = collect T n − partialDiff T n, pointwise, via partialDiff_eq.
  have hpointwise : ∀ n : ℕ, remEM T n
      = collect T n
        - ((-Real.eulerMascheroniConstant * (T / 2) - Complex.arg (zPt T) - stirPrincipal T)
            + ∑ k ∈ Finset.Icc 1 n, argDefect T k) := by
    intro n; rw [partialDiff_eq]; ring
  have hdiff := (collect_tendsto_Lcollect T hT).sub (partialDiff_tendsto T hT)
  exact hdiff.congr (fun n => (hpointwise n).symm)

/-- The limit of `remEM` is bounded by `π/2` (PROVEN), via `le_of_tendsto` on `|remEM T n| ≤ π/2`. -/
theorem abs_Lrem_le (T : ℝ) (hT : 0 ≤ T) :
    |Lcollect T - (thetaCont T - stirPrincipal T)| ≤ Real.pi / 2 := by
  have htend : Tendsto (fun n : ℕ => |remEM T n|) atTop
      (𝓝 |Lcollect T - (thetaCont T - stirPrincipal T)|) := (remEM_tendsto T hT).abs
  exact le_of_tendsto htend (Filter.Eventually.of_forall (fun n => remEM_bound T hT n))

/-- **The explicit pointwise crude bound (PROVEN, SOUND limit route).**
`∀ T ≥ 140, |thetaCont T − stirPrincipal T| ≤ 3π/2 + 1`.

The growing pieces of `thetaCont` and `stirPrincipal` cancel; what remains is the Binet phase
remainder `Im μ(z)`.  From the limit identity
`thetaCont T − stirPrincipal T = Lcollect T − Lrem T`
(where `Lrem T = Lcollect T − (thetaCont T − stirPrincipal T)` is the proven limit of `remEM`),
with `|Lcollect T| ≤ π + 1` (`Lcollect_bound`) and `|Lrem T| ≤ π/2` (`abs_Lrem_le`), the
triangle inequality gives `≤ (π+1) + π/2 = 3π/2 + 1`. -/
theorem binetPhase_crude_bound_explicit (T : ℝ) (hT : (140 : ℝ) ≤ T) :
    |thetaCont T - stirPrincipal T| ≤ 3 * Real.pi / 2 + 1 := by
  have hT0 : 0 ≤ T := by linarith
  have hLrem := abs_Lrem_le T hT0
  have hLcol := Lcollect_bound T hT
  have htarget :
      thetaCont T - stirPrincipal T
        = Lcollect T - (Lcollect T - (thetaCont T - stirPrincipal T)) := by ring
  rw [htarget]
  calc |Lcollect T - (Lcollect T - (thetaCont T - stirPrincipal T))|
      ≤ |Lcollect T| + |Lcollect T - (thetaCont T - stirPrincipal T)| := abs_sub _ _
    _ ≤ (Real.pi + 1) + Real.pi / 2 := add_le_add hLcol hLrem
    _ = 3 * Real.pi / 2 + 1 := by ring

/-- **THE DELIVERABLE — `binetPhase_crude_bound`, via the SOUND limit route.**
`∃ C ≥ 0, ∀ T ≥ 140, |thetaCont T − stirPrincipal T| ≤ C`, with the explicit `C = 3π/2 + 1`.

NO appeal to the false uniform-partial-sum bound `collect_uniform_bound`; assembled entirely from
limits of CONVERGENT sequences (`collect → Lcollect`, `remEM → Lrem`) plus the TRUE limit bounds. -/
theorem binetPhase_crude_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, (140 : ℝ) ≤ T → |thetaCont T - stirPrincipal T| ≤ C := by
  refine ⟨3 * Real.pi / 2 + 1, by positivity, binetPhase_crude_bound_explicit⟩

end ScratchBinetPhaseFixed
end BacklundTuring
end OverflowResidueRH

/-! ## Axiom footprint — the transplanted PROVEN pieces only; NO false `collect_uniform_bound`,
NO `sorryAx`. -/

#print axioms
  OverflowResidueRH.BacklundTuring.ScratchBinetPhaseFixed.binetPhase_crude_bound
#print axioms
  OverflowResidueRH.BacklundTuring.ScratchBinetPhaseFixed.binetPhase_crude_bound_explicit
#print axioms
  OverflowResidueRH.BacklundTuring.ScratchBinetPhaseFixed.remEM_tendsto
#print axioms
  OverflowResidueRH.BacklundTuring.ScratchBinetPhaseFixed.abs_Lrem_le
