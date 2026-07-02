import rh

/-!
# Scratch: inhabiting the 182-zero bracket existence certificate

This file reduces

  `BacklundGrid2First182ZeroBracketExistenceCertificate140_369075049_1000000`

to the **minimal irreducible verified-computation datum** for a Turing/Hardy-Z
zero check, with every *structural* analytic bridge proven.

## What Mathlib provides (probed live)

* `riemannZeta : ℂ → ℂ` as an analytic object: `differentiableAt_riemannZeta`
  (off `s = 1`), the completed/functional-equation API, and zeta values only at
  *trivial* points (`riemannZeta_zero`, `riemannZeta_neg_two_mul_nat_add_one`,
  `riemannZeta_two_mul_nat`).
* **No** computable `riemannZeta` with error bounds.
* **No** Hardy Z-function, **no** Riemann–Siegel formula, **no** θ-function.
* **No** conjugate-symmetry lemma `ζ(conj s) = conj (ζ s)` (so even the
  real-valuedness of `Z(t) = e^{iθ(t)}ζ(½+it)` is not available off the shelf).

Consequently the 182 interval evaluations `Z(aₖ)·Z(bₖ) < 0` are **not**
Lean-verifiable today: they require numerical evaluation of `ζ` on the critical
line with rigorous error bounds, which Mathlib cannot do. They are the genuine
external computation. We isolate them — and *only* them, plus the analytic
ingredients Mathlib lacks (continuity of `Z`, the modulus relation, the count,
and per-bracket monotonicity/simplicity) — into a single hypothesis bundle
`HardyZSignData`.

## What is PROVEN here (the structural bridges)

* `zetaZero_of_Z_zero` : `Z t = 0 → riemannZeta (½ + i t) = 0`, from
  `|Z t| = ‖ζ(½+it)‖` (the Hardy modulus relation).
* `isNontrivialZetaZero_of_Z_zero` : a `Z`-zero is an `IsNontrivialZetaZero`
  (the critical-line real part `½ ∈ (0,1)`).
* `exists_Z_zero_in_Ioo` : **IVT** — a sign change of the continuous real `Z`
  across `(a,b)` produces `t₀ ∈ (a,b)` with `Z t₀ = 0`
  (`intermediate_value_Ioo` / `intermediate_value_Ioo'`).
* assembly of all four certificate fields from `HardyZSignData`.

The result: the certificate is inhabited **modulo `HardyZSignData`**, which is the
irreducible verified-computation residual.
-/

namespace OverflowResidueRH.BacklundTuring.ScratchZeroCert

open OverflowResidueRH OverflowResidueRH.BacklundTuring
open scoped Complex

/-- The point on the critical line at real height `t`: `½ + i·t`. -/
noncomputable def criticalPoint (t : ℝ) : ℂ :=
  (1 / 2 : ℂ) + Complex.I * (t : ℂ)

@[simp] theorem criticalPoint_re (t : ℝ) : (criticalPoint t).re = 1 / 2 := by
  simp [criticalPoint]

@[simp] theorem criticalPoint_im (t : ℝ) : (criticalPoint t).im = t := by
  simp [criticalPoint]

/-- **The irreducible verified-computation datum.**

A `HardyZSignData` packages exactly the inputs that Mathlib *cannot* supply:

* `Z : ℝ → ℝ` — the (real) Hardy Z-function on the critical line, together with
  its continuity `Z_continuous` and the **Hardy modulus relation**
  `Z_modulus : |Z t| = ‖ζ(½ + i t)‖`.  These encode the classical fact that
  `Z(t) = e^{iθ(t)} ζ(½+it)` is real with `|Z(t)| = |ζ(½+it)|`; their proof needs
  the θ-function / functional equation in a real-analytic form Mathlib lacks.

* `sign_change k` — for each of the 182 brackets, the **numerical** sign change
  `Z(aₖ)·Z(bₖ) < 0`.  These are the 182 interval evaluations of `Z`, the true
  external computation (rigorous `ζ` interval arithmetic on the critical line).

* `bracket_unique k` — within bracket `k`, any two nontrivial `ζ`-zeros coincide.
  This is the Turing-method *separation* of consecutive zeros (each `10⁻⁸`
  bracket isolates a single simple zero); it too rests on numerical evaluation.

* `count_complete` — every nontrivial `ζ`-zero up to the cutoff height lies in
  some bracket.  This is the Turing/argument-principle **count** `N(369) = 182`.

* `simple k` — the unique zero in bracket `k` is simple (analytic order 1).
  Simplicity of the first zeros is again a verified-computation fact.

Everything *structural* (IVT, `Z`-zero ⟹ `ζ`-zero ⟹ nontrivial zero, and the
final assembly) is proven from these. -/
structure HardyZSignData where
  /-- The real Hardy Z-function on the critical line. -/
  Z : ℝ → ℝ
  /-- `Z` is continuous (classical: it is real-analytic). -/
  Z_continuous : Continuous Z
  /-- Hardy modulus relation `|Z t| = ‖ζ(½ + i t)‖`. -/
  Z_modulus : ∀ t : ℝ, |Z t| = ‖riemannZeta (criticalPoint t)‖
  /-- The 182 numerical sign changes `Z(aₖ)·Z(bₖ) < 0`. -/
  sign_change :
    ∀ k : Fin 182,
      Z ((backlundGrid2First182ZeroLowerRatAt k : ℚ) : ℝ)
        * Z ((backlundGrid2First182ZeroUpperRatAt k : ℚ) : ℝ) < 0
  /-- Each `10⁻⁸` bracket isolates at most one nontrivial `ζ`-zero. -/
  bracket_unique :
    ∀ k : Fin 182, ∀ s t : ℂ,
      IsNontrivialZetaZero s →
      IsNontrivialZetaZero t →
      ((backlundGrid2First182ZeroLowerRatAt k : ℚ) : ℝ) < s.im →
      s.im < ((backlundGrid2First182ZeroUpperRatAt k : ℚ) : ℝ) →
      ((backlundGrid2First182ZeroLowerRatAt k : ℚ) : ℝ) < t.im →
      t.im < ((backlundGrid2First182ZeroUpperRatAt k : ℚ) : ℝ) →
      s = t
  /-- Turing count: every nontrivial zero up to the cutoff is bracketed. -/
  count_complete :
    ∀ s : ℂ,
      IsZetaZeroUpToHeight (369075049 / 1000000 : ℝ) s →
        ∃ k : Fin 182,
          ((backlundGrid2First182ZeroLowerRatAt k : ℚ) : ℝ) < s.im ∧
          s.im < ((backlundGrid2First182ZeroUpperRatAt k : ℚ) : ℝ)
  /-- The unique zero in bracket `k` is simple (analytic order 1). -/
  simple :
    ∀ k : Fin 182, ∀ s : ℂ,
      IsNontrivialZetaZero s →
      ((backlundGrid2First182ZeroLowerRatAt k : ℚ) : ℝ) < s.im →
      s.im < ((backlundGrid2First182ZeroUpperRatAt k : ℚ) : ℝ) →
      zetaGlobalZeroMultiplicity.mult s = 1

/-! ## Structural bridge 1 : a `Z`-zero is a nontrivial `ζ`-zero -/

/-- From the Hardy modulus relation: if `Z t = 0` then `ζ(½ + i t) = 0`. -/
theorem zetaZero_of_Z_zero (D : HardyZSignData) {t : ℝ} (ht : D.Z t = 0) :
    riemannZeta (criticalPoint t) = 0 := by
  have h : ‖riemannZeta (criticalPoint t)‖ = 0 := by
    have := D.Z_modulus t
    rw [ht] at this
    simpa using this.symm
  simpa using h

/-- A `Z`-zero gives an `IsNontrivialZetaZero` at the critical point, because the
real part `½` lies in `(0, 1)`. -/
theorem isNontrivialZetaZero_of_Z_zero
    (D : HardyZSignData) {t : ℝ} (ht : D.Z t = 0) :
    IsNontrivialZetaZero (criticalPoint t) := by
  refine ⟨zetaZero_of_Z_zero D ht, ?_, ?_⟩
  · simp
  · simp; norm_num

/-! ## Structural bridge 2 : IVT sign-change ⟹ zero in the open bracket -/

/-- **IVT sign-change bridge.** If `Z` is continuous and `Z a · Z b < 0` with
`a < b`, then `Z` has a zero in the *open* interval `(a, b)`. -/
theorem exists_Z_zero_in_Ioo
    (D : HardyZSignData) {a b : ℝ} (hab : a < b)
    (hsign : D.Z a * D.Z b < 0) :
    ∃ t ∈ Set.Ioo a b, D.Z t = 0 := by
  have hcont : ContinuousOn D.Z (Set.Icc a b) := D.Z_continuous.continuousOn
  rcases mul_neg_iff.mp hsign with ⟨hpos, hneg⟩ | ⟨hneg, hpos⟩
  · -- Z a > 0, Z b < 0 : use the reversed IVT  Ioo (Z b) (Z a) ⊆ image
    have hmem : (0 : ℝ) ∈ Set.Ioo (D.Z b) (D.Z a) := ⟨hneg, hpos⟩
    have hsub := intermediate_value_Ioo' (le_of_lt hab) hcont hmem
    rcases hsub with ⟨t, ht, hzt⟩
    exact ⟨t, ht, hzt⟩
  · -- Z a < 0, Z b > 0 : use the forward IVT  Ioo (Z a) (Z b) ⊆ image
    have hmem : (0 : ℝ) ∈ Set.Ioo (D.Z a) (D.Z b) := ⟨hneg, hpos⟩
    have hsub := intermediate_value_Ioo (le_of_lt hab) hcont hmem
    rcases hsub with ⟨t, ht, hzt⟩
    exact ⟨t, ht, hzt⟩

/-! ## Bracket ordering fact -/

/-- Each bracket is nondegenerate: lower endpoint `< ` upper endpoint. -/
theorem lower_lt_upper (k : Fin 182) :
    ((backlundGrid2First182ZeroLowerRatAt k : ℚ) : ℝ)
      < ((backlundGrid2First182ZeroUpperRatAt k : ℚ) : ℝ) := by
  have hq :
      (backlundGrid2First182ZeroLowerRatAt k : ℚ)
        < backlundGrid2First182ZeroUpperRatAt k := by
    unfold backlundGrid2First182ZeroLowerRatAt
    have : (0 : ℚ) < 1 / 100000000 := by norm_num
    linarith
  exact_mod_cast hq

/-! ## Bridge 3 : the existence field for a single bracket -/

/-- For each bracket `k`, the sign change produces a nontrivial `ζ`-zero whose
imaginary part lies strictly inside the bracket, and it is simple. -/
theorem exists_in_bracket_of_data (D : HardyZSignData) (k : Fin 182) :
    ∃ s : ℂ,
      IsNontrivialZetaZero s ∧
      ((backlundGrid2First182ZeroLowerRatAt k : ℚ) : ℝ) < s.im ∧
      s.im < ((backlundGrid2First182ZeroUpperRatAt k : ℚ) : ℝ) ∧
      zetaGlobalZeroMultiplicity.mult s = 1 := by
  obtain ⟨t, ht, hzt⟩ :=
    exists_Z_zero_in_Ioo D (lower_lt_upper k) (D.sign_change k)
  refine ⟨criticalPoint t, isNontrivialZetaZero_of_Z_zero D hzt, ?_, ?_, ?_⟩
  · simpa using ht.1
  · simpa using ht.2
  · exact D.simple k (criticalPoint t)
      (isNontrivialZetaZero_of_Z_zero D hzt)
      (by simpa using ht.1) (by simpa using ht.2)

/-! ## Final assembly -/

/-- **Main reduction.** From the verified-computation datum `HardyZSignData`,
the full bracket existence certificate is inhabited.  All structural content
(IVT sign-change → zero, `Z`-zero → nontrivial `ζ`-zero, simplicity packaging,
uniqueness, completeness packaging) is discharged here; the only external inputs
are the fields of `HardyZSignData`. -/
theorem bracketExistenceCertificate_of_data (D : HardyZSignData) :
    BacklundGrid2First182ZeroBracketExistenceCertificate140_369075049_1000000 where
  exists_in_bracket := exists_in_bracket_of_data D
  unique_in_bracket := D.bracket_unique
  complete_to_cutoff_bracket := D.count_complete

end OverflowResidueRH.BacklundTuring.ScratchZeroCert
