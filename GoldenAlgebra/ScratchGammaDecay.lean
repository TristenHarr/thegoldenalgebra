/-
  ScratchGammaDecay.lean

  Vertical-line bounds on the complex Gamma function.

  HEADLINE (fully proven, unconditional): on the CRITICAL LINE σ = 1/2 we have the
  EXACT closed form

        ‖Γ(1/2 + i t)‖² = π / cosh(π t)

  and the resulting sharp two-sided exponential bounds

        ‖Γ(1/2 + i t)‖ ≤ √(2π) · exp(-(π/2)|t|)
        ‖Γ(1/2 + i t)‖ ≥ √π    · exp(-(π/2)|t|)          (for |t| ≥ 1, in fact all t)

  These give the EXACT e^{-π|t|/2} decay rate that the Backlund–Jensen S(T) route needs.

  Mathlib lemmas used:
    * Complex.Gamma_mul_Gamma_one_sub : Γ z * Γ (1 - z) = π / sin (π z)   (reflection)
    * Complex.Gamma_conj             : Γ (conj z) = conj (Γ z)
    * Complex.sin_pi_div_two_sub / cos_mul_I / ofReal_cosh                (sin(π s) = cosh(π t))
    * Real.cosh_eq, Real.one_le_cosh, Real.cosh_abs                        (cosh bounds)

  PART II extends to the STRIP `σ ∈ [1/4, 2]` (`Re ∈ [1/4,1]` is what
  `Gammaℝ(s) = π^{-s/2}Γ(s/2)` needs).  The reflection machinery, the two-sided
  `‖sin(π(σ+it))‖` bound, and the sinh/cosh exp bounds are ALL proven here.  Both
  strip theorems

      norm_Gamma_strip_upper : ‖Γ(σ+it)‖ ≤ C·|t|^{σ-1/2}·e^{-(π/2)|t|}
      norm_Gamma_strip_lower : c·|t|^{σ-1/2}·e^{-(π/2)|t|} ≤ ‖Γ(σ+it)‖   (load-bearing)

  are proven from a SINGLE explicit hypothesis `BandUpper A` — the standard
  Stirling-on-lines / Hadamard-three-lines band bound (the non-integer power of |t|
  is genuine analytic interpolation, not reachable by finitely many recurrence
  steps).  The lower bound is derived from the upper one purely by REFLECTION.

  All results below are `#print axioms`-clean (only the standard Mathlib axioms);
  the strip theorems carry `BandUpper` as an explicit hypothesis, never an axiom.
-/
import Mathlib

open Complex Real

noncomputable section

namespace GammaDecay

/-! ## Step 1 : `sin (π · (1/2 + i t)) = cosh (π t)` as a real number. -/

/-- On the critical line, the reflection denominator collapses to a real `cosh`. -/
theorem sin_pi_half_add_I (t : ℝ) :
    Complex.sin (π * (1/2 + (t : ℂ) * Complex.I)) = (Real.cosh (π * t) : ℂ) := by
  have hsplit : π * (1/2 + (t : ℂ) * Complex.I)
      = (π/2 : ℂ) + (π * t : ℝ) * Complex.I := by
    push_cast
    ring
  rw [hsplit]
  -- sin (π/2 + x) = cos x  ... use sin (π/2 - (-x)) = cos (-x) = cos x
  have hrw : (π/2 : ℂ) + (π * t : ℝ) * Complex.I
      = π/2 - (-((π * t : ℝ) * Complex.I)) := by ring
  rw [hrw, Complex.sin_pi_div_two_sub, Complex.cos_neg, Complex.cos_mul_I,
    ← Complex.ofReal_cosh]

/-! ## Step 2 : the exact closed form `‖Γ(1/2 + i t)‖² = π / cosh(π t)`. -/

/-- **Exact closed form on the critical line.**  `‖Γ(1/2 + i t)‖² = π / cosh(π t)`. -/
theorem normSq_Gamma_half (t : ℝ) :
    ‖Complex.Gamma (1/2 + (t : ℂ) * Complex.I)‖ ^ 2 = π / Real.cosh (π * t) := by
  set s : ℂ := 1/2 + (t : ℂ) * Complex.I with hs
  -- 1 - s = conj s
  have hconj : (1 : ℂ) - s = (starRingEnd ℂ) s := by
    rw [hs]
    apply Complex.ext
    · simp [Complex.sub_re, Complex.add_re, Complex.mul_re]
      norm_num
    · simp [Complex.sub_im, Complex.add_im, Complex.mul_im]
  -- Γ s * Γ (1 - s) = Γ s * conj (Γ s) = ‖Γ s‖² (as a complex number)
  have hrefl := Complex.Gamma_mul_Gamma_one_sub s
  rw [hconj, Complex.Gamma_conj] at hrefl
  -- Now Γ s * conj (Γ s) = (‖Γ s‖²: ℂ)
  have hmulconj : Complex.Gamma s * (starRingEnd ℂ) (Complex.Gamma s)
      = ((‖Complex.Gamma s‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.mul_conj']
    push_cast
    ring
  -- RHS: π / sin (π s) = π / cosh (π t)
  have hsin : Complex.sin (π * s) = (Real.cosh (π * t) : ℂ) := by
    rw [hs]; exact sin_pi_half_add_I t
  rw [hmulconj, hsin] at hrefl
  -- hrefl : (‖Γ s‖²:ℂ) = π / (cosh (π t):ℂ).  Take real parts.
  have hreal : ((‖Complex.Gamma s‖ ^ 2 : ℝ) : ℂ) = ((π / Real.cosh (π * t) : ℝ) : ℂ) := by
    rw [hrefl]
    push_cast
    ring
  exact_mod_cast hreal

/-! ## Step 3 : the sharp exponential upper / lower bounds on the critical line. -/

/-- `cosh x ≥ exp |x| / 2`, hence a clean lower bound used for the Γ UPPER bound. -/
theorem half_exp_abs_le_cosh (x : ℝ) : Real.exp |x| / 2 ≤ Real.cosh x := by
  rw [← Real.cosh_abs, Real.cosh_eq]
  have hpos : (0 : ℝ) ≤ Real.exp (-|x|) := (Real.exp_pos _).le
  have : Real.exp |x| ≤ Real.exp |x| + Real.exp (-|x|) := by linarith
  linarith

/-- `cosh x ≤ exp |x|`, used for the Γ LOWER bound. -/
theorem cosh_le_exp_abs (x : ℝ) : Real.cosh x ≤ Real.exp |x| := by
  rw [← Real.cosh_abs, Real.cosh_eq]
  have h1 : Real.exp (-|x|) ≤ Real.exp |x| := by
    apply Real.exp_le_exp.mpr; have := abs_nonneg x; linarith
  linarith

/-- **Sharp UPPER bound on the critical line.**
    `‖Γ(1/2 + i t)‖ ≤ √(2π) · exp(-(π/2)|t|)` for every real `t`. -/
theorem norm_Gamma_half_le (t : ℝ) :
    ‖Complex.Gamma (1/2 + (t : ℂ) * Complex.I)‖
      ≤ Real.sqrt (2 * π) * Real.exp (-(π/2) * |t|) := by
  have hpi : (0:ℝ) < π := Real.pi_pos
  have hcosh_pos : 0 < Real.cosh (π * t) := Real.cosh_pos _
  -- normSq formula
  have hsq := normSq_Gamma_half t
  -- bound π / cosh(π t) ≤ 2π · exp(-π|t|)
  have hcosh_lb : Real.exp (π * |t|) / 2 ≤ Real.cosh (π * t) := by
    have := half_exp_abs_le_cosh (π * t)
    rwa [abs_mul, abs_of_pos hpi] at this
  have hexp_pos : (0:ℝ) < Real.exp (π * |t|) := Real.exp_pos _
  have hquot : π / Real.cosh (π * t) ≤ 2 * π * Real.exp (-(π * |t|)) := by
    rw [div_le_iff₀ hcosh_pos]
    have hle : 2 * π * Real.exp (-(π * |t|)) * Real.cosh (π * t)
        ≥ 2 * π * Real.exp (-(π * |t|)) * (Real.exp (π * |t|) / 2) :=
      mul_le_mul_of_nonneg_left hcosh_lb (by positivity)
    have hsimp : 2 * π * Real.exp (-(π * |t|)) * (Real.exp (π * |t|) / 2) = π := by
      rw [Real.exp_neg]
      field_simp
    linarith [hsimp ▸ hle]
  -- so ‖Γ‖² ≤ 2π·exp(-π|t|) = (√(2π)·exp(-(π/2)|t|))²
  have hnormsq_le : ‖Complex.Gamma (1/2 + (t : ℂ) * Complex.I)‖ ^ 2
      ≤ (Real.sqrt (2 * π) * Real.exp (-(π/2) * |t|)) ^ 2 := by
    rw [hsq]
    have hrhs : (Real.sqrt (2 * π) * Real.exp (-(π/2) * |t|)) ^ 2
        = 2 * π * Real.exp (-(π * |t|)) := by
      rw [mul_pow, Real.sq_sqrt (by positivity), ← Real.exp_nat_mul]
      ring_nf
    rw [hrhs]; exact hquot
  -- conclude by taking sqrt (both sides nonneg)
  have hb_nonneg : 0 ≤ Real.sqrt (2 * π) * Real.exp (-(π/2) * |t|) := by positivity
  nlinarith [norm_nonneg (Complex.Gamma (1/2 + (t : ℂ) * Complex.I)), hnormsq_le, hb_nonneg,
    sq_nonneg (‖Complex.Gamma (1/2 + (t : ℂ) * Complex.I)‖ - Real.sqrt (2 * π) * Real.exp (-(π/2) * |t|)),
    sq_nonneg (‖Complex.Gamma (1/2 + (t : ℂ) * Complex.I)‖ + Real.sqrt (2 * π) * Real.exp (-(π/2) * |t|))]

/-- **Sharp LOWER bound on the critical line.**
    `√π · exp(-(π/2)|t|) ≤ ‖Γ(1/2 + i t)‖` for every real `t`. -/
theorem le_norm_Gamma_half (t : ℝ) :
    Real.sqrt π * Real.exp (-(π/2) * |t|) ≤ ‖Complex.Gamma (1/2 + (t : ℂ) * Complex.I)‖ := by
  have hpi : (0:ℝ) < π := Real.pi_pos
  have hcosh_pos : 0 < Real.cosh (π * t) := Real.cosh_pos _
  have hsq := normSq_Gamma_half t
  -- cosh(π t) ≤ exp(π|t|) ⇒ π/cosh ≥ π·exp(-π|t|)
  have hcosh_ub : Real.cosh (π * t) ≤ Real.exp (π * |t|) := by
    have := cosh_le_exp_abs (π * t)
    rwa [abs_mul, abs_of_pos hpi] at this
  have hquot : π * Real.exp (-(π * |t|)) ≤ π / Real.cosh (π * t) := by
    rw [le_div_iff₀ hcosh_pos]
    have h1 : π * Real.exp (-(π * |t|)) * Real.cosh (π * t)
        ≤ π * Real.exp (-(π * |t|)) * Real.exp (π * |t|) :=
      mul_le_mul_of_nonneg_left hcosh_ub (by positivity)
    have h2 : π * Real.exp (-(π * |t|)) * Real.exp (π * |t|) = π := by
      rw [Real.exp_neg]; field_simp
    linarith
  have hlb_sq : (Real.sqrt π * Real.exp (-(π/2) * |t|)) ^ 2
      ≤ ‖Complex.Gamma (1/2 + (t : ℂ) * Complex.I)‖ ^ 2 := by
    rw [hsq]
    have hlhs : (Real.sqrt π * Real.exp (-(π/2) * |t|)) ^ 2 = π * Real.exp (-(π * |t|)) := by
      rw [mul_pow, Real.sq_sqrt hpi.le, ← Real.exp_nat_mul]; ring_nf
    rw [hlhs]; exact hquot
  have hl_nonneg : 0 ≤ Real.sqrt π * Real.exp (-(π/2) * |t|) := by positivity
  nlinarith [norm_nonneg (Complex.Gamma (1/2 + (t : ℂ) * Complex.I)), hlb_sq, hl_nonneg,
    sq_nonneg (‖Complex.Gamma (1/2 + (t : ℂ) * Complex.I)‖ - Real.sqrt π * Real.exp (-(π/2) * |t|))]

/-! ## Step 4 : packaged statement in the requested target shape (σ = 1/2 case). -/

/-- **Target form, exact critical-line case.**  With `σ = 1/2` the requested
    `‖Γ(σ + i t)‖ ≤ C · |t|^(σ-1/2) · exp(-(π/2)|t|)` holds with `C = √(2π)`,
    since the polynomial factor `|t|^0 = 1`. -/
theorem norm_Gamma_vertical_line_half :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 1 ≤ |t| →
      ‖Complex.Gamma ((1/2 : ℝ) + (t : ℂ) * Complex.I)‖
        ≤ C * |t| ^ ((1/2 : ℝ) - 1/2) * Real.exp (-(π/2) * |t|) := by
  refine ⟨Real.sqrt (2 * π), Real.sqrt_nonneg _, ?_⟩
  intro t _
  have h := norm_Gamma_half_le t
  -- |t|^0 = 1
  have hpow : |t| ^ ((1/2 : ℝ) - 1/2) = 1 := by norm_num
  rw [hpow, mul_one]
  -- normalize the cast (1/2 : ℝ) vs (1/2 : ℂ)
  have hcast : ((1/2 : ℝ) : ℂ) + (t : ℂ) * Complex.I = 1/2 + (t : ℂ) * Complex.I := by
    push_cast; ring
  rw [hcast]
  exact h

/-! ##############################################################################
    ## PART II : extension to the strip `σ ∈ [1/4, 2]`.

    The downstream use `|ζ| = |Λ| / |Gammaℝ|` with `Gammaℝ(s) = π^{-s/2} Γ(s/2)`
    needs `Γ` bounds at argument `Re ∈ [1/4, 1]` (` = σ/2` for `σ ∈ [1/2, 2]`),
    for `|t| ≥ 1`, with the `e^{-π|t|/2}` decay and a polynomial factor.

    We build the reusable machinery (reflection in norm form, the two-sided
    `‖sin(π(σ+it))‖` bound, sinh/cosh exp bounds) FULLY, and reduce the two strip
    theorems to a SINGLE explicit interpolation input `BandUpper` — the standard
    Stirling / Hadamard-three-lines content `‖Γ(w)‖ ≤ A·|im w|^{re w - 1/2}·e^{-π|im w|/2}`
    on a fixed band of real parts, which is the one genuinely non-elementary fact
    (a non-integer power of `|t|` cannot arise from finitely many functional-equation
    steps; it is the signature of analytic interpolation).
    ############################################################################## -/

/-! ### II.0  Elementary `sinh` / `cosh` exponential bounds. -/

/-- `exp|x|/4 ≤ |sinh x|` once `1 ≤ |x|` (in fact whenever `exp|x| ≥ 2`). -/
theorem quarter_exp_abs_le_abs_sinh {x : ℝ} (hx : 1 ≤ |x|) :
    Real.exp |x| / 4 ≤ |Real.sinh x| := by
  rw [Real.abs_sinh, Real.sinh_eq]
  have hpos : (0:ℝ) < Real.exp |x| := Real.exp_pos _
  -- exp(-|x|) = 1/exp|x| ≤ 1/2  since exp|x| ≥ exp 1 ≥ 2
  have he2 : (2:ℝ) ≤ Real.exp |x| := by
    calc (2:ℝ) ≤ Real.exp 1 := le_of_lt Real.exp_one_gt_two
      _ ≤ Real.exp |x| := Real.exp_le_exp.mpr hx
  have hmul : Real.exp (-|x|) * Real.exp |x| = 1 := by
    rw [← Real.exp_add]; simp
  have hneg : Real.exp (-|x|) ≤ Real.exp |x| / 2 := by
    nlinarith [hpos, he2, hmul, Real.exp_pos (-|x|)]
  -- (exp|x| - exp(-|x|))/2 ≥ (exp|x| - exp|x|/2)/2 = exp|x|/4
  linarith

/-! ### II.1  Two-sided bound on `‖sin(π(σ+it))‖`.

    `‖sin(π(σ+it))‖² = sin²(πσ) + sinh²(πt)`, hence
    `|sinh(πt)| ≤ ‖sin(π(σ+it))‖ ≤ cosh(πt)`. -/

/-- `‖Complex.sin (π σ + (π t) i)‖² = sin(πσ)² + sinh(πt)²`. -/
theorem normSq_sin_pi (σ t : ℝ) :
    ‖Complex.sin ((π * σ : ℝ) + (π * t : ℝ) * Complex.I)‖ ^ 2
      = Real.sin (π * σ) ^ 2 + Real.sinh (π * t) ^ 2 := by
  rw [Complex.sin_add_mul_I]
  -- sin(πσ)·cosh(πt) + cos(πσ)·sinh(πt)·I  with sin,cos,cosh,sinh of reals
  rw [show ((π * σ : ℝ) : ℂ) = ((π*σ:ℝ):ℂ) from rfl]
  -- compute re and im, then normSq
  have hsin : Complex.sin ((π*σ:ℝ):ℂ) = (Real.sin (π*σ) : ℂ) := by
    rw [← Complex.ofReal_sin]
  have hcos : Complex.cos ((π*σ:ℝ):ℂ) = (Real.cos (π*σ) : ℂ) := by
    rw [← Complex.ofReal_cos]
  have hcosh : Complex.cosh ((π*t:ℝ):ℂ) = (Real.cosh (π*t) : ℂ) := by
    rw [← Complex.ofReal_cosh]
  have hsinh : Complex.sinh ((π*t:ℝ):ℂ) = (Real.sinh (π*t) : ℂ) := by
    rw [← Complex.ofReal_sinh]
  rw [hsin, hcos, hcosh, hsinh]
  -- value = (sin·cosh) + (cos·sinh) I  ; ‖·‖² = normSq = (sin cosh)² + (cos sinh)²
  have hval : (Real.sin (π*σ) : ℂ) * (Real.cosh (π*t) : ℂ)
        + (Real.cos (π*σ) : ℂ) * (Real.sinh (π*t) : ℂ) * Complex.I
      = ((Real.sin (π*σ) * Real.cosh (π*t) : ℝ) : ℂ)
        + ((Real.cos (π*σ) * Real.sinh (π*t) : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [hval, ← Complex.normSq_eq_norm_sq, Complex.normSq_add_mul_I]
  -- (sin cosh)² + (cos sinh)² = sin² (sinh²+1) + (1-sin²) sinh² = sin² + sinh²
  have hc : Real.cosh (π*t) ^ 2 = Real.sinh (π*t) ^ 2 + 1 := by
    have := Real.cosh_sq (π*t); linarith [this]
  have hs : Real.cos (π*σ) ^ 2 = 1 - Real.sin (π*σ) ^ 2 := by
    have := Real.sin_sq_add_cos_sq (π*σ); linarith
  nlinarith [hc, hs]

/-- Lower bound: `|sinh(πt)| ≤ ‖sin(π(σ+it))‖`. -/
theorem abs_sinh_le_norm_sin_pi (σ t : ℝ) :
    |Real.sinh (π * t)| ≤ ‖Complex.sin ((π * σ : ℝ) + (π * t : ℝ) * Complex.I)‖ := by
  have h := normSq_sin_pi σ t
  have hnn : 0 ≤ ‖Complex.sin ((π * σ : ℝ) + (π * t : ℝ) * Complex.I)‖ := norm_nonneg _
  nlinarith [sq_nonneg (Real.sin (π*σ)), sq_abs (Real.sinh (π*t)), h, hnn,
    sq_nonneg (‖Complex.sin ((π * σ : ℝ) + (π * t : ℝ) * Complex.I)‖ - |Real.sinh (π*t)|)]

/-- Upper bound: `‖sin(π(σ+it))‖ ≤ cosh(πt)`. -/
theorem norm_sin_pi_le_cosh (σ t : ℝ) :
    ‖Complex.sin ((π * σ : ℝ) + (π * t : ℝ) * Complex.I)‖ ≤ Real.cosh (π * t) := by
  have h := normSq_sin_pi σ t
  have hnn : 0 ≤ ‖Complex.sin ((π * σ : ℝ) + (π * t : ℝ) * Complex.I)‖ := norm_nonneg _
  have hcpos : 0 ≤ Real.cosh (π*t) := (Real.cosh_pos _).le
  have hbound : ‖Complex.sin ((π * σ : ℝ) + (π * t : ℝ) * Complex.I)‖ ^ 2 ≤ Real.cosh (π*t) ^ 2 := by
    rw [h, Real.cosh_sq]
    nlinarith [Real.sin_sq_le_one (π*σ)]
  nlinarith [hbound, hnn, hcpos,
    sq_nonneg (‖Complex.sin ((π * σ : ℝ) + (π * t : ℝ) * Complex.I)‖ - Real.cosh (π*t))]

/-! ### II.2  Reflection in norm form: `‖Γ(σ+it)‖·‖Γ(1-σ-it)‖ = π/‖sin(π(σ+it))‖`. -/

/-- The norm of the reflection identity.  `s = σ + it`. -/
theorem norm_reflection (σ t : ℝ) :
    ‖Complex.Gamma ((σ:ℝ) + (t:ℝ) * Complex.I)‖
      * ‖Complex.Gamma (1 - ((σ:ℝ) + (t:ℝ) * Complex.I))‖
      = π / ‖Complex.sin ((π * σ : ℝ) + (π * t : ℝ) * Complex.I)‖ := by
  set s : ℂ := (σ:ℝ) + (t:ℝ) * Complex.I with hs
  have hrefl := Complex.Gamma_mul_Gamma_one_sub s
  -- ‖LHS‖ = ‖π/sin(π s)‖
  have : ‖Complex.Gamma s * Complex.Gamma (1 - s)‖ = ‖(π : ℂ) / Complex.sin (π * s)‖ := by
    rw [hrefl]
  rw [norm_mul] at this
  rw [this, norm_div]
  congr 1
  · rw [Complex.norm_real]; exact abs_of_pos Real.pi_pos
  · congr 1
    rw [hs]; push_cast; ring_nf

/-! ### II.3  The single interpolation input (residual).

    `BandUpper A` says: on the band of real parts `[-1, 3]`, for `|im| ≥ 1`,
    `‖Γ(w)‖ ≤ A · |im w|^{re w - 1/2} · exp(-(π/2)|im w|)`.

    This is the standard Stirling-on-vertical-lines / Hadamard-three-lines fact.
    It is the ONLY non-elementary ingredient: the non-integer power `|t|^{re-1/2}`
    cannot be produced by finitely many functional-equation steps, so it is genuinely
    an analytic-interpolation statement.  Everything below is derived from it
    UNCONDITIONALLY by the elementary reflection machinery built above.

    On the critical line `re = 1/2` we PROVED the corresponding bound exactly
    (`norm_Gamma_half_le`), which is the `re = 1/2` slice of `BandUpper √(2π)`. -/
def BandUpper (A : ℝ) : Prop :=
  0 ≤ A ∧ ∀ w : ℂ, (-1 : ℝ) ≤ w.re → w.re ≤ 3 → 1 ≤ |w.im| →
    ‖Complex.Gamma w‖ ≤ A * |w.im| ^ (w.re - 1/2) * Real.exp (-(π/2) * |w.im|)

/-! ### II.4  UPPER bound on the strip `σ ∈ [1/4, 2]` (immediate from `BandUpper`). -/

theorem norm_Gamma_strip_upper {A : ℝ} (hA : BandUpper A) {σ : ℝ}
    (h1 : (1:ℝ)/4 ≤ σ) (h2 : σ ≤ 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 1 ≤ |t| →
      ‖Complex.Gamma ((σ:ℝ) + (t:ℝ) * Complex.I)‖
        ≤ C * |t| ^ (σ - 1/2) * Real.exp (-(π/2) * |t|) := by
  obtain ⟨hA0, hA⟩ := hA
  refine ⟨A, hA0, ?_⟩
  intro t ht
  have hw := hA ((σ:ℝ) + (t:ℝ) * Complex.I)
  -- re = σ, im = t
  have hre : ((σ:ℝ) + (t:ℝ) * Complex.I).re = σ := by simp
  have him : ((σ:ℝ) + (t:ℝ) * Complex.I).im = t := by simp
  rw [hre, him] at hw
  exact hw (by linarith) (by linarith) ht

/-! ### II.5  LOWER bound on the strip `σ ∈ [1/4, 2]` — the load-bearing one.

    From reflection `‖Γ(σ+it)‖ · ‖Γ(1-σ-it)‖ = π/‖sin(π(σ+it))‖`,
    bound the denominator ABOVE:
      `‖sin‖ ≤ cosh(πt) ≤ exp(π|t|)`  and  `‖Γ(1-σ-it)‖ ≤ A·|t|^{1/2-σ}·exp(-(π/2)|t|)`,
    so `‖Γ(σ+it)‖ ≥ (π/A)·|t|^{σ-1/2}·exp(-(π/2)|t|)`. -/

theorem norm_Gamma_strip_lower {A : ℝ} (hA : BandUpper A) (hApos : 0 < A) {σ : ℝ}
    (h1 : (1:ℝ)/4 ≤ σ) (h2 : σ ≤ 2) :
    ∃ c : ℝ, 0 < c ∧ ∀ t : ℝ, 1 ≤ |t| →
      c * |t| ^ (σ - 1/2) * Real.exp (-(π/2) * |t|)
        ≤ ‖Complex.Gamma ((σ:ℝ) + (t:ℝ) * Complex.I)‖ := by
  obtain ⟨hA0, hAb⟩ := hA
  have hpi : (0:ℝ) < π := Real.pi_pos
  refine ⟨π / A, by positivity, ?_⟩
  intro t ht
  have htpos : (0:ℝ) < |t| := lt_of_lt_of_le one_pos ht
  -- partner w = 1 - (σ + it) = (1-σ) - i t,  re = 1-σ, im = -t
  set w : ℂ := 1 - ((σ:ℝ) + (t:ℝ) * Complex.I) with hw
  have hwre : w.re = 1 - σ := by rw [hw]; simp
  have hwim : w.im = -t := by rw [hw]; simp
  -- reflection in norm
  have hrefl := norm_reflection σ t
  -- ‖sin‖ ≤ cosh(πt) ≤ exp(π|t|)
  have hsin_le : ‖Complex.sin ((π * σ : ℝ) + (π * t : ℝ) * Complex.I)‖ ≤ Real.exp (π * |t|) := by
    calc ‖Complex.sin ((π * σ : ℝ) + (π * t : ℝ) * Complex.I)‖
        ≤ Real.cosh (π * t) := norm_sin_pi_le_cosh σ t
      _ ≤ Real.exp |π * t| := cosh_le_exp_abs (π * t)
      _ = Real.exp (π * |t|) := by rw [abs_mul, abs_of_pos hpi]
  -- ‖Γ w‖ ≤ A · |t|^{1/2-σ} · exp(-(π/2)|t|)
  have hGw : ‖Complex.Gamma w‖ ≤ A * |t| ^ (1/2 - σ) * Real.exp (-(π/2) * |t|) := by
    have := hAb w (by rw [hwre]; linarith) (by rw [hwre]; linarith)
      (by rw [hwim, abs_neg]; exact ht)
    rwa [hwre, hwim, abs_neg, show (1 - σ - 1/2 : ℝ) = (1/2 - σ) by ring] at this
  -- positivity facts
  have hsin_pos : 0 < ‖Complex.sin ((π * σ : ℝ) + (π * t : ℝ) * Complex.I)‖ := by
    have hsinh : Real.exp |π*t| / 4 ≤ |Real.sinh (π * t)| := by
      apply quarter_exp_abs_le_abs_sinh
      rw [abs_mul, abs_of_pos hpi]
      nlinarith [ht, Real.pi_gt_three]
    have h2' : |Real.sinh (π*t)| ≤ ‖Complex.sin ((π * σ : ℝ) + (π * t : ℝ) * Complex.I)‖ :=
      abs_sinh_le_norm_sin_pi σ t
    have : (0:ℝ) < Real.exp |π*t| / 4 := by positivity
    linarith
  -- denominator d = ‖sin‖ · ‖Γ w‖ ; we have ‖Γ(σ+it)‖ = π / d  (from reflection rearranged)
  -- Actually hrefl : ‖Γ(σ+it)‖ · ‖Γ w‖ = π / ‖sin‖.
  -- We bound ‖Γ(σ+it)‖ from below.  Need ‖Γ w‖ > 0.
  have htne : t ≠ 0 := by
    intro h; rw [h] at htpos; simp at htpos
  have hGw_pos : 0 < ‖Complex.Gamma w‖ := by
    -- Γ w ≠ 0 : poles of Γ are at non-positive integers (real), but w.im = -t ≠ 0
    have hΓne : Complex.Gamma w ≠ 0 := by
      apply Complex.Gamma_ne_zero
      intro m hcontra
      -- w = -m would force im w = 0, contradicting im w = -t ≠ 0
      have him0 : w.im = 0 := by rw [hcontra]; simp
      rw [hwim] at him0
      exact htne (neg_eq_zero.mp him0)
    exact norm_pos_iff.mpr hΓne
  -- From hrefl: ‖Γ(σ+it)‖ = (π/‖sin‖)/‖Γ w‖
  have hrefl' : ‖Complex.Gamma ((σ:ℝ) + (t:ℝ) * Complex.I)‖ * ‖Complex.Gamma w‖
      = π / ‖Complex.sin ((π * σ : ℝ) + (π * t : ℝ) * Complex.I)‖ := by
    rw [hw]; exact hrefl
  have hkey : ‖Complex.Gamma ((σ:ℝ) + (t:ℝ) * Complex.I)‖
      = (π / ‖Complex.sin ((π * σ : ℝ) + (π * t : ℝ) * Complex.I)‖) / ‖Complex.Gamma w‖ := by
    rw [← hrefl']
    field_simp
  rw [hkey]
  -- lower bound the quotient
  -- target: (π/A)·|t|^{σ-1/2}·exp(-(π/2)|t|) ≤ (π/‖sin‖)/‖Γw‖
  rw [le_div_iff₀ hGw_pos]
  -- (π/A)·|t|^{σ-1/2}·exp·‖Γw‖ ≤ π/‖sin‖
  -- use ‖Γw‖ ≤ A·|t|^{1/2-σ}·exp(-(π/2)|t|)
  have hstep1 : (π / A) * |t| ^ (σ - 1/2) * Real.exp (-(π/2) * |t|) * ‖Complex.Gamma w‖
      ≤ (π / A) * |t| ^ (σ - 1/2) * Real.exp (-(π/2) * |t|)
          * (A * |t| ^ (1/2 - σ) * Real.exp (-(π/2) * |t|)) := by
    apply mul_le_mul_of_nonneg_left hGw
    positivity
  refine hstep1.trans ?_
  -- simplify RHS = π·exp(-π|t|)  using |t|^{σ-1/2}·|t|^{1/2-σ}=1, exp·exp = exp(-π|t|), π/A·A=π
  have hpow : |t| ^ (σ - 1/2) * |t| ^ (1/2 - σ) = 1 := by
    rw [← Real.rpow_add htpos]; norm_num
  have hexp : Real.exp (-(π/2) * |t|) * Real.exp (-(π/2) * |t|) = Real.exp (-(π * |t|)) := by
    rw [← Real.exp_add]; ring_nf
  have hrhs : (π / A) * |t| ^ (σ - 1/2) * Real.exp (-(π/2) * |t|)
          * (A * |t| ^ (1/2 - σ) * Real.exp (-(π/2) * |t|))
      = π * Real.exp (-(π * |t|)) := by
    have : (π / A) * A = π := by field_simp
    calc (π / A) * |t| ^ (σ - 1/2) * Real.exp (-(π/2) * |t|)
            * (A * |t| ^ (1/2 - σ) * Real.exp (-(π/2) * |t|))
        = ((π / A) * A) * (|t| ^ (σ - 1/2) * |t| ^ (1/2 - σ))
            * (Real.exp (-(π/2) * |t|) * Real.exp (-(π/2) * |t|)) := by ring
      _ = π * 1 * Real.exp (-(π * |t|)) := by rw [this, hpow, hexp]
      _ = π * Real.exp (-(π * |t|)) := by ring
  rw [hrhs]
  -- now π·exp(-π|t|) ≤ π/‖sin‖  ⟺  ‖sin‖·exp(-π|t|) ≤ 1 (since both pos), use ‖sin‖ ≤ exp(π|t|)
  rw [le_div_iff₀ hsin_pos]
  -- π·exp(-π|t|)·‖sin‖ ≤ π
  have : ‖Complex.sin ((π * σ : ℝ) + (π * t : ℝ) * Complex.I)‖ * Real.exp (-(π * |t|))
      ≤ Real.exp (π * |t|) * Real.exp (-(π * |t|)) :=
    mul_le_mul_of_nonneg_right hsin_le (Real.exp_pos _).le
  rw [← Real.exp_add, add_neg_cancel, Real.exp_zero] at this
  nlinarith [this, hpi.le, Real.exp_pos (-(π * |t|)),
    norm_nonneg (Complex.sin ((π * σ : ℝ) + (π * t : ℝ) * Complex.I))]

/-! ### II.6  Translation to the requested `σ + t*I` argument shape (matches the prompt). -/

/-- UPPER, in the prompt's exact argument shape `σ + t*Complex.I` with `σ : ℝ` coerced. -/
theorem norm_Gamma_strip_upper' {A : ℝ} (hA : BandUpper A) {σ : ℝ}
    (h1 : (1:ℝ)/4 ≤ σ) (h2 : σ ≤ 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 1 ≤ |t| →
      ‖Complex.Gamma ((σ:ℂ) + (t:ℂ) * Complex.I)‖
        ≤ C * |t| ^ (σ - 1/2) * Real.exp (-(π/2) * |t|) :=
  norm_Gamma_strip_upper hA h1 h2

/-- LOWER, in the prompt's exact argument shape. -/
theorem norm_Gamma_strip_lower' {A : ℝ} (hA : BandUpper A) (hApos : 0 < A) {σ : ℝ}
    (h1 : (1:ℝ)/4 ≤ σ) (h2 : σ ≤ 2) :
    ∃ c : ℝ, 0 < c ∧ ∀ t : ℝ, 1 ≤ |t| →
      c * |t| ^ (σ - 1/2) * Real.exp (-(π/2) * |t|)
        ≤ ‖Complex.Gamma ((σ:ℂ) + (t:ℂ) * Complex.I)‖ :=
  norm_Gamma_strip_lower hA hApos h1 h2

end GammaDecay

-- Axiom audit
#print axioms GammaDecay.normSq_Gamma_half
#print axioms GammaDecay.norm_Gamma_half_le
#print axioms GammaDecay.le_norm_Gamma_half
#print axioms GammaDecay.norm_Gamma_vertical_line_half
#print axioms GammaDecay.normSq_sin_pi
#print axioms GammaDecay.norm_reflection
#print axioms GammaDecay.norm_Gamma_strip_upper
#print axioms GammaDecay.norm_Gamma_strip_lower
