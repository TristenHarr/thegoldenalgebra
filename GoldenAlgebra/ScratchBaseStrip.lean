/-
  ScratchBaseStrip.lean

  GOAL: prove `BandUpper.BaseStrip A₀` of `ScratchBandUpper.lean`, i.e. the Stirling-on-lines
  upper bound on the central unit strip `Re ∈ [1,2]`, `Im ≥ 1`:

      ‖Γ w‖ ≤ A₀ · (Im w)^(Re w − 1/2) · exp(−(π/2)·Im w).

  This is the irreducible analytic input of the band program.  Companion files
  `ScratchBandUpper.lean` (recurrence/conjugation reduction of the full band to this strip)
  and `ScratchGammaDecay.lean` (exact critical-line value `‖Γ(1/2+it)‖²=π/cosh(πt)`) are
  unconditional.

  See the report at the bottom of this file for exactly what is proven unconditionally.
-/
import Mathlib

open Complex Real MeasureTheory Set

noncomputable section

namespace BaseStripProof

/-! ## Step 1 (UNCONDITIONAL): the Im-independent Euler-integral bound
`‖Γ s‖ ≤ Real.Gamma (Re s)` for `0 < Re s`. -/

/-- **Euler-integral majorant.** For `0 < Re s`, `‖Γ s‖ ≤ Real.Gamma (Re s)`.
Proof: `Γ s = ∫₀^∞ e^{-x} x^{s-1}`, and `‖e^{-x} x^{s-1}‖ = e^{-x} x^{Re s - 1}`,
whose integral is `Real.Gamma (Re s)`. -/
theorem norm_Gamma_le_real (s : ℂ) (hs : 0 < s.re) :
    ‖Complex.Gamma s‖ ≤ Real.Gamma s.re := by
  rw [Complex.Gamma_eq_integral hs, Complex.GammaIntegral]
  -- ‖∫ f‖ ≤ ∫ ‖f‖
  refine (norm_integral_le_integral_norm _).trans ?_
  -- ∫ ‖e^{-x} x^{s-1}‖ = ∫ e^{-x} x^{Re s -1} = Real.Gamma (Re s)
  have hpt : ∀ x ∈ Ioi (0:ℝ),
      ‖((↑(Real.exp (-x)) : ℂ) * (↑x : ℂ) ^ (s - 1))‖ = Real.exp (-x) * x ^ (s.re - 1) := by
    intro x hx
    rw [norm_mul, Complex.norm_of_nonneg (le_of_lt (Real.exp_pos _)),
      norm_cpow_eq_rpow_re_of_pos (mem_Ioi.mp hx)]
    simp
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, Real.Gamma_eq_integral hs]

/-! ## Step 2 (UNCONDITIONAL): the comparison power `‖s^{s-1/2}‖` on the half-strip.

We will use the comparison function `F(s) := Γ(s)·e^{-(π/2)Is}·s^{1/2-s}`, so that
`Γ(s) = F(s)·s^{s-1/2}·e^{(π/2)Is}`.  Here we compute/bound the two non-`F` factors.

`s` has `Re s = σ ≥ 1/2 > 0` on the strip, so `s ≠ 0` and `arg s ≥ 0` whenever `Im s ≥ 0`,
keeping us away from the branch cut of `(·)^w` (the negative real axis) for ALL `Im`. -/

/-- `‖exp((π/2)·I·s)‖ = exp(-(π/2)·Im s)`.  (`Re((π/2)I s) = -(π/2) Im s`.) -/
theorem norm_exp_half_pi_I_mul (s : ℂ) :
    ‖Complex.exp ((Real.pi/2) * Complex.I * s)‖ = Real.exp (-(Real.pi/2) * s.im) := by
  rw [Complex.norm_exp]
  congr 1
  simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.div_ofNat_re, Complex.div_ofNat_im]
  ring

/-- **Recovery factor bound.** For `s` with `1/2 ≤ Re s ≤ 5/2` and `Im s ≥ 1`,
`‖s ^ (s - 1/2)‖ ≤ (29/4)·e^{5π/4} · (Im s) ^ (Re s - 1/2) · exp(-(π/2)·Im s)`.

The decay `exp(-(π/2)·Im s)` comes from `arg s ≈ π/2` for large `Im s`:
`‖s^(s-1/2)‖ = ‖s‖^(σ-1/2)·exp(-arg(s)·t)` and `(π/2 - arg s)·t ≤ 5π/4` (Jordan's inequality). -/
theorem norm_cpow_recovery {s : ℂ} (hre1 : (1:ℝ)/2 ≤ s.re) (hre2 : s.re ≤ 5/2)
    (him : 1 ≤ s.im) :
    ‖s ^ (s - 1/2)‖
      ≤ (29/4) * Real.exp (5 * Real.pi / 4) * s.im ^ (s.re - 1/2)
          * Real.exp (-(Real.pi/2) * s.im) := by
  have himpos : (0:ℝ) < s.im := lt_of_lt_of_le one_pos him
  have hsne : s ≠ 0 := by
    intro h; rw [h] at himpos; simp at himpos
  have hnorm_pos : 0 < ‖s‖ := norm_pos_iff.mpr hsne
  -- ‖s^(s-1/2)‖ = ‖s‖^(σ-1/2) / exp(arg s · Im(s-1/2)) = ‖s‖^(σ-1/2)·exp(-arg s·t)
  rw [norm_cpow_of_ne_zero hsne]
  have hwim : (s - 1/2).im = s.im := by simp
  have hwre : (s - 1/2).re = s.re - 1/2 := by simp
  rw [hwim, hwre]
  -- arg s ∈ [0, π/2]
  have harg0 : 0 ≤ Complex.arg s := arg_nonneg_iff.mpr himpos.le
  have hargle : Complex.arg s ≤ Real.pi/2 := arg_le_pi_div_two_iff.mpr (Or.inl (by linarith))
  -- φ := π/2 - arg s ∈ [0, π/2], sin φ = cos(arg s) = re/‖s‖
  set φ : ℝ := Real.pi/2 - Complex.arg s with hφ
  have hφ0 : 0 ≤ φ := by rw [hφ]; linarith
  have hφle : φ ≤ Real.pi/2 := by rw [hφ]; have := Real.pi_pos; linarith
  have hsinφ : Real.sin φ = s.re / ‖s‖ := by
    rw [hφ, Real.sin_pi_div_two_sub, cos_arg hsne]
  -- Jordan: 2/π·φ ≤ sin φ = re/‖s‖ ≤ re/t ≤ (5/2)/t  (since ‖s‖ ≥ im = t)
  have hnorm_ge_im : s.im ≤ ‖s‖ := by
    have := Complex.abs_im_le_norm s; rwa [abs_of_pos himpos] at this
  have hsin_le : Real.sin φ ≤ (5/2) / s.im := by
    rw [hsinφ, div_le_div_iff₀ hnorm_pos himpos]
    nlinarith [hre2, hnorm_ge_im, himpos, hnorm_pos]
  have hjordan : 2 / Real.pi * φ ≤ Real.sin φ := mul_le_sin hφ0 hφle
  -- so φ ≤ (π/2)·(5/2)/t = (5π/4)/t, hence (π/2 - arg s)·t ≤ 5π/4
  have hπpos : 0 < Real.pi := Real.pi_pos
  have hφbound : φ * s.im ≤ 5 * Real.pi / 4 := by
    have h1 : 2 / Real.pi * φ ≤ (5/2) / s.im := le_trans hjordan hsin_le
    -- 2/π·φ ≤ (5/2)/t  ⟹  (2φ)·t ≤ (5/2)·π  ⟹  φ·t ≤ 5π/4
    rw [show 2 / Real.pi * φ = (2 * φ) / Real.pi by ring, div_le_div_iff₀ hπpos himpos] at h1
    nlinarith [h1, hπpos, hφ0, himpos]
  -- exp(-arg s · t) = exp((π/2 - arg s)·t - (π/2)·t) ≤ exp(5π/4)·exp(-(π/2)t)
  have hexp_rw : ‖s‖ ^ (s.re - 1/2) / Real.exp (Complex.arg s * s.im)
      = ‖s‖ ^ (s.re - 1/2) * Real.exp (-(Complex.arg s * s.im)) := by
    rw [Real.exp_neg]; ring
  rw [hexp_rw]
  have hexp_le : Real.exp (-(Complex.arg s * s.im))
      ≤ Real.exp (5 * Real.pi / 4) * Real.exp (-(Real.pi/2) * s.im) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    -- -arg s·t ≤ 5π/4 - (π/2)t  ⟺  (π/2 - arg s)·t ≤ 5π/4 = φ·t
    have : -(Complex.arg s * s.im) = φ * s.im - (Real.pi/2) * s.im := by rw [hφ]; ring
    rw [this]; linarith [hφbound]
  -- ‖s‖^(σ-1/2) ≤ (29/4)·t^(σ-1/2)
  have he_nn : 0 ≤ s.re - 1/2 := by linarith
  have hnorm_le_rpow : ‖s‖ ^ (s.re - 1/2) ≤ (29/4) * s.im ^ (s.re - 1/2) := by
    have hbound_sq : ‖s‖ ^ 2 ≤ (Real.sqrt (29/4) * s.im) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by norm_num),
        show ‖s‖ ^ 2 = s.re ^ 2 + s.im ^ 2 by
          rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring]
      nlinarith [hre1, hre2, him, sq_nonneg s.re, sq_nonneg s.im]
    have hnorm_le : ‖s‖ ≤ Real.sqrt (29/4) * s.im := by
      have h1 : (0:ℝ) ≤ Real.sqrt (29/4) * s.im := by positivity
      nlinarith [hbound_sq, hnorm_pos.le, h1, sq_nonneg (‖s‖ - Real.sqrt (29/4) * s.im)]
    calc ‖s‖ ^ (s.re - 1/2)
        ≤ (Real.sqrt (29/4) * s.im) ^ (s.re - 1/2) :=
          Real.rpow_le_rpow hnorm_pos.le hnorm_le he_nn
      _ = Real.sqrt (29/4) ^ (s.re - 1/2) * s.im ^ (s.re - 1/2) :=
          Real.mul_rpow (Real.sqrt_nonneg _) himpos.le
      _ ≤ (29/4) * s.im ^ (s.re - 1/2) := by
          apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg himpos.le _)
          have hb1 : (1:ℝ) ≤ Real.sqrt (29/4) := by
            rw [show (1:ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt (by norm_num)
          calc Real.sqrt (29/4) ^ (s.re - 1/2)
              ≤ Real.sqrt (29/4) ^ (2:ℝ) :=
                Real.rpow_le_rpow_of_exponent_le hb1 (by linarith)
            _ = 29/4 := by
                rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast,
                  Real.sq_sqrt (by norm_num)]
  -- assemble: ‖s‖^(σ-1/2)·exp(-arg s·t) ≤ (29/4 t^(σ-1/2))·(e^{5π/4} e^{-(π/2)t})
  calc ‖s‖ ^ (s.re - 1/2) * Real.exp (-(Complex.arg s * s.im))
      ≤ ((29/4) * s.im ^ (s.re - 1/2))
          * (Real.exp (5 * Real.pi / 4) * Real.exp (-(Real.pi/2) * s.im)) :=
        mul_le_mul hnorm_le_rpow hexp_le (Real.exp_pos _).le
          (by positivity)
    _ = (29/4) * Real.exp (5 * Real.pi / 4) * s.im ^ (s.re - 1/2)
          * Real.exp (-(Real.pi/2) * s.im) := by ring

/-! ## Step 3: the comparison ("de-Stirling-ised") function and the factorisation identity.

`F(s) := Γ(s) · exp s · s^(1/2 - s)`.  Then `Γ(s) = F(s) · s^(s-1/2) · exp(-s)`, and in norm
`‖Γ s‖ = ‖F s‖ · ‖s^(s-1/2)‖ · exp(-Re s)` (because `‖exp(-s)‖ = exp(-Re s)` and
`‖s^(1/2-s)‖·‖s^(s-1/2)‖ = 1`).  This isolates the polynomial+decay factor `s^(s-1/2)` (bounded
unconditionally above by `norm_cpow_recovery`) from the genuinely Stirling part `F`, which is
*bounded* on the strip (that boundedness is the irreducible analytic core). -/

/-- The comparison function. -/
def Fcmp (s : ℂ) : ℂ := Complex.Gamma s * Complex.exp s * s ^ (1/2 - s)

/-- **Factorisation in norm.** For `s ≠ 0`,
`‖Γ s‖ = ‖Fcmp s‖ · ‖s ^ (s - 1/2)‖ · exp(-Re s)`. -/
theorem norm_Gamma_factor {s : ℂ} (hsne : s ≠ 0) :
    ‖Complex.Gamma s‖ = ‖Fcmp s‖ * ‖s ^ (s - 1/2)‖ * Real.exp (-s.re) := by
  -- ‖Fcmp s‖ = ‖Γ s‖·exp(Re s)·‖s^(1/2-s)‖
  have hexp : ‖Complex.exp s‖ = Real.exp s.re := Complex.norm_exp s
  have hcpow_mul : ‖s ^ (1/2 - s)‖ * ‖s ^ (s - 1/2)‖ = 1 := by
    rw [← norm_mul, ← Complex.cpow_add _ _ hsne,
      show (1/2 - s) + (s - 1/2) = 0 by ring, Complex.cpow_zero, norm_one]
  rw [Fcmp, norm_mul, norm_mul, hexp]
  -- goal: ‖Γ s‖ = ‖Γ s‖·exp(Re s)·‖s^(1/2-s)‖ · ‖s^(s-1/2)‖ · exp(-Re s)
  have hee : Real.exp s.re * Real.exp (-s.re) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  calc ‖Complex.Gamma s‖
      = ‖Complex.Gamma s‖ * (Real.exp s.re * Real.exp (-s.re))
          * (‖s ^ (1/2 - s)‖ * ‖s ^ (s - 1/2)‖) := by rw [hee, hcpow_mul]; ring
    _ = ‖Complex.Gamma s‖ * Real.exp s.re * ‖s ^ (1/2 - s)‖ * ‖s ^ (s - 1/2)‖
          * Real.exp (-s.re) := by ring

/-! ## The residual: boundedness of `Fcmp` on the half-strip.

This is the single irreducible analytic input.  It is the genuine Stirling content
(`Γ(s) ~ √(2π) s^(s-1/2) e^{-s}`, i.e. `Fcmp(s) → √(2π)`); a non-integer power of `|t|`
together with the exponential decay rate cannot be produced by elementary manipulation, so a
maximum-principle / Phragmén–Lindelöf argument is unavoidable.  It is stated for `Im ≥ 1` and
`Re ∈ [1/2, 5/2]`, exactly the region the recovery factor controls. -/
def FcmpBounded (C : ℝ) : Prop :=
  0 ≤ C ∧ ∀ s : ℂ, (1:ℝ)/2 ≤ s.re → s.re ≤ 5/2 → 1 ≤ s.im → ‖Fcmp s‖ ≤ C

/-! ## Auxiliary uniform bounds used by the Phragmén–Lindelöf argument. -/

/-- `|arg s| ≤ π/2` whenever `0 ≤ Re s`, hence `arg s · Im s ≤ (π/2)·|Im s|`. -/
theorem arg_mul_im_le {s : ℂ} (hre : 0 ≤ s.re) :
    Complex.arg s * s.im ≤ (Real.pi/2) * |s.im| := by
  have h1 : Complex.arg s ≤ Real.pi/2 := arg_le_pi_div_two_iff.mpr (Or.inl hre)
  have h2 : -(Real.pi/2) ≤ Complex.arg s := neg_pi_div_two_le_arg_iff.mpr (Or.inl hre)
  have habs : |Complex.arg s| ≤ Real.pi/2 := abs_le.mpr ⟨h2, h1⟩
  calc Complex.arg s * s.im ≤ |Complex.arg s * s.im| := le_abs_self _
    _ = |Complex.arg s| * |s.im| := abs_mul _ _
    _ ≤ (Real.pi/2) * |s.im| := by
        apply mul_le_mul_of_nonneg_right habs (abs_nonneg _)

/-- **Uniform single-exponential bound on the comparison power.**  For `s ≠ 0` with `0 ≤ Re s`,
`‖s ^ (1/2 - s)‖ ≤ ‖s‖ ^ (1/2 - Re s) · exp((π/2)·|Im s|)`. -/
theorem norm_cpow_half_sub_le {s : ℂ} (hsne : s ≠ 0) (hre : 0 ≤ s.re) :
    ‖s ^ (1/2 - s)‖ ≤ ‖s‖ ^ (1/2 - s.re) * Real.exp ((Real.pi/2) * |s.im|) := by
  rw [norm_cpow_of_ne_zero hsne]
  have hwre : (1/2 - s).re = 1/2 - s.re := by simp
  have hwim : (1/2 - s).im = -s.im := by simp
  rw [hwre, hwim]
  -- ‖s‖^(1/2-re)/exp(arg s·(-im)) = ‖s‖^(1/2-re)·exp(arg s·im)
  rw [show Complex.arg s * -s.im = -(Complex.arg s * s.im) by ring, Real.exp_neg, div_inv_eq_mul]
  apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (norm_nonneg _) _)
  exact Real.exp_le_exp.mpr (arg_mul_im_le hre)

/-! ## Critical-line bound (re-proved here, ported from `ScratchGammaDecay.lean`).

`‖Γ(1/2 + i t)‖ ≤ √(2π)·e^{-(π/2)|t|}` for all real `t`.  This is the unconditional
sharp critical-line decay; we use it to bound `Fcmp` on the two strip edges. -/

private theorem sin_pi_half_add_I (t : ℝ) :
    Complex.sin (↑Real.pi * (1/2 + (t : ℂ) * Complex.I)) = (Real.cosh (Real.pi * t) : ℂ) := by
  have hsplit : (↑Real.pi : ℂ) * (1/2 + (t : ℂ) * Complex.I)
      = (↑Real.pi/2 : ℂ) + ((Real.pi * t : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [hsplit, show (↑Real.pi/2 : ℂ) + ((Real.pi * t : ℝ) : ℂ) * Complex.I
      = ↑Real.pi/2 - (-(((Real.pi * t : ℝ) : ℂ) * Complex.I)) by ring,
    Complex.sin_pi_div_two_sub, Complex.cos_neg, Complex.cos_mul_I, ← Complex.ofReal_cosh]

private theorem normSq_Gamma_half (t : ℝ) :
    ‖Complex.Gamma (1/2 + (t : ℂ) * Complex.I)‖ ^ 2 = Real.pi / Real.cosh (Real.pi * t) := by
  set s : ℂ := 1/2 + (t : ℂ) * Complex.I with hs
  have hconj : (1 : ℂ) - s = (starRingEnd ℂ) s := by
    rw [hs]; apply Complex.ext
    · simp [Complex.sub_re, Complex.add_re, Complex.mul_re]; norm_num
    · simp [Complex.sub_im, Complex.add_im, Complex.mul_im]
  have hrefl := Complex.Gamma_mul_Gamma_one_sub s
  rw [hconj, Complex.Gamma_conj] at hrefl
  have hmulconj : Complex.Gamma s * (starRingEnd ℂ) (Complex.Gamma s)
      = ((‖Complex.Gamma s‖ ^ 2 : ℝ) : ℂ) := by rw [Complex.mul_conj']; push_cast; ring
  have hsin : Complex.sin (↑Real.pi * s) = (Real.cosh (Real.pi * t) : ℂ) := by
    rw [hs]; exact sin_pi_half_add_I t
  rw [hmulconj, hsin] at hrefl
  have hreal : ((‖Complex.Gamma s‖ ^ 2 : ℝ) : ℂ)
      = ((Real.pi / Real.cosh (Real.pi * t) : ℝ) : ℂ) := by rw [hrefl]; push_cast; ring
  exact_mod_cast hreal

/-- **Sharp critical-line upper bound.** -/
theorem norm_Gamma_half_le (t : ℝ) :
    ‖Complex.Gamma (1/2 + (t : ℂ) * Complex.I)‖
      ≤ Real.sqrt (2 * Real.pi) * Real.exp (-(Real.pi/2) * |t|) := by
  have hpi : (0:ℝ) < Real.pi := Real.pi_pos
  have hcosh_pos : 0 < Real.cosh (Real.pi * t) := Real.cosh_pos _
  have hsq := normSq_Gamma_half t
  have hcosh_abs_lb : Real.exp |Real.pi * t| / 2 ≤ Real.cosh (Real.pi * t) := by
    rw [← Real.cosh_abs, Real.cosh_eq]
    have : Real.exp |Real.pi*t| ≤ Real.exp |Real.pi*t| + Real.exp (-|Real.pi*t|) := by
      linarith [(Real.exp_pos (-|Real.pi*t|)).le]
    linarith
  have hcosh_lb : Real.exp (Real.pi * |t|) / 2 ≤ Real.cosh (Real.pi * t) := by
    rwa [abs_mul, abs_of_pos hpi] at hcosh_abs_lb
  have hquot : Real.pi / Real.cosh (Real.pi * t) ≤ 2 * Real.pi * Real.exp (-(Real.pi * |t|)) := by
    rw [div_le_iff₀ hcosh_pos]
    have hle : 2 * Real.pi * Real.exp (-(Real.pi * |t|)) * Real.cosh (Real.pi * t)
        ≥ 2 * Real.pi * Real.exp (-(Real.pi * |t|)) * (Real.exp (Real.pi * |t|) / 2) :=
      mul_le_mul_of_nonneg_left hcosh_lb (by positivity)
    have hsimp : 2 * Real.pi * Real.exp (-(Real.pi * |t|)) * (Real.exp (Real.pi * |t|) / 2)
        = Real.pi := by rw [Real.exp_neg]; field_simp
    linarith [hsimp ▸ hle]
  have hnormsq_le : ‖Complex.Gamma (1/2 + (t : ℂ) * Complex.I)‖ ^ 2
      ≤ (Real.sqrt (2 * Real.pi) * Real.exp (-(Real.pi/2) * |t|)) ^ 2 := by
    rw [hsq]
    have hrhs : (Real.sqrt (2 * Real.pi) * Real.exp (-(Real.pi/2) * |t|)) ^ 2
        = 2 * Real.pi * Real.exp (-(Real.pi * |t|)) := by
      rw [mul_pow, Real.sq_sqrt (by positivity), ← Real.exp_nat_mul]; ring_nf
    rw [hrhs]; exact hquot
  have hb_nonneg : 0 ≤ Real.sqrt (2 * Real.pi) * Real.exp (-(Real.pi/2) * |t|) := by positivity
  nlinarith [norm_nonneg (Complex.Gamma (1/2 + (t : ℂ) * Complex.I)), hnormsq_le, hb_nonneg,
    sq_nonneg (‖Complex.Gamma (1/2 + (t : ℂ) * Complex.I)‖
      - Real.sqrt (2 * Real.pi) * Real.exp (-(Real.pi/2) * |t|))]

/-! ## Edge bounds for `Fcmp` (unconditional, all `Im`). -/

/-- A point with `Re s = 1/2` equals `1/2 + (Im s)·I`. -/
private theorem eq_half_add {s : ℂ} (hs : s.re = 1/2) : s = 1/2 + (s.im : ℂ) * Complex.I := by
  apply Complex.ext
  · rw [hs]; simp
  · simp

/-- A point with `Re s = 5/2` equals `5/2 + (Im s)·I`. -/
private theorem eq_fiveHalf_add {s : ℂ} (hs : s.re = 5/2) :
    s = 5/2 + (s.im : ℂ) * Complex.I := by
  apply Complex.ext
  · rw [hs]; simp
  · simp

/-- **Left edge bound.**  `‖Fcmp s‖ ≤ √(2π)·e^{1/2}` for `Re s = 1/2`. -/
theorem Fcmp_edge_left {s : ℂ} (hs : s.re = 1/2) :
    ‖Fcmp s‖ ≤ Real.sqrt (2 * Real.pi) * Real.exp (1/2) := by
  have hsne : s ≠ 0 := by
    intro h; rw [h] at hs; simp at hs
  have hre0 : (0:ℝ) ≤ s.re := by rw [hs]; norm_num
  -- ‖Fcmp s‖ = ‖Γ s‖·e^{re}·‖s^{1/2-s}‖
  rw [Fcmp, norm_mul, norm_mul, Complex.norm_exp]
  -- bound ‖s^{1/2-s}‖ ≤ ‖s‖^0·e^{(π/2)|im|} = e^{(π/2)|im|}
  have hcpow : ‖s ^ (1/2 - s)‖ ≤ Real.exp ((Real.pi/2) * |s.im|) := by
    have h := norm_cpow_half_sub_le hsne hre0
    rwa [hs, sub_self, Real.rpow_zero, one_mul] at h
  -- bound ‖Γ s‖ ≤ √(2π)·e^{-(π/2)|im|}
  have hGamma : ‖Complex.Gamma s‖ ≤ Real.sqrt (2 * Real.pi) * Real.exp (-(Real.pi/2) * |s.im|) := by
    have h := norm_Gamma_half_le s.im
    rwa [← eq_half_add hs] at h
  -- assemble
  rw [hs]
  have hGnn : 0 ≤ ‖Complex.Gamma s‖ := norm_nonneg _
  have hcnn : 0 ≤ ‖s ^ (1/2 - s)‖ := norm_nonneg _
  calc ‖Complex.Gamma s‖ * Real.exp (1/2) * ‖s ^ (1/2 - s)‖
      ≤ (Real.sqrt (2 * Real.pi) * Real.exp (-(Real.pi/2) * |s.im|)) * Real.exp (1/2)
          * Real.exp ((Real.pi/2) * |s.im|) := by
        apply mul_le_mul _ hcpow hcnn (by positivity)
        apply mul_le_mul_of_nonneg_right hGamma (Real.exp_pos _).le
    _ = Real.sqrt (2 * Real.pi) * Real.exp (1/2) := by
        rw [show -(Real.pi/2) * |s.im| = -((Real.pi/2) * |s.im|) by ring]
        rw [show Real.sqrt (2 * Real.pi) * Real.exp (-((Real.pi/2) * |s.im|)) * Real.exp (1/2)
            * Real.exp ((Real.pi/2) * |s.im|)
          = Real.sqrt (2 * Real.pi) * Real.exp (1/2)
            * (Real.exp (-((Real.pi/2) * |s.im|)) * Real.exp ((Real.pi/2) * |s.im|)) by ring,
          ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]

/-- **Right edge bound.**  `‖Fcmp s‖ ≤ √(2π)·e^{5/2}` for `Re s = 5/2`. -/
theorem Fcmp_edge_right {s : ℂ} (hs : s.re = 5/2) :
    ‖Fcmp s‖ ≤ Real.sqrt (2 * Real.pi) * Real.exp (5/2) := by
  have hsne : s ≠ 0 := by intro h; rw [h] at hs; simp at hs; norm_num at hs
  have hre0 : (0:ℝ) ≤ s.re := by rw [hs]; norm_num
  -- u := 1/2 + im·I  ;  s = u + 2
  set u : ℂ := 1/2 + (s.im : ℂ) * Complex.I with hu
  have hure : u.re = 1/2 := by rw [hu]; simp
  have huim : u.im = s.im := by rw [hu]; simp
  have hsu : s = u + 2 := by
    rw [hu]; apply Complex.ext
    · rw [hs]; simp; norm_num
    · simp
  -- recurrence: Γ(u+2) = (u+1)·u·Γ u
  have hune : u ≠ 0 := by intro h; rw [h] at hure; norm_num at hure
  have hu1ne : u + 1 ≠ 0 := by
    intro h; have : (u + 1).re = 0 := by rw [h]; simp
    rw [Complex.add_re, hure] at this; norm_num at this
  have hrec1 : Complex.Gamma (u + 1) = u * Complex.Gamma u := Complex.Gamma_add_one u hune
  have hrec2 : Complex.Gamma (u + 1 + 1) = (u + 1) * Complex.Gamma (u + 1) :=
    Complex.Gamma_add_one (u + 1) hu1ne
  have hGs : Complex.Gamma s = (u + 1) * (u * Complex.Gamma u) := by
    rw [hsu, show u + 2 = u + 1 + 1 by ring, hrec2, hrec1]
  -- ‖Γ s‖ = ‖u+1‖·‖u‖·‖Γ u‖ ≤ ‖u+1‖·‖u‖·√(2π)e^{-(π/2)|im|}
  have hGu : ‖Complex.Gamma u‖ ≤ Real.sqrt (2 * Real.pi) * Real.exp (-(Real.pi/2) * |s.im|) := by
    have h := norm_Gamma_half_le s.im
    rw [show (1/2 : ℂ) + (s.im : ℂ) * Complex.I = u from hu.symm] at h
    exact h
  have hGsnorm : ‖Complex.Gamma s‖
      ≤ ‖u + 1‖ * ‖u‖ * (Real.sqrt (2 * Real.pi) * Real.exp (-(Real.pi/2) * |s.im|)) := by
    rw [hGs, norm_mul, norm_mul, mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    exact mul_le_mul_of_nonneg_left hGu (norm_nonneg _)
  -- ‖s^{1/2-s}‖ ≤ ‖s‖^{-2}·e^{(π/2)|im|}
  have hcpow : ‖s ^ (1/2 - s)‖ ≤ ‖s‖ ^ (-2 : ℝ) * Real.exp ((Real.pi/2) * |s.im|) := by
    have h := norm_cpow_half_sub_le hsne hre0
    rwa [hs, show (1/2 : ℝ) - 5/2 = -2 by norm_num] at h
  -- key: ‖u+1‖·‖u‖·‖s‖^{-2} ≤ 1, i.e. ‖u+1‖·‖u‖ ≤ ‖s‖²
  have hnorm_pos : 0 < ‖s‖ := norm_pos_iff.mpr hsne
  have hsq_u : ‖u‖ ^ 2 = (1/2)^2 + s.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, hure, huim]; ring
  have hsq_u1 : ‖u + 1‖ ^ 2 = (3/2)^2 + s.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.add_im, hure, huim, Complex.one_re, Complex.one_im]
    ring
  have hsq_s : ‖s‖ ^ 2 = (5/2)^2 + s.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, hs]; ring
  have hkey : ‖u + 1‖ * ‖u‖ ≤ ‖s‖ ^ 2 := by
    have h1 : (‖u + 1‖ * ‖u‖) ^ 2 ≤ (‖s‖ ^ 2) ^ 2 := by
      rw [mul_pow, hsq_u, hsq_u1, hsq_s]
      nlinarith [sq_nonneg s.im]
    have h2 : 0 ≤ ‖u + 1‖ * ‖u‖ := by positivity
    have h3 : 0 ≤ ‖s‖ ^ 2 := by positivity
    nlinarith [h1, h2, h3, sq_nonneg (‖u + 1‖ * ‖u‖ - ‖s‖ ^ 2)]
  -- assemble
  rw [Fcmp, norm_mul, norm_mul, Complex.norm_exp, hs]
  -- ‖Γ s‖·e^{5/2}·‖s^{1/2-s}‖ ≤ (‖u+1‖‖u‖√(2π)e^{-(π/2)|im|})·e^{5/2}·(‖s‖^{-2}e^{(π/2)|im|})
  have hGnn : 0 ≤ ‖Complex.Gamma s‖ := norm_nonneg _
  have hcnn : 0 ≤ ‖s ^ (1/2 - s)‖ := norm_nonneg _
  have hrpow_neg2 : ‖s‖ ^ (-2 : ℝ) = (‖s‖ ^ 2)⁻¹ := by
    rw [Real.rpow_neg hnorm_pos.le, show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]
  calc ‖Complex.Gamma s‖ * Real.exp (5/2) * ‖s ^ (1/2 - s)‖
      ≤ (‖u + 1‖ * ‖u‖ * (Real.sqrt (2 * Real.pi) * Real.exp (-(Real.pi/2) * |s.im|)))
          * Real.exp (5/2) * (‖s‖ ^ (-2 : ℝ) * Real.exp ((Real.pi/2) * |s.im|)) := by
        apply mul_le_mul _ hcpow hcnn (by positivity)
        apply mul_le_mul_of_nonneg_right hGsnorm (Real.exp_pos _).le
    _ ≤ Real.sqrt (2 * Real.pi) * Real.exp (5/2) := by
        rw [hrpow_neg2]
        -- = √(2π)·e^{5/2}·(‖u+1‖‖u‖/‖s‖²)·(e^{-(π/2)|im|}e^{(π/2)|im|})
        rw [show -(Real.pi/2) * |s.im| = -((Real.pi/2) * |s.im|) by ring,
          show (‖u + 1‖ * ‖u‖ * (Real.sqrt (2 * Real.pi) * Real.exp (-((Real.pi/2) * |s.im|))))
              * Real.exp (5/2) * ((‖s‖ ^ 2)⁻¹ * Real.exp ((Real.pi/2) * |s.im|))
            = Real.sqrt (2 * Real.pi) * Real.exp (5/2) * ((‖u + 1‖ * ‖u‖) * (‖s‖ ^ 2)⁻¹)
              * (Real.exp (-((Real.pi/2) * |s.im|)) * Real.exp ((Real.pi/2) * |s.im|)) by ring,
          ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]
        -- now √(2π)e^{5/2}·(‖u+1‖‖u‖/‖s‖²) ≤ √(2π)e^{5/2}·1
        have hfrac : (‖u + 1‖ * ‖u‖) * (‖s‖ ^ 2)⁻¹ ≤ 1 := by
          rw [mul_inv_le_iff₀ (by positivity), one_mul]; exact hkey
        have hfrac0 : 0 ≤ (‖u + 1‖ * ‖u‖) * (‖s‖ ^ 2)⁻¹ := by positivity
        calc Real.sqrt (2 * Real.pi) * Real.exp (5/2) * ((‖u + 1‖ * ‖u‖) * (‖s‖ ^ 2)⁻¹)
            ≤ Real.sqrt (2 * Real.pi) * Real.exp (5/2) * 1 :=
              mul_le_mul_of_nonneg_left hfrac (by positivity)
          _ = Real.sqrt (2 * Real.pi) * Real.exp (5/2) := mul_one _

/-! ## Differentiability and growth of `Fcmp` (for the Phragmén–Lindelöf step). -/

/-- `Fcmp` is complex-differentiable at every `s` with `0 < Re s`. -/
theorem differentiableAt_Fcmp {s : ℂ} (hs : 0 < s.re) : DifferentiableAt ℂ Fcmp s := by
  have hΓ : DifferentiableAt ℂ Complex.Gamma s :=
    Complex.differentiableAt_Gamma s (fun m => by
      intro h
      have hre : s.re = (-(m:ℂ)).re := by rw [h]
      rw [Complex.neg_re, Complex.natCast_re] at hre
      have : (0:ℝ) ≤ (m:ℝ) := Nat.cast_nonneg m
      rw [hre] at hs; linarith)
  have hexp : DifferentiableAt ℂ Complex.exp s := Complex.differentiable_exp s
  have hslit : s ∈ Complex.slitPlane := Complex.mem_slitPlane_iff.mpr (Or.inl hs)
  have hg : DifferentiableAt ℂ (fun z : ℂ => (1:ℂ)/2 - z) s :=
    (differentiableAt_const _).sub differentiableAt_id
  have hcpow : DifferentiableAt ℂ (fun z : ℂ => z ^ ((1:ℂ)/2 - z)) s :=
    DifferentiableAt.cpow differentiableAt_id hg hslit
  exact (hΓ.mul hexp).mul hcpow

/-- `DiffContOnCl` of `Fcmp` on the open vertical strip `re ∈ (1/2, 5/2)`. -/
theorem diffContOnCl_Fcmp :
    DiffContOnCl ℂ Fcmp (Complex.re ⁻¹' Set.Ioo (1/2 : ℝ) (5/2)) := by
  -- Fcmp is differentiable on the open set {re > 0} ⊇ closure of the strip.
  have hopen : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hdiff : DifferentiableOn ℂ Fcmp {z : ℂ | 0 < z.re} := fun z hz =>
    (differentiableAt_Fcmp hz).differentiableWithinAt
  apply DifferentiableOn.diffContOnCl
  -- need DifferentiableOn on closure (re ∈ [1/2,5/2]); it lies in {re>0}
  have hsub : closure (Complex.re ⁻¹' Set.Ioo (1/2 : ℝ) (5/2)) ⊆ {z : ℂ | 0 < z.re} := by
    intro z hz
    have : z ∈ Complex.re ⁻¹' Set.Icc (1/2 : ℝ) (5/2) := by
      have hcl : closure (Complex.re ⁻¹' Set.Ioo (1/2 : ℝ) (5/2))
          ⊆ Complex.re ⁻¹' (closure (Set.Ioo (1/2 : ℝ) (5/2))) := by
        apply closure_minimal _ (IsClosed.preimage Complex.continuous_re isClosed_closure)
        exact preimage_mono subset_closure
      have := hcl hz
      rwa [closure_Ioo (by norm_num : (1/2 : ℝ) ≠ 5/2)] at this
    simp only [Set.mem_preimage, Set.mem_Icc] at this
    simp only [Set.mem_setOf_eq]; linarith [this.1]
  exact hdiff.mono hsub

/-- `Real.Gamma` is bounded on `[1/2, 5/2]` by some `Γmax`. -/
theorem exists_Gamma_bound :
    ∃ Γmax : ℝ, 0 ≤ Γmax ∧ ∀ x ∈ Set.Icc (1/2 : ℝ) (5/2), Real.Gamma x ≤ Γmax := by
  have hcont : ContinuousOn Real.Gamma (Set.Icc (1/2 : ℝ) (5/2)) := by
    apply ContinuousOn.mono (s := Set.Ioi 0) _ (by
      intro x hx; simp only [Set.mem_Ioi]; simp only [Set.mem_Icc] at hx; linarith [hx.1])
    exact fun x hx => (Real.differentiableAt_Gamma (by
      intro m; have : (0:ℝ) ≤ (m:ℝ) := Nat.cast_nonneg m
      have hx := Set.mem_Ioi.mp hx; linarith)).continuousAt.continuousWithinAt
  obtain ⟨C, hC⟩ := (isCompact_Icc).exists_bound_of_continuousOn hcont
  refine ⟨max C 0, le_max_right _ _, fun x hx => ?_⟩
  exact (le_abs_self _).trans ((hC x hx).trans (le_max_left _ _))

/-- **Single-exponential growth of `Fcmp` on the strip.**  For `s` with `0 < Re s ≤ 5/2`,
`‖Fcmp s‖ ≤ (Γmax · e^{5/2}) · exp((π/2)·|Im s|)`. -/
theorem Fcmp_growth {Γmax : ℝ} (hΓmax : ∀ x ∈ Set.Icc (1/2 : ℝ) (5/2), Real.Gamma x ≤ Γmax)
    {s : ℂ} (hre1 : (1:ℝ)/2 ≤ s.re) (hre2 : s.re ≤ 5/2) (hsne : s ≠ 0) (hnorm1 : 1 ≤ ‖s‖) :
    ‖Fcmp s‖ ≤ (Γmax * Real.exp (5/2)) * Real.exp ((Real.pi/2) * |s.im|) := by
  have hre0 : 0 < s.re := by linarith
  rw [Fcmp, norm_mul, norm_mul, Complex.norm_exp]
  -- ‖Γ s‖ ≤ Real.Gamma (re s) ≤ Γmax
  have hΓ : ‖Complex.Gamma s‖ ≤ Γmax :=
    (norm_Gamma_le_real s hre0).trans (hΓmax s.re ⟨hre1, hre2⟩)
  have hΓ0 : 0 ≤ Γmax := le_trans (norm_nonneg _) hΓ
  -- e^{re s} ≤ e^{5/2}
  have hexp_re : Real.exp s.re ≤ Real.exp (5/2) := Real.exp_le_exp.mpr hre2
  -- ‖s^{1/2-s}‖ ≤ ‖s‖^{1/2-re}·e^{(π/2)|im|} ≤ e^{(π/2)|im|}  (since ‖s‖≥1, exponent ≤0)
  have hcpow : ‖s ^ (1/2 - s)‖ ≤ Real.exp ((Real.pi/2) * |s.im|) := by
    refine (norm_cpow_half_sub_le hsne hre0.le).trans ?_
    have hexp_nn : 0 ≤ s.re - 1/2 := by linarith
    have : ‖s‖ ^ (1/2 - s.re) ≤ 1 := by
      rw [show (1/2 : ℝ) - s.re = -(s.re - 1/2) by ring, Real.rpow_neg (by linarith)]
      rw [inv_le_one_iff₀]; right
      exact Real.one_le_rpow hnorm1 hexp_nn
    calc ‖s‖ ^ (1/2 - s.re) * Real.exp ((Real.pi/2) * |s.im|)
        ≤ 1 * Real.exp ((Real.pi/2) * |s.im|) :=
          mul_le_mul_of_nonneg_right this (Real.exp_pos _).le
      _ = Real.exp ((Real.pi/2) * |s.im|) := one_mul _
  -- assemble
  calc ‖Complex.Gamma s‖ * Real.exp s.re * ‖s ^ (1/2 - s)‖
      ≤ Γmax * Real.exp (5/2) * Real.exp ((Real.pi/2) * |s.im|) := by
        apply mul_le_mul _ hcpow (norm_nonneg _) (by positivity)
        exact mul_le_mul hΓ hexp_re (Real.exp_pos _).le hΓ0

/-! ## The Phragmén–Lindelöf step: `Fcmp` is bounded on the strip. -/

open Filter Asymptotics in
/-- **`FcmpBounded` — the residual, now PROVED.**  `Fcmp` is bounded on the half-strip by
`C := √(2π)·e^{5/2}` (the larger of the two edge bounds).  The proof is Phragmén–Lindelöf in the
vertical strip `re ∈ (1/2, 5/2)`: `Fcmp` is holomorphic there, has single-exponential growth in
`|Im|` (far below the double-exponential threshold `c < π/(5/2−1/2) = π/2`), and is bounded by `C`
on both edges (unconditional, from the sharp critical-line bound + recurrence). -/
theorem Fcmp_bounded : FcmpBounded (Real.sqrt (2 * Real.pi) * Real.exp (5/2)) := by
  set C : ℝ := Real.sqrt (2 * Real.pi) * Real.exp (5/2) with hC
  have hC0 : 0 ≤ C := by rw [hC]; positivity
  refine ⟨hC0, ?_⟩
  -- It suffices to prove ‖Fcmp s‖ ≤ C for ALL s with re ∈ [1/2, 5/2] (PL conclusion).
  obtain ⟨Γmax, hΓmax0, hΓmax⟩ := exists_Gamma_bound
  have hPL : ∀ z : ℂ, (1/2 : ℝ) ≤ z.re → z.re ≤ 5/2 → ‖Fcmp z‖ ≤ C := by
    intro z hz1 hz2
    -- growth O-estimate with c = 1 < π/2
    have hgrowth : ∃ c < Real.pi / (5/2 - 1/2), ∃ B,
        Fcmp =O[comap (_root_.abs ∘ Complex.im) atTop ⊓ 𝓟 (Complex.re ⁻¹' Set.Ioo (1/2 : ℝ) (5/2))]
          fun w => Real.exp (B * Real.exp (c * |w.im|)) := by
      refine ⟨1, by rw [show (5:ℝ)/2 - 1/2 = 2 by norm_num]; nlinarith [Real.pi_gt_three],
        Real.pi/2, ?_⟩
      rw [isBigO_iff]
      refine ⟨Γmax * Real.exp (5/2), ?_⟩
      rw [eventually_inf_principal]
      -- eventually in |im|→∞ : need |im| ≥ 1 (so ‖w‖ ≥ 1) ; provide via comap atTop
      have hev : ∀ᶠ w : ℂ in comap (_root_.abs ∘ Complex.im) atTop, 1 ≤ |w.im| := by
        have : ∀ᶠ r : ℝ in atTop, (1:ℝ) ≤ r := eventually_ge_atTop 1
        exact (this.comap (_root_.abs ∘ Complex.im))
      filter_upwards [hev] with w hw1 hwInStrip
      -- w in open strip ⇒ re ∈ (1/2,5/2), and |im| ≥ 1
      simp only [Set.mem_preimage, Set.mem_Ioo] at hwInStrip
      have hwne : w ≠ 0 := by
        intro h; rw [h] at hw1; simp at hw1; linarith
      have hnorm1 : 1 ≤ ‖w‖ := le_trans hw1 ((Complex.abs_im_le_norm w))
      have hg := Fcmp_growth hΓmax (le_of_lt hwInStrip.1) (le_of_lt hwInStrip.2) hwne hnorm1
      -- ‖Fcmp w‖ ≤ K·exp((π/2)|im|) ≤ K·‖exp((π/2)·exp(1·|im|))‖
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      refine hg.trans ?_
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Real.exp_le_exp.mpr
      -- (π/2)|im| ≤ (π/2)·exp(|im|) since |im| ≤ exp(|im|)
      have : |w.im| ≤ Real.exp (1 * |w.im|) := by
        rw [one_mul]; exact (Real.add_one_le_exp _).trans' (by linarith) |>.trans' (le_refl _)
      nlinarith [Real.pi_pos, this, abs_nonneg w.im, (Real.exp_pos (1 * |w.im|)).le]
    -- edge bounds
    have hedgeL : ∀ w : ℂ, w.re = 1/2 → ‖Fcmp w‖ ≤ C := fun w hw => by
      refine (Fcmp_edge_left hw).trans ?_
      rw [hC]
      apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by norm_num)) (Real.sqrt_nonneg _)
    have hedgeR : ∀ w : ℂ, w.re = 5/2 → ‖Fcmp w‖ ≤ C := fun w hw => Fcmp_edge_right hw
    exact PhragmenLindelof.vertical_strip diffContOnCl_Fcmp hgrowth hedgeL hedgeR hz1 hz2
  -- specialise to the half-strip Im ≥ 1
  intro s hre1 hre2 _him
  exact hPL s hre1 hre2

/-! ## Step 4: from `FcmpBounded` to the central strip bound `Re ∈ [1,2]`, `Im ≥ 1`. -/

/-- **Conditional `BaseStrip` on `Re ∈ [1,2]`.**  Given boundedness of the Stirling-comparison
function `Fcmp`, the target Stirling-on-lines bound holds on the central strip, with explicit
constant `A₀ = C · (29/4) · e^{5π/4}`. -/
theorem baseStrip_of_FcmpBounded {C : ℝ} (h : FcmpBounded C) :
    ∀ s : ℂ, (1:ℝ) ≤ s.re → s.re ≤ 2 → 1 ≤ s.im →
      ‖Complex.Gamma s‖
        ≤ (C * (29/4) * Real.exp (5 * Real.pi / 4)) * s.im ^ (s.re - 1/2)
            * Real.exp (-(Real.pi/2) * s.im) := by
  obtain ⟨hC, hF⟩ := h
  intro s hre1 hre2 him
  have himpos : (0:ℝ) < s.im := lt_of_lt_of_le one_pos him
  have hsne : s ≠ 0 := by intro h; rw [h] at himpos; simp at himpos
  -- relax the strip to [1/2, 5/2]
  have hre1' : (1:ℝ)/2 ≤ s.re := by linarith
  have hre2' : s.re ≤ 5/2 := by linarith
  -- factorisation + bounds
  rw [norm_Gamma_factor hsne]
  -- ‖Fcmp s‖ ≤ C , ‖s^(s-1/2)‖ ≤ recovery , exp(-Re s) ≤ 1
  have hFb : ‖Fcmp s‖ ≤ C := hF s hre1' hre2' him
  have hrec : ‖s ^ (s - 1/2)‖
      ≤ (29/4) * Real.exp (5 * Real.pi / 4) * s.im ^ (s.re - 1/2)
          * Real.exp (-(Real.pi/2) * s.im) := norm_cpow_recovery hre1' hre2' him
  have hexp_le : Real.exp (-s.re) ≤ 1 := by
    rw [Real.exp_le_one_iff]; linarith
  -- assemble.  Set R := the recovery RHS ≥ 0.
  set R : ℝ := (29/4) * Real.exp (5 * Real.pi / 4) * s.im ^ (s.re - 1/2)
      * Real.exp (-(Real.pi/2) * s.im) with hR
  have hR0 : 0 ≤ R := by
    rw [hR]; positivity
  have hFb0 : 0 ≤ ‖Fcmp s‖ := norm_nonneg _
  have hcpow0 : 0 ≤ ‖s ^ (s - 1/2)‖ := norm_nonneg _
  calc ‖Fcmp s‖ * ‖s ^ (s - 1/2)‖ * Real.exp (-s.re)
      ≤ ‖Fcmp s‖ * ‖s ^ (s - 1/2)‖ * 1 :=
        mul_le_mul_of_nonneg_left hexp_le (by positivity)
    _ = ‖Fcmp s‖ * ‖s ^ (s - 1/2)‖ := mul_one _
    _ ≤ C * R := by
        apply mul_le_mul hFb (hrec.trans (le_of_eq hR.symm)) hcpow0 hC
    _ = (C * (29/4) * Real.exp (5 * Real.pi / 4)) * s.im ^ (s.re - 1/2)
          * Real.exp (-(Real.pi/2) * s.im) := by rw [hR]; ring

/-! ## The main theorem: `BaseStrip`, UNCONDITIONALLY.

This is the residual `BaseStrip A₀` from `ScratchBandUpper.lean` (verbatim predicate), now proved
with NO hypotheses.  Composing `Fcmp_bounded` (the Phragmén–Lindelöf core) with
`baseStrip_of_FcmpBounded` (the elementary factorisation + recovery) yields the bound on the
central unit strip `Re ∈ [1,2]`, `Im ≥ 1`. -/

/-- The explicit constant. -/
def A₀ : ℝ := (Real.sqrt (2 * Real.pi) * Real.exp (5/2)) * (29/4) * Real.exp (5 * Real.pi / 4)

/-- **`BaseStrip`, proved unconditionally.**  For every `w` with `1 ≤ Re w ≤ 2` and `1 ≤ Im w`,
`‖Γ w‖ ≤ A₀ · (Im w)^(Re w − 1/2) · exp(−(π/2)·Im w)`, with the explicit constant `A₀ ≥ 0`. -/
theorem baseStrip :
    0 ≤ A₀ ∧ ∀ w : ℂ, (1 : ℝ) ≤ w.re → w.re ≤ 2 → 1 ≤ w.im →
      ‖Complex.Gamma w‖ ≤ A₀ * w.im ^ (w.re - 1/2) * Real.exp (-(Real.pi/2) * w.im) := by
  refine ⟨by rw [A₀]; positivity, ?_⟩
  intro w hre1 hre2 him
  have h := baseStrip_of_FcmpBounded Fcmp_bounded w hre1 hre2 him
  show ‖Complex.Gamma w‖ ≤ A₀ * w.im ^ (w.re - 1/2) * Real.exp (-(Real.pi/2) * w.im)
  rw [A₀]
  exact h

end BaseStripProof

/-- **The exact `BaseStrip` predicate of `ScratchBandUpper.lean`, satisfied unconditionally.**
(Re-stated here independently so it can be matched against `BandUpper.BaseStrip`.) -/
theorem baseStrip_final :
    0 ≤ BaseStripProof.A₀ ∧ ∀ w : ℂ, (1 : ℝ) ≤ w.re → w.re ≤ 2 → 1 ≤ w.im →
      ‖Complex.Gamma w‖
        ≤ BaseStripProof.A₀ * w.im ^ (w.re - 1/2) * Real.exp (-(Real.pi/2) * w.im) :=
  BaseStripProof.baseStrip

-- Axiom audit
#print axioms BaseStripProof.norm_Gamma_le_real
#print axioms BaseStripProof.norm_cpow_recovery
#print axioms BaseStripProof.norm_Gamma_factor
#print axioms BaseStripProof.norm_Gamma_half_le
#print axioms BaseStripProof.Fcmp_edge_left
#print axioms BaseStripProof.Fcmp_edge_right
#print axioms BaseStripProof.diffContOnCl_Fcmp
#print axioms BaseStripProof.Fcmp_growth
#print axioms BaseStripProof.Fcmp_bounded
#print axioms BaseStripProof.baseStrip_of_FcmpBounded
#print axioms baseStrip_final
