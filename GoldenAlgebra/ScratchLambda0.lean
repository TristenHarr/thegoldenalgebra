import Mathlib

open Complex Filter Topology MeasureTheory Set Real

/-!
# Λ₀ strip bound — the clean route to ξ vertical-strip growth (bypasses ζ / complex Stirling)

`completedRiemannZeta₀` (the ENTIRE completed zeta `Λ₀`) is built in Mathlib as a Mellin
transform of an exponentially-decaying theta-type kernel.  The crucial observation: in the
Mellin integral `∫₀^∞ k(t) · t^{s-1} dt`, the factor `‖t^{s-1}‖ = t^{Re s - 1}` is **independent
of `Im s`** (because `t > 0` is real).  Hence the integral bounds `‖Λ₀(s)‖` by a quantity
depending only on `Re s`, which is **uniformly bounded on a vertical strip** `a ≤ Re s ≤ b`.

## PATH TAKEN

No ready-made vertical-strip boundedness lemma exists in `AbstractFuncEq`/`HurwitzZetaEven`.
We build the constant bound directly from the Mellin representation:

* `completedRiemannZeta₀ s = (hurwitzEvenFEPair 0).Λ₀ (s/2) / 2` and `Λ₀ = mellin f_modif`, where
  `f_modif := (hurwitzEvenFEPair 0).f_modif` is the "strong" kernel that decays faster than any
  power at both `0` and `∞`.
* For any real exponent `c`, `MellinConvergent f_modif (c : ℂ)` holds (it is the `.1` component of
  `StrongFEPair.hasMellin`), i.e. `t ↦ (t:ℂ)^(c-1) • f_modif t` is `IntegrableOn (Ioi 0)`; taking
  norms, `t ↦ t^(c-1) * ‖f_modif t‖` is integrable on `Ioi 0`.
* For `w` with `Re w ∈ [a, b]`, the integrand norm `t^(Re w - 1) ‖f_modif t‖` is dominated by the
  **Im-independent** integrable function `g t := (t^(a-1) + t^(b-1)) * ‖f_modif t‖` (split `t ≤ 1` /
  `t ≥ 1`).  `norm_integral_le_of_norm_le` then gives `‖mellin f_modif w‖ ≤ ∫ g =: C₀`.
* On the strip `-3 ≤ Re s ≤ 4` we have `Re (s/2) ∈ [-3/2, 2]`, giving the uniform bound, hence the
  bound on `Λ₀ s = mellin f_modif (s/2)`.

Mathlib lemmas used: `completedRiemannZeta₀` / `completedHurwitzZetaEven₀` defs,
`WeakFEPair.Λ₀`, `WeakFEPair.toStrongFEPair`, `StrongFEPair.hasMellin`, `StrongFEPair.Λ_eq`,
`MellinConvergent` (= `IntegrableOn` of the weighted integrand), `mellin` (def),
`norm_integral_le_of_norm_le`, `Complex.norm_cpow_eq_rpow_re_of_pos`,
`Real.rpow_le_rpow_of_exponent_le` / `_ge`.

No weakening: the clean Im-independent constant bound goes through.
-/

namespace ScratchLambda0

open HurwitzZeta

/-- The strong kernel underlying `completedRiemannZeta₀`. -/
private noncomputable def F : ℝ → ℂ := (hurwitzEvenFEPair 0).f_modif

/-- `Λ₀(s/2)/2` form of `completedRiemannZeta₀`, written as a Mellin transform of `F`. -/
private lemma completedRiemannZeta0_eq_mellin (s : ℂ) :
    completedRiemannZeta₀ s = mellin F (s / 2) / 2 := by
  rw [show completedRiemannZeta₀ s = completedHurwitzZetaEven₀ 0 s from rfl,
    completedHurwitzZetaEven₀, WeakFEPair.Λ₀]
  rfl

/-- For any real exponent `c`, the weighted norm `t ↦ t^(c-1) * ‖F t‖` is integrable on `Ioi 0`.
This is the norm of the (integrable, by `StrongFEPair.hasMellin`) Mellin integrand. -/
private lemma integrable_weighted_norm (c : ℝ) :
    IntegrableOn (fun t : ℝ => t ^ (c - 1) * ‖F t‖) (Ioi 0) := by
  have hconv : MellinConvergent F (c : ℂ) :=
    ((hurwitzEvenFEPair 0).toStrongFEPair.hasMellin (c : ℂ)).1
  -- `hconv` says `t ↦ (t:ℂ)^(c-1) • F t` is integrable on `Ioi 0`; take norms.
  have hnorm : IntegrableOn (fun t : ℝ => ‖(t : ℂ) ^ ((c : ℂ) - 1) • F t‖) (Ioi 0) := hconv.norm
  refine hnorm.congr ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall (fun t ht => ?_))
  have ht0 : (0 : ℝ) < t := ht
  simp only [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos ht0, sub_re, one_re,
    Complex.ofReal_re]

/-- The pointwise Im-independent domination: for `0 < t` and `a ≤ c ≤ b`,
`t ^ (c - 1) ≤ t ^ (a - 1) + t ^ (b - 1)`. -/
private lemma rpow_sub_one_le {a b c t : ℝ} (ht : 0 < t) (hac : a ≤ c) (hcb : c ≤ b) :
    t ^ (c - 1) ≤ t ^ (a - 1) + t ^ (b - 1) := by
  rcases le_or_gt 1 t with h1 | h1
  · -- `t ≥ 1`: increasing in the exponent, so `t^(c-1) ≤ t^(b-1)`.
    have : t ^ (c - 1) ≤ t ^ (b - 1) :=
      Real.rpow_le_rpow_of_exponent_le h1 (by linarith)
    have h0 : 0 ≤ t ^ (a - 1) := (Real.rpow_pos_of_pos ht _).le
    linarith
  · -- `0 < t ≤ 1`: decreasing in the exponent, so `t^(c-1) ≤ t^(a-1)`.
    have : t ^ (c - 1) ≤ t ^ (a - 1) :=
      Real.rpow_le_rpow_of_exponent_ge ht h1.le (by linarith)
    have h0 : 0 ≤ t ^ (b - 1) := (Real.rpow_pos_of_pos ht _).le
    linarith

/-- Core Im-independent bound: `‖mellin F w‖` is bounded by the integral of the dominating
function, uniformly for `Re w` in a fixed interval `[a, b]`. -/
private lemma norm_mellin_F_le {a b : ℝ} (w : ℂ) (hwa : a ≤ w.re) (hwb : w.re ≤ b) :
    ‖mellin F w‖ ≤ ∫ t in Ioi 0, (t ^ (a - 1) + t ^ (b - 1)) * ‖F t‖ := by
  rw [mellin]
  refine norm_integral_le_of_norm_le ?_ ?_
  · refine ((integrable_weighted_norm a).add (integrable_weighted_norm b)).congr ?_
    exact Filter.Eventually.of_forall (fun t => by simp [add_mul])
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall (fun t ht => ?_))
    have ht0 : (0 : ℝ) < t := ht
    rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos ht0, sub_re, one_re]
    rw [add_mul]
    have hF0 : 0 ≤ ‖F t‖ := norm_nonneg _
    have := rpow_sub_one_le ht0 hwa hwb
    calc t ^ (w.re - 1) * ‖F t‖ ≤ (t ^ (a - 1) + t ^ (b - 1)) * ‖F t‖ :=
            mul_le_mul_of_nonneg_right this hF0
      _ = t ^ (a - 1) * ‖F t‖ + t ^ (b - 1) * ‖F t‖ := by ring

/-! ## GOAL 1 -/

theorem norm_completedRiemannZeta0_le_on_strip :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, -3 ≤ s.re → s.re ≤ 4 → ‖completedRiemannZeta₀ s‖ ≤ C := by
  -- Constant: half the dominating integral with `a = -3/2`, `b = 2`.
  set I : ℝ := ∫ t in Ioi 0, (t ^ ((-3/2 : ℝ) - 1) + t ^ ((2 : ℝ) - 1)) * ‖F t‖ with hI
  have hI_nonneg : 0 ≤ I := by
    rw [hI]
    refine setIntegral_nonneg measurableSet_Ioi (fun t ht => ?_)
    have ht0 : (0 : ℝ) < t := ht
    have : 0 ≤ t ^ ((-3/2 : ℝ) - 1) + t ^ ((2 : ℝ) - 1) :=
      add_nonneg (Real.rpow_pos_of_pos ht0 _).le (Real.rpow_pos_of_pos ht0 _).le
    exact mul_nonneg this (norm_nonneg _)
  refine ⟨I / 2, by linarith, fun s hs1 hs2 => ?_⟩
  rw [completedRiemannZeta0_eq_mellin, norm_div, Complex.norm_ofNat]
  have hwa : (-3/2 : ℝ) ≤ (s / 2).re := by
    rw [Complex.div_re]; simp only [Complex.re_ofNat, Complex.im_ofNat]
    norm_num; linarith
  have hwb : (s / 2).re ≤ (2 : ℝ) := by
    rw [Complex.div_re]; simp only [Complex.re_ofNat, Complex.im_ofNat]
    norm_num; linarith
  have := norm_mellin_F_le (s / 2) hwa hwb
  rw [← hI] at this
  exact div_le_div_of_nonneg_right this (by norm_num) |>.trans_eq rfl

/-! ## GOAL 2 -/

/-- The entire completed Riemann ξ-function. -/
noncomputable def entireRiemannXi (s : ℂ) : ℂ :=
  (1 / 2) * (s * (s - 1) * completedRiemannZeta₀ s + 1)

/-- A power `r^k` is dominated by `exp (A * r * log r)` for `r ≥ 4`, with a suitable `A`. -/
private lemma rpow_two_mul_const_le_exp {C : ℝ} (hC : 0 ≤ C) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ r : ℝ, 4 ≤ r → (C + 1) * r ^ 2 ≤ Real.exp (A * r * Real.log r) := by
  -- Choose `A` so that `log (C+1) + 2 log r ≤ A r log r` for `r ≥ 4`.
  have hlogC : 0 ≤ Real.log (C + 1) := Real.log_nonneg (by linarith)
  refine ⟨Real.log (C + 1) + 2, by linarith, fun r hr => ?_⟩
  have hr0 : (0 : ℝ) < r := by linarith
  have hr1 : (1 : ℝ) ≤ r := by linarith
  have hlogr : 0 ≤ Real.log r := Real.log_nonneg hr1
  have hC1 : (0 : ℝ) < C + 1 := by linarith
  -- Key: for `r ≥ 4`, `1 ≤ r * log r` (since `log r ≥ log 4 > 1`).
  have hlog4 : (1 : ℝ) < Real.log 4 := by
    have he4 : Real.exp 1 < 4 := by linarith [Real.exp_one_lt_d9]
    have := Real.log_lt_log (Real.exp_pos 1) he4
    rwa [Real.log_exp] at this
  have hl4 : Real.log 4 ≤ Real.log r := Real.log_le_log (by norm_num) hr
  have hrlr : (1 : ℝ) ≤ r * Real.log r := by nlinarith
  -- Reduce to comparing logarithms.
  rw [← Real.exp_log (by positivity : (0:ℝ) < (C + 1) * r ^ 2)]
  apply Real.exp_le_exp.mpr
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]
  -- Goal: log (C+1) + 2 * log r ≤ (log (C+1) + 2) * r * log r
  have h1 : Real.log (C + 1) ≤ Real.log (C + 1) * (r * Real.log r) := by
    nlinarith
  have h2 : (2 : ℝ) * Real.log r ≤ 2 * (r * Real.log r) := by
    have : Real.log r ≤ r * Real.log r := by nlinarith
    linarith
  calc Real.log (C + 1) + 2 * Real.log r
      ≤ Real.log (C + 1) * (r * Real.log r) + 2 * (r * Real.log r) := by linarith
    _ = (Real.log (C + 1) + 2) * r * Real.log r := by ring

theorem norm_entireRiemannXi_le_exp_vertical_strip :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ s : ℂ, -3 ≤ s.re → s.re ≤ 4 → 4 ≤ ‖s‖ →
      ‖entireRiemannXi s‖ ≤ Real.exp (A * ‖s‖ * Real.log ‖s‖) := by
  obtain ⟨C, hC0, hC⟩ := norm_completedRiemannZeta0_le_on_strip
  obtain ⟨A, hA0, hA⟩ := rpow_two_mul_const_le_exp hC0
  refine ⟨A, hA0, fun s hs1 hs2 hs4 => ?_⟩
  have hs0 : (0 : ℝ) ≤ ‖s‖ := norm_nonneg _
  -- `‖ξ s‖ ≤ (1/2)(‖s‖·‖s-1‖·C + 1)`
  have hxi : ‖entireRiemannXi s‖ ≤ (1 / 2) * (‖s‖ * ‖s - 1‖ * C + 1) := by
    rw [entireRiemannXi]
    rw [norm_mul, norm_div, norm_one, Complex.norm_ofNat]
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    calc ‖s * (s - 1) * completedRiemannZeta₀ s + 1‖
        ≤ ‖s * (s - 1) * completedRiemannZeta₀ s‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
      _ = ‖s‖ * ‖s - 1‖ * ‖completedRiemannZeta₀ s‖ + 1 := by
            rw [norm_mul, norm_mul, norm_one]
      _ ≤ ‖s‖ * ‖s - 1‖ * C + 1 := by
            have hmono : ‖completedRiemannZeta₀ s‖ ≤ C := hC s hs1 hs2
            have hpos : 0 ≤ ‖s‖ * ‖s - 1‖ := by positivity
            linarith [mul_le_mul_of_nonneg_left hmono hpos]
  -- `‖s-1‖ ≤ 2‖s‖`, so `‖s‖‖s-1‖ ≤ 2‖s‖²`.
  have hs1norm : ‖s - 1‖ ≤ 2 * ‖s‖ := by
    calc ‖s - 1‖ ≤ ‖s‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = ‖s‖ + 1 := by rw [norm_one]
      _ ≤ 2 * ‖s‖ := by nlinarith
  have hbound : (1 / 2) * (‖s‖ * ‖s - 1‖ * C + 1) ≤ (C + 1) * ‖s‖ ^ 2 := by
    have hss : ‖s‖ * ‖s - 1‖ ≤ 2 * ‖s‖ ^ 2 := by
      have := mul_le_mul_of_nonneg_left hs1norm hs0
      calc ‖s‖ * ‖s - 1‖ ≤ ‖s‖ * (2 * ‖s‖) := this
        _ = 2 * ‖s‖ ^ 2 := by ring
    have h1le : (1 : ℝ) ≤ ‖s‖ ^ 2 := by nlinarith
    nlinarith [mul_nonneg hC0 (by positivity : (0:ℝ) ≤ ‖s‖ ^ 2),
      mul_le_mul_of_nonneg_left hss hC0]
  calc ‖entireRiemannXi s‖ ≤ (1 / 2) * (‖s‖ * ‖s - 1‖ * C + 1) := hxi
    _ ≤ (C + 1) * ‖s‖ ^ 2 := hbound
    _ ≤ Real.exp (A * ‖s‖ * Real.log ‖s‖) := hA ‖s‖ hs4

end ScratchLambda0
