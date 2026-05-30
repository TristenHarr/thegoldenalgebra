import Mathlib
open Complex Filter Topology

noncomputable def entireRiemannXi (s : ℂ) : ℂ := (1 / 2) * (s * (s - 1) * completedRiemannZeta₀ s + 1)

theorem differentiable_entireRiemannXi : Differentiable ℂ entireRiemannXi := by
  unfold entireRiemannXi
  exact (((differentiable_id.mul (differentiable_id.sub_const 1)).mul
    differentiable_completedZeta₀).add_const 1).const_mul _

theorem entireRiemannXi_one_sub (s : ℂ) : entireRiemannXi (1 - s) = entireRiemannXi s := by
  unfold entireRiemannXi; rw [completedRiemannZeta₀_one_sub]; ring

/-- Off `s = 0, 1`, `ξ(s) = (1/2) · s · (s-1) · Λ(s)` where `Λ` is the completed zeta. -/
theorem entireRiemannXi_eq_completed {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    entireRiemannXi s = (1 / 2) * (s * (s - 1)) * completedRiemannZeta s := by
  have hΛ : completedRiemannZeta s = completedRiemannZeta₀ s - 1 / s - 1 / (1 - s) :=
    completedRiemannZeta_eq s
  unfold entireRiemannXi
  rw [hΛ]
  have hs1 : (1 - s) ≠ 0 := by
    intro h; apply h1; linear_combination -h
  field_simp
  ring

/-! ## Hypotheses we assume (per task: the three already-proven facts, plus the ζ strip bound).
We assume them as hypotheses to the final theorem rather than re-proving Mathlib-absent facts. -/

/-- The norm of `Λ(w) = Gammaℝ(w) · ζ(w)` for `0 < Re w`. -/
theorem completedZeta_eq_Gammaℝ_mul {w : ℂ} (hw : 0 < w.re) :
    completedRiemannZeta w = Gammaℝ w * riemannZeta w := by
  have hw0 : w ≠ 0 := by intro h; rw [h] at hw; simp at hw
  rw [riemannZeta_def_of_ne_zero hw0, mul_div_cancel₀]
  exact Gammaℝ_ne_zero_of_re_pos hw

/-- `1 ≤ π`. -/
theorem one_le_pi : (1 : ℝ) ≤ Real.pi := by
  have := Real.one_le_pi_div_two; linarith

/-- For `z` with `Re z ≥ 1/4` and `Re z ≤ 2`, the complex Gamma is bounded by an explicit constant,
using the recurrence `Γ(z) = Γ(z+2)/(z(z+1))`.  Conditional on the complex-Gamma-norm bound
`hgnorm` and the real-Gamma growth bound `hrgamma`. -/
theorem norm_Gamma_strip
    (hgnorm : ∀ u : ℂ, 0 < u.re → ‖Complex.Gamma u‖ ≤ Real.Gamma u.re)
    (hrgamma : ∀ x : ℝ, 2 ≤ x → Real.Gamma x ≤ Real.exp (4 * x * Real.log x))
    {z : ℂ} (hz1 : (1:ℝ)/4 ≤ z.re) (hz2 : z.re ≤ 2) :
    ‖Complex.Gamma z‖ ≤ Real.exp (4 * 4 * Real.log 4) * 16 / 5 := by
  have hz0 : z ≠ 0 := by
    intro h; rw [h] at hz1; simp at hz1; linarith
  have hz1' : z + 1 ≠ 0 := by
    intro h
    have : (z + 1).re = 0 := by rw [h]; simp
    simp [Complex.add_re] at this; linarith
  -- Γ(z+2) = (z+1)*z*Γ(z)
  have hrec : Complex.Gamma (z + 2) = (z + 1) * z * Complex.Gamma z := by
    have e1 : Complex.Gamma (z + 1 + 1) = (z + 1) * Complex.Gamma (z + 1) :=
      Complex.Gamma_add_one (z + 1) hz1'
    have e2 : Complex.Gamma (z + 1) = z * Complex.Gamma z := Complex.Gamma_add_one z hz0
    have : z + 1 + 1 = z + 2 := by ring
    rw [this] at e1
    rw [e1, e2]; ring
  -- so Γ(z) = Γ(z+2)/((z+1)*z)
  have hden : (z + 1) * z ≠ 0 := mul_ne_zero hz1' hz0
  have hGz : Complex.Gamma z = Complex.Gamma (z + 2) / ((z + 1) * z) := by
    rw [hrec]; field_simp
  rw [hGz, norm_div, norm_mul]
  -- bound numerator
  have hnum : ‖Complex.Gamma (z + 2)‖ ≤ Real.exp (4 * 4 * Real.log 4) := by
    have hre : 0 < (z + 2).re := by simp [Complex.add_re]; linarith
    have h1 := hgnorm (z + 2) hre
    have hre2 : (2:ℝ) ≤ (z + 2).re := by simp [Complex.add_re]; linarith
    have h2 := hrgamma (z + 2).re hre2
    refine h1.trans (h2.trans ?_)
    have hle : (z + 2).re ≤ 4 := by simp [Complex.add_re]; linarith
    have hge : (2:ℝ) ≤ (z + 2).re := hre2
    -- x*log x increasing on [2,4], bounded by 4*log 4
    apply Real.exp_le_exp.mpr
    have hxlogx : (z + 2).re * Real.log (z + 2).re ≤ 4 * Real.log 4 := by
      have hmono : (z + 2).re * Real.log (z + 2).re ≤ 4 * Real.log (z + 2).re := by
        apply mul_le_mul_of_nonneg_right hle
        apply Real.log_nonneg; linarith
      have hmono2 : (4:ℝ) * Real.log (z + 2).re ≤ 4 * Real.log 4 := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        apply Real.log_le_log (by linarith) hle
      linarith
    linarith
  -- bound denominators below: ‖z+1‖ ≥ 5/4, ‖z‖ ≥ 1/4
  have hzb : (1:ℝ)/4 ≤ ‖z‖ := le_trans (by linarith [hz1]) (Complex.re_le_norm z)
  have hz1b : (5:ℝ)/4 ≤ ‖z + 1‖ := by
    have : (z + 1).re ≤ ‖z + 1‖ := Complex.re_le_norm (z + 1)
    simp only [Complex.add_re, Complex.one_re] at this
    linarith
  -- combine
  have hzpos : (0:ℝ) < ‖z‖ := by linarith
  have hz1pos : (0:ℝ) < ‖z + 1‖ := by linarith
  rw [div_le_iff₀ (by positivity)]
  show ‖Complex.Gamma (z + 2)‖ ≤ Real.exp (4 * 4 * Real.log 4) * 16 / 5 * (‖z + 1‖ * ‖z‖)
  have hprod : Real.exp (4 * 4 * Real.log 4) * 16 / 5 * (‖z + 1‖ * ‖z‖)
      ≥ Real.exp (4 * 4 * Real.log 4) := by
    have h54 : Real.exp (4 * 4 * Real.log 4) * 16 / 5 * (‖z + 1‖ * ‖z‖)
        ≥ Real.exp (4 * 4 * Real.log 4) * 16 / 5 * ((5/4) * (1/4)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply mul_le_mul hz1b hzb (by norm_num) hz1pos.le
    have : Real.exp (4 * 4 * Real.log 4) * 16 / 5 * ((5/4) * (1/4))
        = Real.exp (4 * 4 * Real.log 4) := by ring
    linarith
  exact le_trans hnum hprod

noncomputable def CΓ : ℝ := Real.exp (4 * 4 * Real.log 4) * 16 / 5

/-- `Gammaℝ` is bounded on the vertical strip `1/2 ≤ Re w ≤ 4` by the constant `CΓ`. -/
theorem norm_Gammaℝ_strip
    (hgnorm : ∀ u : ℂ, 0 < u.re → ‖Complex.Gamma u‖ ≤ Real.Gamma u.re)
    (hrgamma : ∀ x : ℝ, 2 ≤ x → Real.Gamma x ≤ Real.exp (4 * x * Real.log x))
    {w : ℂ} (hw1 : (1:ℝ)/2 ≤ w.re) (hw2 : w.re ≤ 4) :
    ‖Gammaℝ w‖ ≤ CΓ := by
  rw [Gammaℝ_def, norm_mul]
  have hpi : ‖(↑Real.pi : ℂ) ^ (-w / 2)‖ ≤ 1 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
    apply Real.rpow_le_one_of_one_le_of_nonpos one_le_pi
    have : (-w / 2).re = -w.re / 2 := by simp [Complex.neg_re]
    rw [this]; linarith
  have hgam : ‖Complex.Gamma (w / 2)‖ ≤ CΓ := by
    have hre : (w / 2).re = w.re / 2 := by simp
    apply norm_Gamma_strip hgnorm hrgamma <;> rw [hre] <;> linarith
  calc ‖(↑Real.pi : ℂ) ^ (-w / 2)‖ * ‖Complex.Gamma (w / 2)‖
      ≤ 1 * CΓ := by
        apply mul_le_mul hpi hgam (norm_nonneg _) (by norm_num)
    _ = CΓ := by ring

/-- For `r ≥ 4` and `M ≥ 0`, the quartic `4 M r^4` is dominated by `exp(A r log r)` for a suitable
constant `A` (depending only on `M`). -/
theorem quartic_le_exp {M : ℝ} (hM : 0 ≤ M) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ r : ℝ, 4 ≤ r → 4 * M * r ^ 4 ≤ Real.exp (A * r * Real.log r) := by
  set L := Real.log 4 with hL
  have hLpos : 0 < L := Real.log_pos (by norm_num)
  set A := 4 + (|Real.log (4 * M + 1)|) / (4 * L) + 1 with hA
  have hAnn : 0 ≤ A := by positivity
  refine ⟨A, hAnn, ?_⟩
  intro r hr
  have hrpos : (0:ℝ) < r := by linarith
  have hr1 : (1:ℝ) ≤ r := by linarith
  have hlogr : Real.log 4 ≤ Real.log r := Real.log_le_log (by norm_num) hr
  have hlogrpos : 0 < Real.log r := lt_of_lt_of_le hLpos hlogr
  -- 4*M*r^4 ≤ (4M+1)*r^4
  have hbound1 : 4 * M * r ^ 4 ≤ (4 * M + 1) * r ^ 4 := by
    have : (0:ℝ) ≤ r ^ 4 := by positivity
    nlinarith [this]
  -- (4M+1)*r^4 = exp(log(4M+1)) * exp(4 log r) = exp(log(4M+1) + 4 log r)
  have h4M1pos : (0:ℝ) < 4 * M + 1 := by linarith
  have hr4 : r ^ 4 = Real.exp (4 * Real.log r) := by
    rw [show (4:ℝ) * Real.log r = Real.log (r^4) by
          rw [Real.log_pow]; push_cast; ring]
    rw [Real.exp_log (by positivity)]
  have hfac : (4 * M + 1) * r ^ 4 = Real.exp (Real.log (4 * M + 1) + 4 * Real.log r) := by
    rw [Real.exp_add, Real.exp_log h4M1pos, hr4]
  rw [hfac] at hbound1
  refine hbound1.trans (Real.exp_le_exp.mpr ?_)
  -- log(4M+1) + 4 log r ≤ A r log r
  -- since A r log r ≥ A * 4 * L and 4 log r ≤ 4 * (r log r) (as r ≥ 1)
  have hrlogr : 4 * L ≤ r * Real.log r := by
    have : (1:ℝ) * Real.log 4 ≤ r * Real.log r :=
      mul_le_mul hr1 hlogr (by positivity) (by linarith)
    nlinarith [this, hLpos]
  have key1 : Real.log (4 * M + 1) ≤ (|Real.log (4 * M + 1)|) / (4 * L) * (r * Real.log r) := by
    have habs : Real.log (4 * M + 1) ≤ |Real.log (4 * M + 1)| := le_abs_self _
    have hdiv : (|Real.log (4 * M + 1)|) / (4 * L) * (4 * L) = |Real.log (4 * M + 1)| := by
      field_simp
    have : (|Real.log (4 * M + 1)|) / (4 * L) * (4 * L)
        ≤ (|Real.log (4 * M + 1)|) / (4 * L) * (r * Real.log r) := by
      apply mul_le_mul_of_nonneg_left hrlogr (by positivity)
    rw [hdiv] at this
    linarith
  have key2 : 4 * Real.log r ≤ 4 * (r * Real.log r) := by
    have : Real.log r ≤ r * Real.log r := by
      nlinarith [hlogrpos, hr1]
    linarith
  -- A r log r = 4*(r log r) + (|log|/(4L))*(r log r) + 1*(r log r)
  have hArw : A * r * Real.log r
      = 4 * (r * Real.log r) + (|Real.log (4 * M + 1)|) / (4 * L) * (r * Real.log r)
        + (r * Real.log r) := by
    rw [hA]; ring
  rw [hArw]
  have hrl_nonneg : 0 ≤ r * Real.log r := by positivity
  linarith

/-- **Order-1 growth bound for `ξ` on the vertical strip `-3 ≤ Re ≤ 4`**, conditional on:
* `hgnorm` — the complex-Gamma norm bound `‖Γ(u)‖ ≤ Real.Gamma(Re u)` for `Re u > 0`;
* `hrgamma` — the real-Gamma growth bound `Real.Gamma x ≤ exp(4 x log x)` for `x ≥ 2`;
* `hzeta` — a polynomial growth bound for `ζ` on the right part of the critical strip
  `1/2 ≤ Re w ≤ 4`, namely `‖ζ(w)‖ ≤ Cζ · (1 + |Im w|)²`.

`hgnorm` and `hrgamma` are the two already-available facts; `hzeta` is the SINGLE remaining gap
(Mathlib has no critical-strip bound for `ζ`). -/
theorem norm_entireRiemannXi_le_exp_vertical_strip_of_zeta
    (hgnorm : ∀ u : ℂ, 0 < u.re → ‖Complex.Gamma u‖ ≤ Real.Gamma u.re)
    (hrgamma : ∀ x : ℝ, 2 ≤ x → Real.Gamma x ≤ Real.exp (4 * x * Real.log x))
    {Cζ : ℝ} (hCζ : 0 ≤ Cζ)
    (hzeta : ∀ w : ℂ, (1:ℝ)/2 ≤ w.re → w.re ≤ 4 →
        ‖riemannZeta w‖ ≤ Cζ * (1 + |w.im|) ^ 2) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ s : ℂ, -3 ≤ s.re → s.re ≤ 4 → 4 ≤ ‖s‖ →
      ‖entireRiemannXi s‖ ≤ Real.exp (A * ‖s‖ * Real.log ‖s‖) := by
  -- Set M := CΓ * Cζ and use quartic_le_exp with that M.
  obtain ⟨A, hA0, hA⟩ := quartic_le_exp (M := CΓ * Cζ)
    (by have : 0 ≤ CΓ := by unfold CΓ; positivity
        exact mul_nonneg this hCζ)
  refine ⟨A, hA0, ?_⟩
  intro s hs1 hs2 hs3
  -- the bound on ‖ξ s‖ by 4 * (CΓ*Cζ) * ‖s‖^4
  have hquartic : ‖entireRiemannXi s‖ ≤ 4 * (CΓ * Cζ) * ‖s‖ ^ 4 := by
    -- basic facts
    have hsne0 : s ≠ 0 := by
      intro h; rw [h] at hs3; simp only [norm_zero] at hs3; linarith
    have hsne1 : s ≠ 1 := by
      intro h; rw [h] at hs3; simp only [norm_one] at hs3; linarith
    -- ‖ξ s‖ = (1/2) ‖s‖ ‖s-1‖ ‖Λ s‖
    have hxi : entireRiemannXi s = (1 / 2) * (s * (s - 1)) * completedRiemannZeta s :=
      entireRiemannXi_eq_completed hsne0 hsne1
    -- choose w in the right half-strip with ‖Λ s‖ = ‖Λ w‖
    -- Λ(1-s) = Λ(s)
    have hFE : completedRiemannZeta (1 - s) = completedRiemannZeta s :=
      completedRiemannZeta_one_sub s
    -- pick w
    obtain ⟨w, hwre1, hwre2, hwim, hΛeq⟩ :
        ∃ w : ℂ, (1:ℝ)/2 ≤ w.re ∧ w.re ≤ 4 ∧ |w.im| = |s.im| ∧
          ‖completedRiemannZeta s‖ = ‖completedRiemannZeta w‖ := by
      by_cases hc : (1:ℝ)/2 ≤ s.re
      · exact ⟨s, hc, hs2, rfl, rfl⟩
      · rw [not_le] at hc
        refine ⟨1 - s, ?_, ?_, ?_, ?_⟩
        · rw [Complex.sub_re, Complex.one_re]; linarith
        · rw [Complex.sub_re, Complex.one_re]; linarith
        · rw [Complex.sub_im, Complex.one_im, zero_sub, abs_neg]
        · rw [hFE]
    -- ‖Λ w‖ = ‖Gammaℝ w‖ * ‖ζ w‖
    have hwpos : 0 < w.re := by linarith
    have hΛw : completedRiemannZeta w = Gammaℝ w * riemannZeta w :=
      completedZeta_eq_Gammaℝ_mul hwpos
    have hnormΛw : ‖completedRiemannZeta w‖ = ‖Gammaℝ w‖ * ‖riemannZeta w‖ := by
      rw [hΛw, norm_mul]
    -- ‖Gammaℝ w‖ ≤ CΓ
    have hGammaℝ : ‖Gammaℝ w‖ ≤ CΓ := norm_Gammaℝ_strip hgnorm hrgamma hwre1 hwre2
    -- ‖ζ w‖ ≤ Cζ * (1+|Im w|)^2 ≤ Cζ * (2‖s‖)^2 = 4 Cζ ‖s‖^2
    have hζw : ‖riemannZeta w‖ ≤ Cζ * (1 + |w.im|) ^ 2 := hzeta w hwre1 hwre2
    have himle : |w.im| ≤ ‖s‖ := by
      rw [hwim]
      exact le_trans (Complex.abs_im_le_norm s) (le_refl _)
    have hs1le : (1:ℝ) ≤ ‖s‖ := by linarith
    have hζw2 : ‖riemannZeta w‖ ≤ Cζ * (2 * ‖s‖) ^ 2 := by
      refine hζw.trans ?_
      apply mul_le_mul_of_nonneg_left _ hCζ
      have hb : 1 + |w.im| ≤ 2 * ‖s‖ := by linarith
      have h0 : (0:ℝ) ≤ 1 + |w.im| := by positivity
      nlinarith [hb, h0]
    -- ‖s-1‖ ≤ 2‖s‖
    have hsm1 : ‖s - 1‖ ≤ 2 * ‖s‖ := by
      calc ‖s - 1‖ ≤ ‖s‖ + ‖(1:ℂ)‖ := norm_sub_le s 1
        _ = ‖s‖ + 1 := by simp
        _ ≤ 2 * ‖s‖ := by linarith
    -- assemble
    have hnormxi : ‖entireRiemannXi s‖
        = (1 / 2) * (‖s‖ * ‖s - 1‖) * ‖completedRiemannZeta s‖ := by
      rw [hxi, norm_mul, norm_mul, norm_mul,
        show ‖(1/2 : ℂ)‖ = 1/2 by norm_num]
    rw [hnormxi, hΛeq, hnormΛw]
    -- now bound: (1/2)*(‖s‖*‖s-1‖)*(‖Gammaℝ w‖ * ‖ζ w‖) ≤ 4*(CΓ*Cζ)*‖s‖^4
    have hGℝnn : 0 ≤ ‖Gammaℝ w‖ := norm_nonneg _
    have hζnn : 0 ≤ ‖riemannZeta w‖ := norm_nonneg _
    have hsnn : 0 ≤ ‖s‖ := norm_nonneg _
    have hsm1nn : 0 ≤ ‖s - 1‖ := norm_nonneg _
    have hCΓnn : 0 ≤ CΓ := by unfold CΓ; positivity
    -- chain of monotone bounds
    calc (1 / 2) * (‖s‖ * ‖s - 1‖) * (‖Gammaℝ w‖ * ‖riemannZeta w‖)
        ≤ (1 / 2) * (‖s‖ * (2 * ‖s‖)) * (CΓ * (Cζ * (2 * ‖s‖) ^ 2)) := by
          apply mul_le_mul
          · apply mul_le_mul_of_nonneg_left _ (by norm_num)
            apply mul_le_mul_of_nonneg_left hsm1 hsnn
          · apply mul_le_mul hGammaℝ hζw2 hζnn hCΓnn
          · positivity
          · positivity
      _ = 4 * (CΓ * Cζ) * ‖s‖ ^ 4 := by ring
  -- finish with quartic_le_exp
  exact hquartic.trans (hA ‖s‖ hs3)
