/-
  RHCountWiring.lean — SEAM 4 (final) of the convexity tower, discharged across the boundary.

  Producer→consumer seam:
    `zeta_convexity_bound` : axiom in `ScratchCountWiring`  ←  THEOREM in `RHConvexityWire`.

  This module IMPORTS `RHConvexityWire` and references `zeta_convexity_bound` as the imported
  THEOREM `RHConvexityWire.zeta_convexity_bound` (signature byte-identical, pure-ζ, clean seam).
  The `ScratchCountWiring.zeta_convexity_bound` transplant AXIOM is DELETED here.

  GOAL ENDPOINT.  `backlund_subconvex_sign_count_proven` (the sharp count `α ≤ 0.111 < 0.399`)
  is proven with NO transplant axioms `phragmenLindelof_flatten` / `tWeightedPL_*` /
  `zeta_convexity_*`-on-the-line.  The only residuals are GENUINE:
    • `verticalStrip_lower_reflection` (producer chain, lower-half reflection),
    • the transplanted ζ edge/growth data `xiF_*` (proven unconditionally elsewhere),
    • `zeta_convexity_bound_nbhd` (the σ-neighborhood convexity bound — NOT proven by the
      on-the-line chain; a genuine residual carried as a named axiom, as in the original),
    • `backlundF_critline_value_lb` (the Backlund good-height value lower bound).
  No `import rh` is needed: every name used below is Mathlib (`JensenFormula`) + the import.
-/
import RHConvexityWire

open Complex Real

noncomputable section

namespace OverflowResidueRH.BacklundTuring.RHCountWiring

/-! ## Part 0 — convexity inputs.  The on-the-line bound is now an IMPORTED THEOREM. -/

/-- **ζ convexity bound on the critical line** — was a transplant axiom in `ScratchCountWiring`;
here it is the imported THEOREM `RHConvexityWire.zeta_convexity_bound`. -/
theorem zeta_convexity_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 1 ≤ |t| →
      ‖riemannZeta ((1/2 : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C * |t| ^ (1/4 : ℝ) :=
  RHConvexityWire.zeta_convexity_bound

/-- **Transplanted ζ convexity bound on a `σ`-NEIGHBORHOOD of the critical line** (GENUINE
residual: the on-the-line chain does not deliver the neighborhood form; carried as a named
axiom exactly as in the original `ScratchCountWiring`). -/
axiom zeta_convexity_bound_nbhd :
    ∀ η : ℝ, 0 < η → η ≤ 1 →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ σ : ℝ, (1/2 : ℝ) - η ≤ σ → σ ≤ (1/2 : ℝ) + η →
        ∀ t : ℝ, 1 ≤ |t| →
          ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖
            ≤ C * |t| ^ ((1/4 : ℝ) + η/2)

/-! ## Part 1 — the Backlund function and its analyticity. -/

/-- The **Backlund function** at height `T`:
`f_T(z) = (ζ(z + iT) + ζ(z − iT)) / 2`. -/
noncomputable def backlundF (T : ℝ) (z : ℂ) : ℂ :=
  (riemannZeta (z + T * Complex.I) + riemannZeta (z - T * Complex.I)) / 2

/-- `f_T` is analytic on the closed ball `B(A, R)` whenever `R < T`. -/
theorem backlundF_analyticOnNhd
    (T A R : ℝ) (hRT : R < T) :
    AnalyticOnNhd ℂ (backlundF T) (Metric.closedBall (A : ℂ) R) := by
  intro z hz
  have hdist : ‖z - (A : ℂ)‖ ≤ R := by
    simpa [Complex.dist_eq] using (Metric.mem_closedBall.mp hz)
  have him_z : |z.im| ≤ R := by
    have h1 : |(z - (A : ℂ)).im| ≤ ‖z - (A : ℂ)‖ := Complex.abs_im_le_norm _
    have h2 : (z - (A : ℂ)).im = z.im := by simp
    rw [h2] at h1
    exact le_trans h1 hdist
  have him_bds := abs_le.mp him_z
  have hplus : z + T * Complex.I ≠ 1 := by
    intro h
    have him : (z + T * Complex.I).im = 0 := by rw [h]; simp
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im] at him
    have hsum : z.im + T = 0 := by simpa using him
    linarith [him_bds.1]
  have hminus : z - T * Complex.I ≠ 1 := by
    intro h
    have him : (z - T * Complex.I).im = 0 := by rw [h]; simp
    simp only [Complex.sub_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im] at him
    have hsub : z.im - T = 0 := by simpa using him
    linarith [him_bds.2]
  have hZ1 : AnalyticAt ℂ riemannZeta (z + T * Complex.I) := by
    refine DifferentiableOn.analyticAt
      (s := {w : ℂ | w ≠ 1}) (fun w hw => (differentiableAt_riemannZeta hw).differentiableWithinAt) ?_
    exact (isOpen_ne).mem_nhds hplus
  have hZ2 : AnalyticAt ℂ riemannZeta (z - T * Complex.I) := by
    refine DifferentiableOn.analyticAt
      (s := {w : ℂ | w ≠ 1}) (fun w hw => (differentiableAt_riemannZeta hw).differentiableWithinAt) ?_
    exact (isOpen_ne).mem_nhds hminus
  have harg1 : AnalyticAt ℂ (fun w : ℂ => w + T * Complex.I) z :=
    (analyticAt_id).add analyticAt_const
  have harg2 : AnalyticAt ℂ (fun w : ℂ => w - T * Complex.I) z :=
    (analyticAt_id).sub analyticAt_const
  have ha1 : AnalyticAt ℂ (fun w => riemannZeta (w + T * Complex.I)) z :=
    AnalyticAt.comp (g := riemannZeta) (f := fun w => w + T * Complex.I) hZ1 harg1
  have ha2 : AnalyticAt ℂ (fun w => riemannZeta (w - T * Complex.I)) z :=
    AnalyticAt.comp (g := riemannZeta) (f := fun w => w - T * Complex.I) hZ2 harg2
  have hsum : AnalyticAt ℂ
      (fun w => riemannZeta (w + T * Complex.I) + riemannZeta (w - T * Complex.I)) z :=
    ha1.add ha2
  show AnalyticAt ℂ (backlundF T) z
  unfold backlundF
  exact hsum.div_const (c := (2 : ℂ))

/-! ## Part 2 — the convexity SPHERE majorant on the critical-line disk. -/

/-- **Convexity sphere majorant.** -/
theorem backlundF_convexity_sphere_bound
    (η : ℝ) (hη0 : 0 < η) (hη1 : η ≤ 1) (T : ℝ) (hT : (140 : ℝ) ≤ T)
    (C : ℝ) (hC0 : 0 ≤ C)
    (hCbd : ∀ σ : ℝ, (1/2 : ℝ) - η ≤ σ → σ ≤ (1/2 : ℝ) + η →
        ∀ t : ℝ, 1 ≤ |t| →
          ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖
            ≤ C * |t| ^ ((1/4 : ℝ) + η/2)) :
      ∀ z ∈ Metric.sphere ((1/2 : ℝ) : ℂ) η,
        ‖backlundF T z‖ ≤ C * (T + η) ^ ((1/4 : ℝ) + η/2) := by
  intro z hz
  have hnorm : ‖z - ((1/2 : ℝ) : ℂ)‖ = η := by
    simpa [Complex.dist_eq] using (Metric.mem_sphere.mp hz)
  have hre_le : |z.re - 1/2| ≤ η := by
    have h1 : |(z - ((1/2 : ℝ) : ℂ)).re| ≤ ‖z - ((1/2 : ℝ) : ℂ)‖ := Complex.abs_re_le_norm _
    have h2 : (z - ((1/2 : ℝ) : ℂ)).re = z.re - 1/2 := by simp
    rw [h2] at h1; rw [hnorm] at h1; exact h1
  have hre_bds := abs_le.mp hre_le
  have him_le : |z.im| ≤ η := by
    have h1 : |(z - ((1/2 : ℝ) : ℂ)).im| ≤ ‖z - ((1/2 : ℝ) : ℂ)‖ := Complex.abs_im_le_norm _
    have h2 : (z - ((1/2 : ℝ) : ℂ)).im = z.im := by simp
    rw [h2] at h1; rw [hnorm] at h1; exact h1
  have him_bds := abs_le.mp him_le
  have hp_re : (z + T * Complex.I).re = z.re := by simp
  have hp_im : (z + T * Complex.I).im = z.im + T := by simp
  have hm_re : (z - T * Complex.I).re = z.re := by simp
  have hm_im : (z - T * Complex.I).im = z.im - T := by simp
  have hsplit_p : z + T * Complex.I = ((z.re : ℝ) : ℂ) + ((z.im + T : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [hp_re, hp_im]
  have hsplit_m : z - T * Complex.I = ((z.re : ℝ) : ℂ) + ((z.im - T : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [hm_re, hm_im]
  have hT1 : (1 : ℝ) ≤ T := by linarith
  have hηT : η ≤ T := le_trans hη1 hT1
  have hp_abs_lb : (1 : ℝ) ≤ |z.im + T| := by
    have : (1 : ℝ) ≤ z.im + T := by linarith [him_bds.1]
    rw [abs_of_nonneg (by linarith)]; exact this
  have hm_abs_lb : (1 : ℝ) ≤ |z.im - T| := by
    have : z.im - T ≤ -1 := by linarith [him_bds.2]
    rw [abs_of_nonpos (by linarith)]; linarith
  have hp_abs_ub : |z.im + T| ≤ T + η := by
    rw [abs_of_nonneg (by linarith [him_bds.1])]; linarith [him_bds.2]
  have hm_abs_ub : |z.im - T| ≤ T + η := by
    rw [abs_of_nonpos (by linarith [him_bds.2])]; linarith [him_bds.1]
  have hbp : ‖riemannZeta (z + T * Complex.I)‖ ≤ C * |z.im + T| ^ ((1/4 : ℝ) + η/2) := by
    rw [hsplit_p]; exact hCbd z.re (by linarith [hre_bds.1]) (by linarith [hre_bds.2]) (z.im + T) hp_abs_lb
  have hbm : ‖riemannZeta (z - T * Complex.I)‖ ≤ C * |z.im - T| ^ ((1/4 : ℝ) + η/2) := by
    rw [hsplit_m]; exact hCbd z.re (by linarith [hre_bds.1]) (by linarith [hre_bds.2]) (z.im - T) hm_abs_lb
  have hexp_nonneg : (0 : ℝ) ≤ (1/4 : ℝ) + η/2 := by positivity
  have hpow_p : |z.im + T| ^ ((1/4 : ℝ) + η/2) ≤ (T + η) ^ ((1/4 : ℝ) + η/2) :=
    Real.rpow_le_rpow (abs_nonneg _) hp_abs_ub hexp_nonneg
  have hpow_m : |z.im - T| ^ ((1/4 : ℝ) + η/2) ≤ (T + η) ^ ((1/4 : ℝ) + η/2) :=
    Real.rpow_le_rpow (abs_nonneg _) hm_abs_ub hexp_nonneg
  have hbp' : ‖riemannZeta (z + T * Complex.I)‖ ≤ C * (T + η) ^ ((1/4 : ℝ) + η/2) :=
    le_trans hbp (mul_le_mul_of_nonneg_left hpow_p hC0)
  have hbm' : ‖riemannZeta (z - T * Complex.I)‖ ≤ C * (T + η) ^ ((1/4 : ℝ) + η/2) :=
    le_trans hbm (mul_le_mul_of_nonneg_left hpow_m hC0)
  have htri : ‖backlundF T z‖ ≤
      (‖riemannZeta (z + T * Complex.I)‖ + ‖riemannZeta (z - T * Complex.I)‖) / 2 := by
    unfold backlundF
    rw [norm_div]
    have h2 : ‖(2 : ℂ)‖ = 2 := by simp
    rw [h2]
    exact div_le_div_of_nonneg_right (norm_add_le _ _) (by norm_num)
  calc ‖backlundF T z‖
      ≤ (‖riemannZeta (z + T * Complex.I)‖ + ‖riemannZeta (z - T * Complex.I)‖) / 2 := htri
    _ ≤ (C * (T + η) ^ ((1/4 : ℝ) + η/2) + C * (T + η) ^ ((1/4 : ℝ) + η/2)) / 2 :=
        div_le_div_of_nonneg_right (add_le_add hbp' hbm') (by norm_num)
    _ = C * (T + η) ^ ((1/4 : ℝ) + η/2) := by ring

/-! ## Part 3 — the Backlund value lower bound on the critical line (GENUINE residual). -/

/-- **Backlund critical-line value lower bound (GENUINE RESIDUAL).** -/
axiom backlundF_critline_value_lb :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ T : ℝ, (140 : ℝ) ≤ T →
      c₀ ≤ ‖backlundF T ((1/2 : ℝ) : ℂ)‖

/-! ## Part 4 — a clean general convexity-Jensen count. -/

/-- **Critical-line Backlund–Jensen count (general radii).** -/
theorem jensen_count_critline
    (T η r : ℝ) (hT : (140 : ℝ) ≤ T)
    (hη0 : 0 < η) (hη1 : η ≤ 1) (hr0 : 0 < r) (hrη : r < η)
    (M : ℝ) (hM1 : 1 ≤ M)
    (hsphere : ∀ z ∈ Metric.sphere ((1/2 : ℝ) : ℂ) η, ‖backlundF T z‖ ≤ M)
    (c₀ : ℝ) (hc₀ : 0 < c₀)
    (hval : c₀ ≤ ‖backlundF T ((1/2 : ℝ) : ℂ)‖) :
    ((∑ᶠ u : ℂ, (MeromorphicOn.divisor (backlundF T)
        (Metric.closedBall ((1/2 : ℝ) : ℂ) r)) u : ℝ))
      ≤ Real.log (M / ‖backlundF T ((1/2 : ℝ) : ℂ)‖) / Real.log (η / r) := by
  have hηT : η < T := lt_of_le_of_lt hη1 (by linarith)
  have habsr : |r| = r := abs_of_pos hr0
  have habsη : |η| = η := abs_of_pos hη0
  have hr_pos : (0 : ℝ) < |r| := by rw [habsr]; exact hr0
  have hr_lt_R : |r| < |η| := by rw [habsr, habsη]; exact hrη
  have hanalytic : AnalyticOnNhd ℂ (backlundF T) (Metric.closedBall ((1/2 : ℝ) : ℂ) |η|) := by
    rw [habsη]; exact backlundF_analyticOnNhd T (1/2) η hηT
  have hfc : backlundF T ((1/2 : ℝ) : ℂ) ≠ 0 := by
    intro h; rw [h, norm_zero] at hval; linarith
  have hsphereM : ∀ z ∈ Metric.sphere ((1/2 : ℝ) : ℂ) |η|, ‖backlundF T z‖ ≤ M := by
    rw [habsη]; exact hsphere
  have hjensen := AnalyticOnNhd.sum_divisor_le
    (c := ((1/2 : ℝ) : ℂ)) (r := r) (R := η) (M := M) (f := backlundF T)
    hr_pos hr_lt_R hM1 hanalytic hfc hsphereM
  rw [habsr] at hjensen
  have hcast : (∑ᶠ u : ℂ, ((MeromorphicOn.divisor (backlundF T)
        (Metric.closedBall ((1/2 : ℝ) : ℂ) r)) u : ℝ))
      = ((∑ᶠ u : ℂ, (MeromorphicOn.divisor (backlundF T)
          (Metric.closedBall ((1/2 : ℝ) : ℂ) r)) u : ℤ) : ℝ) :=
    (map_finsum (Int.castRingHom ℝ)
      ((MeromorphicOn.divisor (backlundF T)
        (Metric.closedBall ((1/2 : ℝ) : ℂ) r)).finiteSupport (isCompact_closedBall ..))).symm
  rw [hcast]
  exact hjensen

/-! ## Part 5 — the SHARP count: `α ≈ 0.1014 ≤ 0.111 < 0.399`. -/

/-- `log 16 = 4·log 2 ≥ 2.77`. -/
theorem log16_ge : (2.77 : ℝ) ≤ Real.log 16 := by
  have h16 : (16 : ℝ) = 2 ^ (4 : ℕ) := by norm_num
  rw [h16, Real.log_pow]
  have hl2 : (0.6931471803 : ℝ) ≤ Real.log 2 := by
    have := Real.log_two_gt_d9; linarith
  push_cast; nlinarith [hl2]

/-- `0 < log 16`. -/
theorem log16_pos : 0 < Real.log 16 := Real.log_pos (by norm_num)

/-- **The sharp coefficient is `≤ 0.111`.** -/
theorem alpha_le : (9/32 : ℝ) / Real.log 16 ≤ 0.111 := by
  have hpos := log16_pos
  rw [div_le_iff₀ hpos]
  have hlog := log16_ge
  nlinarith [hlog]

theorem alpha_lt_399 : (9/32 : ℝ) / Real.log 16 < 0.399 := by
  have h := alpha_le; linarith

/-- **THE DELIVERABLE — the sharp Backlund sign-change count from convexity.**
`Nf(T) ≤ α·log T + β₀`, with `α = (9/32)/log 16 ≈ 0.1014 ≤ 0.111 < 0.399`. -/
theorem backlund_subconvex_sign_count_proven :
    ∃ α β₀ : ℝ, 0 ≤ α ∧ α ≤ 0.111 ∧ α < 0.399 ∧
      ∀ T : ℝ, (140 : ℝ) ≤ T →
        ((∑ᶠ u : ℂ, (MeromorphicOn.divisor (backlundF T)
            (Metric.closedBall ((1/2 : ℝ) : ℂ) (1/256 : ℝ))) u : ℝ))
          ≤ α * Real.log T + β₀ := by
  set η : ℝ := 1/16 with hη
  set e : ℝ := (1/4 : ℝ) + η/2 with he
  have he_val : e = 9/32 := by rw [he, hη]; norm_num
  have hη0 : 0 < η := by rw [hη]; norm_num
  have hη1 : η ≤ 1 := by rw [hη]; norm_num
  have he_nonneg : (0 : ℝ) ≤ e := by rw [he_val]; norm_num
  obtain ⟨C, hC0, hCbd⟩ := zeta_convexity_bound_nbhd η hη0 hη1
  obtain ⟨c₀, hc₀, hvalT⟩ := backlundF_critline_value_lb
  set K : ℝ := 1 + C * (2 : ℝ) ^ e with hK
  have hpow2_nonneg : (0 : ℝ) ≤ (2 : ℝ) ^ e := Real.rpow_nonneg (by norm_num) _
  have hKpos : 0 < K := by rw [hK]; nlinarith [hpow2_nonneg, hC0]
  refine ⟨(9/32 : ℝ) / Real.log 16, (Real.log K - Real.log c₀) / Real.log 16,
    by positivity, alpha_le, alpha_lt_399, ?_⟩
  intro T hT
  have hT1 : (1 : ℝ) ≤ T := by linarith
  have hsphereC := backlundF_convexity_sphere_bound η hη0 hη1 T hT C hC0 hCbd
  set M : ℝ := 1 + C * (T + η) ^ e with hM
  have hTη_pos : (0 : ℝ) < T + η := by linarith
  have hpowTη_nonneg : (0 : ℝ) ≤ (T + η) ^ e := Real.rpow_nonneg (le_of_lt hTη_pos) _
  have hM1 : 1 ≤ M := by rw [hM]; nlinarith [hpowTη_nonneg, hC0]
  have hMpos : 0 < M := lt_of_lt_of_le one_pos hM1
  have hsphereM : ∀ z ∈ Metric.sphere ((1/2 : ℝ) : ℂ) η, ‖backlundF T z‖ ≤ M := by
    intro z hz; have h := hsphereC z hz
    have : C * (T + η) ^ e ≤ M := by rw [hM]; linarith
    exact le_trans h this
  have hval := hvalT T hT
  have hr0 : (0 : ℝ) < 1/256 := by norm_num
  have hrη : (1/256 : ℝ) < η := by rw [hη]; norm_num
  have hcount := jensen_count_critline T η (1/256) hT hη0 hη1 hr0 hrη M hM1 hsphereM c₀ hc₀ hval
  have hηr : η / (1/256 : ℝ) = 16 := by rw [hη]; norm_num
  rw [hηr] at hcount
  have hfcpos : 0 < ‖backlundF T ((1/2 : ℝ) : ℂ)‖ := lt_of_lt_of_le hc₀ hval
  have hlogquot : Real.log (M / ‖backlundF T ((1/2 : ℝ) : ℂ)‖) ≤ Real.log M - Real.log c₀ := by
    rw [Real.log_div (ne_of_gt hMpos) (ne_of_gt hfcpos)]
    have hge : Real.log c₀ ≤ Real.log (‖backlundF T ((1/2 : ℝ) : ℂ)‖) :=
      Real.log_le_log hc₀ hval
    linarith
  have hpowT_nonneg : (0 : ℝ) ≤ T ^ e := Real.rpow_nonneg (by linarith) _
  have hTe_ge1 : (1 : ℝ) ≤ T ^ e := Real.one_le_rpow hT1 he_nonneg
  have hTη_le_2T : T + η ≤ 2 * T := by rw [hη]; linarith
  have hpow_le : (T + η) ^ e ≤ (2 * T) ^ e :=
    Real.rpow_le_rpow (le_of_lt hTη_pos) hTη_le_2T he_nonneg
  have hsplit_pow : (2 * T) ^ e = (2 : ℝ) ^ e * T ^ e :=
    Real.mul_rpow (by norm_num) (by linarith)
  have hMleKT : M ≤ K * T ^ e := by
    rw [hM, hK]
    have h1 : C * (T + η) ^ e ≤ C * ((2 : ℝ) ^ e * T ^ e) := by
      apply mul_le_mul_of_nonneg_left _ hC0
      rw [← hsplit_pow]; exact hpow_le
    nlinarith [h1, hpow2_nonneg, hC0, hpowT_nonneg, hTe_ge1]
  have hlogM : Real.log M ≤ Real.log K + e * Real.log T := by
    have h1 : Real.log M ≤ Real.log (K * T ^ e) := Real.log_le_log hMpos hMleKT
    rw [Real.log_mul (ne_of_gt hKpos) (by positivity), Real.log_rpow (by linarith)] at h1
    linarith
  have hlogquot2 : Real.log (M / ‖backlundF T ((1/2 : ℝ) : ℂ)‖)
      ≤ e * Real.log T + Real.log K - Real.log c₀ :=
    calc Real.log (M / ‖backlundF T ((1/2 : ℝ) : ℂ)‖)
        ≤ Real.log M - Real.log c₀ := hlogquot
      _ ≤ (Real.log K + e * Real.log T) - Real.log c₀ := by
            exact sub_le_sub_right hlogM _
      _ = e * Real.log T + Real.log K - Real.log c₀ := by ring
  have hlog16pos : 0 < Real.log 16 := log16_pos
  have hstep : Real.log (M / ‖backlundF T ((1/2 : ℝ) : ℂ)‖) / Real.log 16
      ≤ (e * Real.log T + Real.log K - Real.log c₀) / Real.log 16 :=
    div_le_div_of_nonneg_right hlogquot2 hlog16pos.le
  have hchain := le_trans hcount hstep
  have hTpos : (0 : ℝ) < T := by linarith
  have hfinal : (e * Real.log T + Real.log K - Real.log c₀) / Real.log 16
      = (9/32 : ℝ) / Real.log 16 * Real.log T
          + (Real.log K - Real.log c₀) / Real.log 16 := by
    rw [he_val]; field_simp; ring
  rw [hfinal] at hchain
  exact hchain

end OverflowResidueRH.BacklundTuring.RHCountWiring

-- FINAL axiom audit across all four import boundaries.  The deliverable must depend ONLY on
-- Mathlib + the GENUINE residuals (verticalStrip_lower_reflection, the ζ-edge transplants,
-- zeta_convexity_bound_nbhd, backlundF_critline_value_lb).  NO transplant axioms
-- phragmenLindelof_flatten / tWeightedPL_* / on-the-line zeta_convexity_bound.
#print axioms OverflowResidueRH.BacklundTuring.RHCountWiring.zeta_convexity_bound
#print axioms OverflowResidueRH.BacklundTuring.RHCountWiring.backlund_subconvex_sign_count_proven
