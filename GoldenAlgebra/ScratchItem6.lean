import Mathlib
open Complex Filter Topology

noncomputable def genus1Factor (ρ s : ℂ) : ℂ := (1 - s / ρ) * Complex.exp (s / ρ)

theorem logDeriv_genus1Factor {ρ s : ℂ} (hρ : ρ ≠ 0) (hsρ : s ≠ ρ) :
    logDeriv (genus1Factor ρ) s = 1 / (s - ρ) + 1 / ρ := by
  have h1 : HasDerivAt (fun w : ℂ => 1 - w / ρ) (-(1 / ρ)) s := by
    have : HasDerivAt (fun w : ℂ => w / ρ) (1 / ρ) s := by simpa using (hasDerivAt_id s).div_const ρ
    simpa using (this.const_sub 1)
  have h2 : HasDerivAt (fun w : ℂ => Complex.exp (w / ρ)) (Complex.exp (s / ρ) * (1 / ρ)) s := by
    have hin : HasDerivAt (fun w : ℂ => w / ρ) (1 / ρ) s := by simpa using (hasDerivAt_id s).div_const ρ
    simpa [mul_comm] using (hin.cexp)
  have hval1 : (1 : ℂ) - s / ρ ≠ 0 := by
    intro h; apply hsρ; have hdiv : s / ρ = 1 := by linear_combination -h
    field_simp at hdiv; exact hdiv
  have hexp : Complex.exp (s / ρ) ≠ 0 := Complex.exp_ne_zero _
  change logDeriv (fun w => (1 - w / ρ) * Complex.exp (w / ρ)) s = 1 / (s - ρ) + 1 / ρ
  rw [logDeriv_mul s hval1 hexp h1.differentiableAt h2.differentiableAt]
  rw [logDeriv_apply, logDeriv_apply, h1.deriv, h2.deriv]
  have e1 : (-(1 / ρ)) / (1 - s / ρ) = 1 / (s - ρ) := by
    rw [div_eq_div_iff hval1 (sub_ne_zero.mpr hsρ)]; field_simp; ring
  have e2 : (Complex.exp (s / ρ) * (1 / ρ)) / Complex.exp (s / ρ) = 1 / ρ := by
    rw [mul_comm, mul_div_assoc, div_self hexp, mul_one]
  rw [e1, e2]

theorem genus1Factor_ne_zero {ρ s : ℂ} (hρ : ρ ≠ 0) (hsρ : s ≠ ρ) :
    genus1Factor ρ s ≠ 0 := by
  unfold genus1Factor
  apply mul_ne_zero
  · intro h
    apply hsρ
    have hdiv : s / ρ = 1 := by linear_combination -h
    field_simp at hdiv; exact hdiv
  · exact Complex.exp_ne_zero _

theorem differentiable_genus1Factor {ρ : ℂ} : Differentiable ℂ (genus1Factor ρ) := by
  unfold genus1Factor
  fun_prop

theorem logDeriv_genus1Product_eq_tsum
    {ι : Type*} (loc : ι → ℂ) (s : ℂ)
    (hne : ∀ i, loc i ≠ 0)
    (hsne : ∀ i, s ≠ loc i)
    (hmul : MultipliableLocallyUniformlyOn (fun i z => genus1Factor (loc i) z) Set.univ)
    (hsumm : Summable (fun i => logDeriv (genus1Factor (loc i)) s))
    (hprodne : ∏' i, genus1Factor (loc i) s ≠ 0) :
    logDeriv (fun z => ∏' i, genus1Factor (loc i) z) s
      = ∑' i, (1 / (s - loc i) + 1 / loc i) := by
  have key := logDeriv_tprod_eq_tsum (s := Set.univ) isOpen_univ (Set.mem_univ s)
    (f := fun i z => genus1Factor (loc i) z)
    (fun i => genus1Factor_ne_zero (hne i) (hsne i))
    (fun i => (differentiable_genus1Factor).differentiableOn)
    hsumm hmul hprodne
  rw [key]
  apply tsum_congr
  intro i
  exact logDeriv_genus1Factor (hne i) (hsne i)
