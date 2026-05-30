import Mathlib

open Complex Filter Topology ComplexConjugate

namespace ScratchBridges

/-! ## Bridge 1 — entire + real-on-ℝ ⟹ Schwarz conjugation symmetry
Reusable, domain-agnostic. Uses `DifferentiableAt.conj_conj` + identity theorem. -/

theorem entire_conj_symm_of_real_on_real
    {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hreal : ∀ x : ℝ, f (x : ℂ) = conj (f (x : ℂ))) :
    ∀ z : ℂ, f (conj z) = conj (f z) := by
  set g : ℂ → ℂ := conj ∘ f ∘ conj with hg_def
  -- g is entire
  have hg : Differentiable ℂ g := by
    intro z
    have h := (hf (conj z)).conj_conj
    -- h : DifferentiableAt ℂ (conj ∘ f ∘ conj) (conj (conj z))
    simpa [hg_def, Complex.conj_conj] using h
  have hfA : AnalyticOnNhd ℂ f Set.univ :=
    hf.differentiableOn.analyticOnNhd isOpen_univ
  have hgA : AnalyticOnNhd ℂ g Set.univ :=
    hg.differentiableOn.analyticOnNhd isOpen_univ
  -- f and g agree on ℝ
  have hagree : ∀ x : ℝ, f (x : ℂ) = g (x : ℂ) := by
    intro x
    have : g (x : ℂ) = conj (f (conj (x : ℂ))) := rfl
    rw [this, Complex.conj_ofReal, ← hreal x]
  -- reals accumulate at 0 (within punctured nhds): get ∃ᶠ
  have hfreq : ∃ᶠ z in 𝓝[≠] (0 : ℂ), f z = g z := by
    -- the sequence (1/(n+1) : ℂ) → 0, nonzero, all satisfy f = g
    set u : ℕ → ℂ := fun n => ((1 / (n + 1 : ℝ) : ℝ) : ℂ) with hu_def
    have htend : Tendsto u atTop (𝓝[≠] 0) := by
      apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      · have h0 : Tendsto (fun n : ℕ => (1 / (n + 1 : ℝ) : ℝ)) atTop (𝓝 0) :=
          tendsto_one_div_add_atTop_nhds_zero_nat
        have hc := (Complex.continuous_ofReal.tendsto (0:ℝ)).comp h0
        rw [Complex.ofReal_zero] at hc
        simpa [hu_def, Function.comp_def] using hc
      · filter_upwards with n
        have hpos : (0 : ℝ) < 1 / (n + 1 : ℝ) := by positivity
        simp only [hu_def, Set.mem_compl_iff, Set.mem_singleton_iff, ne_eq,
          Complex.ofReal_eq_zero]
        exact ne_of_gt hpos
    have heq : ∀ n : ℕ, f (u n) = g (u n) := fun n => hagree _
    rw [Filter.frequently_iff]
    intro s hs
    have hev : ∀ᶠ n in atTop, u n ∈ s := htend hs
    obtain ⟨n, hn⟩ := hev.exists
    exact ⟨u n, hn, heq n⟩
  have hfg := hfA.eq_of_frequently_eq hgA (z₀ := 0) hfreq
  intro z
  have hz : f z = conj (f (conj z)) := congrFun hfg z
  -- want : f (conj z) = conj (f z)
  rw [hz, Complex.conj_conj]

/-! ## Bridge 2 — clean wrapper for logDeriv of a tprod (the Hadamard `luc` field) -/

theorem logDeriv_tprod_eq_tsum_wrapper
    {ι : Type*} {f : ι → ℂ → ℂ} {x : ℂ}
    (hf : ∀ i, f i x ≠ 0)
    (hd : ∀ i, Differentiable ℂ (f i))
    (hm : Summable fun i ↦ logDeriv (f i) x)
    (htend : MultipliableLocallyUniformlyOn f Set.univ)
    (hnez : ∏' i, f i x ≠ 0) :
    logDeriv (fun y => ∏' i, f i y) x = ∑' i, logDeriv (f i) x :=
  logDeriv_tprod_eq_tsum isOpen_univ (Set.mem_univ x) hf
    (fun i => (hd i).differentiableOn) hm htend hnez

/-! ## Bridge 3 — Jensen zero-count bound (the RvM / A1 / P1 main-term engine)

For an entire `f`, nonzero at the center, bounded by `M` on the sphere of radius `R`,
the weighted count of zeros in the disk of radius `r < R` is `≤ log(M/‖f c‖)/log(R/r)`.
This is the Mathlib-grounded RvM upper bound: it directly majorizes `canonicalShellCard`
and the `N(T)` main term feeding the Turing envelope. -/

open MeromorphicOn in
theorem jensen_zero_count_le
    {c : ℂ} {r R M : ℝ} {f : ℂ → ℂ}
    (r_pos : 0 < |r|) (r_lt_R : |r| < |R|) (hM : 1 ≤ M)
    (hf : Differentiable ℂ f) (h₂f : f c ≠ 0)
    (f_bound : ∀ z ∈ Metric.sphere c |R|, ‖f z‖ ≤ M) :
    ∑ᶠ u, divisor f (Metric.closedBall c |r|) u
      ≤ Real.log (M / ‖f c‖) / Real.log (R / r) :=
  AnalyticOnNhd.sum_divisor_le r_pos r_lt_R hM
    ((hf.differentiableOn.analyticOnNhd isOpen_univ).mono (Set.subset_univ _))
    h₂f f_bound

/-! ## Bridge 4 — genus-1 factor log-derivative keystone

`hadamardGenus1Factor ρ s := (1 - s/ρ) * exp(s/ρ)`. Its log-derivative is the
single regularized residue term `1/(s−ρ) + 1/ρ`. This is the per-factor input that
lets `logDeriv_tprod_eq_tsum` discharge the genus-1 Hadamard `logDeriv = Σ` field. -/

noncomputable def genus1Factor (ρ s : ℂ) : ℂ := (1 - s / ρ) * Complex.exp (s / ρ)

theorem logDeriv_genus1Factor {ρ s : ℂ} (hρ : ρ ≠ 0) (hsρ : s ≠ ρ) :
    logDeriv (genus1Factor ρ) s = 1 / (s - ρ) + 1 / ρ := by
  have hsub : s - ρ ≠ 0 := sub_ne_zero.mpr hsρ
  -- derivative of each piece
  have h1 : HasDerivAt (fun w : ℂ => 1 - w / ρ) (-(1 / ρ)) s := by
    have : HasDerivAt (fun w : ℂ => w / ρ) (1 / ρ) s := by
      simpa using (hasDerivAt_id s).div_const ρ
    simpa using (this.const_sub 1)
  have h2 : HasDerivAt (fun w : ℂ => Complex.exp (w / ρ))
      (Complex.exp (s / ρ) * (1 / ρ)) s := by
    have hin : HasDerivAt (fun w : ℂ => w / ρ) (1 / ρ) s := by
      simpa using (hasDerivAt_id s).div_const ρ
    simpa [mul_comm] using (hin.cexp)
  have hval1 : (1 : ℂ) - s / ρ ≠ 0 := by
    intro h
    apply hsρ
    have hdiv : s / ρ = 1 := by linear_combination -h
    field_simp at hdiv
    exact hdiv
  have hexp : Complex.exp (s / ρ) ≠ 0 := Complex.exp_ne_zero _
  -- logDeriv of product, unfolding the def
  show logDeriv (fun w => (1 - w / ρ) * Complex.exp (w / ρ)) s = 1 / (s - ρ) + 1 / ρ
  rw [logDeriv_mul s hval1 hexp h1.differentiableAt h2.differentiableAt]
  rw [logDeriv_apply, logDeriv_apply, h1.deriv, h2.deriv]
  -- first term: -(1/ρ) / (1 - s/ρ) = 1/(s-ρ);  second: (exp·(1/ρ))/exp = 1/ρ
  have e1 : (-(1 / ρ)) / (1 - s / ρ) = 1 / (s - ρ) := by
    rw [div_eq_div_iff hval1 (sub_ne_zero.mpr hsρ)]
    field_simp
    ring
  have e2 : (Complex.exp (s / ρ) * (1 / ρ)) / Complex.exp (s / ρ) = 1 / ρ := by
    rw [mul_comm, mul_div_assoc, div_self hexp, mul_one]
  rw [e1, e2]

end ScratchBridges
