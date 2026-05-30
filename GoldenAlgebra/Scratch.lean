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

end ScratchBridges
