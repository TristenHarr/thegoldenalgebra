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
  change logDeriv (fun w => (1 - w / ρ) * Complex.exp (w / ρ)) s = 1 / (s - ρ) + 1 / ρ
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

/-! ## Bridge 5 — Jensen + order-≤1 growth ⟹ explicit linear zero count

Compose Bridge 3 with an order-≤1 growth bound `‖f z‖ ≤ exp(A·‖z−c‖)` on the
sphere of radius `R = e·r`. Choosing `R/r = e` makes `log(R/r) = 1`, collapsing
Jensen's bound to a clean **linear-in-`r`** count `≤ A·e·r − log‖f c‖`.

This is the concrete RvM-shaped consequence: it makes the only genuinely missing
input explicit — the order-1 growth constant `A` for `f = ξ` (the Γ·ζ estimate that
Mathlib does not provide). Everything else is now a compiled theorem. -/

open MeromorphicOn in
theorem jensen_zero_count_le_of_expBound
    {c : ℂ} {r A : ℝ} {f : ℂ → ℂ}
    (r_pos : 0 < r) (hA : 0 ≤ A)
    (hf : Differentiable ℂ f) (h₂f : f c ≠ 0)
    (f_bound : ∀ z ∈ Metric.sphere c (Real.exp 1 * r),
        ‖f z‖ ≤ Real.exp (A * (Real.exp 1 * r))) :
    ∑ᶠ u, divisor f (Metric.closedBall c r) u
      ≤ A * (Real.exp 1 * r) - Real.log ‖f c‖ := by
  set R : ℝ := Real.exp 1 * r with hR_def
  set M : ℝ := Real.exp (A * R) with hM_def
  have he1 : (1 : ℝ) < Real.exp 1 := by
    have := Real.add_one_lt_exp (x := 1) (by norm_num); linarith
  have hR_pos : 0 < R := by rw [hR_def]; positivity
  have hRr : r < R := by rw [hR_def]; nlinarith [r_pos, he1]
  have hAR : 0 ≤ A * R := mul_nonneg hA hR_pos.le
  have hM1 : 1 ≤ M := by rw [hM_def]; exact Real.one_le_exp hAR
  have hfc_pos : 0 < ‖f c‖ := norm_pos_iff.mpr h₂f
  -- apply Bridge 3 with |r| = r, |R| = R
  have hbridge := jensen_zero_count_le (c := c) (r := r) (R := R) (M := M) (f := f)
    (by rwa [abs_of_pos r_pos])
    (by rw [abs_of_pos r_pos, abs_of_pos hR_pos]; exact hRr)
    hM1 hf h₂f
    (by rw [abs_of_pos hR_pos]; intro z hz; rw [hM_def]; exact f_bound z hz)
  rw [abs_of_pos r_pos] at hbridge
  -- simplify the Jensen RHS
  have hlogM : Real.log M = A * R := by rw [hM_def, Real.log_exp]
  have hRr_ratio : Real.log (R / r) = 1 := by
    rw [hR_def, mul_div_assoc, div_self (ne_of_gt r_pos), mul_one, Real.log_exp]
  have hrhs : Real.log (M / ‖f c‖) / Real.log (R / r)
      = A * R - Real.log ‖f c‖ := by
    rw [hRr_ratio, div_one, Real.log_div (by positivity) (ne_of_gt hfc_pos), hlogM]
  rw [hrhs] at hbridge
  exact hbridge

/-! ## Bridge 6 — Jensen + ξ-type growth `exp(A·R·log R)` ⟹ `r·log r` count

Riemann ξ has order 1 of **maximal type**: its true growth is `exp(A·|s|·log|s|)`,
not `exp(A·|s|)`. With that growth on the sphere `R = e·r`, Jensen gives a count
`≤ A·(e·r)·log(e·r) − log‖f c‖`, i.e. the genuine **`N(T) ~ T·log T`** Riemann–von
Mangoldt shape. This is the correct count for ξ; Bridge 5's linear bound was for
finite-type functions only. The remaining input is exactly the constant `A` in
ξ's growth — the Γ·ζ estimate Mathlib lacks. -/

open MeromorphicOn in
theorem jensen_zero_count_le_of_xiTypeGrowth
    {c : ℂ} {r A : ℝ} {f : ℂ → ℂ}
    (r_ge : 1 ≤ r) (hA : 0 ≤ A)
    (hf : Differentiable ℂ f) (h₂f : f c ≠ 0)
    (f_bound : ∀ z ∈ Metric.sphere c (Real.exp 1 * r),
        ‖f z‖ ≤ Real.exp (A * (Real.exp 1 * r) * Real.log (Real.exp 1 * r))) :
    ∑ᶠ u, divisor f (Metric.closedBall c r) u
      ≤ A * (Real.exp 1 * r) * Real.log (Real.exp 1 * r) - Real.log ‖f c‖ := by
  have r_pos : 0 < r := lt_of_lt_of_le one_pos r_ge
  set R : ℝ := Real.exp 1 * r with hR_def
  set M : ℝ := Real.exp (A * R * Real.log R) with hM_def
  have he1 : (1 : ℝ) < Real.exp 1 := by
    have := Real.add_one_lt_exp (x := 1) (by norm_num); linarith
  have hR_pos : 0 < R := by rw [hR_def]; positivity
  have hR_ge1 : 1 ≤ R := by rw [hR_def]; nlinarith [r_ge, he1.le]
  have hlogR_nonneg : 0 ≤ Real.log R := Real.log_nonneg hR_ge1
  have hRr : r < R := by rw [hR_def]; nlinarith [r_pos, he1]
  have hARlog : 0 ≤ A * R * Real.log R := by positivity
  have hM1 : 1 ≤ M := by rw [hM_def]; exact Real.one_le_exp hARlog
  have hfc_pos : 0 < ‖f c‖ := norm_pos_iff.mpr h₂f
  have hbridge := jensen_zero_count_le (c := c) (r := r) (R := R) (M := M) (f := f)
    (by rwa [abs_of_pos r_pos])
    (by rw [abs_of_pos r_pos, abs_of_pos hR_pos]; exact hRr)
    hM1 hf h₂f
    (by rw [abs_of_pos hR_pos]; intro z hz; rw [hM_def]; exact f_bound z hz)
  rw [abs_of_pos r_pos] at hbridge
  have hlogM : Real.log M = A * R * Real.log R := by rw [hM_def, Real.log_exp]
  have hRr_ratio : Real.log (R / r) = 1 := by
    rw [hR_def, mul_div_assoc, div_self (ne_of_gt r_pos), mul_one, Real.log_exp]
  have hrhs : Real.log (M / ‖f c‖) / Real.log (R / r)
      = A * R * Real.log R - Real.log ‖f c‖ := by
    rw [hRr_ratio, div_one, Real.log_div (by positivity) (ne_of_gt hfc_pos), hlogM]
  rw [hrhs] at hbridge
  exact hbridge

/-! ## Bridge 7 — genus-1 primary factor Taylor bound (P2 convergence engine)

The quadratic Taylor bound for the genus-1 factor minus one: for `‖w‖ ≤ 1`,
`‖(1-w)·exp w - 1‖ ≤ 3·‖w‖²`. This is the input to
`Complex.multipliable_one_add_of_summable`: with `Σ 1/‖ρᵢ‖² < ∞` it makes the
genus-1 Hadamard product `Multipliable` — the genuine P2 convergence content. -/

theorem norm_genus1_sub_one_le {w : ℂ} (hw : ‖w‖ ≤ 1) :
    ‖(1 - w) * Complex.exp w - 1‖ ≤ 3 * ‖w‖ ^ 2 := by
  have hkey : (1 - w) * Complex.exp w - 1
      = (Complex.exp w - 1 - w) - w * (Complex.exp w - 1) := by ring
  -- piece 1: ‖exp w - (1+w)‖ ≤ (3/4)‖w‖²  (exp_bound at n=2)
  have hp1 : ‖Complex.exp w - 1 - w‖ ≤ ‖w‖ ^ 2 := by
    have h := Complex.exp_bound (x := w) hw (n := 2) (by norm_num)
    have hsum : ∑ i ∈ Finset.range 2, w ^ i / (Nat.factorial i : ℂ) = 1 + w := by
      simp [Finset.sum_range_succ, Nat.factorial]
    rw [hsum] at h
    have heq : ‖Complex.exp w - (1 + w)‖ = ‖Complex.exp w - 1 - w‖ := by
      congr 1; ring
    rw [heq] at h
    -- h : ‖…‖ ≤ ‖w‖^2 * (fraction); the fraction ≤ 1, so drop it
    refine h.trans (mul_le_of_le_one_right (sq_nonneg _) ?_)
    norm_num [Nat.factorial]
  -- piece 2: ‖w·(exp w - 1)‖ ≤ 2‖w‖²  (exp_bound at n=1 gives ‖exp w - 1‖ ≤ 2‖w‖)
  have hp2 : ‖w * (Complex.exp w - 1)‖ ≤ 2 * ‖w‖ ^ 2 := by
    have h := Complex.exp_bound (x := w) hw (n := 1) (by norm_num)
    have hsum : ∑ i ∈ Finset.range 1, w ^ i / (Nat.factorial i : ℂ) = 1 := by simp
    rw [hsum] at h
    -- h : ‖exp w - 1‖ ≤ ‖w‖^1 * (fraction = 2); rewrite RHS to 2‖w‖
    have hle : ‖Complex.exp w - 1‖ ≤ 2 * ‖w‖ := by
      refine h.trans (le_of_eq ?_)
      simp only [Nat.factorial_one, Nat.cast_one, mul_one, pow_one]
      ring
    rw [norm_mul]
    calc ‖w‖ * ‖Complex.exp w - 1‖
        ≤ ‖w‖ * (2 * ‖w‖) := mul_le_mul_of_nonneg_left hle (norm_nonneg w)
      _ = 2 * ‖w‖ ^ 2 := by ring
  rw [hkey]
  calc ‖(Complex.exp w - 1 - w) - w * (Complex.exp w - 1)‖
      ≤ ‖Complex.exp w - 1 - w‖ + ‖w * (Complex.exp w - 1)‖ := norm_sub_le _ _
    _ ≤ ‖w‖ ^ 2 + 2 * ‖w‖ ^ 2 := add_le_add hp1 hp2
    _ = 3 * ‖w‖ ^ 2 := by ring

end ScratchBridges

#print axioms ScratchBridges.norm_genus1_sub_one_le
