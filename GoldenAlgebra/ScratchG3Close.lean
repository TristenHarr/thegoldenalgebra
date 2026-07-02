import Mathlib

open Complex Filter Topology ComplexConjugate

/-! # G3 closure verification (transplanted)

This file transplants the FULL dependency chain of `xi_zero_invSq_summable` from
`Scratch.lean` verbatim, wrapped under the namespace
`OverflowResidueRH.BacklundTuring.ScratchG3Close`, and runs `#print axioms` on the
final G3 inverse-square summability theorem to confirm it is axiom-clean and
UNCONDITIONAL (no residual hypotheses, no `sorryAx`).
-/

namespace OverflowResidueRH.BacklundTuring.ScratchG3Close


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

/-! ## Next 10 bridge theorems

These are intended to sit after Bridge 7, inside `namespace ScratchBridges`.
They avoid new global architecture and give small reusable lemmas for the Hadamard/Jensen path.
-/

/-- The genus-1 primary factor is normalized to be `1` at the origin. -/
theorem genus1Factor_zero_right {ρ : ℂ} :
    genus1Factor ρ 0 = 1 := by
  simp [genus1Factor]

/-- At its own zero, the genus-1 primary factor vanishes. -/
theorem genus1Factor_self {ρ : ℂ} (hρ : ρ ≠ 0) :
    genus1Factor ρ ρ = 0 := by
  simp [genus1Factor, hρ]

/-- The genus-1 primary factor vanishes exactly at `s = ρ`. -/
theorem genus1Factor_eq_zero_iff {ρ s : ℂ} (hρ : ρ ≠ 0) :
    genus1Factor ρ s = 0 ↔ s = ρ := by
  constructor
  · intro h
    unfold genus1Factor at h
    have hexp : Complex.exp (s / ρ) ≠ 0 := Complex.exp_ne_zero _
    have hlin : (1 - s / ρ : ℂ) = 0 := by
      exact eq_zero_of_ne_zero_of_mul_right_eq_zero hexp h
    have hsdiv : s / ρ = 1 := by
      linear_combination -hlin
    have hs : s = ρ := by
      have := congrArg (fun z : ℂ => z * ρ) hsdiv
      simpa [div_eq_mul_inv, hρ, mul_assoc] using this
    exact hs
  · intro hs
    subst hs
    exact genus1Factor_self hρ

/-- Away from `ρ`, the genus-1 primary factor is nonzero. -/
theorem genus1Factor_ne_zero {ρ s : ℂ} (hρ : ρ ≠ 0) (hsρ : s ≠ ρ) :
    genus1Factor ρ s ≠ 0 := by
  intro h
  exact hsρ ((genus1Factor_eq_zero_iff hρ).mp h)

/-- The genus-1 primary factor is entire in the variable `s`. -/
theorem differentiable_genus1Factor {ρ : ℂ} :
    Differentiable ℂ (genus1Factor ρ) := by
  unfold genus1Factor
  fun_prop

/-- Pointwise differentiability of the genus-1 primary factor. -/
theorem differentiableAt_genus1Factor {ρ s : ℂ} :
    DifferentiableAt ℂ (genus1Factor ρ) s := by
  exact differentiable_genus1Factor s

/-- Explicit derivative of the genus-1 primary factor. -/
theorem hasDerivAt_genus1Factor {ρ s : ℂ} :
    HasDerivAt (genus1Factor ρ)
      ((-(1 / ρ)) * Complex.exp (s / ρ)
        + (1 - s / ρ) * (Complex.exp (s / ρ) * (1 / ρ))) s := by
  unfold genus1Factor
  have h1 : HasDerivAt (fun w : ℂ => 1 - w / ρ) (-(1 / ρ)) s := by
    have hdiv : HasDerivAt (fun w : ℂ => w / ρ) (1 / ρ) s := by
      simpa using (hasDerivAt_id s).div_const ρ
    simpa using hdiv.const_sub 1
  have h2 : HasDerivAt (fun w : ℂ => Complex.exp (w / ρ))
      (Complex.exp (s / ρ) * (1 / ρ)) s := by
    have hdiv : HasDerivAt (fun w : ℂ => w / ρ) (1 / ρ) s := by
      simpa using (hasDerivAt_id s).div_const ρ
    simpa [mul_comm] using hdiv.cexp
  have hmul := h1.mul h2
  convert hmul using 1

/-- The derivative of the genus-1 primary factor, expressed via `deriv`. -/
theorem deriv_genus1Factor {ρ s : ℂ} :
    deriv (genus1Factor ρ) s =
      (-(1 / ρ)) * Complex.exp (s / ρ)
        + (1 - s / ρ) * (Complex.exp (s / ρ) * (1 / ρ)) := by
  exact (hasDerivAt_genus1Factor (ρ := ρ) (s := s)).deriv

/-- The logarithmic derivative identity, with the nonzero condition packaged using
`genus1Factor_ne_zero`. This is the version you actually want to feed into a product. -/
theorem logDeriv_genus1Factor_of_ne {ρ s : ℂ}
    (hρ : ρ ≠ 0) (hsρ : s ≠ ρ) :
    logDeriv (genus1Factor ρ) s = 1 / (s - ρ) + 1 / ρ := by
  exact logDeriv_genus1Factor hρ hsρ

/-! Jensen with the standard `R = e r` radius, but with the bound already stated as an
arbitrary exponential majorant. This is a clean adapter between growth estimates and zero count. -/
open MeromorphicOn in
theorem jensen_zero_count_le_of_expMajorant
    {c : ℂ} {r B : ℝ} {f : ℂ → ℂ}
    (r_pos : 0 < r) (hB : 0 ≤ B)
    (hf : Differentiable ℂ f) (h₂f : f c ≠ 0)
    (f_bound : ∀ z ∈ Metric.sphere c (Real.exp 1 * r), ‖f z‖ ≤ Real.exp B) :
    ∑ᶠ u, divisor f (Metric.closedBall c r) u
      ≤ B - Real.log ‖f c‖ := by
  set R : ℝ := Real.exp 1 * r with hR_def
  set M : ℝ := Real.exp B with hM_def
  have he1 : (1 : ℝ) < Real.exp 1 := by
    have h := Real.add_one_lt_exp (x := 1) (by norm_num)
    linarith
  have hR_pos : 0 < R := by
    rw [hR_def]
    positivity
  have hRr : r < R := by
    rw [hR_def]
    nlinarith [r_pos, he1]
  have hM1 : 1 ≤ M := by
    rw [hM_def]
    exact Real.one_le_exp hB
  have hfc_pos : 0 < ‖f c‖ := norm_pos_iff.mpr h₂f
  have hbridge := jensen_zero_count_le
    (c := c) (r := r) (R := R) (M := M) (f := f)
    (by rwa [abs_of_pos r_pos])
    (by
      rw [abs_of_pos r_pos, abs_of_pos hR_pos]
      exact hRr)
    hM1 hf h₂f
    (by
      rw [abs_of_pos hR_pos]
      intro z hz
      rw [hM_def]
      exact f_bound z hz)
  rw [abs_of_pos r_pos] at hbridge
  have hlogM : Real.log M = B := by
    rw [hM_def, Real.log_exp]
  have hRr_ratio : Real.log (R / r) = 1 := by
    rw [hR_def, mul_div_assoc, div_self (ne_of_gt r_pos), mul_one, Real.log_exp]
  have hrhs :
      Real.log (M / ‖f c‖) / Real.log (R / r)
        = B - Real.log ‖f c‖ := by
    rw [hRr_ratio, div_one, Real.log_div (by positivity) (ne_of_gt hfc_pos), hlogM]
  exact hbridge.trans_eq hrhs

/-! ## Bridge 18 — the ACTUAL ξ, grounded in `completedRiemannZeta₀`

This is the payoff of the Mathlib v4.31 landing. The hardest classical leg of the
Hadamard program — analytic continuation of ζ, the Γ poles, the ζ pole at `s=1`,
trivial-zero cancellation, removable singularities — is ALREADY DONE in Mathlib via
`completedRiemannZeta₀` (the entire `Λ₀`). We package the completed ξ as an entire
function with one definition and reduce the proposed boss axiom `xi_entire` to a
one-line theorem.

Key algebraic identity (away from `s = 0, 1`):
  `Λ(s) = Λ₀(s) − 1/s − 1/(1−s)`        [`completedRiemannZeta_eq`]
  `ξ(s) = ½·s·(s−1)·Λ(s)`               [classical completed ξ]
  ⟹ `ξ(s) = ½·(s·(s−1)·Λ₀(s) + 1)`     [the pole terms collapse to the constant `+1`]
The RHS is manifestly entire, so we DEFINE `entireRiemannXi` by it. -/

noncomputable def entireRiemannXi (s : ℂ) : ℂ :=
  (1 / 2) * (s * (s - 1) * completedRiemannZeta₀ s + 1)

/-- **`xi_entire` is a theorem, not an axiom.** ξ is entire — immediate from
`differentiable_completedZeta₀`. This discharges field A/the entireness obligation of
`EntireXiClassicalHadamardTheorem` outright. -/
theorem differentiable_entireRiemannXi : Differentiable ℂ entireRiemannXi := by
  unfold entireRiemannXi
  exact (((differentiable_id.mul (differentiable_id.sub_const 1)).mul
    differentiable_completedZeta₀).add_const 1).const_mul _

/-- ξ as an `AnalyticOnNhd` on all of ℂ — the form the Jensen/Hadamard lemmas consume. -/
theorem analyticOnNhd_entireRiemannXi :
    AnalyticOnNhd ℂ entireRiemannXi Set.univ :=
  differentiable_entireRiemannXi.differentiableOn.analyticOnNhd isOpen_univ

/-- The entire ξ agrees with the classical `½·s·(s−1)·Λ(s)` wherever `Λ` is defined. -/
theorem entireRiemannXi_eq (s : ℂ) (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    entireRiemannXi s = (1 / 2) * (s * (s - 1)) * completedRiemannZeta s := by
  unfold entireRiemannXi
  rw [completedRiemannZeta_eq]
  have h1s : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs1)
  field_simp
  ring

/-- **Functional equation for ξ**, fully entire: `ξ(1−s) = ξ(s)`. Free from
`completedRiemannZeta₀_one_sub` plus the symmetry of `s(s−1)` under `s ↦ 1−s`.
This is the Schwarz/reflection-symmetry input for the critical-line argument. -/
theorem entireRiemannXi_one_sub (s : ℂ) :
    entireRiemannXi (1 - s) = entireRiemannXi s := by
  unfold entireRiemannXi
  rw [completedRiemannZeta₀_one_sub]
  ring

/-- ξ(0) = ½, so the origin is a free Jensen center (`f c ≠ 0` with no extra work). -/
theorem entireRiemannXi_zero : entireRiemannXi 0 = 1 / 2 := by
  simp [entireRiemannXi]

theorem entireRiemannXi_zero_ne : entireRiemannXi 0 ≠ 0 := by
  rw [entireRiemannXi_zero]; norm_num

/-- Away from `s = 0, 1`, ξ vanishes exactly where the completed zeta `Λ` vanishes:
the nontrivial-zero set of ξ IS the zero set of `completedRiemannZeta`. This is the
clean handle for indexing the Hadamard zeros (`zeroLoc : ι → ℂ`, field B/C). -/
theorem entireRiemannXi_eq_zero_iff (s : ℂ) (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    entireRiemannXi s = 0 ↔ completedRiemannZeta s = 0 := by
  rw [entireRiemannXi_eq s hs0 hs1, mul_eq_zero]
  have hfac : (1 / 2 : ℂ) * (s * (s - 1)) ≠ 0 :=
    mul_ne_zero (by norm_num) (mul_ne_zero hs0 (sub_ne_zero.mpr hs1))
  constructor
  · rintro (h | h)
    · exact absurd h hfac
    · exact h
  · intro h; right; exact h

/-! ## Bridge 19 — the SINGLE remaining input, on the real ξ

Specialize Bridge 6 (`jensen_zero_count_le_of_xiTypeGrowth`) to `f = entireRiemannXi`,
center `c = 0` (where ξ(0) = ½ ≠ 0 for free). Every hypothesis is now discharged by a
compiled theorem EXCEPT the sphere growth bound `f_bound`. That single hypothesis — the
order-1 `exp(A·R·log R)` envelope coming from the Γ·ζ (Stirling) estimate Mathlib does
not yet package — is provably the ONLY analytic content left between us and the genuine
Riemann–von Mangoldt `N(T) ~ T·log T` zero count for ξ. -/
open MeromorphicOn in
theorem xi_zero_count_le_of_growth
    {r A : ℝ} (r_ge : 1 ≤ r) (hA : 0 ≤ A)
    (f_bound : ∀ z ∈ Metric.sphere (0 : ℂ) (Real.exp 1 * r),
        ‖entireRiemannXi z‖
          ≤ Real.exp (A * (Real.exp 1 * r) * Real.log (Real.exp 1 * r))) :
    ∑ᶠ u, divisor entireRiemannXi (Metric.closedBall (0 : ℂ) r) u
      ≤ A * (Real.exp 1 * r) * Real.log (Real.exp 1 * r)
        - Real.log ‖entireRiemannXi 0‖ :=
  jensen_zero_count_le_of_xiTypeGrowth r_ge hA differentiable_entireRiemannXi
    entireRiemannXi_zero_ne f_bound

/-! ## Bridge 20 — the complex-Stirling brick: `‖Γ(s)‖ ≤ Γ(Re s)` on the right half-plane

The boss (#1, the ξ growth bound) bottlenecks on a vertical-line estimate for the Gamma
factor, which the deep Mathlib survey confirmed is ABSENT. We supply its fundamental form
directly from Euler's integral `Γ(s) = ∫₀^∞ e^{-x} x^{s-1} dx` (`Complex.Gamma_eq_integral`,
valid for `Re s > 0`): since `‖x^{s-1}‖ = x^{Re s - 1}` for `x > 0`
(`norm_cpow_eq_rpow_re_of_pos`) and `e^{-x} > 0`, the triangle inequality collapses the
complex integral exactly onto the REAL Gamma integral. This `‖Γ(σ+it)‖ ≤ Γ(σ)` is the
keystone that — combined with Mathlib's real Stirling on `Γ(σ)`, the elementary
`‖π^{-s/2}‖ = π^{-σ/2}`, the absolute-convergence bound on `ζ` for `Re s > 1`, and
`PhragmenLindelof.vertical_strip` — assembles the order-1 envelope `‖ξ(s)‖ ≤ exp(A‖s‖log‖s‖)`
that `xi_zero_count_le_of_growth` consumes. -/

open MeasureTheory in
theorem norm_Gamma_le_real_Gamma_re {s : ℂ} (hs : 0 < s.re) :
    ‖Complex.Gamma s‖ ≤ Real.Gamma s.re := by
  rw [Complex.Gamma_eq_integral hs, Real.Gamma_eq_integral hs]
  simp only [Complex.GammaIntegral]
  refine (norm_integral_le_integral_norm _).trans_eq ?_
  refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
  have hx0 : (0 : ℝ) < x := hx
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx0, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Complex.sub_re, Complex.one_re]

/-! ## Bridge 21 — the formal ξ zero-index system (Hadamard fields A–D + discreteness)

Mirrors `Mathlib/NumberTheory/LSeries/ZetaZeros.lean`, but ξ is ENTIRE so the argument is
strictly cleaner (no `{1}ᶜ` puncture): ξ is analytic on the connected `univ` and `ξ(0)=½≠0`,
so by `AnalyticOnNhd.preimage_zero_mem_codiscrete` the zero set is codiscrete. This furnishes
the Hadamard index type, closedness, discreteness, local finiteness of the zero divisor, the
`zeroLoc ρ ≠ 0` field, and the crucial **`cofinite → cocompact`** escape — the cofinite
Weierstrass M-test driver that makes the genus-1 product converge locally uniformly. -/

/-- The zeros of the entire completed ξ (Hadamard zero locus, field B). -/
def riemannXiZeros : Set ℂ := entireRiemannXi ⁻¹' {0}

@[simp] lemma mem_riemannXiZeros {z : ℂ} :
    z ∈ riemannXiZeros ↔ entireRiemannXi z = 0 := Iff.rfl

/-- The complement of the ξ-zero set is codiscrete (ξ entire, not ≡ 0 since ξ(0)=½). -/
lemma compl_riemannXiZeros_mem_codiscrete :
    riemannXiZerosᶜ ∈ codiscrete ℂ :=
  analyticOnNhd_entireRiemannXi.preimage_zero_mem_codiscrete entireRiemannXi_zero_ne

lemma isClosed_riemannXiZeros : IsClosed riemannXiZeros := by
  simpa using (mem_codiscrete'.mp compl_riemannXiZeros_mem_codiscrete).1

lemma isDiscrete_riemannXiZeros : IsDiscrete riemannXiZeros := by
  simpa using (mem_codiscrete'.mp compl_riemannXiZeros_mem_codiscrete).2

/-- **Local finiteness of the ξ-zero divisor**: every compact set meets only finitely many
ξ-zeros. This is the `(divisor f U).support.Finite` precondition for Jensen and for
`extract_zeros_poles`. -/
lemma isCompact_inter_riemannXiZeros_finite {S : Set ℂ} (hS : IsCompact S) :
    (S ∩ riemannXiZeros).Finite := by
  apply (hS.inter_right isClosed_riemannXiZeros).finite
  exact isDiscrete_riemannXiZeros.mono Set.inter_subset_right

/-- The Hadamard zero-index type for ξ (field A). -/
abbrev XiZeroIndex : Type := riemannXiZeros

/-- Location of an indexed ξ-zero (field B: `zeroLoc : ι → ℂ`). -/
def xiZeroLoc (ρ : XiZeroIndex) : ℂ := (ρ : ℂ)

/-- Each indexed location is genuinely a zero of ξ (field C). -/
lemma entireRiemannXi_xiZeroLoc (ρ : XiZeroIndex) :
    entireRiemannXi (xiZeroLoc ρ) = 0 := ρ.2

/-- ξ-zeros are nonzero, since `ξ(0) = ½ ≠ 0` (field C: `zeroLoc ρ ≠ 0`). -/
lemma xiZeroLoc_ne_zero (ρ : XiZeroIndex) : xiZeroLoc ρ ≠ 0 := by
  intro h
  have hz := entireRiemannXi_xiZeroLoc ρ
  rw [h] at hz
  exact entireRiemannXi_zero_ne hz

/-- **ξ-zeros escape every compact set** (tend to `cocompact` along `cofinite`). This is the
convergence engine: it gives the cofinite Weierstrass M-test bound that powers
`hasProdLocallyUniformlyOn_one_add` for the genus-1 Hadamard product (field F). -/
lemma tendsto_riemannXiZeros_cofinite_cocompact :
    Tendsto ((↑) : riemannXiZeros → ℂ) cofinite (cocompact ℂ) :=
  isClosed_riemannXiZeros.tendsto_coe_cofinite_of_isDiscrete isDiscrete_riemannXiZeros

/-! ## Bridge 22 — vertical-line bound for the archimedean factor `Gammaℝ`

`Gammaℝ s = π^{-s/2}·Γ(s/2)`. Combining B20 (`‖Γ(s/2)‖ ≤ Γ(Re(s/2))`) with the elementary
`‖π^{-s/2}‖ = π^{Re(-s/2)}` (`norm_cpow_eq_rpow_re_of_pos`, π > 0) gives the right-half-plane
envelope for the completed-zeta's Gamma factor — the Gamma half of the ξ growth bound. -/
theorem norm_Gammaℝ_le {s : ℂ} (hs : 0 < (s / 2).re) :
    ‖Gammaℝ s‖ ≤ Real.pi ^ ((-s / 2 : ℂ).re) * Real.Gamma ((s / 2).re) := by
  rw [Gammaℝ_def, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
  gcongr
  exact norm_Gamma_le_real_Gamma_re hs

/-! ## Bridge 23 — Dirichlet-series bound for ζ on `Re s > 1`

`‖ζ(s)‖ ≤ ∑ₙ 1/n^{Re s}` by the triangle inequality on the absolutely convergent Dirichlet
series (`zeta_eq_tsum_one_div_nat_cpow`). This is the ζ half of the growth bound; on `Re s ≥ 2`
the RHS is `≤ ζ(2)`, a uniform constant. -/
theorem norm_riemannZeta_le_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
    ‖riemannZeta s‖ ≤ ∑' n : ℕ, 1 / (n : ℝ) ^ s.re := by
  rw [zeta_eq_tsum_one_div_nat_cpow hs]
  have hterm : ∀ n : ℕ, ‖(1 : ℂ) / (n : ℂ) ^ s‖ = 1 / (n : ℝ) ^ s.re := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [Complex.zero_cpow (Complex.ne_zero_of_one_lt_re hs),
        Real.zero_rpow (show s.re ≠ 0 by linarith)]
    · rw [norm_div, norm_one, ← Complex.ofReal_natCast,
        Complex.norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast hn)]
  have hsumm : Summable (fun n : ℕ => ‖(1 : ℂ) / (n : ℂ) ^ s‖) :=
    (Real.summable_one_div_nat_rpow.mpr hs).congr (fun n => (hterm n).symm)
  calc ‖∑' n : ℕ, (1 : ℂ) / (n : ℂ) ^ s‖
      ≤ ∑' n : ℕ, ‖(1 : ℂ) / (n : ℂ) ^ s‖ := norm_tsum_le_tsum_norm hsumm
    _ = ∑' n : ℕ, 1 / (n : ℝ) ^ s.re := tsum_congr hterm

/-! ## Bridge 24 — right-half-plane growth bound for the actual ξ (boss #1, `Re s > 1`)

Assembles B22 + B23 through the two structural identities `ξ(s) = ½·s(s−1)·Λ(s)`
(`entireRiemannXi_eq`) and `Λ(s) = ζ(s)·Gammaℝ(s)` (`riemannZeta_def_of_ne_zero`). The result
is a concrete, fully-factored majorant for `‖ξ(s)‖` on `Re s > 1`. The remaining mile to the
clean `exp(A‖s‖log‖s‖)` envelope is: bound `Γ((s/2).re)` by Stirling (`Real.Gamma σ ≤ exp(Cσlogσ)`),
absorb the `∑ₙ 1/n^σ ≤ ζ(2)` and `s(s−1)` polynomial factors into the exponential, then reflect
the left half via `entireRiemannXi_one_sub`. This brick turns the growth wall from "vague Γ·ζ
estimates" into a single explicit inequality. -/
theorem norm_entireRiemannXi_le_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
    ‖entireRiemannXi s‖ ≤
      1 / 2 * (‖s‖ * ‖s - 1‖) *
        ((∑' n : ℕ, 1 / (n : ℝ) ^ s.re) *
          (Real.pi ^ ((-s / 2 : ℂ).re) * Real.Gamma ((s / 2).re))) := by
  have hspos : 0 < s.re := by linarith
  have hs0 : s ≠ 0 := Complex.ne_zero_of_one_lt_re hs
  have hs1 : s ≠ 1 := by intro h; rw [h] at hs; simp at hs
  have hs2pos : 0 < (s / 2).re := by
    rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, Complex.div_ofReal_re]; linarith
  have hcomp : completedRiemannZeta s = riemannZeta s * Gammaℝ s := by
    have hG : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos hspos
    rw [riemannZeta_def_of_ne_zero hs0]; field_simp
  have hhalf : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num, Complex.norm_real,
      Real.norm_eq_abs]; norm_num
  rw [entireRiemannXi_eq s hs0 hs1, hcomp, norm_mul, norm_mul, norm_mul, norm_mul, hhalf]
  gcongr
  · exact norm_riemannZeta_le_of_one_lt_re hs
  · exact norm_Gammaℝ_le hs2pos

/-! ## Bridge 25 — π-factor absorption: `π^{-Re s/2} ≤ 1` for `Re s ≥ 0`

The archimedean `π^{-s/2}` factor only helps (it is `≤ 1` in the right half-plane), so it drops
out of the growth majorant entirely. Pure order arithmetic via `rpow_le_one_of_one_le_of_nonpos`. -/
theorem pi_factor_le_one_of_re_nonneg {s : ℂ} (hs : 0 ≤ s.re) :
    Real.pi ^ ((-s / 2 : ℂ).re) ≤ 1 := by
  have he : (-s / 2 : ℂ).re = -s.re / 2 := by
    rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, Complex.div_ofReal_re, Complex.neg_re]
  rw [he]
  exact Real.rpow_le_one_of_one_le_of_nonpos (by linarith [Real.pi_gt_three]) (by linarith)

/-! ## Bridge 26 — polynomial-factor absorption: `‖s‖·‖s−1‖ ≤ 2‖s‖²`

The `½·s(s−1)` prefactor is dominated by `‖s‖²` for `‖s‖ ≥ 1`, which the final exponential
envelope swallows (`‖s‖² = exp(2 log‖s‖) ≤ exp(‖s‖ log‖s‖)`). -/
theorem poly_factor_le {s : ℂ} (hs : 1 ≤ ‖s‖) :
    ‖s‖ * ‖s - 1‖ ≤ 2 * ‖s‖ ^ 2 := by
  have h1 : ‖s - 1‖ ≤ 2 * ‖s‖ := by
    calc ‖s - 1‖ ≤ ‖s‖ + ‖(1 : ℂ)‖ := norm_sub_le s 1
      _ = ‖s‖ + 1 := by rw [norm_one]
      _ ≤ 2 * ‖s‖ := by linarith
  calc ‖s‖ * ‖s - 1‖ ≤ ‖s‖ * (2 * ‖s‖) := mul_le_mul_of_nonneg_left h1 (norm_nonneg s)
    _ = 2 * ‖s‖ ^ 2 := by ring

/-! ## Bridge 27 — ζ Dirichlet-factor absorption: `∑ₙ 1/n^σ ≤ ∑ₙ 1/n²` for `σ ≥ 2`

The zeta factor is uniformly bounded on `Re s ≥ 2` by the fixed constant `∑ₙ 1/n²` (a finite
`ζ(2) = π²/6`), which the exponential envelope absorbs. Termwise `n^σ ≥ n²` comparison. -/
theorem tsum_one_div_nat_rpow_le_sq {σ : ℝ} (hσ : 2 ≤ σ) :
    (∑' n : ℕ, 1 / (n : ℝ) ^ σ) ≤ ∑' n : ℕ, 1 / (n : ℝ) ^ (2 : ℝ) := by
  refine (Real.summable_one_div_nat_rpow.mpr (by linarith)).tsum_le_tsum ?_
    (Real.summable_one_div_nat_rpow.mpr (by norm_num))
  intro n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [Real.zero_rpow (show (2:ℝ) ≠ 0 by norm_num), Real.zero_rpow (show σ ≠ 0 by linarith)]
  · have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hpow : (n : ℝ) ^ (2 : ℝ) ≤ (n : ℝ) ^ σ := Real.rpow_le_rpow_of_exponent_le hn1 hσ
    have h2pos : (0 : ℝ) < (n : ℝ) ^ (2 : ℝ) := Real.rpow_pos_of_pos (by exact_mod_cast hn) _
    exact one_div_le_one_div_of_le h2pos hpow

/-! ## Bridge 28 — **real Gamma growth** (the growth bottleneck): `Γ(x) ≤ exp(4·x·log x)`, `x ≥ 2`

The hard sub-boss, made tractable by Mathlib's `Real.Gamma_strictMonoOn_Ici` (Γ increasing on
`[2,∞)`), `Real.Gamma_nat_eq_factorial`, and `Nat.factorial_le_pow`. With `m := ⌈x⌉`:
`Γ(x) ≤ Γ(m) = (m−1)! ≤ m^m = exp(m·log m) ≤ exp(4·x·log x)` (since `m ≤ 2x`, `log m ≤ 2 log x`).
No sharp Stirling needed — this crude order-1 bound is exactly what Jensen consumes. -/
theorem real_Gamma_le_exp {x : ℝ} (hx : 2 ≤ x) :
    Real.Gamma x ≤ Real.exp (4 * x * Real.log x) := by
  set m : ℕ := ⌈x⌉₊ with hm
  have hx0 : (0 : ℝ) ≤ x := by linarith
  have hxm : x ≤ (m : ℝ) := Nat.le_ceil x
  have hm2 : 2 ≤ m := by exact_mod_cast le_trans hx hxm
  have hm1 : 1 ≤ m := le_trans (by norm_num) hm2
  have hmR2 : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm2
  have hmpos : (0 : ℝ) < (m : ℝ) := by linarith
  have hmlt : (m : ℝ) < x + 1 := Nat.ceil_lt_add_one hx0
  -- Γ x ≤ Γ ⌈x⌉  (monotone on [2,∞))
  have hstep1 : Real.Gamma x ≤ Real.Gamma (m : ℝ) :=
    Real.Gamma_strictMonoOn_Ici.monotoneOn (Set.mem_Ici.mpr hx) (Set.mem_Ici.mpr hmR2) hxm
  -- Γ ⌈x⌉ = (⌈x⌉-1)!
  have hmeq : ((m - 1 : ℕ) : ℝ) + 1 = (m : ℝ) := by
    have h : (m - 1 : ℕ) + 1 = m := Nat.sub_add_cancel hm1
    calc ((m - 1 : ℕ) : ℝ) + 1 = (((m - 1) + 1 : ℕ) : ℝ) := by push_cast; ring
      _ = (m : ℝ) := by rw [h]
  have hstep2 : Real.Gamma (m : ℝ) = (Nat.factorial (m - 1) : ℝ) := by
    rw [← hmeq, Real.Gamma_nat_eq_factorial]
  -- (m-1)! ≤ m^m
  have hfp : (Nat.factorial (m - 1) : ℝ) ≤ (m : ℝ) ^ m := by
    have hnat : Nat.factorial (m - 1) ≤ m ^ m :=
      le_trans (Nat.factorial_le_pow (m - 1))
        (le_trans (Nat.pow_le_pow_left (Nat.sub_le m 1) (m - 1))
          (Nat.pow_le_pow_right (by omega) (Nat.sub_le m 1)))
    calc (Nat.factorial (m - 1) : ℝ) ≤ ((m ^ m : ℕ) : ℝ) := by exact_mod_cast hnat
      _ = (m : ℝ) ^ m := by push_cast; ring
  -- m^m = exp(log m · m)
  have hpow_exp : (m : ℝ) ^ m = Real.exp (Real.log (m : ℝ) * (m : ℝ)) := by
    rw [← Real.rpow_natCast (m : ℝ) m, Real.rpow_def_of_pos hmpos]
  -- arithmetic absorption: log m · m ≤ 4 x log x
  have hmle2x : (m : ℝ) ≤ 2 * x := by linarith
  have hlogx0 : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have hlogm : Real.log (m : ℝ) ≤ 2 * Real.log x := by
    have hstep : Real.log (m : ℝ) ≤ Real.log (2 * x) := by
      apply Real.log_le_log hmpos hmle2x
    rw [Real.log_mul (by norm_num) (by linarith)] at hstep
    have hlog2x : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) (by linarith)
    linarith
  have hkey : Real.log (m : ℝ) * (m : ℝ) ≤ 4 * x * Real.log x := by
    calc Real.log (m : ℝ) * (m : ℝ)
        ≤ (2 * Real.log x) * (2 * x) :=
          mul_le_mul hlogm hmle2x (by linarith) (by linarith)
      _ = 4 * x * Real.log x := by ring
  calc Real.Gamma x ≤ Real.Gamma (m : ℝ) := hstep1
    _ = (Nat.factorial (m - 1) : ℝ) := hstep2
    _ ≤ (m : ℝ) ^ m := hfp
    _ = Real.exp (Real.log (m : ℝ) * (m : ℝ)) := hpow_exp
    _ ≤ Real.exp (4 * x * Real.log x) := Real.exp_le_exp.mpr hkey

/-! ## Bridge 29 — uniform ζ-series constant: `∑ₙ 1/n^σ ≤ 2` for `σ ≥ 2`

Finishes B27 by pinning the comparison sum to the Basel value `∑ₙ 1/n² = π²/6 < 2`
(`hasSum_zeta_two`). The zeta factor is now a clean absolute constant on `Re s ≥ 2`. -/
theorem zeta_dirichlet_sum_le_two {σ : ℝ} (hσ : 2 ≤ σ) :
    (∑' n : ℕ, 1 / (n : ℝ) ^ σ) ≤ 2 := by
  refine (tsum_one_div_nat_rpow_le_sq hσ).trans ?_
  have hconv : (∑' n : ℕ, 1 / (n : ℝ) ^ (2 : ℝ)) = ∑' n : ℕ, 1 / (n : ℝ) ^ 2 := by
    refine tsum_congr (fun n => ?_)
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [hconv, hasSum_zeta_two.tsum_eq]
  nlinarith [Real.pi_lt_d2, Real.pi_pos]

/-! ## Bridge 30 — **right-half-plane ξ growth**: `‖ξ(s)‖ ≤ exp(10·‖s‖·log‖s‖)` for `Re s ≥ 4`

The payoff of Bridges 24–29. Each of the four factors of the B24 majorant is replaced by an
exponential bound — polynomial `≤ ‖s‖² = exp(2 log‖s‖)` (B26), ζ-series `≤ 2 = exp(log 2)` (B29),
π-factor `≤ 1 = exp 0` (B25), `Γ(σ/2) ≤ exp(2σ·log(σ/2))` (B28, needs `σ/2 ≥ 2` ⟸ `Re s ≥ 4`) —
then the exponents add and are dominated by `10·‖s‖·log‖s‖`. This is the order-1 envelope on
the right half-plane; the functional equation `entireRiemannXi_one_sub` reflects it to the left. -/
theorem norm_entireRiemannXi_le_exp_right_half {s : ℂ} (hre : 4 ≤ s.re) :
    ‖entireRiemannXi s‖ ≤ Real.exp (10 * ‖s‖ * Real.log ‖s‖) := by
  have hsnorm : (4 : ℝ) ≤ ‖s‖ := le_trans hre (Complex.re_le_norm s)
  have hnorm_pos : (0 : ℝ) < ‖s‖ := by linarith
  have hlogs : 0 ≤ Real.log ‖s‖ := Real.log_nonneg (by linarith)
  have hσ : s.re ≤ ‖s‖ := Complex.re_le_norm s
  have hre2 : (s / 2).re = s.re / 2 := by
    rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, Complex.div_ofReal_re]
  -- ‖s‖² = exp(2 log‖s‖)
  have hsq : ‖s‖ ^ 2 = Real.exp (2 * Real.log ‖s‖) := by
    rw [← Real.exp_log (show (0 : ℝ) < ‖s‖ ^ 2 by positivity), Real.log_pow]; norm_num
  -- four factor → exp bounds
  have hA : 1 / 2 * (‖s‖ * ‖s - 1‖) ≤ Real.exp (2 * Real.log ‖s‖) := by
    rw [← hsq]; linarith [poly_factor_le (show (1 : ℝ) ≤ ‖s‖ by linarith)]
  have hZ : (∑' n : ℕ, 1 / (n : ℝ) ^ s.re) ≤ Real.exp (Real.log 2) := by
    rw [Real.exp_log (by norm_num : (0 : ℝ) < 2)]; exact zeta_dirichlet_sum_le_two (by linarith)
  have hPi : Real.pi ^ ((-s / 2 : ℂ).re) ≤ Real.exp 0 := by
    rw [Real.exp_zero]; exact pi_factor_le_one_of_re_nonneg (by linarith)
  have hG : Real.Gamma ((s / 2).re) ≤ Real.exp (4 * ((s / 2).re) * Real.log ((s / 2).re)) :=
    real_Gamma_le_exp (by rw [hre2]; linarith)
  -- exponent absorption
  have hσ2pos : 0 < s.re / 2 := by linarith
  have hlog_half_le : Real.log (s.re / 2) ≤ Real.log ‖s‖ :=
    Real.log_le_log hσ2pos (by linarith)
  have hlog_half_nn : 0 ≤ Real.log (s.re / 2) := Real.log_nonneg (by linarith)
  have hlog2_le : Real.log 2 ≤ Real.log ‖s‖ := Real.log_le_log (by norm_num) (by linarith)
  have hGterm : 4 * ((s / 2).re) * Real.log ((s / 2).re) ≤ 4 * ‖s‖ * Real.log ‖s‖ := by
    rw [hre2]
    have hprod : s.re * Real.log (s.re / 2) ≤ ‖s‖ * Real.log ‖s‖ :=
      mul_le_mul hσ hlog_half_le hlog_half_nn (by linarith)
    nlinarith [hprod, mul_nonneg (show (0 : ℝ) ≤ ‖s‖ by linarith) hlogs]
  have key : 2 * Real.log ‖s‖ + (Real.log 2 + (0 + 4 * ((s / 2).re) * Real.log ((s / 2).re)))
      ≤ 10 * ‖s‖ * Real.log ‖s‖ := by
    nlinarith [hGterm, hlog2_le, hlogs, mul_nonneg (show (0 : ℝ) ≤ ‖s‖ - 1 by linarith) hlogs]
  -- assemble
  have hbound :
      1 / 2 * (‖s‖ * ‖s - 1‖) * ((∑' n : ℕ, 1 / (n : ℝ) ^ s.re) *
        (Real.pi ^ ((-s / 2 : ℂ).re) * Real.Gamma ((s / 2).re)))
      ≤ Real.exp (2 * Real.log ‖s‖) *
          (Real.exp (Real.log 2) *
            (Real.exp 0 * Real.exp (4 * ((s / 2).re) * Real.log ((s / 2).re)))) := by
    have hGnn : 0 ≤ Real.Gamma ((s / 2).re) :=
      (Real.Gamma_pos_of_pos (by rw [hre2]; linarith)).le
    have hPinn : 0 ≤ Real.pi ^ ((-s / 2 : ℂ).re) := Real.rpow_nonneg Real.pi_pos.le _
    have hZnn : 0 ≤ (∑' n : ℕ, 1 / (n : ℝ) ^ s.re) := tsum_nonneg fun n => by positivity
    gcongr
  refine le_trans (norm_entireRiemannXi_le_of_one_lt_re (show (1 : ℝ) < s.re by linarith))
    (le_trans hbound ?_)
  rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
  exact Real.exp_le_exp.mpr key

/-! ## Bridge 31 — **left-half-plane ξ growth** via the functional equation

For `Re s ≤ -3`, reflect through `ξ(s) = ξ(1−s)` (`entireRiemannXi_one_sub`): then
`(1−s).re = 1 − Re s ≥ 4`, so B30 applies to `1 − s`. Together with B30 this covers the entire
plane OUTSIDE the vertical strip `-3 ≤ Re s ≤ 4`. The strip is the sole remaining region; on a
large circle it is the high-`|Im|` part, requiring either `PhragmenLindelof.vertical_strip`
(boundary bounds from B30/B31 + a crude order ceiling) or a vertical-line Γ estimate. -/
theorem norm_entireRiemannXi_le_exp_left_half {s : ℂ} (hre : s.re ≤ -3) :
    ‖entireRiemannXi s‖ ≤ Real.exp (10 * ‖1 - s‖ * Real.log ‖1 - s‖) := by
  have hw : (4 : ℝ) ≤ (1 - s).re := by rw [Complex.sub_re, Complex.one_re]; linarith
  have h := norm_entireRiemannXi_le_exp_right_half hw
  rwa [entireRiemannXi_one_sub] at h

/-! ## Bridge 32 — **global ξ growth** (modulo the strip): `‖ξ(z)‖ ≤ exp(A·‖z‖·log‖z‖)`

Combines the right half (B30), the reflected left half (B31), and a strip-growth hypothesis
into a single pointwise order-1 envelope valid for all `‖z‖ ≥ 4`. The strip hypothesis is the
ONLY remaining analytic input — exactly the high-`|Im|` vertical-strip bound that
`PhragmenLindelof.vertical_strip` (boundary data from B30/B31) is designed to supply. Everything
else (right/left coverage, constant bookkeeping) is discharged here. -/
theorem exists_norm_entireRiemannXi_le_exp_of_strip
    (hstrip : ∃ B : ℝ, 0 ≤ B ∧ ∀ z : ℂ, -3 ≤ z.re → z.re ≤ 4 →
        ‖entireRiemannXi z‖ ≤ Real.exp (B * ‖z‖ * Real.log ‖z‖)) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ z : ℂ, 4 ≤ ‖z‖ →
        ‖entireRiemannXi z‖ ≤ Real.exp (A * ‖z‖ * Real.log ‖z‖) := by
  obtain ⟨B, hB0, hB⟩ := hstrip
  refine ⟨max 40 B, le_trans hB0 (le_max_right _ _), fun z hz => ?_⟩
  have hzlog : (0 : ℝ) ≤ ‖z‖ * Real.log ‖z‖ :=
    mul_nonneg (by linarith) (Real.log_nonneg (by linarith))
  by_cases hr : 4 ≤ z.re
  · -- right half-plane
    refine (norm_entireRiemannXi_le_exp_right_half hr).trans (Real.exp_le_exp.mpr ?_)
    nlinarith [le_max_left (40 : ℝ) B, hzlog]
  · have hr' : z.re ≤ 4 := (not_le.mp hr).le
    by_cases hl : z.re ≤ -3
    · -- reflected left half-plane: bound ‖1-z‖·log‖1-z‖ ≤ 4·‖z‖·log‖z‖
      have hz1 : ‖1 - z‖ ≤ 2 * ‖z‖ := by
        have h := norm_sub_le (1 : ℂ) z; rw [norm_one] at h; linarith
      have hz1' : (1 : ℝ) ≤ ‖1 - z‖ := by
        have h := norm_sub_norm_le z (1 : ℂ); rw [norm_sub_rev, norm_one] at h; linarith
      have hlogz1 : Real.log ‖1 - z‖ ≤ 2 * Real.log ‖z‖ := by
        have h2 : Real.log ‖1 - z‖ ≤ Real.log (2 * ‖z‖) := Real.log_le_log (by linarith) hz1
        rw [Real.log_mul (by norm_num) (by linarith)] at h2
        have : Real.log 2 ≤ Real.log ‖z‖ := Real.log_le_log (by norm_num) (by linarith)
        linarith
      have hprod : ‖1 - z‖ * Real.log ‖1 - z‖ ≤ 2 * ‖z‖ * (2 * Real.log ‖z‖) :=
        mul_le_mul hz1 hlogz1 (Real.log_nonneg hz1') (by linarith)
      refine (norm_entireRiemannXi_le_exp_left_half hl).trans (Real.exp_le_exp.mpr ?_)
      nlinarith [hprod, le_max_left (40 : ℝ) B, hzlog]
    · -- middle strip: the hypothesis
      have hmid : -3 ≤ z.re := (not_le.mp hl).le
      refine (hB z hmid hr').trans (Real.exp_le_exp.mpr ?_)
      nlinarith [le_max_right (40 : ℝ) B, hzlog]

/-! ## Bridge 33 — **Riemann–von Mangoldt zero count** `N(r) = O(r log r)` (modulo the strip)

Feeds the global growth envelope (B32) into the specialized Jensen bound (B19). For every
`r ≥ 2`, the weighted ξ-zero count in the disk of radius `r` is bounded by `A·(e r)·log(e r)` — the
genuine `T log T` Riemann–von Mangoldt shape. This is the count half of the Hadamard program,
now reduced (like everything upstream) to the single vertical-strip growth input. -/
open MeromorphicOn in
theorem xi_zero_count_bigO_of_strip
    (hstrip : ∃ B : ℝ, 0 ≤ B ∧ ∀ z : ℂ, -3 ≤ z.re → z.re ≤ 4 →
        ‖entireRiemannXi z‖ ≤ Real.exp (B * ‖z‖ * Real.log ‖z‖)) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ r : ℝ, 2 ≤ r →
      ∑ᶠ u, divisor entireRiemannXi (Metric.closedBall (0 : ℂ) r) u
        ≤ A * (Real.exp 1 * r) * Real.log (Real.exp 1 * r) - Real.log ‖entireRiemannXi 0‖ := by
  obtain ⟨A, hA0, hA⟩ := exists_norm_entireRiemannXi_le_exp_of_strip hstrip
  refine ⟨A, hA0, fun r hr => ?_⟩
  refine xi_zero_count_le_of_growth (by linarith : (1 : ℝ) ≤ r) hA0 (fun z hz => ?_)
  rw [Metric.mem_sphere, dist_zero_right] at hz
  have he2 : (2 : ℝ) ≤ Real.exp 1 := by have := Real.add_one_le_exp (1 : ℝ); linarith
  have hge4 : (4 : ℝ) ≤ ‖z‖ := by rw [hz]; nlinarith [he2, hr]
  have hb := hA z hge4
  rwa [hz] at hb

/-! ## Bridge 34 — **genus-1 Hadamard product converges** (item 5, modulo Σ1/‖ρ‖²)

Given inverse-square summability of the zeros, the genus-1 product `∏ᵨ E₁(s/ρ)` is `Multipliable`
at every `s`. Engine: write each factor as `1 + (E₁−1)`, bound `‖E₁(s/ρ)−1‖ ≤ 3‖s/ρ‖² ≤
3‖s‖²/‖ρ‖²` (B7 `norm_genus1_sub_one_le`) for the cofinitely-many ρ with `‖ρ‖ ≥ ‖s‖` (B21's
`tendsto_..._cocompact`), then `Summable.of_norm_bounded_eventually` +
`Complex.multipliable_one_add_of_summable`. This is the convergence content of the Hadamard
product, reduced to the single summability input (item 4). -/
theorem xi_genus1Product_multipliable {s : ℂ}
    (hsumm : Summable fun ρ : XiZeroIndex => 1 / ‖xiZeroLoc ρ‖ ^ 2) :
    Multipliable fun ρ : XiZeroIndex => genus1Factor (xiZeroLoc ρ) s := by
  have hev : ∀ᶠ ρ : XiZeroIndex in Filter.cofinite, ‖s‖ ≤ ‖xiZeroLoc ρ‖ :=
    tendsto_riemannXiZeros_cofinite_cocompact.eventually
      (tendsto_norm_cocompact_atTop.eventually_ge_atTop ‖s‖)
  have hfactor : (fun ρ : XiZeroIndex => genus1Factor (xiZeroLoc ρ) s)
      = fun ρ => 1 + (genus1Factor (xiZeroLoc ρ) s - 1) := by funext ρ; ring
  rw [hfactor]
  refine Complex.multipliable_one_add_of_summable ?_
  refine Summable.of_norm_bounded_eventually
    (g := fun ρ => 3 * ‖s‖ ^ 2 * (1 / ‖xiZeroLoc ρ‖ ^ 2)) (hsumm.mul_left (3 * ‖s‖ ^ 2)) ?_
  filter_upwards [hev] with ρ hρ
  have hle1 : ‖s / xiZeroLoc ρ‖ ≤ 1 := by
    rw [norm_div, div_le_one (norm_pos_iff.mpr (xiZeroLoc_ne_zero ρ))]; exact hρ
  have hB7 := norm_genus1_sub_one_le hle1
  simp only [genus1Factor]
  refine hB7.trans (le_of_eq ?_)
  rw [norm_div, div_pow]; ring


/-! ## Bridge 35 — counting ⇒ inverse-square summability (item 4, ABSTRACT)
Dyadic-shell decomposition: a zero family whose shell-cardinalities grow like `C·(k+1)·2^k`
(the RvM `N(r)=O(r log r)` shape) has summable inverse-squares. Engine for the Hadamard product. -/

theorem summable_inv_sq_of_shellCard
    {ι : Type*} (loc : ι → ℂ) (C : ℝ)
    (hlb : ∀ i, (1 : ℝ) ≤ ‖loc i‖)
    (hfin : ∀ k : ℕ, {i | ‖loc i‖ < 2 ^ (k+1)}.Finite)
    (hcard : ∀ k : ℕ,
      (Nat.card {i | (2:ℝ) ^ k ≤ ‖loc i‖ ∧ ‖loc i‖ < 2 ^ (k+1)} : ℝ) ≤ C * (k+1) * 2 ^ k) :
    Summable (fun i => 1 / ‖loc i‖ ^ 2) := by
  classical
  -- the shell index of point i
  set shell : ι → ℕ := fun i => ⌊Real.logb 2 ‖loc i‖⌋₊ with hshell
  -- membership: i lies in shell (shell i)
  have hmem : ∀ i, (2:ℝ) ^ (shell i) ≤ ‖loc i‖ ∧ ‖loc i‖ < 2 ^ (shell i + 1) := by
    intro i
    have hx : (1:ℝ) ≤ ‖loc i‖ := hlb i
    have hxpos : (0:ℝ) < ‖loc i‖ := lt_of_lt_of_le one_pos hx
    have hL0 : 0 ≤ Real.logb 2 ‖loc i‖ := Real.logb_nonneg (by norm_num) hx
    set L := Real.logb 2 ‖loc i‖ with hLdef
    constructor
    · -- 2^(shell i) ≤ ‖loc i‖
      have hk : ((shell i : ℝ)) ≤ L := by
        simpa [hshell] using Nat.floor_le hL0
      have : (2:ℝ) ^ ((shell i : ℝ)) ≤ ‖loc i‖ := by
        rw [← Real.le_logb_iff_rpow_le (by norm_num) hxpos]
        exact hk
      rwa [Real.rpow_natCast] at this
    · -- ‖loc i‖ < 2^(shell i + 1)
      have hk : L < (shell i : ℝ) + 1 := by
        simpa [hshell] using Nat.lt_floor_add_one L
      have : ‖loc i‖ < (2:ℝ) ^ ((shell i : ℝ) + 1) := by
        rw [← Real.logb_lt_iff_lt_rpow (by norm_num) hxpos]
        exact hk
      have hcast : ((shell i : ℝ) + 1) = ((shell i + 1 : ℕ) : ℝ) := by push_cast; ring
      rw [hcast, Real.rpow_natCast] at this
      exact this
  -- the fiber over shell index k is a subset of the (finite) ball, hence finite
  have hfiberfin : ∀ k : ℕ, {i | shell i = k}.Finite := by
    intro k
    apply Set.Finite.subset (hfin k)
    intro i hi
    simp only [Set.mem_setOf_eq] at hi ⊢
    have := (hmem i).2
    rw [hi] at this
    exact this
  -- abbreviate the summand
  set g : ι → ℝ := fun i => 1 / ‖loc i‖ ^ 2 with hg
  have hgnn : ∀ i, 0 ≤ g i := by
    intro i; positivity
  -- Use the sigma fiber equivalence to regroup the sum.
  rw [← (Equiv.sigmaFiberEquiv shell).summable_iff]
  -- Now summing g (e ⟨k, i⟩) over the sigma type.
  rw [summable_sigma_of_nonneg (by intro x; exact hgnn _)]
  refine ⟨?_, ?_⟩
  · -- each fiber summable (it is finite)
    intro k
    have : Finite {i // shell i = k} := (hfiberfin k).to_subtype
    exact summable_of_hasFiniteSupport (by exact Set.toFinite _)
  · -- the outer sum over k is summable, bounded by C*(k+1)/2^k
    -- give each fiber a Fintype instance
    have hfintype : ∀ k : ℕ, Fintype {i // shell i = k} := fun k => (hfiberfin k).fintype
    -- bound the per-fiber tsum by C*(k+1)/2^k
    have hbound : ∀ k : ℕ,
        (∑' (i : {i // shell i = k}), g (Equiv.sigmaFiberEquiv shell ⟨k, i⟩))
          ≤ C * (k+1) / 2 ^ k := by
      intro k
      have hft := hfintype k
      -- convert tsum to finset sum
      rw [tsum_fintype]
      -- each term ≤ 1/4^k
      have hterm : ∀ i : {i // shell i = k},
          g (Equiv.sigmaFiberEquiv shell ⟨k, i⟩) ≤ 1 / (4:ℝ) ^ k := by
        intro i
        have he : (Equiv.sigmaFiberEquiv shell ⟨k, i⟩) = (i : ι) := rfl
        rw [he, hg]
        simp only
        have hlow : (2:ℝ) ^ k ≤ ‖loc (i : ι)‖ := by
          have := (hmem (i : ι)).1
          rwa [i.2] at this
        have h2k : (0:ℝ) < (2:ℝ) ^ k := by positivity
        have hsq : ((2:ℝ) ^ k) ^ 2 ≤ ‖loc (i : ι)‖ ^ 2 := by
          apply pow_le_pow_left₀ (le_of_lt h2k) hlow
        have h4 : ((2:ℝ) ^ k) ^ 2 = (4:ℝ) ^ k := by
          rw [← pow_mul, mul_comm, pow_mul]; norm_num
        rw [h4] at hsq
        have h4pos : (0:ℝ) < (4:ℝ) ^ k := by positivity
        have hnpos : (0:ℝ) < ‖loc (i : ι)‖ ^ 2 := by
          have : (0:ℝ) < ‖loc (i : ι)‖ := lt_of_lt_of_le one_pos (hlb _)
          positivity
        rw [div_le_div_iff₀ hnpos h4pos]
        rw [one_mul, one_mul]
        exact hsq
      -- sum ≤ card • (1/4^k)
      have hsum_le : (∑ i : {i // shell i = k}, g (Equiv.sigmaFiberEquiv shell ⟨k, i⟩))
          ≤ (Finset.univ : Finset {i // shell i = k}).card • (1 / (4:ℝ) ^ k) := by
        apply Finset.sum_le_card_nsmul
        intro x _
        exact hterm x
      refine le_trans hsum_le ?_
      rw [nsmul_eq_mul]
      -- card = Nat.card fiber ≤ C(k+1)2^k
      have hcard_eq : ((Finset.univ : Finset {i // shell i = k}).card : ℝ)
          = (Nat.card {i // shell i = k} : ℝ) := by
        rw [Nat.card_eq_fintype_card]; rfl
      rw [hcard_eq]
      -- Nat.card fiber ≤ Nat.card shell-set
      have hsub : {i | shell i = k} ⊆
          {i | (2:ℝ) ^ k ≤ ‖loc i‖ ∧ ‖loc i‖ < 2 ^ (k+1)} := by
        intro i hi
        simp only [Set.mem_setOf_eq] at hi ⊢
        have h1 := (hmem i).1
        have h2 := (hmem i).2
        rw [hi] at h1 h2
        exact ⟨h1, h2⟩
      have hcardmono : (Nat.card {i // shell i = k} : ℝ) ≤
          (Nat.card {i | (2:ℝ) ^ k ≤ ‖loc i‖ ∧ ‖loc i‖ < 2 ^ (k+1)} : ℝ) := by
        have hfinbig : {i | (2:ℝ) ^ k ≤ ‖loc i‖ ∧ ‖loc i‖ < 2 ^ (k+1)}.Finite := by
          apply Set.Finite.subset (hfin k)
          intro i hi
          exact hi.2
        have : Nat.card {i // shell i = k} ≤
            Nat.card {i | (2:ℝ) ^ k ≤ ‖loc i‖ ∧ ‖loc i‖ < 2 ^ (k+1)} := by
          apply Nat.card_mono hfinbig hsub
        exact_mod_cast this
      -- chain: card * (1/4^k) ≤ C(k+1)2^k * (1/4^k) = C(k+1)/2^k
      have h4pos : (0:ℝ) < (4:ℝ) ^ k := by positivity
      have hstep1 : (Nat.card {i // shell i = k} : ℝ) * (1 / (4:ℝ) ^ k)
          ≤ (C * (k+1) * 2 ^ k) * (1 / (4:ℝ) ^ k) := by
        apply mul_le_mul_of_nonneg_right
        · exact le_trans hcardmono (hcard k)
        · positivity
      refine le_trans hstep1 ?_
      -- (C(k+1)2^k)/4^k = C(k+1)/2^k
      have h4eq : (4:ℝ) ^ k = (2:ℝ) ^ k * (2:ℝ) ^ k := by
        rw [← pow_add, ← two_mul, pow_mul]; norm_num
      rw [h4eq]
      have h2pos : (0:ℝ) < (2:ℝ) ^ k := by positivity
      have hne : (2:ℝ) ^ k ≠ 0 := ne_of_gt h2pos
      have hcompute : C * (↑k + 1) * 2 ^ k * (1 / (2 ^ k * 2 ^ k))
          = C * (↑k + 1) / 2 ^ k := by
        field_simp
      rw [hcompute]
    -- now: the outer sum is summable, since dominated by C*(k+1)/2^k which is summable
    apply Summable.of_nonneg_of_le _ hbound
    · -- summability of k ↦ C*(k+1)/2^k
      have hgeo : Summable (fun n : ℕ => (n:ℝ) ^ 1 * ((1:ℝ)/2) ^ n) :=
        summable_pow_mul_geometric_of_norm_lt_one 1 (by rw [Real.norm_eq_abs]; norm_num)
      have hgeo0 : Summable (fun n : ℕ => (n:ℝ) ^ 0 * ((1:ℝ)/2) ^ n) :=
        summable_pow_mul_geometric_of_norm_lt_one 0 (by rw [Real.norm_eq_abs]; norm_num)
      have hsum : Summable (fun k : ℕ => C * (k+1) / 2 ^ k) := by
        have heq : (fun k : ℕ => C * (k+1) / 2 ^ k)
            = (fun k : ℕ => C * ((k:ℝ) ^ 1 * ((1:ℝ)/2) ^ k) + C * ((k:ℝ) ^ 0 * ((1:ℝ)/2) ^ k)) := by
          funext k
          have h2pos : (0:ℝ) < (2:ℝ) ^ k := by positivity
          have hhalf : ((1:ℝ)/2) ^ k = 1 / (2:ℝ) ^ k := by
            rw [div_pow]; norm_num
          rw [hhalf]
          field_simp
        rw [heq]
        exact (hgeo.mul_left C).add (hgeo0.mul_left C)
      exact hsum
    · intro k
      apply tsum_nonneg
      intro i
      exact hgnn _

/-! ## Bridge 36 — genus-1 product converges LOCALLY UNIFORMLY (item 5, ABSTRACT)
Given Σ1/‖ρ‖² and zeros escaping to ∞, `∏ E₁(s/ρ)` is `MultipliableLocallyUniformlyOn univ`. -/

/-- Pointwise: `genus1Factor (loc i) s - 1 = (1 - s/loc i)·exp(s/loc i) - 1`,
so the norm bound applies with `w = s / loc i`. -/
theorem norm_genus1Factor_sub_one_le {ρ s : ℂ} (h : ‖s / ρ‖ ≤ 1) :
    ‖genus1Factor ρ s - 1‖ ≤ 3 * ‖s / ρ‖ ^ 2 := by
  unfold genus1Factor
  exact norm_genus1_sub_one_le h

theorem genus1Product_multipliableLocallyUniformlyOn
    {ι : Type*} (loc : ι → ℂ)
    (_hne : ∀ i, loc i ≠ 0)
    (hsumm : Summable (fun i => 1 / ‖loc i‖ ^ 2))
    (hcofin : Tendsto (fun i => ‖loc i‖) cofinite atTop) :
    MultipliableLocallyUniformlyOn (fun i s => genus1Factor (loc i) s) Set.univ := by
  -- Each factor is continuous (entire).
  have hcts : ∀ i, Continuous (fun s : ℂ => genus1Factor (loc i) s) := by
    intro i
    unfold genus1Factor
    fun_prop
  -- Continuity of `s ↦ genus1Factor (loc i) s - 1`.
  have hcts' : ∀ i, Continuous (fun s : ℂ => genus1Factor (loc i) s - 1) := by
    intro i; exact (hcts i).sub continuous_const
  -- Reduce to the `1 + f` shape and use the congr lemma.
  apply MultipliableLocallyUniformlyOn_congr
    (f := fun i s => 1 + (genus1Factor (loc i) s - 1))
    (f' := fun i s => genus1Factor (loc i) s)
  · intro i s _hs; ring
  -- Now prove the `1 + f` version converges locally uniformly on `univ`.
  apply multipliableLocallyUniformlyOn_of_of_forall_exists_nhds
  intro x _hx
  -- Pick R big enough so that the closed ball of radius R is a nbhd of x.
  set R : ℝ := ‖x‖ + 1 with hR
  have hRpos : 0 < R := by positivity
  refine ⟨Metric.closedBall (0 : ℂ) R, ?_, ?_⟩
  · -- closedBall 0 R ∈ 𝓝[univ] x
    rw [nhdsWithin_univ]
    refine Metric.closedBall_mem_nhds_of_mem ?_
    simp only [Metric.mem_ball, dist_zero_right]
    rw [hR]; linarith [norm_nonneg x]
  · -- MultipliableUniformlyOn on the compact closed ball.
    have hK : IsCompact (Metric.closedBall (0 : ℂ) R) := isCompact_closedBall _ _
    -- summable majorant u i = 3 R^2 * (1 / ‖loc i‖^2)
    have hu : Summable (fun i => 3 * R ^ 2 * (1 / ‖loc i‖ ^ 2)) := hsumm.mul_left _
    -- the M-test bound: cofinitely many i with ‖loc i‖ ≥ R
    have hge : ∀ᶠ i in cofinite, R ≤ ‖loc i‖ := hcofin.eventually_ge_atTop R
    have hbound : ∀ᶠ i in cofinite,
        ∀ s ∈ Metric.closedBall (0 : ℂ) R, ‖genus1Factor (loc i) s - 1‖
          ≤ 3 * R ^ 2 * (1 / ‖loc i‖ ^ 2) := by
      filter_upwards [hge] with i hi s hs
      have hsR : ‖s‖ ≤ R := by simpa [dist_zero_right] using hs
      have hlocpos : 0 < ‖loc i‖ := by linarith
      -- ‖s / loc i‖ ≤ 1
      have hdiv : ‖s / loc i‖ ≤ 1 := by
        rw [norm_div]
        rw [div_le_one hlocpos]
        exact le_trans hsR hi
      have hb := norm_genus1Factor_sub_one_le (ρ := loc i) (s := s) hdiv
      refine hb.trans ?_
      -- 3 * ‖s/loc i‖^2 ≤ 3 * R^2 * (1/‖loc i‖^2)
      have hsq : ‖s‖ ^ 2 ≤ R ^ 2 := by
        apply pow_le_pow_left₀ (norm_nonneg s) hsR
      have hlsq : 0 < ‖loc i‖ ^ 2 := by positivity
      rw [norm_div, div_pow]
      calc 3 * (‖s‖ ^ 2 / ‖loc i‖ ^ 2)
          ≤ 3 * (R ^ 2 / ‖loc i‖ ^ 2) := by
            gcongr
        _ = 3 * R ^ 2 * (1 / ‖loc i‖ ^ 2) := by ring
    -- assemble via multipliableUniformlyOn_one_add
    have := Summable.multipliableUniformlyOn_one_add (f := fun i s => genus1Factor (loc i) s - 1)
      (K := Metric.closedBall (0 : ℂ) R) (u := fun i => 3 * R ^ 2 * (1 / ‖loc i‖ ^ 2))
      hK hu hbound (fun i => (hcts' i).continuousOn)
    exact this

/-! ## Bridge 37 — product log-derivative = regularized zero sum (item 6, ABSTRACT)
`logDeriv (∏ E₁(·/ρ)) s = Σ (1/(s-ρ) + 1/ρ)`, via `logDeriv_tprod_eq_tsum` + B4 per-factor. -/

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

/-! ## Bridge 38/39 — ξ-specializations of the Hadamard product (items 5–6 on the real zeros)

Instantiate the abstract product theorems on `xiZeroLoc : XiZeroIndex → ℂ`: B21 supplies the
nonvanishing (`xiZeroLoc_ne_zero`) and the cofinite escape (`tendsto_riemannXiZeros_cofinite_cocompact`).
Given inverse-square summability (item 4, gated on the divisor↔count bridge), the genus-1 product
over ξ's zeros converges locally uniformly and its log-derivative is the regularized zero sum —
exactly the Hadamard log-derivative spine `EntireXiClassicalHadamardTheorem` consumes. -/

theorem xi_genus1Product_multipliableLocallyUniformlyOn
    (hsumm : Summable fun ρ : XiZeroIndex => 1 / ‖xiZeroLoc ρ‖ ^ 2) :
    MultipliableLocallyUniformlyOn (fun ρ s => genus1Factor (xiZeroLoc ρ) s) Set.univ :=
  genus1Product_multipliableLocallyUniformlyOn xiZeroLoc xiZeroLoc_ne_zero hsumm
    (tendsto_norm_cocompact_atTop.comp tendsto_riemannXiZeros_cofinite_cocompact)

theorem xi_genus1Product_logDeriv_eq_tsum {s : ℂ}
    (hsne : ∀ ρ : XiZeroIndex, s ≠ xiZeroLoc ρ)
    (hmul : MultipliableLocallyUniformlyOn (fun ρ s => genus1Factor (xiZeroLoc ρ) s) Set.univ)
    (hsumm : Summable fun ρ : XiZeroIndex => logDeriv (genus1Factor (xiZeroLoc ρ)) s)
    (hprodne : ∏' ρ : XiZeroIndex, genus1Factor (xiZeroLoc ρ) s ≠ 0) :
    logDeriv (fun z => ∏' ρ : XiZeroIndex, genus1Factor (xiZeroLoc ρ) z) s
      = ∑' ρ : XiZeroIndex, (1 / (s - xiZeroLoc ρ) + 1 / xiZeroLoc ρ) :=
  logDeriv_genus1Product_eq_tsum xiZeroLoc s xiZeroLoc_ne_zero hsne hmul hsumm hprodne


/-! ## Bridge 40/41 — generalized Liouville + zero-free⇒exp (item 7 building blocks)
`affine_of_entire_of_linear_growth`: entire + linear growth ⇒ affine (Cauchy estimate + Liouville).
`exists_entire_exp_eq`: zero-free entire ⇒ `exp` of an entire function (holomorphic primitive of f'/f).
These are the two inputs the Hadamard final step `Q = ξ/∏ = C·exp(a+bs)` consumes. -/

open Metric in
/-- The derivative of an entire function of linear growth is bounded by the growth constant. -/
theorem norm_deriv_le_of_linear_growth
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) {C : ℝ} (hC : 0 ≤ C)
    (hgrow : ∀ z : ℂ, ‖f z‖ ≤ C * (1 + ‖z‖)) :
    ∀ z : ℂ, ‖deriv f z‖ ≤ C := by
  intro z
  -- For each R > 0, Cauchy estimate gives ‖deriv f z‖ ≤ C * (1 + ‖z‖ + R) / R.
  have key : ∀ R : ℝ, 0 < R → ‖deriv f z‖ ≤ C * (1 + ‖z‖ + R) / R := by
    intro R hR
    have hsphere : ∀ w ∈ sphere z R, ‖f w‖ ≤ C * (1 + ‖z‖ + R) := by
      intro w hw
      rw [mem_sphere_iff_norm] at hw
      have hwnorm : ‖w‖ ≤ ‖z‖ + R := by
        have heq : w = (w - z) + z := by ring
        calc ‖w‖ = ‖(w - z) + z‖ := by rw [← heq]
          _ ≤ ‖w - z‖ + ‖z‖ := norm_add_le _ _
          _ = R + ‖z‖ := by rw [hw]
          _ = ‖z‖ + R := by ring
      calc ‖f w‖ ≤ C * (1 + ‖w‖) := hgrow w
        _ ≤ C * (1 + (‖z‖ + R)) := by
            apply mul_le_mul_of_nonneg_left _ hC
            linarith
        _ = C * (1 + ‖z‖ + R) := by ring
    have := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hR hf.diffContOnCl hsphere
    exact this
  -- Take R → ∞: C * (1 + ‖z‖ + R) / R → C.
  have htend : Tendsto (fun R : ℝ => C * (1 + ‖z‖ + R) / R) atTop (𝓝 C) := by
    have h1 : Tendsto (fun R : ℝ => (1 + ‖z‖ + R) / R) atTop (𝓝 1) := by
      have : (fun R : ℝ => (1 + ‖z‖ + R) / R) =ᶠ[atTop] (fun R : ℝ => (1 + ‖z‖) / R + 1) := by
        filter_upwards [eventually_gt_atTop 0] with R hR
        field_simp
      rw [tendsto_congr' this]
      have : Tendsto (fun R : ℝ => (1 + ‖z‖) / R) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop tendsto_id
      simpa using this.add tendsto_const_nhds
    have : Tendsto (fun R : ℝ => C * ((1 + ‖z‖ + R) / R)) atTop (𝓝 (C * 1)) :=
      tendsto_const_nhds.mul h1
    simp only [mul_one] at this
    convert this using 2 with R
    ring
  refine le_of_tendsto_of_tendsto tendsto_const_nhds htend ?_
  filter_upwards [eventually_gt_atTop 0] with R hR
  exact key R hR

-- (1) linear growth ⇒ the second derivative vanishes ⇒ affine
theorem affine_of_entire_of_linear_growth
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) (C : ℝ)
    (hgrow : ∀ z : ℂ, ‖f z‖ ≤ C * (1 + ‖z‖)) :
    ∃ a b : ℂ, ∀ z, f z = a * z + b := by
  -- WLOG C ≥ 0 (since ‖f 0‖ ≤ C * 1 forces C ≥ 0).
  have hC : 0 ≤ C := by
    have := hgrow 0
    simp only [norm_zero, add_zero, mul_one] at this
    exact le_trans (norm_nonneg _) this
  -- deriv f is bounded by C.
  have hbound := norm_deriv_le_of_linear_growth hf hC hgrow
  -- deriv f is entire.
  have hderiv_diff : Differentiable ℂ (deriv f) := by
    have := hf.differentiableOn.deriv isOpen_univ
    rw [differentiableOn_univ] at this
    exact this
  -- deriv f is bounded, hence constant by Liouville.
  have hconst : ∀ z, deriv f z = deriv f 0 := by
    intro z
    apply hderiv_diff.apply_eq_apply_of_bounded
    rw [isBounded_iff_forall_norm_le]
    exact ⟨C, by rintro x ⟨w, rfl⟩; exact hbound w⟩
  -- Set a := deriv f 0, b := f 0.  Show g z := f z - a * z is constant.
  set a := deriv f 0 with ha
  have hg_diff : Differentiable ℂ (fun z => f z - a * z) :=
    hf.sub ((differentiable_const a).mul differentiable_id)
  have hg_deriv : ∀ z, deriv (fun z => f z - a * z) z = 0 := by
    intro z
    have h1 : HasDerivAt f (deriv f z) z := (hf z).hasDerivAt
    have h2 : HasDerivAt (fun z => a * z) a z := by
      simpa using (hasDerivAt_id z).const_mul a
    have : HasDerivAt (fun z => f z - a * z) (deriv f z - a) z := h1.sub h2
    rw [this.deriv, hconst z, ha]
    ring
  have hg_const : ∀ z, (fun z => f z - a * z) z = (fun z => f z - a * z) 0 :=
    fun z => is_const_of_deriv_eq_zero hg_diff hg_deriv z 0
  refine ⟨a, f 0, fun z => ?_⟩
  have hz := hg_const z
  simp only [mul_zero, sub_zero] at hz
  -- hz : f z - a * z = f 0
  linear_combination hz

-- (2) zero-free entire ⇒ exp of an entire function (on all of ℂ, which is simply connected)
theorem exists_entire_exp_eq {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hne : ∀ z, f z ≠ 0) :
    ∃ g : ℂ → ℂ, Differentiable ℂ g ∧ ∀ z, f z = Complex.exp (g z) := by
  -- The logarithmic derivative deriv f / f is entire.
  have hlog_diff : Differentiable ℂ (fun z => deriv f z / f z) := by
    have hderiv_diff : Differentiable ℂ (deriv f) := by
      have := hf.differentiableOn.deriv isOpen_univ
      rw [differentiableOn_univ] at this
      exact this
    exact hderiv_diff.div hf (fun z => hne z)
  -- It has a primitive g₀ : HasDerivAt g₀ (deriv f z / f z) z for all z.
  obtain ⟨g₀, hg₀⟩ := hlog_diff.isExactOn_univ
  have hg₀' : ∀ z, HasDerivAt g₀ (deriv f z / f z) z := fun z => hg₀ z (Set.mem_univ z)
  have hg₀_diff : Differentiable ℂ g₀ := fun z => (hg₀' z).differentiableAt
  -- h z := f z * exp(- g₀ z) has derivative 0 everywhere.
  set h : ℂ → ℂ := fun z => f z * Complex.exp (- g₀ z) with hh
  have hderiv_h : ∀ z, HasDerivAt h 0 z := by
    intro z
    have hf' : HasDerivAt f (deriv f z) z := (hf z).hasDerivAt
    have hexp : HasDerivAt (fun z => Complex.exp (- g₀ z))
        (Complex.exp (- g₀ z) * (- (deriv f z / f z))) z :=
      ((hg₀' z).neg).cexp
    have hprod : HasDerivAt h
        (deriv f z * Complex.exp (- g₀ z)
          + f z * (Complex.exp (- g₀ z) * (- (deriv f z / f z)))) z :=
      hf'.mul hexp
    have heq : deriv f z * Complex.exp (- g₀ z)
        + f z * (Complex.exp (- g₀ z) * (- (deriv f z / f z))) = 0 := by
      have hfz : f z ≠ 0 := hne z
      field_simp
      ring
    rwa [heq] at hprod
  -- Hence h is constant.
  have hh_diff : Differentiable ℂ h := fun z => (hderiv_h z).differentiableAt
  have hh_deriv0 : ∀ z, deriv h z = 0 := fun z => (hderiv_h z).deriv
  have hh_const : ∀ z, h z = h 0 :=
    fun z => is_const_of_deriv_eq_zero hh_diff hh_deriv0 z 0
  -- h 0 = f 0 * exp(- g₀ 0) ≠ 0.
  set c : ℂ := h 0 with hc
  have hc_ne : c ≠ 0 := by
    rw [hc, hh]
    exact mul_ne_zero (hne 0) (Complex.exp_ne_zero _)
  -- f z = c * exp (g₀ z) since f z * exp(-g₀ z) = c.
  set d : ℂ := Complex.log c with hd
  have hcd : Complex.exp d = c := Complex.exp_log hc_ne
  refine ⟨fun z => g₀ z + d, hg₀_diff.add_const d, fun z => ?_⟩
  have hz := hh_const z
  simp only [hh] at hz
  -- hz : f z * exp(- g₀ z) = c
  rw [Complex.exp_add, hcd]
  -- goal: f z = exp (g₀ z) * c
  have key : f z = c * Complex.exp (g₀ z) := by
    have hstep : f z * Complex.exp (- g₀ z) * Complex.exp (g₀ z) = c * Complex.exp (g₀ z) := by
      rw [hz]
    rw [mul_assoc, ← Complex.exp_add] at hstep
    simp only [neg_add_cancel, Complex.exp_zero, mul_one] at hstep
    exact hstep
  rw [key]; ring


/-! ## Bridge 42/43 — Hadamard final step: zero-free entire order-1 ⇒ `C·exp(a+b·z)`
`exp_affine_of_zerofree_order_one` takes the two building blocks as parameters; B40/B41 discharge
them, so `xi_exp_affine_of_zerofree_order_one` below is UNCONDITIONAL. Borel–Carathéodory turns the
one-sided `Re g ≤ linear` bound into `‖g‖ ≤ linear`, then generalized Liouville gives `g` affine. -/

open Metric in
theorem exp_affine_of_zerofree_order_one
    (liouville : ∀ {f : ℂ → ℂ}, Differentiable ℂ f →
      (∃ C : ℝ, ∀ z, ‖f z‖ ≤ C * (1 + ‖z‖)) → ∃ a b : ℂ, ∀ z, f z = a * z + b)
    (zerofree_exp : ∀ {f : ℂ → ℂ}, Differentiable ℂ f → (∀ z, f z ≠ 0) →
      ∃ g : ℂ → ℂ, Differentiable ℂ g ∧ ∀ z, f z = Complex.exp (g z))
    {Q : ℂ → ℂ} (hQ : Differentiable ℂ Q) (hne : ∀ z, Q z ≠ 0)
    (hgrow : ∃ C : ℝ, ∀ z, ‖Q z‖ ≤ Real.exp (C * (1 + ‖z‖))) :
    ∃ a b : ℂ, ∀ z, Q z = Complex.exp (a + b * z) := by
  -- Step 1: zero-free entire ⇒ Q = exp ∘ g for an entire g.
  obtain ⟨g, hg_diff, hg_eq⟩ := zerofree_exp hQ hne
  -- Step 2: extract the growth constant and turn the modulus bound into a real-part bound.
  obtain ⟨C, hC⟩ := hgrow
  -- A nonnegative version of the growth constant, used throughout.
  set C₀ : ℝ := max C 0 with hC₀def
  have hC₀nonneg : 0 ≤ C₀ := le_max_right _ _
  have hCC₀ : C ≤ C₀ := le_max_left _ _
  -- `Re (g w) ≤ C₀ * (1 + ‖w‖)` for every `w`.
  have hRe : ∀ w, (g w).re ≤ C₀ * (1 + ‖w‖) := by
    intro w
    have h1 : ‖Q w‖ = Real.exp (g w).re := by
      rw [hg_eq w, Complex.norm_exp]
    have h2 : Real.exp (g w).re ≤ Real.exp (C * (1 + ‖w‖)) := h1 ▸ hC w
    have h3 : (g w).re ≤ C * (1 + ‖w‖) := Real.exp_le_exp.mp h2
    refine h3.trans ?_
    have : (0:ℝ) ≤ 1 + ‖w‖ := by positivity
    nlinarith [this, hCC₀]
  -- Step 3: Borel–Carathéodory ⇒ a two-sided linear modulus bound on `g`.
  -- We prove `‖g z‖ ≤ C' * (1 + ‖z‖)` with `C' := 7 * C₀ + 4 * ‖g 0‖ + 1`.
  set C' : ℝ := 7 * C₀ + 4 * ‖g 0‖ + 2 with hC'def
  have hbound : ∀ z, ‖g z‖ ≤ C' * (1 + ‖z‖) := by
    intro z
    -- Choose radius `R := 2 * (1 + ‖z‖)` and bound `M := C₀ * (1 + R) + 1 > 0`.
    set R : ℝ := 2 * (1 + ‖z‖) with hRdef
    have hzn : 0 ≤ ‖z‖ := norm_nonneg z
    have hR0 : 0 < R := by rw [hRdef]; positivity
    have hzR : ‖z‖ < R := by rw [hRdef]; nlinarith [hzn]
    have hzmem : z ∈ Metric.ball (0 : ℂ) R := by
      rw [mem_ball_zero_iff]; exact hzR
    -- The sup of `Re g` on the ball is bounded by `M`.
    set M : ℝ := C₀ * (1 + R) + 1 with hMdef
    have hM0 : 0 < M := by
      rw [hMdef]
      have : 0 ≤ C₀ * (1 + R) := by positivity
      linarith
    -- `g` maps the ball into `{w | w.re ≤ M}`.
    have hmaps : Set.MapsTo g (Metric.ball (0 : ℂ) R) {w | w.re ≤ M} := by
      intro x hx
      simp only [Set.mem_setOf_eq]
      have hxR : ‖x‖ < R := mem_ball_zero_iff.mp hx
      have : (g x).re ≤ C₀ * (1 + ‖x‖) := hRe x
      refine this.trans ?_
      rw [hMdef]
      have hxRle : ‖x‖ ≤ R := hxR.le
      have hle : C₀ * (1 + ‖x‖) ≤ C₀ * (1 + R) := by gcongr
      linarith
    have hdiffOn : DifferentiableOn ℂ g (Metric.ball (0 : ℂ) R) :=
      hg_diff.differentiableOn
    -- Apply Borel–Carathéodory.
    have hBC := Complex.borelCaratheodory hM0 hdiffOn hmaps hR0 hzmem
    -- Now simplify the right-hand side.  We have `R - ‖z‖ = 2 + ‖z‖ ≥ 2`.
    have hRz : R - ‖z‖ = 2 + ‖z‖ := by rw [hRdef]; ring
    have hRzpos : 0 < R - ‖z‖ := by rw [hRz]; linarith
    -- Bound each of the two terms of the BC estimate.
    -- term1 = 2 * M * ‖z‖ / (R - ‖z‖) ;  term2 = ‖g 0‖ * (R + ‖z‖) / (R - ‖z‖).
    refine hBC.trans ?_
    -- We show: term1 + term2 ≤ C' * (1 + ‖z‖).
    -- First, `2*M = 2*C₀*(1+R) + 2 = 2*C₀*(3 + 2‖z‖) + 2 = 6*C₀ + 4*C₀*‖z‖ + 2`.
    have hM_eq : M = C₀ * (3 + 2 * ‖z‖) + 1 := by
      rw [hMdef, hRdef]; ring
    -- Bound term1 ≤ 2*M, since ‖z‖ / (2 + ‖z‖) ≤ 1.
    have hMnn : 0 ≤ M := le_of_lt hM0
    have hterm1 : 2 * M * ‖z‖ / (R - ‖z‖) ≤ 2 * M := by
      rw [hRz, div_le_iff₀ (by linarith : (0:ℝ) < 2 + ‖z‖)]
      nlinarith [hMnn, hzn]
    -- Bound term2 ≤ 3 * ‖g 0‖, since (2 + 3‖z‖) / (2 + ‖z‖) ≤ 3.
    have hg0 : 0 ≤ ‖g 0‖ := norm_nonneg _
    have hterm2 : ‖g 0‖ * (R + ‖z‖) / (R - ‖z‖) ≤ 3 * ‖g 0‖ := by
      have hRpz : R + ‖z‖ = 2 + 3 * ‖z‖ := by rw [hRdef]; ring
      rw [hRz, hRpz, div_le_iff₀ (by linarith : (0:ℝ) < 2 + ‖z‖)]
      nlinarith [hg0, hzn]
    -- Combine: term1 + term2 ≤ 2*M + 3*‖g 0‖.
    have hcomb : 2 * M * ‖z‖ / (R - ‖z‖) + ‖g 0‖ * (R + ‖z‖) / (R - ‖z‖)
        ≤ 2 * M + 3 * ‖g 0‖ := by
      linarith [hterm1, hterm2]
    refine hcomb.trans ?_
    -- Finally 2*M + 3*‖g0‖ ≤ C' * (1 + ‖z‖).
    -- 2*M = 6*C₀ + 4*C₀*‖z‖ + 2.
    rw [hM_eq, hC'def]
    nlinarith [hC₀nonneg, hzn, hg0, mul_nonneg hC₀nonneg hzn]
  -- Step 4: Liouville-type recognition ⇒ g is affine.
  obtain ⟨a, b, hab⟩ := liouville hg_diff ⟨C', hbound⟩
  -- Step 5: assemble.  Q z = exp (g z) = exp (a*z + b) = exp (b + a*z).
  refine ⟨b, a, ?_⟩
  intro z
  rw [hg_eq z, hab z, add_comm]

/-- Bonus corollary: the result has the `C · exp (a + b s)` shape with `C ≠ 0`. -/
theorem exp_affine_const_of_zerofree_order_one
    (liouville : ∀ {f : ℂ → ℂ}, Differentiable ℂ f →
      (∃ C : ℝ, ∀ z, ‖f z‖ ≤ C * (1 + ‖z‖)) → ∃ a b : ℂ, ∀ z, f z = a * z + b)
    (zerofree_exp : ∀ {f : ℂ → ℂ}, Differentiable ℂ f → (∀ z, f z ≠ 0) →
      ∃ g : ℂ → ℂ, Differentiable ℂ g ∧ ∀ z, f z = Complex.exp (g z))
    {Q : ℂ → ℂ} (hQ : Differentiable ℂ Q) (hne : ∀ z, Q z ≠ 0)
    (hgrow : ∃ C : ℝ, ∀ z, ‖Q z‖ ≤ Real.exp (C * (1 + ‖z‖))) :
    ∃ (C : ℂ) (a b : ℂ), C ≠ 0 ∧ ∀ z, Q z = C * Complex.exp (a + b * z) := by
  obtain ⟨a, b, hab⟩ :=
    exp_affine_of_zerofree_order_one liouville zerofree_exp hQ hne hgrow
  refine ⟨Complex.exp a, 0, b, Complex.exp_ne_zero a, ?_⟩
  intro z
  rw [hab z, zero_add, ← Complex.exp_add]

/-- **Unconditional Hadamard final step**: combines B42 with B40 (Liouville) and B41 (zero-free⇒exp). -/
theorem xi_exp_affine_of_zerofree_order_one
    {Q : ℂ → ℂ} (hQ : Differentiable ℂ Q) (hne : ∀ z, Q z ≠ 0)
    (hgrow : ∃ C : ℝ, ∀ z, ‖Q z‖ ≤ Real.exp (C * (1 + ‖z‖))) :
    ∃ a b : ℂ, ∀ z, Q z = Complex.exp (a + b * z) :=
  exp_affine_of_zerofree_order_one
    (fun {_f} hf hCg => affine_of_entire_of_linear_growth hf _ hCg.choose_spec)
    (fun {_f} hf hfne => exists_entire_exp_eq hf hfne)
    hQ hne hgrow


/-! ## Bridge 44 — divisor ⇒ cardinality (item-4 wiring: closes B33→B35 gap)
The number of ξ-zeros in a ball is ≤ the weighted divisor finsum (each zero has multiplicity ≥ 1).
Combined with B33's `∑ᶠ divisor ≤ A r log r` this bounds the actual zero count, feeding B35's
shell-card hypothesis ⇒ `Σ1/‖ρ‖² < ∞` for the real ξ. -/

open MeromorphicOn in
theorem natCard_zeros_le_finsum_divisor
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f Set.univ) (hf0 : ∃ z₀, f z₀ ≠ 0) {r : ℝ} (_hr : 0 ≤ r) :
    (Nat.card {z : ℂ // f z = 0 ∧ z ∈ Metric.closedBall (0:ℂ) r} : ℝ)
      ≤ ∑ᶠ u, MeromorphicOn.divisor f (Metric.closedBall (0:ℂ) r) u := by
  classical
  set K : Set ℂ := Metric.closedBall (0:ℂ) r with hK
  -- `f` is analytic on the ball, hence meromorphic there.
  have hfK : AnalyticOnNhd ℂ f K := hf.mono (Set.subset_univ _)
  have hmK : MeromorphicOn f K := hfK.meromorphicOn
  -- `f` has finite analytic order everywhere (it is not identically zero on the connected `univ`).
  obtain ⟨z₀, hz₀⟩ := hf0
  have horder : ∀ z : ℂ, analyticOrderAt f z ≠ ⊤ := by
    intro z
    have h₀ : analyticOrderAt f z₀ ≠ ⊤ := by
      rw [(hf z₀ (Set.mem_univ _)).analyticOrderAt_eq_zero.2 hz₀]
      exact (by simp : (0 : ℕ∞) ≠ ⊤)
    exact hf.analyticOrderAt_ne_top_of_isPreconnected isPreconnected_univ
      (Set.mem_univ z₀) (Set.mem_univ z) h₀
  -- The support of the divisor is finite (`K` is compact).
  have hKcompact : IsCompact K := isCompact_closedBall _ _
  have hSfin : (MeromorphicOn.divisor f K).support.Finite :=
    (MeromorphicOn.divisor f K).finiteSupport hKcompact
  set S : Finset ℂ := hSfin.toFinset with hSdef
  -- The divisor of an analytic function is everywhere nonnegative.
  have hnonneg : ∀ z : ℂ, 0 ≤ MeromorphicOn.divisor f K z := hfK.divisor_nonneg
  -- On `K`, the divisor is nonzero exactly at the zeros of `f`.
  have hdivne : ∀ z ∈ K, f z = 0 → MeromorphicOn.divisor f K z ≠ 0 := by
    intro z hz hfz
    rw [hfK.divisor_apply hz]
    have hne0 : analyticOrderAt f z ≠ 0 :=
      (hfK z hz).analyticOrderAt_ne_zero.2 hfz
    obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.1 (horder z)
    rw [← hn] at hne0 ⊢
    have hn1 : 1 ≤ n := by
      rcases Nat.eq_zero_or_pos n with h | h
      · rw [h] at hne0; exact absurd rfl hne0
      · exact h
    rw [Ne, WithTop.untop₀_eq_zero, not_or]
    refine ⟨?_, ?_⟩
    · rw [ENat.map_natCast_eq_zero]; exact hne0
    · exact ENat.map_coe (Nat.cast : ℕ → ℤ) n ▸ (by exact WithTop.coe_ne_top)
  -- Hence at each zero the divisor is `≥ 1`.
  have hpos : ∀ z ∈ K, f z = 0 → 1 ≤ MeromorphicOn.divisor f K z := by
    intro z hz hfz
    have h0 := hnonneg z
    have hne := hdivne z hz hfz
    omega
  -- Membership characterisation of the support.
  have hmem : ∀ z : ℂ, z ∈ S ↔ (f z = 0 ∧ z ∈ K) := by
    intro z
    rw [hSdef, Set.Finite.mem_toFinset, Function.mem_support]
    constructor
    · intro hz
      by_cases hzK : z ∈ K
      · refine ⟨?_, hzK⟩
        by_contra hfz
        have : analyticOrderAt f z = 0 := (hfK z hzK).analyticOrderAt_eq_zero.2 hfz
        apply hz
        rw [hfK.divisor_apply hzK, this]
        simp
      · exact absurd ((MeromorphicOn.divisor f K).apply_eq_zero_of_notMem hzK) hz
    · rintro ⟨hfz, hzK⟩
      have := hpos z hzK hfz
      omega
  -- The zero subtype has cardinality `S.card`.
  have hcard : Nat.card {z : ℂ // f z = 0 ∧ z ∈ K} = S.card := by
    have : {z : ℂ // f z = 0 ∧ z ∈ K} ≃ {z : ℂ // z ∈ S} := by
      apply Equiv.subtypeEquivRight
      intro z
      rw [hmem z]
    rw [Nat.card_congr this, Nat.card_eq_finsetCard]
  -- Rewrite the finsum as a finite sum over `S` (the support).
  have hfinsum : ∑ᶠ u, MeromorphicOn.divisor f K u = ∑ u ∈ S, MeromorphicOn.divisor f K u := by
    rw [finsum_eq_finsetSum_of_support_subset _ (s := S)]
    rw [hSdef, Set.Finite.coe_toFinset]
  -- Each term is `≥ 1`, so the sum dominates `S.card`.
  have hsum_ge : (S.card : ℤ) ≤ ∑ u ∈ S, MeromorphicOn.divisor f K u := by
    calc (S.card : ℤ) = ∑ _u ∈ S, (1 : ℤ) := by simp
      _ ≤ ∑ u ∈ S, MeromorphicOn.divisor f K u := by
          apply Finset.sum_le_sum
          intro u hu
          obtain ⟨hfu, huK⟩ := (hmem u).1 hu
          exact hpos u huK hfu
  -- Combine.
  rw [hcard]
  have : (∑ᶠ u, MeromorphicOn.divisor f K u : ℤ) = ∑ u ∈ S, MeromorphicOn.divisor f K u := hfinsum
  calc (S.card : ℝ) = ((S.card : ℤ) : ℝ) := by push_cast; ring
    _ ≤ ((∑ u ∈ S, MeromorphicOn.divisor f K u : ℤ) : ℝ) := by
        exact_mod_cast hsum_ge
    _ = ∑ᶠ u, MeromorphicOn.divisor f K u := by rw [← this]

end ScratchBridges

section Lambda0Strip
open Complex Filter Topology MeasureTheory Set Real
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
end Lambda0Strip

namespace ScratchBridges

/-! ## Bridge 45 — entire quotient with matching zero-orders (G5 structural core)
If two entire functions vanish to the same order at every point, their quotient extends to an
entire ZERO-FREE function. This makes `Q = ξ/∏` well-defined; with B42 (`xi_exp_affine`) it gives
the Hadamard factorization `ξ = ∏ · C·exp(a+bz)` once `Q` has order-1 growth. -/

/-- Structural heart of Hadamard factorization: if two entire functions vanish to the
same order at every point, their quotient extends to a zero-free entire function. -/
theorem entire_quotient_of_analyticOrderAt_eq
    {f P : ℂ → ℂ} (hf : Differentiable ℂ f) (hP : Differentiable ℂ P)
    (hP0 : ∃ z₀, P z₀ ≠ 0)
    (horder : ∀ z, analyticOrderAt f z = analyticOrderAt P z) :
    ∃ Q : ℂ → ℂ, Differentiable ℂ Q ∧ (∀ z, Q z ≠ 0) ∧ ∀ z, f z = P z * Q z := by
  -- Analyticity of `f` and `P` at every point.
  have hfa : ∀ z, AnalyticAt ℂ f z := hf.analyticAt
  have hPa : ∀ z, AnalyticAt ℂ P z := hP.analyticAt
  -- The quotient `f / P` is meromorphic at every point.
  have hmero : ∀ z, MeromorphicAt (f / P) z := fun z =>
    (hfa z).meromorphicAt.div (hPa z).meromorphicAt
  -- `P` is not identically zero, so it never vanishes to infinite order (identity principle).
  have hPonNhd : AnalyticOnNhd ℂ P Set.univ := fun z _ => hPa z
  have hPnotTop : ∀ z, analyticOrderAt P z ≠ ⊤ := by
    intro z htop
    obtain ⟨z₀, hz₀⟩ := hP0
    have hev : P =ᶠ[𝓝 z] 0 := analyticOrderAt_eq_top.mp htop
    have : Set.EqOn P 0 Set.univ :=
      hPonNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero
        isPreconnected_univ (Set.mem_univ z) hev
    exact hz₀ (this (Set.mem_univ z₀))
  -- Its meromorphic order is `0` everywhere (orders cancel by `horder`).
  have horder0 : ∀ z, meromorphicOrderAt (f / P) z = 0 := by
    intro z
    rw [meromorphicOrderAt_div (hfa z).meromorphicAt (hPa z).meromorphicAt,
      (hfa z).meromorphicOrderAt_eq, (hPa z).meromorphicOrderAt_eq, horder z]
    exact LinearOrderedAddCommGroupWithTop.sub_self_eq_zero_of_ne_top
      (by rw [Ne, ENat.map_eq_top_iff]; exact hPnotTop z)
  -- Define `Q` as the meromorphic normal form of `f / P` on the whole plane.
  set Q : ℂ → ℂ := toMeromorphicNFOn (f / P) Set.univ with hQdef
  have hmeroOn : MeromorphicOn (f / P) Set.univ := fun z _ => hmero z
  -- `Q` agrees with `f / P` outside a discrete set; in particular its order is `0`.
  have hQorder : ∀ z, meromorphicOrderAt Q z = 0 := by
    intro z
    rw [hQdef, meromorphicOrderAt_toMeromorphicNFOn hmeroOn (Set.mem_univ z), horder0 z]
  -- `Q` is in normal form at every point, hence (order `0 ≥ 0`) analytic everywhere.
  have hQnf : ∀ z, MeromorphicNFAt Q z := fun z =>
    meromorphicNFOn_toMeromorphicNFOn (f / P) Set.univ (Set.mem_univ z)
  have hQa : ∀ z, AnalyticAt ℂ Q z := by
    intro z
    exact (hQnf z).meromorphicOrderAt_nonneg_iff_analyticAt.mp (by rw [hQorder z])
  -- `Q` is differentiable everywhere.
  have hQdiff : Differentiable ℂ Q := fun z => (hQa z).differentiableAt
  -- `Q` is zero-free: analytic with meromorphic order `0` means nonzero value.
  have hQne : ∀ z, Q z ≠ 0 := by
    intro z
    have hAorder : analyticOrderAt Q z = 0 := by
      have hmap := (hQa z).meromorphicOrderAt_eq
      rw [hQorder z] at hmap
      -- `0 = (analyticOrderAt Q z).map (↑)`, so the analytic order is `0`.
      rw [eq_comm, ENat.map_natCast_eq_zero] at hmap
      exact hmap
    exact ((hQa z).analyticOrderAt_eq_zero).mp hAorder
  refine ⟨Q, hQdiff, hQne, ?_⟩
  -- Pointwise identity `f z = P z * Q z`.
  intro z
  by_cases hPz : P z = 0
  · -- At a zero of `P`: matching order forces `f z = 0`, and `P z * Q z = 0`.
    have hPorderne : analyticOrderAt P z ≠ 0 := (hPa z).analyticOrderAt_ne_zero.mpr hPz
    have hforderne : analyticOrderAt f z ≠ 0 := by rw [horder z]; exact hPorderne
    have hfz : f z = 0 := apply_eq_zero_of_analyticOrderAt_ne_zero hforderne
    rw [hfz, hPz, zero_mul]
  · -- Away from zeros of `P`: `Q =ᶠ f/P` on a punctured nbhd, so `P*Q =ᶠ f`; conclude by continuity.
    have hQeq : Q =ᶠ[𝓝[≠] z] (f / P) :=
      hmeroOn.toMeromorphicNFOn_eq_self_on_nhdsNE (Set.mem_univ z)
    -- `P ≠ 0` on a neighborhood of `z`.
    have hPne_nhds : ∀ᶠ w in 𝓝 z, P w ≠ 0 :=
      (hPa z).continuousAt.eventually_ne hPz
    -- On the punctured nbhd, `P w * Q w = f w`.
    have hkey : (fun w => P w * Q w) =ᶠ[𝓝[≠] z] f := by
      filter_upwards [hQeq, hPne_nhds.filter_mono nhdsWithin_le_nhds] with w hw hPw
      rw [hw, Pi.div_apply, mul_div_cancel₀ _ hPw]
    -- `fun w => P w * Q w` is continuous at `z`, so it tends to its value there along `𝓝[≠] z`.
    have hcontPQ : ContinuousAt (fun w => P w * Q w) z :=
      ((hPa z).continuousAt).mul ((hQa z).continuousAt)
    have htends_val : Tendsto (fun w => P w * Q w) (𝓝[≠] z) (𝓝 (P z * Q z)) :=
      hcontPQ.continuousWithinAt.tendsto
    -- It also tends to `f z` (eventual equality with `f`, which is continuous at `z`).
    have htends_f : Tendsto (fun w => P w * Q w) (𝓝[≠] z) (𝓝 (f z)) :=
      ((hfa z).continuousAt.continuousWithinAt.tendsto).congr' hkey.symm
    -- `𝓝[≠] z` is nontrivial in `ℂ`, so the two limits coincide.
    exact (tendsto_nhds_unique htends_val htends_f).symm

/-! ## Bridge 46/47 — UNCONDITIONAL global ξ growth + RvM count (strip now proven via Λ₀-Mellin)
The vertical-strip bound is now a THEOREM (`ScratchLambda0.norm_entireRiemannXi_le_exp_vertical_strip`,
proved Im-independently from the Mellin representation of Λ₀ — no ζ-critical-strip, no complex
Stirling). So B32/B33's strip hypothesis is discharged: the global order-1 growth and the
Riemann–von Mangoldt zero count `N(r)=O(r log r)` are now UNCONDITIONAL. -/

/-- **Unconditional global ξ growth**: `‖ξ z‖ ≤ exp(A‖z‖log‖z‖)` for all `‖z‖ ≥ 4`. -/
theorem exists_norm_entireRiemannXi_le_exp_global :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ z : ℂ, 4 ≤ ‖z‖ →
      ‖entireRiemannXi z‖ ≤ Real.exp (A * ‖z‖ * Real.log ‖z‖) := by
  obtain ⟨Bs, hBs0, hBs⟩ := ScratchLambda0.norm_entireRiemannXi_le_exp_vertical_strip
  refine ⟨max 40 Bs, le_trans hBs0 (le_max_right _ _), fun z hz => ?_⟩
  have hzlog : (0 : ℝ) ≤ ‖z‖ * Real.log ‖z‖ :=
    mul_nonneg (by linarith) (Real.log_nonneg (by linarith))
  by_cases hr : 4 ≤ z.re
  · refine (norm_entireRiemannXi_le_exp_right_half hr).trans (Real.exp_le_exp.mpr ?_)
    nlinarith [le_max_left (40 : ℝ) Bs, hzlog]
  · have hr' : z.re ≤ 4 := (not_le.mp hr).le
    by_cases hl : z.re ≤ -3
    · have hz1 : ‖1 - z‖ ≤ 2 * ‖z‖ := by
        have h := norm_sub_le (1 : ℂ) z; rw [norm_one] at h; linarith
      have hz1' : (1 : ℝ) ≤ ‖1 - z‖ := by
        have h := norm_sub_norm_le z (1 : ℂ); rw [norm_sub_rev, norm_one] at h; linarith
      have hlogz1 : Real.log ‖1 - z‖ ≤ 2 * Real.log ‖z‖ := by
        have h2 : Real.log ‖1 - z‖ ≤ Real.log (2 * ‖z‖) := Real.log_le_log (by linarith) hz1
        rw [Real.log_mul (by norm_num) (by linarith)] at h2
        have : Real.log 2 ≤ Real.log ‖z‖ := Real.log_le_log (by norm_num) (by linarith)
        linarith
      have hprod : ‖1 - z‖ * Real.log ‖1 - z‖ ≤ 2 * ‖z‖ * (2 * Real.log ‖z‖) :=
        mul_le_mul hz1 hlogz1 (Real.log_nonneg hz1') (by linarith)
      refine (norm_entireRiemannXi_le_exp_left_half hl).trans (Real.exp_le_exp.mpr ?_)
      nlinarith [hprod, le_max_left (40 : ℝ) Bs, hzlog]
    · have hmid : -3 ≤ z.re := (not_le.mp hl).le
      have hstrip := hBs z hmid hr' hz
      have heq : ScratchLambda0.entireRiemannXi z = entireRiemannXi z := rfl
      rw [heq] at hstrip
      refine hstrip.trans (Real.exp_le_exp.mpr ?_)
      nlinarith [le_max_right (40 : ℝ) Bs, hzlog]

open MeromorphicOn in
/-- **Unconditional Riemann–von Mangoldt zero count** `N(r) = O(r log r)` for the real ξ. -/
theorem xi_zero_count_bigO :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ r : ℝ, 2 ≤ r →
      ∑ᶠ u, divisor entireRiemannXi (Metric.closedBall (0 : ℂ) r) u
        ≤ A * (Real.exp 1 * r) * Real.log (Real.exp 1 * r) - Real.log ‖entireRiemannXi 0‖ := by
  obtain ⟨A, hA0, hA⟩ := exists_norm_entireRiemannXi_le_exp_global
  refine ⟨A, hA0, fun r hr => ?_⟩
  refine xi_zero_count_le_of_growth (by linarith : (1 : ℝ) ≤ r) hA0 (fun z hz => ?_)
  rw [Metric.mem_sphere, dist_zero_right] at hz
  have he2 : (2 : ℝ) ≤ Real.exp 1 := by have := Real.add_one_le_exp (1 : ℝ); linarith
  have hge4 : (4 : ℝ) ≤ ‖z‖ := by rw [hz]; nlinarith [he2, hr]
  have hb := hA z hge4
  rwa [hz] at hb


/-! ## Bridge 48 — ball-count ⇒ Σ1/‖ρ‖² (G3 engine; abstract, hlb-free variant for ξ)
`summable_inv_sq_of_ballCount'` drops the `‖loc i‖≥1` assumption (small-modulus points are finite),
so it applies directly to ξ's zeros. Built on B35 `summable_inv_sq_of_shellCard`. -/

/-- Ball-count ⇒ inverse-square summability: the abstract G3 engine. -/
theorem summable_inv_sq_of_ballCount
    {ι : Type*} (loc : ι → ℂ) (A : ℝ) (_hA : 0 ≤ A)
    (hlb : ∀ i, (1 : ℝ) ≤ ‖loc i‖)
    (hfin : ∀ R : ℝ, {i | ‖loc i‖ ≤ R}.Finite)
    (hcount : ∀ R : ℝ, 2 ≤ R → (Nat.card {i | ‖loc i‖ ≤ R} : ℝ) ≤ A * R * Real.log R) :
    Summable (fun i => 1 / ‖loc i‖ ^ 2) := by
  -- Apply the dyadic-shell engine with C := 2 * A * Real.log 2.
  apply summable_inv_sq_of_shellCard loc (2 * A * Real.log 2) hlb
  · -- hfin (shell): {‖loc i‖ < 2^(k+1)} ⊆ {‖loc i‖ ≤ 2^(k+1)} which is finite.
    intro k
    apply Set.Finite.subset (hfin ((2:ℝ) ^ (k+1)))
    intro i hi
    simp only [Set.mem_setOf_eq] at hi ⊢
    exact le_of_lt hi
  · -- hcard: shell k ⊆ ball 2^(k+1), and count bound gives ≤ C*(k+1)*2^k.
    intro k
    -- R := 2^(k+1)
    set R : ℝ := (2:ℝ) ^ (k+1) with hR
    have hR2 : (2:ℝ) ≤ R := by
      rw [hR]
      calc (2:ℝ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (k+1) := by
              apply pow_le_pow_right₀ (by norm_num)
              omega
    -- shell ⊆ ball R
    have hsub : {i | (2:ℝ) ^ k ≤ ‖loc i‖ ∧ ‖loc i‖ < 2 ^ (k+1)} ⊆ {i | ‖loc i‖ ≤ R} := by
      intro i hi
      simp only [Set.mem_setOf_eq] at hi ⊢
      rw [hR]
      exact le_of_lt hi.2
    -- ball R is finite
    have hballfin : {i | ‖loc i‖ ≤ R}.Finite := hfin R
    -- Nat.card shell ≤ Nat.card ball
    have hcardmono : Nat.card {i | (2:ℝ) ^ k ≤ ‖loc i‖ ∧ ‖loc i‖ < 2 ^ (k+1)}
        ≤ Nat.card {i | ‖loc i‖ ≤ R} := Nat.card_mono hballfin hsub
    -- count bound for ball R
    have hcountR : (Nat.card {i | ‖loc i‖ ≤ R} : ℝ) ≤ A * R * Real.log R := hcount R hR2
    -- log R = (k+1) * log 2
    have hlogR : Real.log R = ((k:ℝ)+1) * Real.log 2 := by
      rw [hR, Real.log_pow]; push_cast; ring
    -- chain: card shell ≤ A*R*log R = A*2^(k+1)*(k+1)*log2 = (2*A*log2)*(k+1)*2^k
    have hchain : (Nat.card {i | (2:ℝ) ^ k ≤ ‖loc i‖ ∧ ‖loc i‖ < 2 ^ (k+1)} : ℝ)
        ≤ A * R * Real.log R := by
      refine le_trans ?_ hcountR
      exact_mod_cast hcardmono
    refine le_trans hchain (le_of_eq ?_)
    -- A * R * log R = (2*A*log2)*(k+1)*2^k
    rw [hlogR, hR]
    have hpow : (2:ℝ) ^ (k+1) = 2 ^ k * 2 := by rw [pow_succ]
    rw [hpow]
    ring

/-- Ball-count ⇒ inverse-square summability, WITHOUT the `1 ≤ ‖loc i‖` hypothesis.
Replaces it with `loc i ≠ 0` (so each summand is finite); the small-modulus points
`{i | ‖loc i‖ ≤ 1}` are finite, so summability is unaffected by them. -/
theorem summable_inv_sq_of_ballCount'
    {ι : Type*} (loc : ι → ℂ) (A : ℝ)
    (_hne : ∀ i, loc i ≠ 0)
    (hfin : ∀ R : ℝ, {i | ‖loc i‖ ≤ R}.Finite)
    (hcount : ∀ R : ℝ, 2 ≤ R → (Nat.card {i | ‖loc i‖ ≤ R} : ℝ) ≤ A * R * Real.log R) :
    Summable (fun i => 1 / ‖loc i‖ ^ 2) := by
  classical
  -- The small-modulus index set is finite.
  set S : Set ι := {i | ‖loc i‖ ≤ 1} with hS
  have hSfin : S.Finite := hfin 1
  -- Summability is unaffected by the finite set S: reduce to the complement subtype.
  rw [← hSfin.summable_compl_iff (f := fun i => 1 / ‖loc i‖ ^ 2)]
  -- `0 ≤ A` is forced by the count bound at R = 2 (the count is nonneg, log 2 > 0).
  have hA : 0 ≤ A := by
    have h2 := hcount 2 (le_refl 2)
    have hnn : (0:ℝ) ≤ (Nat.card {i | ‖loc i‖ ≤ (2:ℝ)} : ℝ) := by positivity
    have hle : (0:ℝ) ≤ A * 2 * Real.log 2 := le_trans hnn h2
    have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    nlinarith [hle, hlog2]
  -- On Sᶜ, restrict and apply the `1 ≤ ‖loc i‖` engine to `loc ∘ Subtype.val`.
  -- The summand `(fun i => 1/‖loc i‖^2) ∘ Subtype.val` equals
  -- `fun j => 1 / ‖loc ↑j‖ ^ 2` for j : ↥Sᶜ.
  apply summable_inv_sq_of_ballCount (fun j : (Sᶜ : Set ι) => loc (j : ι)) A hA
  · -- hlb on the complement: 1 ≤ ‖loc ↑j‖ since j ∉ S means ¬(‖loc ↑j‖ ≤ 1).
    intro j
    have hj : (j : ι) ∉ S := j.2
    simp only [hS, Set.mem_setOf_eq, not_le] at hj
    exact le_of_lt hj
  · -- hfin on the complement subtype.
    intro R
    -- inclusion of the subtype set into the ball, transported through Subtype.val.
    have : {j : (Sᶜ : Set ι) | ‖loc (j : ι)‖ ≤ R}
        = (Subtype.val : (Sᶜ : Set ι) → ι) ⁻¹' {i | ‖loc i‖ ≤ R} := by
      ext j; simp
    rw [this]
    apply Set.Finite.preimage _ (hfin R)
    exact (Subtype.val_injective).injOn
  · -- hcount on the complement subtype: card ≤ card of full ball.
    intro R hR
    refine le_trans ?_ (hcount R hR)
    -- Nat.card {j : ↥Sᶜ | ‖loc ↑j‖ ≤ R} ≤ Nat.card {i | ‖loc i‖ ≤ R}
    have hcardle : Nat.card {j : (Sᶜ : Set ι) | ‖loc (j : ι)‖ ≤ R}
        ≤ Nat.card {i | ‖loc i‖ ≤ R} := by
      -- image of the subtype set under Subtype.val sits inside the ball
      have himg : (Subtype.val : (Sᶜ : Set ι) → ι) '' {j | ‖loc (j : ι)‖ ≤ R}
          ⊆ {i | ‖loc i‖ ≤ R} := by
        rintro i ⟨j, hj, rfl⟩
        exact hj
      have hcard_img : Nat.card ((Subtype.val : (Sᶜ : Set ι) → ι) '' {j | ‖loc (j : ι)‖ ≤ R})
          = Nat.card {j : (Sᶜ : Set ι) | ‖loc (j : ι)‖ ≤ R} :=
        Nat.card_image_of_injective Subtype.val_injective _
      rw [← hcard_img]
      exact Nat.card_mono (hfin R) himg
    exact_mod_cast hcardle


/-! ## Bridge 49 — genus-1 product zero ORDERS (G5 multiplicity matching)
Per-factor order (simple zero at ρ, 0 elsewhere); finite-product order = sum of orders; and the
loc-unif product order = hitting-index count, CONDITIONAL on the factorization `hsplit` (finite
hitting factors × analytic nonvanishing tail) — the one piece Mathlib lacks an order-of-product
lemma for. With B45 this gives `Q=ξ/∏` entire once ξ's and ∏'s orders match. -/
/-! ## PART 1 (tractable): the order of a single genus-1 factor.
`genus1Factor ρ` is entire, vanishes only at `ρ`, to order exactly 1. -/

/-- `genus1Factor ρ` is analytic everywhere. -/
theorem analyticAt_genus1Factor (ρ : ℂ) (z : ℂ) : AnalyticAt ℂ (genus1Factor ρ) z := by
  unfold genus1Factor
  fun_prop

/-- The cofactor `g s = -(1/ρ) * exp (s/ρ)` extracted from `genus1Factor ρ`, so that
`genus1Factor ρ s = (s - ρ) ^ 1 • g s`. -/
theorem analyticOrderAt_genus1Factor_self {ρ : ℂ} (hρ : ρ ≠ 0) :
    analyticOrderAt (genus1Factor ρ) ρ = 1 := by
  rw [show (1 : ℕ∞) = ((1 : ℕ) : ℕ∞) from rfl,
    (analyticAt_genus1Factor ρ ρ).analyticOrderAt_eq_natCast]
  refine ⟨fun s => -(1 / ρ) * Complex.exp (s / ρ), by fun_prop, ?_, ?_⟩
  · exact mul_ne_zero (neg_ne_zero.mpr (div_ne_zero one_ne_zero hρ)) (Complex.exp_ne_zero _)
  · filter_upwards with s
    unfold genus1Factor
    rw [pow_one, smul_eq_mul]
    field_simp
    ring

theorem analyticOrderAt_genus1Factor_ne {ρ z : ℂ} (hρ : ρ ≠ 0) (hz : z ≠ ρ) :
    analyticOrderAt (genus1Factor ρ) z = 0 := by
  rw [(analyticAt_genus1Factor ρ z).analyticOrderAt_eq_zero]
  unfold genus1Factor
  refine mul_ne_zero ?_ (Complex.exp_ne_zero _)
  rw [sub_ne_zero, ne_comm, ne_eq, div_eq_one_iff_eq hρ]
  exact hz

/-! ## PART 2 (the hard one): order of the infinite product = sum of factor orders.
Investigate Mathlib for `analyticOrderAt` of a locally-uniform `tprod`. The order of a
locally-uniformly-convergent product at `z` should equal the (finite) sum of the factor orders
at `z` — because only finitely many factors vanish at `z` (the locations are discrete), and the
tail product is analytic and nonzero near `z`.

Target (state precisely; you MAY add hypotheses — discreteness of `loc`, `loc i ≠ 0`, the
loc-uniform multipliability, and `Summable (1/‖loc i‖²)` — whatever the proof needs): -/

/-- Order of a finite product of analytic functions is the sum of the orders. -/
theorem analyticOrderAt_finsetProd {ι : Type*} (s : Finset ι) (F : ι → ℂ → ℂ) (z : ℂ)
    (hF : ∀ i ∈ s, AnalyticAt ℂ (F i) z) :
    analyticOrderAt (fun w => ∏ i ∈ s, F i w) z = ∑ i ∈ s, analyticOrderAt (F i) z := by
  classical
  induction s using Finset.induction with
  | empty =>
    simp only [Finset.prod_empty, Finset.sum_empty]
    rw [analyticOrderAt_eq_zero]; right; simp
  | insert a s ha ih =>
    simp only [Finset.prod_insert ha, Finset.sum_insert ha]
    have hAa : AnalyticAt ℂ (F a) z := hF a (Finset.mem_insert_self a s)
    have hArest : AnalyticAt ℂ (fun w => ∏ i ∈ s, F i w) z := by
      have := Finset.analyticAt_prod (𝕜 := ℂ) (f := F) s
        (fun i hi => hF i (Finset.mem_insert_of_mem hi))
      rw [Finset.prod_fn] at this; exact this
    have key : analyticOrderAt (fun w => F a w * ∏ i ∈ s, F i w) z
        = analyticOrderAt (F a) z + analyticOrderAt (fun w => ∏ i ∈ s, F i w) z := by
      have := analyticOrderAt_mul (f := F a) (g := fun w => ∏ i ∈ s, F i w) hAa hArest
      simpa [Pi.mul_def] using this
    rw [key, ih (fun i hi => hF i (Finset.mem_insert_of_mem hi))]

/-!
The order of the locally-uniform genus-1 product at `z` equals the number of indices hitting `z`.

We isolate the genuinely-missing analytic-number-theory input as the hypothesis `hsplit`: near
`z`, the full product factors as the FINITE product over the indices that hit `z` times an
analytic, nonvanishing TAIL. This is exactly the content of "order of a locally-uniform product"
that Mathlib does not yet provide as a lemma (Mathlib has no `analyticOrderAt` lemma for a
`tprod` / `MultipliableLocallyUniformlyOn` product). The standard proof of `hsplit` splits the
product into the finite hitting factors times the complement tail
(`Multipliable.prod_mul_tprod_subtype_compl`, available pointwise from `hmul.multipliable`) and
shows the tail is analytic (locally-uniform limit of analytic partial products) and nonvanishing
at `z` (each tail factor is nonzero there and the product is a genuine ξ-type Hadamard product).
Everything ELSE — that this factorization forces the order to be the hitting count — is proved
here unconditionally.
-/
theorem analyticOrderAt_genus1Product
    {ι : Type*} (loc : ι → ℂ) (z : ℂ)
    (hne : ∀ i, loc i ≠ 0)
    -- `z` is hit by only finitely many indices (from discreteness of the zero set):
    (hfin : {i | loc i = z}.Finite)
    -- The full product factors near `z` as (finite hitting product) · (analytic nonvanishing tail).
    -- This is the precise locally-uniform-product factorization Mathlib lacks an order lemma for.
    (tail : ℂ → ℂ)
    (htail_an : AnalyticAt ℂ tail z)
    (htail_ne : tail z ≠ 0)
    (hsplit : ∀ᶠ s in nhds z,
      (∏' i, genus1Factor (loc i) s) = (∏ i ∈ hfin.toFinset, genus1Factor (loc i) s) * tail s) :
    analyticOrderAt (fun s => ∏' i, genus1Factor (loc i) s) z
      = (Nat.card {i | loc i = z} : ℕ∞) := by
  classical
  set F : ι → ℂ → ℂ := fun i s => genus1Factor (loc i) s with hFdef
  set Hfin : Finset ι := hfin.toFinset with hHfindef
  -- order of the product = order of (finite hitting product · tail), by the local factorization
  have horder : analyticOrderAt (fun s => ∏' i, F i s) z
      = analyticOrderAt (fun s => (∏ i ∈ Hfin, F i s) * tail s) z :=
    analyticOrderAt_congr hsplit
  rw [horder]
  have hAfin : AnalyticAt ℂ (fun s => ∏ i ∈ Hfin, F i s) z := by
    have := Finset.analyticAt_prod (𝕜 := ℂ) (f := F) Hfin
      (fun i _ => analyticAt_genus1Factor (loc i) z)
    rw [Finset.prod_fn] at this; exact this
  have hmul_eq : analyticOrderAt (fun s => (∏ i ∈ Hfin, F i s) * tail s) z
      = analyticOrderAt (fun s => ∏ i ∈ Hfin, F i s) z + analyticOrderAt tail z := by
    have := analyticOrderAt_mul (f := fun s => ∏ i ∈ Hfin, F i s) (g := tail) hAfin htail_an
    simpa [Pi.mul_def] using this
  rw [hmul_eq]
  -- tail order is 0 (nonvanishing at z)
  have htail0 : analyticOrderAt tail z = 0 := by
    rw [htail_an.analyticOrderAt_eq_zero]; exact htail_ne
  rw [htail0, add_zero]
  -- finite product order = sum of (order-1) factors = card
  rw [analyticOrderAt_finsetProd Hfin F z (fun i _ => analyticAt_genus1Factor (loc i) z)]
  have hmemz : ∀ i ∈ Hfin, loc i = z := fun i hi => (hfin.mem_toFinset.mp hi)
  have hsum : ∑ i ∈ Hfin, analyticOrderAt (F i) z = ∑ _i ∈ Hfin, (1 : ℕ∞) := by
    apply Finset.sum_congr rfl
    intro i hi
    have hlocz : loc i = z := hmemz i hi
    change analyticOrderAt (genus1Factor (loc i)) z = 1
    rw [hlocz]
    exact analyticOrderAt_genus1Factor_self (hlocz ▸ hne i)
  rw [hsum]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
  -- card of the finite set = card of the finset
  rw [Nat.card_eq_card_finite_toFinset hfin]

/-! ## Bridge 50 — G3 CLOSED: `Σ_ρ 1/‖ρ‖² < ∞`, and UNCONDITIONAL genus-1 product convergence
Wires the unconditional RvM count (B47) through B44 + B21 into the abstract engine (B48'). Then
the genus-1 Hadamard product over ξ's zeros converges locally uniformly — UNCONDITIONALLY. -/

/-- **ξ inverse-square zero summability** (G3). -/
theorem xi_zero_invSq_summable :
    Summable (fun ρ : XiZeroIndex => 1 / ‖xiZeroLoc ρ‖ ^ 2) := by
  -- Extract the growth constant `A` from the unconditional zero count.
  obtain ⟨A, hA0, hA⟩ := xi_zero_count_bigO
  -- Final dominating constant.
  set C : ℝ :=
    A * Real.exp 1 / Real.log 2 + A * Real.exp 1
      + |Real.log ‖entireRiemannXi 0‖| / Real.log 2 + 1 with hC
  -- Map a small-norm zero index into the compact-intersection finite set.
  -- (`closedBall 0 R ∩ riemannXiZeros`).
  have hfin : ∀ R : ℝ, {ρ : XiZeroIndex | ‖xiZeroLoc ρ‖ ≤ R}.Finite := by
    intro R
    -- The finite set we inject into.
    have hcpt : (Metric.closedBall (0 : ℂ) R ∩ riemannXiZeros).Finite :=
      isCompact_inter_riemannXiZeros_finite (isCompact_closedBall 0 R)
    -- The image of our set under `Subtype.val` lands in that finite set.
    apply Set.Finite.of_finite_image (f := (Subtype.val : XiZeroIndex → ℂ))
    · apply hcpt.subset
      rintro z ⟨ρ, hρ, rfl⟩
      refine ⟨?_, ?_⟩
      · -- z = ↑ρ ∈ closedBall 0 R
        simp only [Metric.mem_closedBall, dist_zero_right]
        simpa [xiZeroLoc] using hρ
      · exact ρ.2
    · -- `Subtype.val` is injective, hence injective on any set.
      exact Subtype.val_injective.injOn
  -- The counting bound.
  have hcount : ∀ R : ℝ, 2 ≤ R →
      (Nat.card {ρ : XiZeroIndex | ‖xiZeroLoc ρ‖ ≤ R} : ℝ) ≤ C * R * Real.log R := by
    intro R hR
    -- Target subtype of zeros in the ball; it is finite.
    have hballfin : (Metric.closedBall (0 : ℂ) R ∩ riemannXiZeros).Finite :=
      isCompact_inter_riemannXiZeros_finite (isCompact_closedBall 0 R)
    have : Finite {z : ℂ // entireRiemannXi z = 0 ∧ z ∈ Metric.closedBall (0 : ℂ) R} := by
      have hsub : {z : ℂ | entireRiemannXi z = 0 ∧ z ∈ Metric.closedBall (0 : ℂ) R}
          ⊆ Metric.closedBall (0 : ℂ) R ∩ riemannXiZeros := by
        rintro z ⟨hz0, hzb⟩
        exact ⟨hzb, by simpa [riemannXiZeros] using hz0⟩
      exact (hballfin.subset hsub).to_subtype
    -- Inject small-norm indices into the ball-zero subtype.
    have hcard_le :
        Nat.card {ρ : XiZeroIndex | ‖xiZeroLoc ρ‖ ≤ R}
          ≤ Nat.card {z : ℂ // entireRiemannXi z = 0 ∧ z ∈ Metric.closedBall (0 : ℂ) R} := by
      refine Nat.card_le_card_of_injective
        (fun ρ => ⟨(ρ.1 : ℂ), ?_, ?_⟩) ?_
      · -- ξ (↑ρ) = 0
        exact (mem_riemannXiZeros).1 ρ.1.2
      · -- ↑ρ ∈ closedBall 0 R
        have hρ2 : ‖xiZeroLoc ρ.1‖ ≤ R := ρ.2
        simp only [Metric.mem_closedBall, dist_zero_right]
        simpa [xiZeroLoc] using hρ2
      · -- injectivity
        rintro ⟨⟨ρ, hρmem⟩, hρ⟩ ⟨⟨σ, hσmem⟩, hσ⟩ h
        simp only [Subtype.mk.injEq] at h
        exact Subtype.ext (Subtype.ext h)
    -- Cast to ℝ and chain through divisor / RvM bounds.
    have hcard_leR :
        (Nat.card {ρ : XiZeroIndex | ‖xiZeroLoc ρ‖ ≤ R} : ℝ)
          ≤ (Nat.card {z : ℂ // entireRiemannXi z = 0 ∧ z ∈ Metric.closedBall (0 : ℂ) R} : ℝ) := by
      exact_mod_cast hcard_le
    have hdiv :
        (Nat.card {z : ℂ // entireRiemannXi z = 0 ∧ z ∈ Metric.closedBall (0 : ℂ) R} : ℝ)
          ≤ ∑ᶠ u, MeromorphicOn.divisor entireRiemannXi (Metric.closedBall (0 : ℂ) R) u :=
      natCard_zeros_le_finsum_divisor analyticOnNhd_entireRiemannXi
        ⟨0, entireRiemannXi_zero_ne⟩ (by linarith)
    have hrvm := hA R hR
    -- Now the arithmetic: A·(eR)·log(eR) − log‖ξ0‖ ≤ C·R·log R.
    have hlog : Real.log (Real.exp 1 * R) = 1 + Real.log R := by
      rw [Real.log_mul (Real.exp_pos 1).ne' (by linarith), Real.log_exp]
    have hRpos : (0 : ℝ) < R := by linarith
    have hlog2pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    have hlogR : Real.log 2 ≤ Real.log R := Real.log_le_log (by norm_num) hR
    have hlogRpos : (0 : ℝ) < Real.log R := lt_of_lt_of_le hlog2pos hlogR
    have hRlogR : Real.log 2 ≤ R * Real.log R := by
      have : (1 : ℝ) * Real.log 2 ≤ R * Real.log R :=
        mul_le_mul (by linarith) hlogR hlog2pos.le hRpos.le
      linarith
    have hexp1pos : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
    -- `-log‖ξ0‖ ≤ |log‖ξ0‖|`
    have hcabs : -Real.log ‖entireRiemannXi 0‖ ≤ |Real.log ‖entireRiemannXi 0‖| :=
      neg_le_abs _
    -- `A·e·R ≤ (A·e/log2)·R·logR`  (since logR ≥ log2 > 0)
    have hterm1 : A * Real.exp 1 * R ≤ (A * Real.exp 1 / Real.log 2) * R * Real.log R := by
      have key : (A * Real.exp 1 / Real.log 2) * R * Real.log R
          = (A * Real.exp 1 * R) * (Real.log R / Real.log 2) := by
        field_simp
      rw [key]
      have hge1 : (1 : ℝ) ≤ Real.log R / Real.log 2 := by
        rw [le_div_iff₀ hlog2pos]; linarith
      nlinarith [hge1, mul_nonneg (mul_nonneg hA0 hexp1pos.le) hRpos.le]
    -- `|log‖ξ0‖| ≤ (|log‖ξ0‖|/log2)·R·logR`  (since R·logR ≥ log2)
    have hterm2 : |Real.log ‖entireRiemannXi 0‖|
        ≤ (|Real.log ‖entireRiemannXi 0‖| / Real.log 2) * R * Real.log R := by
      have key : (|Real.log ‖entireRiemannXi 0‖| / Real.log 2) * R * Real.log R
          = |Real.log ‖entireRiemannXi 0‖| * (R * Real.log R / Real.log 2) := by
        field_simp
      rw [key]
      have hge1 : (1 : ℝ) ≤ R * Real.log R / Real.log 2 := by
        rw [le_div_iff₀ hlog2pos]; linarith
      nlinarith [hge1, abs_nonneg (Real.log ‖entireRiemannXi 0‖)]
    -- Assemble.
    calc
      (Nat.card {ρ : XiZeroIndex | ‖xiZeroLoc ρ‖ ≤ R} : ℝ)
          ≤ A * (Real.exp 1 * R) * Real.log (Real.exp 1 * R)
              - Real.log ‖entireRiemannXi 0‖ :=
            le_trans hcard_leR (le_trans hdiv hrvm)
      _ = A * Real.exp 1 * R * (1 + Real.log R) - Real.log ‖entireRiemannXi 0‖ := by
            rw [hlog]; ring
      _ ≤ C * R * Real.log R := by
            rw [hC]
            have hRlogRnn : 0 ≤ R * Real.log R := by positivity
            nlinarith [hterm1, hterm2, hcabs, hRlogRnn]
  exact summable_inv_sq_of_ballCount' xiZeroLoc C xiZeroLoc_ne_zero hfin hcount

/-- **Unconditional** local-uniform convergence of the genus-1 Hadamard product over ξ's zeros. -/
theorem xi_genus1Product_LU :
    MultipliableLocallyUniformlyOn (fun ρ s => genus1Factor (xiZeroLoc ρ) s) Set.univ :=
  xi_genus1Product_multipliableLocallyUniformlyOn xi_zero_invSq_summable

end ScratchBridges


-- G3 deliverable: confirm the inverse-square zero summability is axiom-clean.
-- The statement takes NO hypotheses (the residual is fully discharged): the chain
--   xi_zero_invSq_summable
--     ← xi_zero_count_bigO              (unconditional N(R)=O(R log R), via Λ₀-Mellin strip)
--     ← summable_inv_sq_of_ballCount'   (B48 ball-count engine)
--        ← summable_inv_sq_of_ballCount ← summable_inv_sq_of_shellCard (B35 dyadic shells)
--     ← natCard_zeros_le_finsum_divisor (B44 divisor ⇒ cardinality)
-- is therefore UNCONDITIONAL.
#check @ScratchBridges.xi_zero_invSq_summable
#print axioms ScratchBridges.xi_zero_invSq_summable
#print axioms ScratchBridges.xi_genus1Product_LU

end OverflowResidueRH.BacklundTuring.ScratchG3Close