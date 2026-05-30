import Mathlib

open Complex Metric

/-- The **Hadamard final step**: a zero-free entire function of order ≤ 1 (growth
`‖Q z‖ ≤ exp (C (1 + ‖z‖))`) equals `exp (a + b z)` for constants `a, b`.

The two standard building blocks (Liouville-type polynomial recognition for
sub-linear growth, and the existence of an entire logarithm for a zero-free entire
function) are taken as explicit hypothesis parameters. -/
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
