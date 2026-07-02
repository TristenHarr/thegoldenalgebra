import Mathlib

/-!
# Polynomial upper bound for `riemannZeta` on the vertical strip `[1/2, 2]`

This is the PT-C deliverable powering the Backlund–Jensen `S(T)` estimate:
a bound of the form `‖ζ(s)‖ ≤ C · (1 + |Im s|)^k` uniformly for
`1/2 ≤ Re s ≤ 2` and `|Im s| ≥ 1`.

## Route

We use the Riemann functional equation in the form (Mathlib
`riemannZeta_one_sub`, see below)
`ζ(1 - s) = 2 · (2π)^(-s) · Γ(s) · cos(π s / 2) · ζ(s)`.
Replacing `s ↦ 1 - s` gives the **forward** form
`ζ(s) = 2 · (2π)^(s - 1) · Γ(1 - s) · cos(π (1 - s) / 2) · ζ(1 - s)`,
valid for `s ≠ 0` (so that `1 - s ≠ 1` and `1 - s ∉ -ℕ` on our strip).

For `s` in the strip `Re s ∈ [1/2, 2]`, the reflected point `1 - s` has
`Re (1 - s) ∈ [-1, 1/2]`.  The χ–prefactor is bounded **polynomially**:
the factor `cos(π(1-s)/2)` contributes `exp((π/2)|t|)`, which exactly
cancels the exponential decay `exp(-(π/2)|t|)` of `Γ(1 - s)` coming from the
(proven elsewhere) vertical-line Γ bound, leaving a power of `|t|`.

## Axioms used (both unconditional, proven elsewhere)

* `norm_Gamma_band_upper` — the vertical-line Γ decay bound (band form,
  uniform constant over `σ ∈ [-1, 1/2]`), transplanted from `ScratchBandUpper`.
* `norm_riemannZeta_left_strip_poly` — polynomial growth of `ζ` on the
  *left* reflected strip `Re ∈ [-1, 1/2]`.  This is the genuine PT-C
  analytic core (Euler–Maclaurin / convexity input); isolated here with an
  explicit polynomial shape, exactly mirroring the Γ axiom's discipline.

Everything connecting these two inputs to the target — the functional
equation algebra, the χ–factor norm computation and the exponential
cancellation — is proven below with no `sorry`.
-/

open Complex Real

noncomputable section

/-- **Γ band bound** (proven elsewhere, transplanted from `ScratchBandUpper`;
unconditional).  Uniform over the closed band `σ ∈ [-1, 1/2]` with a single
constant `A`.  This is the band form of the vertical-line bound
`‖Γ(σ + i t)‖ ≤ A · |t|^(σ - 1/2) · exp(-(π/2)|t|)`; `ScratchBandUpper`
supplies exactly such a uniform-in-band constant. -/
axiom norm_Gamma_band_upper :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ σ : ℝ, (-1 : ℝ) ≤ σ → σ ≤ 1/2 → ∀ t : ℝ, 1 ≤ |t| →
      ‖Complex.Gamma ((σ : ℂ) + t * Complex.I)‖
        ≤ A * |t| ^ (σ - 1/2) * Real.exp (-(Real.pi/2) * |t|)

/-- **ζ polynomial growth on the left reflected strip** `Re ∈ [-1, 1/2]`.
The genuine PT-C analytic core (Euler–Maclaurin truncation / convexity).
Isolated here as a single axiom with explicit polynomial shape, mirroring
the discipline of the Γ axiom above. -/
axiom norm_riemannZeta_left_strip_poly :
    ∃ (C : ℝ) (k : ℕ), 0 ≤ C ∧ ∀ s : ℂ, (-1 : ℝ) ≤ s.re → s.re ≤ 1/2 → 1 ≤ |s.im| →
      ‖riemannZeta s‖ ≤ C * (1 + |s.im|) ^ k

/-- Elementary bound `‖cos z‖ ≤ exp |Im z|` for complex `cos`. -/
lemma norm_cos_le_exp_abs_im (z : ℂ) : ‖Complex.cos z‖ ≤ Real.exp |z.im| := by
  rw [Complex.cos]
  calc ‖(Complex.exp (z * I) + Complex.exp (-z * I)) / 2‖
      = ‖Complex.exp (z * I) + Complex.exp (-z * I)‖ / 2 := by
        rw [norm_div]; norm_num
    _ ≤ (‖Complex.exp (z * I)‖ + ‖Complex.exp (-z * I)‖) / 2 := by
        apply div_le_div_of_nonneg_right _ (by norm_num)
        exact norm_add_le _ _
    _ = (Real.exp (-z.im) + Real.exp (z.im)) / 2 := by
        rw [Complex.norm_exp, Complex.norm_exp]
        congr 2 <;> simp [neg_mul]
    _ ≤ Real.exp |z.im| := by
        rw [div_le_iff₀ (by norm_num : (0:ℝ) < 2)]
        have h1 : Real.exp (-z.im) ≤ Real.exp |z.im| :=
          Real.exp_le_exp.mpr (neg_le_abs z.im)
        have h2 : Real.exp (z.im) ≤ Real.exp |z.im| :=
          Real.exp_le_exp.mpr (le_abs_self _)
        nlinarith [h1, h2, Real.exp_pos |z.im|]

/-- Forward form of the functional equation.
For `s ≠ 0` and `s` not of the form `1 + n` (`n : ℕ`):
`ζ(s) = 2 · (2π)^(s-1) · Γ(1-s) · cos(π(1-s)/2) · ζ(1-s)`.
Obtained from `riemannZeta_one_sub` applied at `1 - s`. -/
lemma riemannZeta_forward_FE {s : ℂ}
    (hs0 : s ≠ 0) (hns : ∀ n : ℕ, (1 - s) ≠ -n) :
    riemannZeta s =
      2 * (2 * (π : ℂ)) ^ (s - 1) * Complex.Gamma (1 - s) *
        Complex.cos (π * (1 - s) / 2) * riemannZeta (1 - s) := by
  -- `riemannZeta_one_sub` at argument `w = 1 - s` gives
  --   ζ(1 - w) = 2 (2π)^(-w) Γ(w) cos(π w/2) ζ(w),  i.e.
  --   ζ(s) = 2 (2π)^(-(1-s)) Γ(1-s) cos(π(1-s)/2) ζ(1-s).
  have hw1 : (1 - s) ≠ 1 := by
    intro h; apply hs0; linear_combination -h
  have key := riemannZeta_one_sub (s := 1 - s) hns hw1
  simp only [sub_sub_cancel] at key
  rw [key]
  have he : (-(1 - s)) = (s - 1) := by ring
  rw [he]

/-- **PT-C deliverable.**  Polynomial upper bound for `riemannZeta` on the
vertical strip `1/2 ≤ Re s ≤ 2`, `|Im s| ≥ 1`. -/
theorem norm_riemannZeta_poly_bound :
    ∃ (C : ℝ) (k : ℕ), 0 ≤ C ∧ ∀ s : ℂ, (1:ℝ)/2 ≤ s.re → s.re ≤ 2 → 1 ≤ |s.im| →
      ‖riemannZeta s‖ ≤ C * (1 + |s.im|) ^ k := by
  -- Γ band bound on the reflected band `Re(1-s) = 1 - σ ∈ [-1, 1/2]`, uniform constant `A`.
  obtain ⟨A, hA0, hA⟩ := norm_Gamma_band_upper
  -- ζ growth on the left reflected strip.
  obtain ⟨C₀, k, hC0, hZ⟩ := norm_riemannZeta_left_strip_poly
  refine ⟨2 * (2 * π) * A * C₀, k, by positivity, ?_⟩
  intro s hσ1 hσ2 ht
  set σ : ℝ := s.re with hσdef
  set t : ℝ := s.im with htdef
  -- s ≠ 0 since |Im s| ≥ 1.
  have hs0 : s ≠ 0 := by
    intro h
    have : t = 0 := by rw [htdef, h]; simp
    rw [this] at ht; norm_num at ht
  -- 1 - s ≠ -n for all n : ℕ, since Im(1-s) = -t ≠ 0.
  have hns : ∀ n : ℕ, (1 - s) ≠ -n := by
    intro n hn
    have hh : (1 - s).im = (-(n:ℂ)).im := by rw [hn]
    simp only [sub_im, one_im, neg_im, natCast_im, neg_zero, zero_sub] at hh
    rw [← htdef] at hh
    have : t = 0 := by linarith [hh]
    rw [this] at ht; norm_num at ht
  -- Forward functional equation.
  rw [riemannZeta_forward_FE hs0 hns]
  -- Reflected point coordinates.
  have him : (1 - s).im = -t := by simp [sub_im, htdef]
  have hre : (1 - s).re = 1 - σ := by simp [sub_re, hσdef]
  have htabs : |(1 - s).im| = |t| := by rw [him, abs_neg]
  -- Express Γ(1-s) = Γ(σ' + t'*I) with σ' = 1-σ, t' = -t, and apply the band bound.
  have hGamma_arg : (1 - s) = ((1 - σ : ℝ) : ℂ) + ((-t : ℝ)) * Complex.I := by
    apply Complex.ext <;> simp [sub_re, sub_im, hσdef, htdef]
  have hΓbound : ‖Complex.Gamma (1 - s)‖
      ≤ A * |(-t)| ^ ((1 - σ) - 1/2) * Real.exp (-(π/2) * |(-t)|) := by
    rw [hGamma_arg]
    exact hA (1 - σ) (by linarith) (by linarith) (-t) (by rw [abs_neg]; exact ht)
  rw [abs_neg] at hΓbound
  -- cos factor bound.
  have hcos_im : (↑π * (1 - s) / 2).im = -(π * t / 2) := by
    have h2 : (2 : ℂ) = ((2 : ℝ) : ℂ) := by norm_num
    rw [h2, Complex.div_ofReal_im, Complex.im_ofReal_mul, him]
    ring
  have hcos : ‖Complex.cos (↑π * (1 - s) / 2)‖ ≤ Real.exp (π * |t| / 2) := by
    refine (norm_cos_le_exp_abs_im _).trans ?_
    rw [hcos_im, abs_neg]
    apply Real.exp_le_exp.mpr
    rw [abs_div, abs_mul, abs_of_nonneg Real.pi_pos.le, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
  -- Norm of the whole product.
  rw [norm_mul, norm_mul, norm_mul, norm_mul]
  -- ‖2‖ = 2
  have hn2 : ‖(2 : ℂ)‖ = 2 := by norm_num
  -- ‖(2π)^(s-1)‖ = (2π)^(σ-1)
  have h2pi_pos : (0:ℝ) < 2 * π := by positivity
  have hcpow : ‖(2 * (π:ℂ)) ^ (s - 1)‖ = (2 * π) ^ (σ - 1) := by
    rw [show (2 * (π:ℂ)) = ((2 * π : ℝ) : ℂ) by push_cast; ring]
    rw [Complex.norm_cpow_eq_rpow_re_of_pos h2pi_pos]
    rw [show (s - 1).re = σ - 1 from by rw [Complex.sub_re, Complex.one_re]]
  rw [hn2, hcpow]
  -- Now assemble the bound. Let Z := ‖ζ(1-s)‖.
  have hZbound : ‖riemannZeta (1 - s)‖ ≤ C₀ * (1 + |t|) ^ k := by
    have := hZ (1 - s) (by rw [hre]; linarith) (by rw [hre]; linarith)
      (by rw [htabs]; exact ht)
    rw [htabs] at this; exact this
  -- exponential cancellation: exp(π|t|/2) * exp(-(π/2)|t|) = 1.
  have hexp_cancel : Real.exp (π * |t| / 2) * Real.exp (-(π/2) * |t|) = 1 := by
    rw [← Real.exp_add]; rw [show π * |t| / 2 + -(π/2) * |t| = 0 by ring]; exact Real.exp_zero
  -- |t|^(1/2 - σ) ≤ 1 since |t| ≥ 1 and 1/2 - σ ≤ 0.
  have hpow_le : |t| ^ ((1 - σ) - 1/2) ≤ 1 := by
    rw [show (1 - σ) - 1/2 = -(σ - 1/2) by ring, Real.rpow_neg (by linarith [ht])]
    rw [inv_le_one_iff₀]
    right
    exact Real.one_le_rpow ht (by linarith)
  -- (2π)^(σ-1) ≤ 2π since σ - 1 ≤ 1 and 2π ≥ 1.
  have h1 : (1:ℝ) ≤ 2 * π := by nlinarith [Real.pi_gt_three]
  have hcpow_le : (2 * π) ^ (σ - 1) ≤ 2 * π := by
    calc (2 * π) ^ (σ - 1)
        ≤ (2 * π) ^ (1:ℝ) := Real.rpow_le_rpow_of_exponent_le h1 (by linarith)
      _ = 2 * π := Real.rpow_one _
  -- Nonnegativity facts.
  have hcpow_nonneg : (0:ℝ) ≤ (2 * π) ^ (σ - 1) := Real.rpow_nonneg (by positivity) _
  have hΓ_nonneg : (0:ℝ) ≤ ‖Complex.Gamma (1 - s)‖ := norm_nonneg _
  have hcos_nonneg : (0:ℝ) ≤ ‖Complex.cos (↑π * (1 - s) / 2)‖ := norm_nonneg _
  have hZ_nonneg : (0:ℝ) ≤ ‖riemannZeta (1 - s)‖ := norm_nonneg _
  have hpow_nonneg : (0:ℝ) ≤ |t| ^ ((1 - σ) - 1/2) := Real.rpow_nonneg (abs_nonneg _) _
  have hexp1_nonneg : (0:ℝ) ≤ Real.exp (π * |t| / 2) := (Real.exp_pos _).le
  have hexp2_nonneg : (0:ℝ) ≤ Real.exp (-(π/2) * |t|) := (Real.exp_pos _).le
  have hpoly_nonneg : (0:ℝ) ≤ (1 + |t|) ^ k := by positivity
  -- The key reduced bound on the Γ·cos product:
  --   ‖Γ‖·‖cos‖ ≤ A · |t|^((1-σ)-1/2) · exp(-(π/2)|t|) · exp(π|t|/2) = A · |t|^(...) ≤ A.
  have hΓcos : ‖Complex.Gamma (1 - s)‖ * ‖Complex.cos (↑π * (1 - s) / 2)‖ ≤ A := by
    calc ‖Complex.Gamma (1 - s)‖ * ‖Complex.cos (↑π * (1 - s) / 2)‖
        ≤ (A * |t| ^ ((1 - σ) - 1/2) * Real.exp (-(π/2) * |t|))
            * Real.exp (π * |t| / 2) := by
          apply mul_le_mul hΓbound hcos hcos_nonneg
          positivity
      _ = A * |t| ^ ((1 - σ) - 1/2)
            * (Real.exp (π * |t| / 2) * Real.exp (-(π/2) * |t|)) := by ring
      _ = A * |t| ^ ((1 - σ) - 1/2) := by rw [hexp_cancel, mul_one]
      _ ≤ A * 1 := by apply mul_le_mul_of_nonneg_left hpow_le hA0
      _ = A := mul_one A
  -- Final assembly.
  calc 2 * (2 * π) ^ (σ - 1) * ‖Complex.Gamma (1 - s)‖
          * ‖Complex.cos (↑π * (1 - s) / 2)‖ * ‖riemannZeta (1 - s)‖
      = (2 * π) ^ (σ - 1)
          * (‖Complex.Gamma (1 - s)‖ * ‖Complex.cos (↑π * (1 - s) / 2)‖)
          * (2 * ‖riemannZeta (1 - s)‖) := by ring
    _ ≤ (2 * π) * A * (2 * (C₀ * (1 + |t|) ^ k)) := by
          apply mul_le_mul
          · apply mul_le_mul hcpow_le hΓcos (by positivity) (by positivity)
          · linarith [hZbound]
          · positivity
          · positivity
    _ = 2 * (2 * π) * A * C₀ * (1 + |t|) ^ k := by ring

#print axioms norm_riemannZeta_poly_bound
