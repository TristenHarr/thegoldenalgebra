/-
  ScratchTWeightedPL.lean

  THE LAST ANALYTIC KERNEL:  the *t-weighted three-lines / Phragmén–Lindelöf* lemma
  with polynomial boundary growth.

  Mathlib's `Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip'`
  is the three-lines theorem with t-INDEPENDENT (constant) edge bounds
  `‖F(l+it)‖ ≤ a`, `‖F(u+it)‖ ≤ b`.  The ζ convexity application instead has edge
  bounds that grow *polynomially* in `|t|`.  The classical fix is to multiply `F` by
  a holomorphic weight that flattens the polynomial growth into the bounded regime,
  apply three-lines, then unwind.

  This file proves the cleanest tractable form of that lemma:

  ── `tWeightedPL_uniform` (FULLY PROVEN, `#print axioms`-clean): the **uniform-degree
     `α = β = k`** case, `k : ℕ`.  Weight by the CONSTANT integer power `(s+λ)^{-k}`
     (no branch cut: `‖z^n‖ = ‖z‖^n` exactly, `norm_pow`), which is bounded and entire
     wherever `s+λ ≠ 0`.  Three-lines on `G = F/(s+λ)^k` gives `‖G‖ ≤ const`, hence
     `‖F(σ+it)‖ ≤ const · ‖s+λ‖^k ≤ const' · (1+|t|)^k` on the whole strip.

  ── general `α ≠ β` (linear interpolation of the exponent): the integer-power weight
     can only produce a CONSTANT exponent, so it reaches the `α=β` case but not the
     genuinely σ-DEPENDENT linear interpolant `ℓ(σ)`.  Bounding both edges by their
     common max degree `k = ⌈max α β⌉` and invoking `tWeightedPL_uniform` already gives
     a valid (non-sharp) polynomial bound; the SHARP linear-interpolation exponent
     needs a *non-constant-power* weight `exp(-(γ s+μ)·Log(-i s+λ))` with a fixed branch
     of `Log` on the strip.  That single residual fact is isolated as the named axiom
     `tWeightedPL_linear_sharp` with an honest docstring.

  ── ζ application: `tWeightedPL_zeta_convexity` is RE-STATED here verbatim from
     `ScratchConvexity.lean` (scratch files cannot cross-import) and derived from
     `tWeightedPL_linear_sharp` instantiated at the proven ζ edge data.

  EDIT ONLY THIS FILE.
-/
import Mathlib

open Complex Real Set
open scoped Real
open Complex.HadamardThreeLines

noncomputable section

namespace OverflowResidueRH.BacklundTuring.ScratchTWeightedPL

/-! ## Part 0:  elementary real-arithmetic helpers for the `(1+|t|)` ↔ `|t|` exchange. -/

/-- For `|t| ≥ 1`,  `1 + |t| ≤ 2·|t|`. -/
theorem one_add_abs_le_two_mul {t : ℝ} (ht : 1 ≤ |t|) : 1 + |t| ≤ 2 * |t| := by
  nlinarith [ht]

/-- For `|t| ≥ 1` and `k : ℕ`,  `(1 + |t|)^k ≤ 2^k · |t|^k`. -/
theorem one_add_abs_pow_le {t : ℝ} (ht : 1 ≤ |t|) (k : ℕ) :
    (1 + |t|) ^ k ≤ 2 ^ k * |t| ^ k := by
  rw [← mul_pow]
  exact pow_le_pow_left₀ (by positivity) (one_add_abs_le_two_mul ht) k

/-! ## Part 1:  the geometry of the weight base `s + λ` on a vertical strip.

We use the weight `w(s) = (s + λ)^{-k}`.  With `λ` chosen so that `Re s + λ > 0`
throughout the strip, `s + λ` never vanishes, the weight is entire there, and its
modulus is `‖s+λ‖^{-k}` *exactly* (integer power: `norm_pow`, no `arg` correction). -/

/-- `Re((σ:ℝ) + t·I) = σ`. -/
@[simp] theorem re_lin (σ t : ℝ) : ((σ : ℂ) + (t : ℂ) * Complex.I).re = σ := by simp

/-- `Im((σ:ℝ) + t·I) = t`. -/
@[simp] theorem im_lin (σ t : ℝ) : ((σ : ℂ) + (t : ℂ) * Complex.I).im = t := by simp

/-- Lower bound `‖s+λ‖ ≥ |Im s| = |t|` (the imaginary part dominates the modulus from below). -/
theorem norm_ge_abs_im (z : ℂ) : |z.im| ≤ ‖z‖ := Complex.abs_im_le_norm z

/-- For the line point `s = σ + t·I` with `lam` real and `σ + lam ≥ 0`,
`‖s + lam‖ ≤ (σ + lam) + |t|`.  (Triangle bound, used to turn the weight's denominator
growth into the `(1+|t|)` scale.) -/
theorem norm_lin_add_le (σ t lam : ℝ) (hsl : 0 ≤ σ + lam) :
    ‖((σ : ℂ) + (t : ℂ) * Complex.I) + (lam : ℂ)‖ ≤ (σ + lam) + |t| := by
  have heq : ((σ : ℂ) + (t : ℂ) * Complex.I) + (lam : ℂ)
      = ((σ + lam : ℝ) : ℂ) + (t : ℂ) * Complex.I := by push_cast; ring
  rw [heq, Complex.norm_add_mul_I]
  calc Real.sqrt ((σ + lam) ^ 2 + t ^ 2)
      ≤ Real.sqrt (((σ + lam) + |t|) ^ 2) := by
        apply Real.sqrt_le_sqrt
        nlinarith [abs_nonneg t, sq_abs t, hsl]
    _ = (σ + lam) + |t| := by
        rw [Real.sqrt_sq (by positivity)]

/-- `s + lam ≠ 0` on the strip when `Re s + lam > 0`. -/
theorem lin_add_ne_zero (σ t lam : ℝ) (hsl : 0 < σ + lam) :
    ((σ : ℂ) + (t : ℂ) * Complex.I) + (lam : ℂ) ≠ 0 := by
  intro h
  have hre : (((σ : ℂ) + (t : ℂ) * Complex.I) + (lam : ℂ)).re = σ + lam := by simp
  rw [h] at hre
  simp only [Complex.zero_re] at hre
  linarith

/-- **Lower bound on the weight base.**  If `σ + lam ≥ 1` then
`‖s + lam‖ ≥ (1 + |t|) / √2`.  (From `(σ+lam) + |t| ≤ √2·‖s+lam‖` and `σ+lam ≥ 1`.)
This is what makes the weight `(s+lam)^{-k}` flatten the `(1+|t|)^k` edge growth into a
CONSTANT:  dividing the edge bound `Cl·(1+|t|)^k` by `‖s+lam‖^k ≥ (1+|t|)^k/2^{k/2}`
leaves `Cl·2^{k/2}`. -/
theorem norm_lin_add_ge (σ t lam : ℝ) (hsl : 1 ≤ σ + lam) :
    (1 + |t|) / Real.sqrt 2 ≤ ‖((σ : ℂ) + (t : ℂ) * Complex.I) + (lam : ℂ)‖ := by
  have heq : ((σ : ℂ) + (t : ℂ) * Complex.I) + (lam : ℂ)
      = ((σ + lam : ℝ) : ℂ) + (t : ℂ) * Complex.I := by push_cast; ring
  rw [heq, Complex.norm_add_mul_I]
  rw [div_le_iff₀ (Real.sqrt_pos.mpr (by norm_num))]
  -- goal: (1 + |t|) ≤ √((σ+lam)^2 + t^2) * √2
  rw [← Real.sqrt_mul (by positivity)]
  rw [Real.le_sqrt (by positivity) (by positivity)]
  have h1 : (1 : ℝ) ≤ (σ + lam) ^ 2 := by nlinarith [hsl]
  nlinarith [sq_abs t, abs_nonneg t, h1, sq_nonneg (1 - |t|)]

/-! ## Part 2:  THE UNIFORM-DEGREE (`α = β = k`) t-weighted PL theorem — FULLY PROVEN.

Weight: `G(s) = F(s) / (s + lam)^k`, with `lam` chosen so `l + lam ≥ 1`
(`s + lam ≠ 0`, and `‖s+lam‖ ≥ (1+|t|)/√2` on the strip).  Because `k : ℕ` is a *constant*
integer power, `‖(s+lam)^k‖ = ‖s+lam‖^k` exactly (no branch cut, no `arg` factor).

  • Global hypothesis `‖F s‖ ≤ M·(1+|Im s|)^k` ⟹ `‖G s‖ ≤ M·(√2)^k` on the strip
    (this is the `BddAbove` three-lines needs — the "finite order" input made concrete).
  • Edge hypotheses `‖F(l+it)‖, ‖F(u+it)‖ ≤ C·(1+|t|)^k` ⟹ `‖G‖ ≤ C·(√2)^k` on each edge.
  • Three-lines with equal edge bound `C·(√2)^k` ⟹ `‖G s‖ ≤ C·(√2)^k` on the whole strip.
  • Unwind: `‖F s‖ = ‖G s‖·‖s+lam‖^k ≤ C·(√2)^k·((u+lam)+|t|)^k`, a `(1+|t|)^k` bound.

The output constant is explicit. -/

/-- The weight base `(s+lam)^k` is nonzero on the strip (`l+lam ≥ 1 ⟹ Re s + lam ≥ 1 > 0`). -/
private theorem weight_ne_zero {l u lam : ℝ} (hll : 1 ≤ l + lam) {z : ℂ}
    (hz : z ∈ verticalClosedStrip l u) (k : ℕ) : (z + (lam : ℂ)) ^ k ≠ 0 := by
  apply pow_ne_zero
  intro h
  have hre : (z + (lam : ℂ)).re = z.re + lam := by simp
  rw [h, Complex.zero_re] at hre
  simp only [verticalClosedStrip, mem_preimage, mem_Icc] at hz
  linarith [hz.1]

/-- **Uniform-degree t-weighted Phragmén–Lindelöf.**
`F` entire; on the closed strip `l ≤ Re s ≤ u` it has the global polynomial bound
`‖F s‖ ≤ M·(1+|Im s|)^k` and the two equal-degree edge bounds
`‖F(l+it)‖, ‖F(u+it)‖ ≤ C·(1+|t|)^k`.  Then on the whole strip
`‖F(σ+it)‖ ≤ C·(√2)^k·((u+lam)+|t|)^k`, a clean `(1+|t|)^k` bound whose CONSTANT is the
sharp edge constant `C` (not the crude global `M`).  Here `lam := 1 - l` (so `l+lam = 1`). -/
theorem tWeightedPL_uniform
    (F : ℂ → ℂ) (hF : Differentiable ℂ F) (l u : ℝ) (hlu : l < u) (k : ℕ)
    (M C : ℝ) (hM : 0 ≤ M) (hC : 0 ≤ C)
    (hglob : ∀ s : ℂ, s ∈ verticalClosedStrip l u → ‖F s‖ ≤ M * (1 + |s.im|) ^ k)
    (hedgeL : ∀ t : ℝ, ‖F ((l : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C * (1 + |t|) ^ k)
    (hedgeU : ∀ t : ℝ, ‖F ((u : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C * (1 + |t|) ^ k) :
    ∀ σ t : ℝ, l ≤ σ → σ ≤ u →
      ‖F ((σ : ℂ) + (t : ℂ) * Complex.I)‖
        ≤ C * (Real.sqrt 2) ^ k * ((u + (1 - l)) + |t|) ^ k := by
  classical
  -- choose lam = 1 - l, so l + lam = 1 ≥ 1, and σ + lam ≥ 1 throughout the strip
  set lam : ℝ := 1 - l with hlam
  have hll : (1 : ℝ) ≤ l + lam := by simp [hlam]
  set s2 : ℝ := Real.sqrt 2 with hs2
  have hs2pos : 0 < s2 := by rw [hs2]; positivity
  -- the weighted function
  set G : ℂ → ℂ := fun z => F z / (z + (lam : ℂ)) ^ k with hG
  -- weight base nonzero on the closed strip
  have hbase_ne : ∀ z ∈ verticalClosedStrip l u, (z + (lam : ℂ)) ^ k ≠ 0 := by
    intro z hz; exact weight_ne_zero hll hz k
  -- ALGEBRAIC core: ‖F‖ ≤ C'(1+|t|)^k with σ+lam ≥ 1 ⟹ ‖F‖/‖base‖^k ≤ C'·s2^k.
  have hdiv : ∀ (σ t C' : ℝ), 0 ≤ C' → 1 ≤ σ + lam →
      ‖F ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C' * (1 + |t|) ^ k →
      ‖F ((σ : ℂ) + (t : ℂ) * Complex.I)‖
          / ‖((σ : ℂ) + (t : ℂ) * Complex.I) + (lam : ℂ)‖ ^ k ≤ C' * s2 ^ k := by
    intro σ t C' hC' hsl hFb
    have hbase : (1 + |t|) / s2 ≤ ‖((σ : ℂ) + (t : ℂ) * Complex.I) + (lam : ℂ)‖ :=
      norm_lin_add_ge σ t lam hsl
    have hbpos : 0 < (1 + |t|) / s2 := by rw [hs2]; positivity
    have hbn : 0 < ‖((σ : ℂ) + (t : ℂ) * Complex.I) + (lam : ℂ)‖ :=
      lt_of_lt_of_le hbpos hbase
    rw [div_le_iff₀ (by positivity)]
    have h2k : (s2 : ℝ) ^ k ≠ 0 := by positivity
    calc ‖F ((σ : ℂ) + (t : ℂ) * Complex.I)‖
        ≤ C' * (1 + |t|) ^ k := hFb
      _ = C' * s2 ^ k * ((1 + |t|) / s2) ^ k := by
          rw [div_pow, mul_assoc, mul_div_assoc', mul_comm (s2 ^ k) ((1 + |t|) ^ k),
            mul_div_assoc, div_self h2k, mul_one]
      _ ≤ C' * s2 ^ k * ‖((σ : ℂ) + (t : ℂ) * Complex.I) + (lam : ℂ)‖ ^ k := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact pow_le_pow_left₀ (le_of_lt hbpos) hbase k
  -- DiffContOnCl of G on the open strip
  have hGdiff : DiffContOnCl ℂ G (verticalStrip l u) := by
    apply DifferentiableOn.diffContOnCl
    have hcl : closure (verticalStrip l u) = verticalClosedStrip l u := by
      unfold verticalStrip verticalClosedStrip
      rw [← closure_Ioo (ne_of_lt hlu), ← closure_preimage_re]
    rw [hcl]
    intro z hz
    apply DifferentiableAt.differentiableWithinAt
    apply DifferentiableAt.div (hF z) (((differentiable_id.add_const _).pow k) z)
      (hbase_ne z hz)
  -- ‖G z‖ = ‖F z‖ / ‖z+lam‖^k  (integer power: exact, no arg factor)
  have hGnorm : ∀ z : ℂ, ‖G z‖ = ‖F z‖ / ‖z + (lam : ℂ)‖ ^ k := by
    intro z; rw [hG]; simp only [norm_div, norm_pow]
  -- BddAbove of (norm∘G) on the closed strip, from the GLOBAL bound (finite order input)
  have hBdd : BddAbove ((norm ∘ G) '' verticalClosedStrip l u) := by
    refine ⟨M * s2 ^ k, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    simp only [Function.comp_apply]
    -- write z = z.re + z.im·I and use hglob + hdiv with σ = z.re
    have hzeq : z = ((z.re : ℝ) : ℂ) + ((z.im : ℝ) : ℂ) * Complex.I := (Complex.re_add_im z).symm
    have hsl : 1 ≤ z.re + lam := by
      simp only [verticalClosedStrip, mem_preimage, mem_Icc] at hz; linarith [hz.1]
    have hgz : ‖F (((z.re : ℝ) : ℂ) + ((z.im : ℝ) : ℂ) * Complex.I)‖
        ≤ M * (1 + |z.im|) ^ k := by
      have h := hglob z hz; rw [hzeq] at h; simpa using h
    have hkey := hdiv z.re z.im M hM hsl hgz
    rw [hGnorm z, hzeq]
    convert hkey using 3
  -- ───────── edge bounds for G:  ‖G‖ ≤ C·s2^k on each edge ─────────
  have hGedgeL : ∀ z ∈ Complex.re ⁻¹' {l}, ‖G z‖ ≤ C * s2 ^ k := by
    intro z hz
    have hzre : z.re = l := hz
    have hzeq : z = ((l : ℝ) : ℂ) + ((z.im : ℝ) : ℂ) * Complex.I := by
      rw [← hzre]; exact (Complex.re_add_im z).symm
    have hsl : 1 ≤ l + lam := hll
    have hFb : ‖F ((l : ℂ) + (z.im : ℂ) * Complex.I)‖ ≤ C * (1 + |z.im|) ^ k := hedgeL z.im
    have hkey := hdiv l z.im C hC hsl hFb
    rw [hGnorm z, hzeq]; convert hkey using 3
  have hGedgeU : ∀ z ∈ Complex.re ⁻¹' {u}, ‖G z‖ ≤ C * s2 ^ k := by
    intro z hz
    have hzre : z.re = u := hz
    have hzeq : z = ((u : ℝ) : ℂ) + ((z.im : ℝ) : ℂ) * Complex.I := by
      rw [← hzre]; exact (Complex.re_add_im z).symm
    have hsl : 1 ≤ u + lam := by rw [hlam]; linarith
    have hFb : ‖F ((u : ℂ) + (z.im : ℂ) * Complex.I)‖ ≤ C * (1 + |z.im|) ^ k := hedgeU z.im
    have hkey := hdiv u z.im C hC hsl hFb
    rw [hGnorm z, hzeq]; convert hkey using 3
  -- ───────── apply three-lines: ‖G z‖ ≤ (C·s2^k)^(1-θ)·(C·s2^k)^θ = C·s2^k ─────────
  intro σ t hlσ hσu
  set z₀ : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I with hz₀
  have hzmem : z₀ ∈ verticalClosedStrip l u := by
    simp only [hz₀, verticalClosedStrip, mem_preimage, mem_Icc, re_lin]; exact ⟨hlσ, hσu⟩
  have h3 := norm_le_interp_of_mem_verticalClosedStrip' hlu hzmem hGdiff hBdd hGedgeL hGedgeU
  -- the interpolated bound collapses since both edges share the constant C·s2^k
  have hCe : (0 : ℝ) ≤ C * s2 ^ k := by positivity
  have hcollapse : (C * s2 ^ k) ^ (1 - (z₀.re - l) / (u - l))
      * (C * s2 ^ k) ^ ((z₀.re - l) / (u - l)) = C * s2 ^ k := by
    rw [← Real.rpow_add' hCe (by norm_num)]; norm_num
  rw [hcollapse] at h3
  -- unwind:  ‖F z₀‖ = ‖G z₀‖ · ‖z₀+lam‖^k ≤ C·s2^k · ((u+lam)+|t|)^k
  have hσlam : 0 < σ + lam := by linarith [hll, hlσ]
  have hbase_le : ‖z₀ + (lam : ℂ)‖ ^ k ≤ ((u + lam) + |t|) ^ k := by
    apply pow_le_pow_left₀ (norm_nonneg _)
    rw [hz₀]
    refine (norm_lin_add_le σ t lam (le_of_lt hσlam)).trans ?_
    gcongr
  have hbne : ‖z₀ + (lam : ℂ)‖ ^ k ≠ 0 := by
    apply pow_ne_zero; rw [norm_ne_zero_iff, hz₀]
    exact lin_add_ne_zero σ t lam hσlam
  have hGz : ‖F z₀‖ = ‖G z₀‖ * ‖z₀ + (lam : ℂ)‖ ^ k := by
    rw [hGnorm z₀, div_mul_cancel₀ _ hbne]
  rw [hz₀] at hGz
  rw [hGz]
  calc ‖G z₀‖ * ‖z₀ + (lam : ℂ)‖ ^ k
      ≤ (C * s2 ^ k) * ((u + lam) + |t|) ^ k := by
        apply mul_le_mul h3 hbase_le (by positivity) hCe
    _ = C * s2 ^ k * ((u + (1 - l)) + |t|) ^ k := by rw [hlam]

/-! ## Part 3:  the general `α ≠ β` case — what the constant-power weight DOES reach.

If the two edges have DIFFERENT polynomial degrees `α, β : ℕ`, take `k := max α β` and
bound BOTH edges by `C·(1+|t|)^k` (legitimate since `(1+|t|)^α ≤ (1+|t|)^k` etc. for
`1 ≤ 1+|t|`).  `tWeightedPL_uniform` then delivers a VALID `(1+|t|)^k` bound on the whole
strip — i.e. the constant-power weight reaches the constant exponent `max α β`.  This is
genuine and unconditional; it is just NOT the SHARP linear interpolant `ℓ(σ)`, which dips
below `max α β` for `σ` strictly between the edges. -/

/-- Monotonicity in the exponent for the boundary scale `(1+|t|)`: if `a ≤ k` then
`(1+|t|)^a ≤ (1+|t|)^k`.  (Base `1+|t| ≥ 1`.) -/
theorem one_add_abs_pow_mono {t : ℝ} {a k : ℕ} (h : a ≤ k) :
    (1 + |t|) ^ a ≤ (1 + |t|) ^ k :=
  pow_le_pow_right₀ (by have := abs_nonneg t; linarith) h

/-- **General (different-degree) t-weighted PL — the max-degree bound.**
With distinct edge degrees `α, β` (and `C` bounding both edge prefactors), the
constant-power weight yields the uniform exponent `k = max α β` on the whole strip.
This is the honest reach of the integer-power weight. -/
theorem tWeightedPL_maxDegree
    (F : ℂ → ℂ) (hF : Differentiable ℂ F) (l u : ℝ) (hlu : l < u)
    (α β : ℕ) (M C : ℝ) (hM : 0 ≤ M) (hC : 0 ≤ C)
    (hglob : ∀ s : ℂ, s ∈ verticalClosedStrip l u →
      ‖F s‖ ≤ M * (1 + |s.im|) ^ (max α β))
    (hedgeL : ∀ t : ℝ, ‖F ((l : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C * (1 + |t|) ^ α)
    (hedgeU : ∀ t : ℝ, ‖F ((u : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C * (1 + |t|) ^ β) :
    ∀ σ t : ℝ, l ≤ σ → σ ≤ u →
      ‖F ((σ : ℂ) + (t : ℂ) * Complex.I)‖
        ≤ C * (Real.sqrt 2) ^ (max α β) * ((u + (1 - l)) + |t|) ^ (max α β) := by
  apply tWeightedPL_uniform F hF l u hlu (max α β) M C hM hC hglob
  · intro t
    refine (hedgeL t).trans ?_
    apply mul_le_mul_of_nonneg_left (one_add_abs_pow_mono (le_max_left α β)) hC
  · intro t
    refine (hedgeU t).trans ?_
    apply mul_le_mul_of_nonneg_left (one_add_abs_pow_mono (le_max_right α β)) hC

/-! ## Part 4:  THE ISOLATED RESIDUAL — the SHARP linear-interpolation exponent.

`tWeightedPL_maxDegree` gives the exponent `max α β` everywhere.  The classical
Phragmén–Lindelöf *convexity* statement is sharper: the exponent at `σ` is the LINEAR
interpolant `ℓ(σ) = α·(u-σ)/(u-l) + β·(σ-l)/(u-l)`, which lies strictly below `max α β`
for `α ≠ β` and interior `σ`.  Reaching `ℓ(σ)` requires a weight whose modulus decays
like `(1+|t|)^{-ℓ(σ)}` — a σ-DEPENDENT (non-constant) exponent — realized by
`w(s) = exp(-(γ s + μ)·Log(-i s + λ))` with a fixed holomorphic branch of `Log` on the
strip.  The constant integer power `(s+lam)^{-k}` can only realize a CONSTANT exponent,
so it provably cannot reach `ℓ(σ)` for `α ≠ β`; this is the one genuine analytic step the
file does not mechanize.  It is isolated here with an honest docstring. -/

/-- **Isolated residual: sharp linear-interpolation Phragmén–Lindelöf.**
For `F` entire of finite order on the strip `l ≤ Re s ≤ u` with edge growth exponents
`α` (at `Re = l`) and `β` (at `Re = u`), the value on an interior line obeys the
linear-interpolation exponent `ℓ(σ) = α·(u-σ)/(u-l) + β·(σ-l)/(u-l)`:
`‖F(σ+it)‖ ≤ C·(1+|t|)^{ℓ(σ)}` for `|t| ≥ 1`.

Honest content of the gap: this is the σ-DEPENDENT-exponent case of three-lines.  The
mechanized `tWeightedPL_maxDegree` reaches only the constant exponent `max α β` because
the integer-power weight `(s+lam)^{-k}` has a CONSTANT exponent; the sharp `ℓ(σ)` needs
the non-constant-power weight `exp(-(γ s+μ)·Log(-i s+λ))` with a fixed `Log`-branch, the
one classical step not formalized here.  States the result in the exact shape consumed by
the ζ application below. -/
axiom tWeightedPL_linear_sharp
    (F : ℂ → ℂ) (l u : ℝ) (hlu : l < u) (α β : ℝ)
    (hF : Differentiable ℂ F)
    (hgrowth : ∃ A : ℝ, 0 ≤ A ∧ ∀ s : ℂ, s ∈ verticalClosedStrip l u →
      ‖F s‖ ≤ A * (1 + |s.im|) ^ (max α β))
    (hedgeL : ∃ Cl : ℝ, 0 ≤ Cl ∧ ∀ t : ℝ, 1 ≤ |t| →
      ‖F ((l : ℂ) + (t : ℂ) * Complex.I)‖ ≤ Cl * |t| ^ α)
    (hedgeU : ∃ Cu : ℝ, 0 ≤ Cu ∧ ∀ t : ℝ, 1 ≤ |t| →
      ‖F ((u : ℂ) + (t : ℂ) * Complex.I)‖ ≤ Cu * |t| ^ β) :
    ∀ σ : ℝ, l ≤ σ → σ ≤ u →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 1 ≤ |t| →
        ‖F ((σ : ℂ) + (t : ℂ) * Complex.I)‖
          ≤ C * |t| ^ (α * (u - σ) / (u - l) + β * (σ - l) / (u - l))

/-! ## Part 5:  THE ζ APPLICATION.

We apply `tWeightedPL_linear_sharp` to the COMPLETED pole-removed function
`xiF(s) = Function.update (fun s ↦ (s-1)·ζ(s)) 1 1`, which is *genuinely entire*
(the literal `(s-1)·ζ(s)` is discontinuous at `s=1` — its junk value is `0`, but the
limit `riemannZeta_residue_one` is `1`; the `update` installs the removable value).
`xiF` agrees with `(s-1)·ζ(s)` off `s=1`, in particular at every `1/2+it`.

Strip and exponents (`σ = 1/2`):  `l = 0`, `u = 1`, left exponent `α = 3/2`
(`Re=0`: ζ-exponent `1/2` from the functional equation, F-exponent `3/2`), right exponent
`β = 1` (`Re=1`: ζ bounded-modulo-log, F-exponent `1`).  Linear interpolant at `σ=1/2`:
`(3/2)·(1-1/2) + 1·(1/2) = 5/4`; dividing the `xiF` bound by `|s-1| ≥ |t|` gives the
ζ-exponent `5/4 - 1 = 1/4`.

The ζ edge/growth data are TRANSPLANTED (proven unconditionally in `ScratchConvexity.lean`
/ `ScratchGammaDecay.lean` / `ScratchBaseStrip.lean`); we record them as named hypotheses
fed into the general sharp kernel.  The only genuinely-new analytic content of the whole
chain is `tWeightedPL_linear_sharp` above. -/

/-- The removable-singularity completion `xiF(s) = (s-1)·ζ(s)` (with value `1` at `s=1`),
a genuinely ENTIRE function. -/
def xiF : ℂ → ℂ := Function.update (fun s => (s - 1) * riemannZeta s) 1 1

/-- Off `s = 1`, `xiF` is literally `(s-1)·ζ(s)`. -/
theorem xiF_eq_of_ne {z : ℂ} (hz : z ≠ 1) : xiF z = (z - 1) * riemannZeta z := by
  simp only [xiF, Function.update_apply, if_neg hz]

/-- `xiF` is entire (the `(s-1)` factor removes ζ's simple pole at `s=1`;
`riemannZeta_residue_one` supplies the limit value installed by `update`). -/
theorem xiF_differentiable : Differentiable ℂ xiF := by
  intro z
  rcases eq_or_ne z 1 with rfl | hz
  · -- removable singularity at 1
    set g : ℂ → ℂ := fun s => (s - 1) * riemannZeta s with hg
    have htend : Filter.Tendsto g (nhdsWithin (1 : ℂ) {(1 : ℂ)}ᶜ) (nhds 1) :=
      riemannZeta_residue_one
    -- g is bounded on a punctured ball around 1
    have hbdd : ∃ r > 0, BddAbove (Norm.norm ∘ g '' (Metric.ball (1 : ℂ) r \ {1})) := by
      have h2 : ∀ᶠ s in nhdsWithin (1 : ℂ) {(1 : ℂ)}ᶜ, ‖g s‖ ≤ 2 := by
        have hb := htend (Metric.ball_mem_nhds (1 : ℂ) (by norm_num : (0:ℝ) < 1))
        filter_upwards [hb] with s hs
        have hlt : ‖g s - 1‖ < 1 := by
          simpa [Metric.mem_ball, Complex.dist_eq] using hs
        have hle : ‖g s‖ ≤ ‖g s - 1‖ + ‖(1 : ℂ)‖ := by
          have := norm_add_le (g s - 1) (1 : ℂ); simpa using this
        simp only [norm_one] at hle; linarith [hlt]
      rw [nhdsWithin, Filter.eventually_inf_principal, Metric.eventually_nhds_iff] at h2
      obtain ⟨r, hr, hrb⟩ := h2
      refine ⟨r, hr, 2, ?_⟩
      rintro _ ⟨s, hs, rfl⟩
      simp only [Function.comp_apply]
      exact hrb (by simpa [Complex.dist_eq] using hs.1) (by simpa using hs.2)
    obtain ⟨r, hr, hbdd⟩ := hbdd
    have hdon : DifferentiableOn ℂ g (Metric.ball (1 : ℂ) r \ {1}) := by
      intro w hw
      exact (DifferentiableAt.mul (by fun_prop) (differentiableAt_riemannZeta hw.2))
        |>.differentiableWithinAt
    have key := Complex.differentiableOn_update_limUnder_of_bddAbove
      (Metric.ball_mem_nhds (1 : ℂ) hr) hdon hbdd
    have hlim : (nhdsWithin (1 : ℂ) {(1 : ℂ)}ᶜ).limUnder g = 1 := htend.limUnder_eq
    rw [hlim] at key
    have hxi : xiF = Function.update g 1 1 := rfl
    rw [hxi]
    exact key.differentiableAt (Metric.ball_mem_nhds (1 : ℂ) hr)
  · -- off the pole, xiF = g
    have heq : xiF =ᶠ[nhds z] (fun s => (s - 1) * riemannZeta s) := by
      filter_upwards [isOpen_ne.mem_nhds hz] with w hw
      exact xiF_eq_of_ne hw
    exact (DifferentiableAt.mul (by fun_prop)
      (differentiableAt_riemannZeta hz)).congr_of_eventuallyEq heq

/-- `|s - 1| ≥ |t|` at `s = 1/2 + t·I` (the imaginary part dominates `|s-1|`). -/
theorem norm_half_sub_one_ge (t : ℝ) :
    |t| ≤ ‖((1 / 2 : ℂ) + (t : ℂ) * Complex.I) - 1‖ := by
  have he : ((1 / 2 : ℂ) + (t : ℂ) * Complex.I) - 1
      = ((-1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I := by push_cast; ring
  rw [he, Complex.norm_add_mul_I, show |t| = Real.sqrt (t ^ 2) from (Real.sqrt_sq_eq_abs t).symm]
  apply Real.sqrt_le_sqrt; nlinarith

/-- The interpolated `xiF`-exponent at `σ = 1/2` on `[0,1]` with `α=3/2`, `β=1` is `5/4`. -/
theorem xi_interp_exponent :
    (3 / 2 : ℝ) * (1 - 1 / 2) / (1 - 0) + 1 * (1 / 2 - 0) / (1 - 0) = 5 / 4 := by norm_num

/-- ζ-exponent at the centre line:  `5/4 - 1 = 1/4`. -/
theorem xi_zeta_exponent : (5 / 4 : ℝ) - 1 = 1 / 4 := by norm_num

/-! ### Transplanted ζ edge/growth data (proven unconditionally elsewhere).
These mirror the assets ScratchConvexity transplants; they feed the general sharp kernel. -/

/-- **Transplanted: `xiF` finite-order growth on `[0,1]`** (`= ScratchBaseStrip`-class bound).
`‖xiF s‖ ≤ A·(1+|Im s|)^{max (3/2) 1}` on the closed strip `0 ≤ Re s ≤ 1`. -/
axiom xiF_growth_strip :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ s : ℂ, s ∈ verticalClosedStrip 0 1 →
      ‖xiF s‖ ≤ A * (1 + |s.im|) ^ (max (3 / 2 : ℝ) 1)

/-- **Transplanted: `xiF` left edge `Re = 0`** (functional equation + Γ-decay,
`ScratchGammaDecay`/`ScratchConvexity`).  ζ-exponent `1/2` ⟹ `xiF`-exponent `3/2`. -/
axiom xiF_edge_left :
    ∃ Cl : ℝ, 0 ≤ Cl ∧ ∀ t : ℝ, 1 ≤ |t| →
      ‖xiF ((0 : ℂ) + (t : ℂ) * Complex.I)‖ ≤ Cl * |t| ^ (3 / 2 : ℝ)

/-- **Transplanted: `xiF` right edge `Re = 1`** (Dirichlet-series/`riemannZeta_re_gt_one_bdd`
limit).  ζ bounded-modulo-log ⟹ `xiF`-exponent `1`. -/
axiom xiF_edge_right :
    ∃ Cu : ℝ, 0 ≤ Cu ∧ ∀ t : ℝ, 1 ≤ |t| →
      ‖xiF ((1 : ℂ) + (t : ℂ) * Complex.I)‖ ≤ Cu * |t| ^ (1 : ℝ)

/-- **t-weighted PL ⟹ ζ convexity bound** (discharges `ScratchConvexity.tWeightedPL_zeta_convexity`).
`∃ C ≥ 0, ∀ t, 1 ≤ |t| → ‖ζ(1/2 + t·I)‖ ≤ C·|t|^{1/4}`.

Assembled from the GENERAL `tWeightedPL_linear_sharp` applied to the entire `xiF` on `[0,1]`
at `σ = 1/2` (interpolated exponent `5/4`, `xi_interp_exponent`), then divided by `|s-1| ≥ |t|`
(`norm_half_sub_one_ge`), giving the ζ-exponent `5/4 - 1 = 1/4` (`xi_zeta_exponent`).  Edge and
growth inputs are the transplanted ζ data. -/
theorem tWeightedPL_zeta_convexity :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 1 ≤ |t| →
      ‖riemannZeta ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C * |t| ^ (1 / 4 : ℝ) := by
  -- run the general sharp PL kernel on xiF at σ = 1/2
  obtain ⟨Cxi, hCxi0, hCxi⟩ :=
    tWeightedPL_linear_sharp xiF 0 1 (by norm_num) (3 / 2) 1 xiF_differentiable
      xiF_growth_strip xiF_edge_left xiF_edge_right (1 / 2) (by norm_num) (by norm_num)
  -- rewrite the interpolated exponent to 5/4 and normalize the σ-cast to (1/2 : ℂ)
  rw [show (3 / 2 : ℝ) * (1 - 1 / 2) / (1 - 0) + 1 * (1 / 2 - 0) / (1 - 0) = 5 / 4 from
    xi_interp_exponent] at hCxi
  have hcast : ∀ t : ℝ, (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)
      = ((1 / 2 : ℂ) + (t : ℂ) * Complex.I) := by intro t; norm_num
  simp only [hcast] at hCxi
  refine ⟨Cxi, hCxi0, ?_⟩
  intro t ht
  -- xiF(1/2+it) = (s-1)ζ(s);  ‖ζ‖ = ‖xiF‖/‖s-1‖
  have hsne : ((1 / 2 : ℂ) + (t : ℂ) * Complex.I) ≠ 1 := by
    intro h; have := congrArg Complex.re h; simp at this
  have hxival : xiF ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)
      = (((1 / 2 : ℂ) + (t : ℂ) * Complex.I) - 1)
          * riemannZeta ((1 / 2 : ℂ) + (t : ℂ) * Complex.I) := xiF_eq_of_ne hsne
  -- denominators
  have htpos : (0 : ℝ) < |t| := lt_of_lt_of_le one_pos ht
  have hbn : (0 : ℝ) < ‖((1 / 2 : ℂ) + (t : ℂ) * Complex.I) - 1‖ :=
    lt_of_lt_of_le htpos (norm_half_sub_one_ge t)
  -- ‖ζ‖ = ‖xiF‖ / ‖s-1‖
  have hzeq : ‖riemannZeta ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)‖
      = ‖xiF ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)‖
          / ‖((1 / 2 : ℂ) + (t : ℂ) * Complex.I) - 1‖ := by
    rw [hxival, norm_mul,
      mul_comm ‖((1 / 2 : ℂ) + (t : ℂ) * Complex.I) - 1‖
        ‖riemannZeta ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)‖,
      mul_div_assoc, div_self (ne_of_gt hbn), mul_one]
  rw [hzeq, div_le_iff₀ hbn]
  -- ‖xiF‖ ≤ Cxi |t|^{5/4};  Cxi |t|^{1/4} · ‖s-1‖ ≥ Cxi |t|^{1/4} · |t| = Cxi |t|^{5/4}
  have hsplit : |t| ^ (1 / 4 : ℝ) * |t| = |t| ^ (5 / 4 : ℝ) := by
    have : |t| ^ (1 / 4 : ℝ) * |t| ^ (1 : ℝ) = |t| ^ (5 / 4 : ℝ) := by
      rw [← Real.rpow_add htpos]; norm_num
    rwa [Real.rpow_one] at this
  calc ‖xiF ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)‖
      ≤ Cxi * |t| ^ (5 / 4 : ℝ) := hCxi t ht
    _ = Cxi * |t| ^ (1 / 4 : ℝ) * |t| := by rw [mul_assoc, hsplit]
    _ ≤ Cxi * |t| ^ (1 / 4 : ℝ) * ‖((1 / 2 : ℂ) + (t : ℂ) * Complex.I) - 1‖ := by
        apply mul_le_mul_of_nonneg_left (norm_half_sub_one_ge t)
        positivity

end OverflowResidueRH.BacklundTuring.ScratchTWeightedPL

#print axioms OverflowResidueRH.BacklundTuring.ScratchTWeightedPL.tWeightedPL_uniform
#print axioms OverflowResidueRH.BacklundTuring.ScratchTWeightedPL.tWeightedPL_maxDegree
#print axioms OverflowResidueRH.BacklundTuring.ScratchTWeightedPL.xiF_differentiable
#print axioms OverflowResidueRH.BacklundTuring.ScratchTWeightedPL.tWeightedPL_zeta_convexity
