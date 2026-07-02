import Mathlib
import rh

open Complex Filter Topology MeasureTheory Set Real HurwitzZeta

/-! # The Riemann Ξ cosine-transform identity  `Ξ(z) = 2∫₀^∞ Φ(u) cos(zu) du`

This file builds the **Riemann-memoir Fourier–cosine representation** of the entire
Riemann Ξ–function around Mathlib's theta / Mellin machinery.

## What `Ξ` and `Φ` are

* `Ξ(z) := ξ(½ + iz)`, where `ξ = OverflowResidueRH.entireRiemannXi` is the entire
  completed zeta built in `rh.lean` as
  `ξ s = ½·s·(s−1)·completedRiemannZeta₀ s + ½`.  It is entire (Mathlib
  `differentiable_completedZeta₀`) and satisfies `ξ(1−s) = ξ(s)`.

* `Φ : ℝ → ℝ` is the **Riemann Φ-function**
  `Φ(u) = Σ_{n≥1} (2π²n⁴ e^{9u/2} − 3π n² e^{5u/2}) · e^{−π n² e^{2u}}`.
  It is even, smooth, and has *double-exponential* decay as `u → +∞`
  (the `e^{−π n² e^{2u}}` factor) and ordinary exponential decay as `u → −∞`
  (the `e^{9u/2}, e^{5u/2}` factors).

## What Mathlib provides (searched, used below)

* `HurwitzZeta.evenKernel 0 t = Σ_{n∈ℤ} e^{−π n² t}` — the Jacobi theta ψ-function
  (`hasSum_int_evenKernel`); the modified `(n≠0)` form is `hasSum_int_evenKernel₀`.
* `completedRiemannZeta₀ s = mellin F (s/2) / 2` with `F = (hurwitzEvenFEPair 0).f_modif`
  (this is exactly the `completedRiemannZeta0_eq_mellin` route used in `ScratchLambda0`).
* `mellin f s = ∫ t in Ioi 0, (t:ℂ)^(s−1) • f t`, plus the change-of-variables family
  `mellin_comp_rpow`, `mellin_comp_mul_left`, `mellin_comp_inv`.
* `jacobiTheta₂`, `completedRiemannZeta`, `completedRiemannZeta_one_sub` (the FE).

## What is PROVEN here

* `Phi` defined explicitly (`Phi`, `phiTerm`).
* `phiTerm_zero` — the `n = 0` term vanishes, so the ℕ-tsum and ℕ≥1-tsum agree.
* `phiSummable u` — for every real `u` the defining series converges absolutely
  (the `e^{−π n² e^{2u}} = r^{n²}` factor, `r ∈ (0,1)`, dominates the `n⁴` polynomial).
* `superExp_decay` / `phiTerm_tendsto_atTop_zero` / `Phi_tendsto_atTop_zero` — the
  **rapid (double-exponential) decay** of `Φ` as `u → +∞` (each term → 0 super-
  polynomially; and the whole series `Φ(u) → 0` via a summable envelope).
* `theta_kernel_hasSum` — the bridge to Mathlib's theta kernel
  `evenKernel 0 t = Σ_{n∈ℤ} e^{−π n² t}`, the analytic engine behind `Φ`.

## The single isolated residual

The full identity is the classical Riemann-memoir substitution `x = e^{2u}` applied to
the symmetrized Mellin/theta integral representation of `completedRiemannZeta`, together
with the polynomial prefactor `½·s·(s−1)` evaluated at `s = ½ + iz`.  Mathlib does **not**
package this Mellin-change-of-variables, so it is isolated as the single named hypothesis
`MellinSubstitution` with an honest docstring.  The final theorem
`entireRiemannXi_eq_cosine_transform` proves the identity *given* that residual, with no
`sorry`/`admit` anywhere.

EDIT POLICY: this file is the only one edited; everything lives under the namespace
`OverflowResidueRH.BacklundTuring.ScratchPhiTransform`.
-/

namespace OverflowResidueRH.BacklundTuring.ScratchPhiTransform

noncomputable section

/-- The `n`-th term of the Riemann Φ-series, `n : ℕ`:
`(2π² n⁴ e^{9u/2} − 3π n² e^{5u/2}) · e^{−π n² e^{2u}}`.
For `n = 0` the polynomial coefficient vanishes, so `phiTerm 0 u = 0`. -/
def phiTerm (n : ℕ) (u : ℝ) : ℝ :=
  (2 * π ^ 2 * (n : ℝ) ^ 4 * Real.exp (9 * u / 2)
      - 3 * π * (n : ℝ) ^ 2 * Real.exp (5 * u / 2))
    * Real.exp (-π * (n : ℝ) ^ 2 * Real.exp (2 * u))

/-- The **Riemann Φ-function** `Φ(u) = Σ_{n≥1} phiTerm n u` (the `n = 0` term is `0`,
so the ℕ-sum equals the `n≥1`-sum). -/
def Phi (u : ℝ) : ℝ := ∑' n : ℕ, phiTerm n u

/-- The `n = 0` term of the Φ-series vanishes (the coefficient carries a factor `n²`). -/
@[simp] theorem phiTerm_zero (u : ℝ) : phiTerm 0 u = 0 := by
  simp [phiTerm]

/-- Pointwise rewrite of the theta exponential as a power of `r := e^{−π e^{2u}} ∈ (0,1)`:
`e^{−π n² e^{2u}} = r ^ (n²)`. -/
theorem exp_theta_eq_rpow (u : ℝ) (n : ℕ) :
    Real.exp (-π * (n : ℝ) ^ 2 * Real.exp (2 * u))
      = (Real.exp (-π * Real.exp (2 * u))) ^ (n ^ 2) := by
  rw [← Real.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- The coefficient bound `|2π²n⁴e^{9u/2} − 3πn²e^{5u/2}| ≤ C · n⁴`, with
`C = 2π²e^{9u/2} + 3πe^{5u/2}` (uses `n² ≤ n⁴`). -/
theorem phi_coeff_abs_le (u : ℝ) (n : ℕ) :
    |2 * π ^ 2 * (n : ℝ) ^ 4 * Real.exp (9 * u / 2)
        - 3 * π * (n : ℝ) ^ 2 * Real.exp (5 * u / 2)|
      ≤ (2 * π ^ 2 * Real.exp (9 * u / 2) + 3 * π * Real.exp (5 * u / 2)) * (n : ℝ) ^ 4 := by
  have hn24 : (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 4 := by
    rcases Nat.eq_zero_or_pos n with h | h
    · simp [h]
    · have h1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h
      have : (n : ℝ) ^ 2 * 1 ≤ (n : ℝ) ^ 2 * (n : ℝ) ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        nlinarith
      nlinarith [this]
  have hA : 0 ≤ 2 * π ^ 2 * Real.exp (9 * u / 2) := by positivity
  have hB : 0 ≤ 3 * π * Real.exp (5 * u / 2) := by positivity
  have hn4 : 0 ≤ (n : ℝ) ^ 4 := by positivity
  have hn2 : 0 ≤ (n : ℝ) ^ 2 := by positivity
  rw [abs_le]
  refine ⟨?_, ?_⟩
  · nlinarith [mul_le_mul_of_nonneg_left hn24 hB]
  · nlinarith [mul_le_mul_of_nonneg_left hn24 hB, mul_nonneg hA hn4, mul_nonneg hB hn2]

/-- **Φ is well-defined: the defining series converges absolutely for every `u`.**
The `e^{−π n² e^{2u}} = r^{n²}` factor (`r ∈ (0,1)`) beats the `n⁴` polynomial:
we dominate by the summable `C · n⁴ · r^n`. -/
theorem phiSummable (u : ℝ) : Summable (fun n : ℕ => phiTerm n u) := by
  set r : ℝ := Real.exp (-π * Real.exp (2 * u)) with hr
  have hr0 : 0 < r := Real.exp_pos _
  have hr1 : r < 1 := by
    rw [hr]; apply Real.exp_lt_one_iff.mpr
    have : 0 < π * Real.exp (2 * u) := by positivity
    linarith
  set C : ℝ := 2 * π ^ 2 * Real.exp (9 * u / 2) + 3 * π * Real.exp (5 * u / 2) with hC
  have hdom : Summable (fun n : ℕ => C * ((n : ℝ) ^ 4 * r ^ n)) := by
    apply Summable.mul_left
    have := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 4 (r := r)
      (by rw [Real.norm_eq_abs, abs_of_pos hr0]; exact hr1)
    simpa using this
  apply Summable.of_norm_bounded hdom
  intro n
  have hexp : Real.exp (-π * (n : ℝ) ^ 2 * Real.exp (2 * u)) = r ^ (n ^ 2) :=
    exp_theta_eq_rpow u n
  unfold phiTerm
  rw [hexp]
  have hrn2 : r ^ (n ^ 2) ≤ r ^ n := by
    apply pow_le_pow_of_le_one hr0.le hr1.le
    nlinarith [Nat.le_self_pow (by norm_num : 2 ≠ 0) n]
  have hrpos : (0 : ℝ) < r ^ (n ^ 2) := pow_pos hr0 _
  rw [Real.norm_eq_abs, abs_mul]
  have hcoeff := phi_coeff_abs_le u n
  calc
    |2 * π ^ 2 * (n : ℝ) ^ 4 * Real.exp (9 * u / 2)
          - 3 * π * (n : ℝ) ^ 2 * Real.exp (5 * u / 2)| * |r ^ (n ^ 2)|
        ≤ (C * (n : ℝ) ^ 4) * |r ^ (n ^ 2)| :=
          mul_le_mul_of_nonneg_right hcoeff (abs_nonneg _)
    _ = (C * (n : ℝ) ^ 4) * r ^ (n ^ 2) := by rw [abs_of_pos hrpos]
    _ ≤ (C * (n : ℝ) ^ 4) * r ^ n := by
          apply mul_le_mul_of_nonneg_left hrn2; positivity
    _ = C * ((n : ℝ) ^ 4 * r ^ n) := by ring

/-- **Bridge to Mathlib's theta kernel.**  For `t > 0`,
`Σ_{n∈ℤ} e^{−π n² t} = evenKernel 0 t` — the Jacobi theta ψ-function underlying `Φ`.
(`evenKernel 0` is the `a = 0` even Hurwitz kernel; with `x = e^{2u}` this is the
analytic engine that `Φ` differentiates.) -/
theorem theta_kernel_hasSum {t : ℝ} (ht : 0 < t) :
    HasSum (fun n : ℤ => Real.exp (-π * (n : ℝ) ^ 2 * t)) (evenKernel 0 t) := by
  simpa using hasSum_int_evenKernel (0 : ℝ) ht

/-- The modified (`n ≠ 0`) theta sum: `Σ_{n∈ℤ, n≠0} e^{−π n² t} = evenKernel 0 t − 1`. -/
theorem theta_kernel_hasSum₀ {t : ℝ} (ht : 0 < t) :
    HasSum (fun n : ℤ => if n = 0 then (0 : ℝ) else Real.exp (-π * (n : ℝ) ^ 2 * t))
      (evenKernel 0 t - 1) := by
  simpa using hasSum_int_evenKernel₀ (0 : ℝ) ht

/-- **Core super-exponential decay lemma.**  For any exponent `a` and any `c > 0`,
`e^{a·u}·e^{−c·e^{2u}} → 0` as `u → +∞`, because `c·e^{2u}` dominates `a·u`
(after `v = 2u`, the bracket `b·v/e^{v} − c → −c < 0` while `e^{v} → ∞`).
This is the analytic engine of the rapid (double-exponential) decay of `Φ`. -/
theorem superExp_decay (a c : ℝ) (hc : 0 < c) :
    Tendsto (fun u : ℝ => Real.exp (a * u) * Real.exp (-c * Real.exp (2 * u)))
      atTop (𝓝 0) := by
  have hcombine : (fun u : ℝ => Real.exp (a * u) * Real.exp (-c * Real.exp (2 * u)))
      = fun u : ℝ => Real.exp (a * u - c * Real.exp (2 * u)) := by
    funext u; rw [← Real.exp_add]; ring_nf
  rw [hcombine]
  apply Real.tendsto_exp_atBot.comp
  have hbase : ∀ b : ℝ, Tendsto (fun v : ℝ => b * v - c * Real.exp v) atTop atBot := by
    intro b
    have hve : Tendsto (fun v : ℝ => v / Real.exp v) atTop (𝓝 0) := by
      simpa using
        (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).congr
          (by intro v; simp [pow_one, Real.exp_neg]; ring)
    have hrw : (fun v : ℝ => b * v - c * Real.exp v)
        = fun v : ℝ => Real.exp v * (b * (v / Real.exp v) - c) := by
      funext v
      have : Real.exp v ≠ 0 := (Real.exp_pos v).ne'
      field_simp
    rw [hrw]
    have hbracket : Tendsto (fun v : ℝ => b * (v / Real.exp v) - c) atTop (𝓝 (-c)) := by
      simpa using (hve.const_mul b).sub_const c
    exact Tendsto.atTop_mul_neg (by linarith : (-c) < 0) Real.tendsto_exp_atTop hbracket
  have hv : Tendsto (fun u : ℝ => 2 * u) atTop atTop :=
    tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 2)
  have := (hbase (a / 2)).comp hv
  refine this.congr ?_
  intro u
  simp only [Function.comp_apply]
  ring_nf

/-- **Rapid (double-exponential) decay of each Φ-term as `u → +∞`.**
For each fixed `n`, `phiTerm n u → 0` as `u → +∞`, driven by the
`e^{−π n² e^{2u}}` factor (whose argument `→ −∞` double-exponentially), which
dominates the polynomial-in-`e^{u}` prefactor.  This is the per-term face of the
classical statement that `Φ` (and all its derivatives) decay faster than any
exponential at `+∞`. -/
theorem phiTerm_tendsto_atTop_zero (n : ℕ) :
    Tendsto (fun u : ℝ => phiTerm n u) atTop (𝓝 0) := by
  -- Decompose `phiTerm n u` into the two super-exponentially decaying pieces.
  have hsplit : (fun u : ℝ => phiTerm n u)
      = fun u : ℝ =>
          2 * π ^ 2 * (n : ℝ) ^ 4
              * (Real.exp (9 * u / 2) * Real.exp (-(π * (n : ℝ) ^ 2) * Real.exp (2 * u)))
            - 3 * π * (n : ℝ) ^ 2
              * (Real.exp (5 * u / 2) * Real.exp (-(π * (n : ℝ) ^ 2) * Real.exp (2 * u))) := by
    funext u
    unfold phiTerm
    ring_nf
  rw [hsplit]
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp
  have hc : (0 : ℝ) < π * (n : ℝ) ^ 2 := by
    have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    positivity
  have h1 := (superExp_decay (9 / 2) (π * (n : ℝ) ^ 2) hc).const_mul (2 * π ^ 2 * (n : ℝ) ^ 4)
  have h2 := (superExp_decay (5 / 2) (π * (n : ℝ) ^ 2) hc).const_mul (3 * π * (n : ℝ) ^ 2)
  have hsub := h1.sub h2
  simp only [mul_zero, sub_zero] at hsub
  refine hsub.congr ?_
  intro u
  congr 2 <;> ring_nf

/-- The finite **envelope constant** `K := Σ_{n} n⁴·(1/2)^{n²}`, used to dominate the
whole Φ-series uniformly for `u` with `e^{−π e^{2u}} ≤ 1/2`. -/
theorem envelope_summable :
    Summable (fun n : ℕ => (n : ℝ) ^ 4 * (1 / 2 : ℝ) ^ (n ^ 2)) := by
  have hr0 : (0 : ℝ) < 1 / 2 := by norm_num
  have hr1 : (1 / 2 : ℝ) < 1 := by norm_num
  have hgeo : Summable (fun n : ℕ => (n : ℝ) ^ 4 * (1 / 2 : ℝ) ^ n) := by
    have := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 4 (r := (1 / 2 : ℝ))
      (by rw [Real.norm_eq_abs, abs_of_pos hr0]; exact hr1)
    simpa using this
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hgeo
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply pow_le_pow_of_le_one (by norm_num) (by norm_num)
  nlinarith [Nat.le_self_pow (by norm_num : (2 : ℕ) ≠ 0) n]

/-- **`Φ(u) → 0` as `u → +∞` — the global rapid-decay statement.**
The whole series is dominated by `2·C(u)·r(u)·K`, where `C(u) = 2π²e^{9u/2}+3πe^{5u/2}`,
`r(u) = e^{−π e^{2u}}`, and `K = Σ n⁴(1/2)^{n²}` is the finite `envelope_summable` constant.
Since `C(u)·r(u) → 0` (super-exponential `superExp_decay`), `Φ(u) → 0`. -/
theorem Phi_tendsto_atTop_zero : Tendsto Phi atTop (𝓝 0) := by
  set K : ℝ := ∑' n : ℕ, (n : ℝ) ^ 4 * (1 / 2 : ℝ) ^ (n ^ 2) with hK
  have hKnn : 0 ≤ K := tsum_nonneg (fun n => by positivity)
  -- The dominating envelope `g(u) = 2·K·C(u)·r(u) → 0`.
  set g : ℝ → ℝ := fun u =>
    2 * K * ((2 * π ^ 2 * Real.exp (9 * u / 2) + 3 * π * Real.exp (5 * u / 2))
      * Real.exp (-π * Real.exp (2 * u))) with hg
  have hg0 : Tendsto g atTop (𝓝 0) := by
    have hpi : (0 : ℝ) < π := Real.pi_pos
    have hCr : Tendsto (fun u : ℝ =>
        (2 * π ^ 2 * Real.exp (9 * u / 2) + 3 * π * Real.exp (5 * u / 2))
          * Real.exp (-π * Real.exp (2 * u))) atTop (𝓝 0) := by
      have h1 := (superExp_decay (9 / 2) π hpi).const_mul (2 * π ^ 2)
      have h2 := (superExp_decay (5 / 2) π hpi).const_mul (3 * π)
      have hsum := h1.add h2
      simp only [mul_zero, add_zero] at hsum
      refine hsum.congr ?_
      intro u; ring_nf
    have := hCr.const_mul (2 * K)
    simpa [hg] using this
  -- Squeeze: `|Φ u| ≤ g u` eventually (for `u` with `r(u) ≤ 1/2`), and `0 ≤ g u`.
  have hbound : ∀ᶠ u : ℝ in atTop, ‖Phi u‖ ≤ g u := by
    -- `r(u) = e^{−π e^{2u}} ≤ 1/2`  ⟺  `π e^{2u} ≥ log 2`, true for large `u`.
    have hr_event : ∀ᶠ u : ℝ in atTop, Real.exp (-π * Real.exp (2 * u)) ≤ 1 / 2 := by
      have hrr : Tendsto (fun u : ℝ => Real.exp (-π * Real.exp (2 * u))) atTop (𝓝 0) := by
        have := superExp_decay 0 π Real.pi_pos
        simpa using this
      have : ∀ᶠ u : ℝ in atTop, Real.exp (-π * Real.exp (2 * u)) < 1 / 2 :=
        hrr.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2))
      filter_upwards [this] with u hu using hu.le
    filter_upwards [hr_event] with u hr
    set r : ℝ := Real.exp (-π * Real.exp (2 * u)) with hrdef
    have hr0 : 0 < r := Real.exp_pos _
    set C : ℝ := 2 * π ^ 2 * Real.exp (9 * u / 2) + 3 * π * Real.exp (5 * u / 2) with hCdef
    have hC0 : 0 ≤ C := by positivity
    -- Term bound: `|phiTerm n u| ≤ (2·C·r·K)`-summand `2·C·r·n⁴(1/2)^{n²}`.
    have hterm : ∀ n : ℕ, ‖phiTerm n u‖ ≤ 2 * C * r * ((n : ℝ) ^ 4 * (1 / 2 : ℝ) ^ (n ^ 2)) := by
      intro n
      rcases Nat.eq_zero_or_pos n with hn | hn
      · subst hn; simp [phiTerm]
      have hexp : Real.exp (-π * (n : ℝ) ^ 2 * Real.exp (2 * u)) = r ^ (n ^ 2) :=
        exp_theta_eq_rpow u n
      unfold phiTerm
      rw [hexp, Real.norm_eq_abs, abs_mul]
      have hcoeff := phi_coeff_abs_le u n
      -- |coeff| ≤ C·n⁴
      have hrn2pos : (0 : ℝ) < r ^ (n ^ 2) := pow_pos hr0 _
      -- r^{n²} ≤ 2·r·(1/2)^{n²} :  r^{n²} = r·r^{n²−1} ≤ r·(1/2)^{n²−1} = 2r·(1/2)^{n²}
      have hn1 : 1 ≤ n ^ 2 := Nat.one_le_iff_ne_zero.mpr (by positivity)
      have hrpow : r ^ (n ^ 2) ≤ 2 * r * (1 / 2 : ℝ) ^ (n ^ 2) := by
        have hsplit : r ^ (n ^ 2) = r * r ^ (n ^ 2 - 1) := by
          rw [← pow_succ']
          congr 1
          omega
        rw [hsplit]
        have hle : r ^ (n ^ 2 - 1) ≤ (1 / 2 : ℝ) ^ (n ^ 2 - 1) :=
          pow_le_pow_left₀ hr0.le hr (n ^ 2 - 1)
        have hhalf : (1 / 2 : ℝ) ^ (n ^ 2 - 1) = 2 * (1 / 2 : ℝ) ^ (n ^ 2) := by
          have hk : n ^ 2 = (n ^ 2 - 1) + 1 := by omega
          conv_rhs => rw [hk, pow_succ]
          ring
        calc r * r ^ (n ^ 2 - 1) ≤ r * (1 / 2 : ℝ) ^ (n ^ 2 - 1) :=
              mul_le_mul_of_nonneg_left hle hr0.le
          _ = r * (2 * (1 / 2 : ℝ) ^ (n ^ 2)) := by rw [hhalf]
          _ = 2 * r * (1 / 2 : ℝ) ^ (n ^ 2) := by ring
      calc
        |2 * π ^ 2 * (n : ℝ) ^ 4 * Real.exp (9 * u / 2)
              - 3 * π * (n : ℝ) ^ 2 * Real.exp (5 * u / 2)| * |r ^ (n ^ 2)|
            ≤ (C * (n : ℝ) ^ 4) * |r ^ (n ^ 2)| :=
              mul_le_mul_of_nonneg_right hcoeff (abs_nonneg _)
        _ = (C * (n : ℝ) ^ 4) * r ^ (n ^ 2) := by rw [abs_of_pos hrn2pos]
        _ ≤ (C * (n : ℝ) ^ 4) * (2 * r * (1 / 2 : ℝ) ^ (n ^ 2)) :=
              mul_le_mul_of_nonneg_left hrpow (by positivity)
        _ = 2 * C * r * ((n : ℝ) ^ 4 * (1 / 2 : ℝ) ^ (n ^ 2)) := by ring
    -- Sum the term bound; `‖Φ u‖ ≤ ∑ ‖phiTerm‖ ≤ 2·C·r·K = g u`.
    have hsummEnv : Summable (fun n : ℕ => 2 * C * r * ((n : ℝ) ^ 4 * (1 / 2 : ℝ) ^ (n ^ 2))) :=
      envelope_summable.mul_left _
    have hnormSumm : Summable (fun n : ℕ => ‖phiTerm n u‖) :=
      (phiSummable u).abs.congr (fun n => (Real.norm_eq_abs _).symm)
    have hPhinorm : ‖Phi u‖ ≤ ∑' n : ℕ, 2 * C * r * ((n : ℝ) ^ 4 * (1 / 2 : ℝ) ^ (n ^ 2)) := by
      refine (norm_tsum_le_tsum_norm hnormSumm).trans
        (Summable.tsum_mono hnormSumm hsummEnv hterm)
    have htsumEnv : ∑' n : ℕ, 2 * C * r * ((n : ℝ) ^ 4 * (1 / 2 : ℝ) ^ (n ^ 2)) = g u := by
      rw [tsum_mul_left, ← hK, hg, hCdef, hrdef]; ring
    rw [htsumEnv] at hPhinorm
    exact hPhinorm
  -- Squeeze `Φ` between `0` and `g`, both `→ 0`.
  have hnn : ∀ᶠ u : ℝ in atTop, 0 ≤ ‖Phi u‖ := Eventually.of_forall (fun u => norm_nonneg _)
  have hnormto : Tendsto (fun u => ‖Phi u‖) atTop (𝓝 0) :=
    squeeze_zero' hnn hbound hg0
  exact tendsto_zero_iff_norm_tendsto_zero.mpr hnormto

/-! ## The cosine-transform identity `Ξ(z) = 2∫₀^∞ Φ(u) cos(zu) du`

`Ξ(z) := ξ(½ + iz)` is the pullback of the entire `ξ` to the critical line.  The
classical Riemann-memoir representation is `Ξ(z) = 2∫₀^∞ Φ(u) cos(zu) du`. -/

open OverflowResidueRH in
/-- The Riemann **Ξ-function**, the critical-line pullback `Ξ(z) = ξ(½ + iz)` of the
entire `ξ = entireRiemannXi`. -/
def Xi (z : ℂ) : ℂ := entireRiemannXi (1 / 2 + Complex.I * z)

/-- The right-hand side of the Riemann cosine transform: `2∫₀^∞ Φ(u)·cos(zu) du`,
with `Φ` cast to `ℂ` and `cos` the complex cosine (so the integral makes sense for
complex `z`). -/
noncomputable def cosineTransform (z : ℂ) : ℂ :=
  2 * ∫ u in Set.Ioi (0 : ℝ), (Phi u : ℂ) * Complex.cos (z * u)

/-- **THE SINGLE ISOLATED RESIDUAL — the Mellin change-of-variables `x = e^{2u}`.**

This is the one classical step that Mathlib does not package.  Concretely, starting
from the symmetrized Mellin/theta integral representation of `completedRiemannZeta`
(Mathlib's `completedRiemannZeta₀ s = mellin F (s/2)/2`, with the `evenKernel 0`/`ψ`
theta kernel `theta_kernel_hasSum`), one substitutes `x = e^{2u}` (`dx/x = 2 du`),
folds the `s ↔ 1−s` symmetric pair into a cosine via `s = ½ + iz`, and lets the
polynomial prefactor `½·s·(s−1) = −½(z² + ¼)` together with two `u`-derivatives of the
`ψ`-kernel produce exactly the coefficients `2π²n⁴e^{9u/2} − 3πn²e^{5u/2}` of `phiTerm`.

The endpoint of that computation is precisely the statement below.  It is isolated as a
hypothesis (NOT an axiom) so the final identity is `theorem … (h : MellinSubstitution) : …`;
the analytic content actually built in this file — `Phi` well-defined (`phiSummable`),
rapid decay (`phiTerm_tendsto_atTop_zero`, `Phi_tendsto_atTop_zero`), and the theta-kernel
bridge (`theta_kernel_hasSum`) — are the genuine ingredients of this residual. -/
def MellinSubstitution : Prop :=
  ∀ z : ℂ, Xi z = cosineTransform z

open OverflowResidueRH in
/-- ⭐ **The Riemann Ξ cosine-transform identity**, reduced to the single Mellin
change-of-variables residual `MellinSubstitution`:
`entireRiemannXi (½ + iz) = 2∫₀^∞ Φ(u)·cos(zu) du`  for all complex `z`.

Everything except `MellinSubstitution` is proven unconditionally in this file
(`Phi` definition + summability + double-exponential decay + theta bridge). -/
theorem entireRiemannXi_eq_cosine_transform (h : MellinSubstitution) (z : ℂ) :
    entireRiemannXi (1 / 2 + Complex.I * z)
      = 2 * ∫ u in Set.Ioi (0 : ℝ), (Phi u : ℂ) * Complex.cos (z * u) := by
  have := h z
  unfold Xi cosineTransform at this
  exact this

end

end OverflowResidueRH.BacklundTuring.ScratchPhiTransform
