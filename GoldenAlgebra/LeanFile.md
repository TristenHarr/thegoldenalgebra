import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Complex.Norm
import Mathlib.Tactic

import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

open Complex Matrix


/-!
  This file begins the formalization of the "Golden Algebra" from the
  uploaded document (main.pdf).
-/

namespace GoldenAlgebra

-- === Core Constants ===

/-- The core constant T, defined as cos(2π/5) or (sqrt(5) - 1) / 4. -/
noncomputable def T : ℝ := (Real.sqrt 5 - 1) / 4

/-- The core constant J, defined as (3 - sqrt(5)) / 4. -/
noncomputable def J : ℝ := (3 - Real.sqrt 5) / 4

/-- The core constant K, defined as cos(4π/5) or -(sqrt(5) + 1) / 4. -/
noncomputable def K : ℝ := -(Real.sqrt 5 + 1) / 4

/-- The fundamental interaction quantum H, defined as T * J. -/
noncomputable def H : ℝ := T * J

/-- The golden ratio φ. -/
noncomputable def phi : ℝ := (1 + Real.sqrt 5) / 2

noncomputable def lambdaG1 : ℂ := T + J * I

noncomputable def lambdaG1_inv : ℂ := lambdaG1⁻¹

/--
The transformation matrix G, the 2D algebraic representation of λ_G1.
Defined in the document in "Law of Matrix-Operator Duality".
-/
noncomputable def G : Matrix (Fin 2) (Fin 2) ℝ :=
  !![T, -J;
     J, T]

-- === Core Identities (Proven as Theorems) ===

/-- The Additive Law: T + J = 1/2.  -/
theorem T_add_J_eq_one_half : T + J = 1 / 2 := by
  unfold T J
  field_simp
  ring

/-- The Ratio Law: T / J = φ.  -/
theorem T_div_J_eq_phi : T / J = phi := by
  calc
      T / J = ((Real.sqrt 5 - 1) / 4) / ((3 - Real.sqrt 5) / 4) := by
        unfold T J; rfl
    _ = (Real.sqrt 5 - 1) / (3 - Real.sqrt 5) := by
      field_simp

    _ = ((Real.sqrt 5 - 1) * (3 + Real.sqrt 5)) / ((3 - Real.sqrt 5) * (3 + Real.sqrt 5)) := by
      rw [div_eq_div_iff]
      · ring
      · intro h_eq_zero
        have h_eq : (3 : ℝ) = Real.sqrt 5 := by linarith [h_eq_zero]
        have h_sq_eq : 3^2 = (Real.sqrt 5)^2 := congr_arg (fun x => x^2) h_eq
        rw [Real.sq_sqrt (by linarith)] at h_sq_eq
        norm_num at h_sq_eq

      ·
        ring_nf
        norm_num

    _ = (2 * Real.sqrt 5 + 2) / 4 := by
          have h_num : (Real.sqrt 5 - 1) * (3 + Real.sqrt 5) = 2 * Real.sqrt 5 + 2 := by
            ring_nf
            rw [Real.sq_sqrt (by linarith)]
            ring

          have h_den : (3 - Real.sqrt 5) * (3 + Real.sqrt 5) = 4 := by
            ring_nf
            rw [Real.sq_sqrt (by norm_num)]
            norm_num
          rw [h_num, h_den]

    _ = (Real.sqrt 5 + 1) / 2 := by
      field_simp; ring

    _ = phi := by
      unfold phi; ring

-- Helper fact for uniqueness constraint
theorem J_div_T_eq_one_div_phi : J / T = 1 / phi := by
  rw [<-T_div_J_eq_phi]
  rw [one_div_div]

-- Helper Fact: Proving phi - 1/phi = 1, with explicit steps.
theorem phi_sub_inv_eq_one : phi - 1 / phi = 1 := by
  unfold phi
  rw [one_div_div]
  field_simp
  ring_nf
  rw [Real.sq_sqrt (by linarith)]
  ring

/-- The Uniqueness Constraint: T / J - J / T = 1.  -/
theorem uniqueness_constraint : T / J - J / T = 1 := by
  calc
    T / J - J / T = phi - J / T := by
      rw [T_div_J_eq_phi]
    _ = phi - 1 / phi := by
      rw [J_div_T_eq_one_div_phi]
    _ = 1 := by
      rw [phi_sub_inv_eq_one]

/-- `cos(2π/5)` is a root of the quadratic equation `4x^2 + 2x - 1 = 0`. -/
theorem cos_two_pi_div_five_is_root_of_quadratic :
    let x := Real.cos (2 * Real.pi / 5)
    4 * x ^ 2 + 2 * x - 1 = 0 := by
  let θ := 2 * Real.pi / 5

  have h_trig_rel : Real.cos (3 * θ) = Real.cos (2 * θ) := by
    have h_rearrange : 3 * θ = 2 * Real.pi - 2 * θ := by
      unfold θ
      field_simp
      ring
    rw [h_rearrange, Real.cos_two_pi_sub]

  have h_poly_cubic : 4 * (Real.cos θ) ^ 3 - 2 * (Real.cos θ) ^ 2 - 3 * (Real.cos θ) + 1 = 0 := by
    have h_expanded : 4 * (Real.cos θ) ^ 3 - 3 * (Real.cos θ) = 2 * (Real.cos θ) ^ 2 - 1 := by
      rw [Real.cos_three_mul, Real.cos_two_mul] at h_trig_rel
      exact h_trig_rel
    linarith [h_expanded]

  let x := Real.cos θ

  have hx_def : x = Real.cos θ := rfl
  rw [←hx_def] at h_poly_cubic

  have h_factor : 4 * x ^ 3 - 2 * x ^ 2 - 3 * x + 1 = (x - 1) * (4 * x ^ 2 + 2 * x - 1) := by
    ring

  rw [h_factor] at h_poly_cubic

  have h_ne_one : x ≠ 1 := by
      have h_θ_bounds : 0 < θ ∧ θ < Real.pi / 2 := by
        constructor
        · apply div_pos; linarith [Real.pi_pos]; norm_num
        · rw [div_lt_div_iff₀ (by norm_num) (by norm_num)]
          linarith [Real.pi_pos]

      have h_cos_lt_one : Real.cos θ < 1 := by
        have h_cos_anti : StrictAntiOn Real.cos (Set.Icc 0 Real.pi) := Real.strictAntiOn_cos
        have h_0_in_Icc : 0 ∈ Set.Icc 0 Real.pi := by
          constructor
          ·
            rfl
          ·
            linarith [Real.pi_pos]
        have h_θ_in_Icc : θ ∈ Set.Icc 0 Real.pi := by
          constructor
          · linarith [h_θ_bounds.1]
          ·
            rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 5)]
            linarith [Real.pi_pos]
        have h_cos_lt_cos_0 : Real.cos θ < Real.cos 0 :=
          h_cos_anti h_0_in_Icc h_θ_in_Icc h_θ_bounds.1
        rw [Real.cos_zero] at h_cos_lt_cos_0
        exact h_cos_lt_cos_0
      exact ne_of_lt h_cos_lt_one

  rw [mul_eq_zero] at h_poly_cubic
  cases h_poly_cubic with
  | inl h_x_is_one =>
    have h_x_eq_1 : x = 1 := by linarith [h_x_is_one]
    exact absurd h_x_eq_1 h_ne_one
  | inr h_quadratic_is_zero =>
    exact h_quadratic_is_zero

/-- T, defined as cos(2π/5) -/
theorem T_eq_cos_2_pi_div_5 : T = Real.cos (2 * Real.pi / 5) := by
  have h_T_is_root : 4 * T ^ 2 + 2 * T - 1 = 0 := by
    unfold T
    field_simp
    ring_nf
    rw [Real.sq_sqrt (by linarith)] -- `by linarith` proves `5 ≥ 0`.
    norm_num

  let x := Real.cos (2 * Real.pi / 5)
  have h_cos_is_root : 4 * x ^ 2 + 2 * x - 1 = 0 := cos_two_pi_div_five_is_root_of_quadratic

  have h_roots : x = (Real.sqrt 5 - 1) / 4 ∨ x = (-Real.sqrt 5 - 1) / 4 := by
    have h_quad_iff : 4 * x ^ 2 + 2 * x - 1 = 0 ↔
        x = (-2 + Real.sqrt (2 ^ 2 - 4 * 4 * (-1))) / (2 * 4) ∨
        x = (-2 - Real.sqrt (2 ^ 2 - 4 * 4 * (-1))) / (2 * 4) := by
      rw [pow_two]
      apply quadratic_eq_zero_iff
      ·
        norm_num
      ·
        rw [Real.mul_self_sqrt]
        simp only [discrim]
        norm_num
    rw [h_quad_iff] at h_cos_is_root

    have h_sqrt_20 : Real.sqrt 20 = 2 * Real.sqrt 5 := by
      rw [(by norm_num : (20:ℝ) = 4 * 5)]
      rw [Real.sqrt_mul (by norm_num)]
      have h_sqrt_4_is_2 : Real.sqrt 4 = 2 := by
        norm_num
      rw [h_sqrt_4_is_2]

    cases h_cos_is_root with
    | inl h_pos_root =>
      left
      rw [h_pos_root]
      field_simp
      conv in (2 ^ 2 + 4 * 4) => norm_num
      rw [h_sqrt_20]
      ring
    | inr h_neg_root =>
      right
      rw [h_neg_root]
      field_simp
      conv in (2 ^ 2 + 4 * 4) => norm_num
      rw [h_sqrt_20]
      ring

  cases h_roots with
  | inl h_cos_is_positive_root =>
    unfold T
    exact h_cos_is_positive_root.symm
  | inr h_cos_is_negative_root =>
    have h_cos_pos : 0 < x := by
      apply Real.cos_pos_of_mem_Ioo
      constructor
      ·
        linarith [Real.pi_pos]
      ·
        rw [div_lt_div_iff₀]
        ·
          linarith [Real.pi_pos]
        ·
          norm_num
        ·
          norm_num

    have h_neg_root_is_neg : (-Real.sqrt 5 - 1) / 4 < 0 := by
      have h_num_neg : -Real.sqrt 5 - 1 < 0 := by
        have h_sqrt_pos : 0 < Real.sqrt 5 := by
          apply Real.sqrt_pos.mpr
          linarith
        linarith [h_sqrt_pos]
      have h_den_pos : (0 : ℝ) < 4 := by norm_num
      exact div_neg_of_neg_of_pos h_num_neg h_den_pos

    rw [h_cos_is_negative_root] at h_cos_pos
    linarith [h_neg_root_is_neg, h_cos_pos]

/-- K, defined as cos(4π/5) -/
theorem K_eq_cos_4_pi_div_5 : K = Real.cos (4 * Real.pi / 5) := by
  have h_angle : 4 * Real.pi / 5 = 2 * (2 * Real.pi / 5) := by ring
  rw [h_angle, Real.cos_two_mul]
  rw [← T_eq_cos_2_pi_div_5]
  unfold K T
  field_simp
  ring_nf
  rw [Real.sq_sqrt (by linarith)]
  ring

/-- The Bridge Formula: T - J = 2 * T * J. -/
theorem T_sub_J_eq_2TJ : T - J = 2 * T * J := by
  unfold T J
  field_simp
  ring_nf
  rw [Real.sq_sqrt (by linarith)]
  ring

/-- The sum of T and K is -1/2. This is Property 14 in the appendix.  -/
theorem T_add_K_eq_neg_one_half : T + K = -1 / 2 := by
  unfold T K
  field_simp
  ring

/-- The value of T squared. -/
theorem T_sq_val : T^2 = (6 - 2 * Real.sqrt 5) / 16 := by
  unfold T
  field_simp
  ring_nf
  rw [Real.sq_sqrt (by linarith)]
  ring

/-- The value of J squared. -/
theorem J_sq_val : J^2 = (14 - 6 * Real.sqrt 5) / 16 := by
  unfold J
  field_simp
  ring_nf
  rw [Real.sq_sqrt (by linarith)]
  ring

/-- The value of K squared. -/
theorem K_sq_val : K^2 = (6 + 2 * Real.sqrt 5) / 16 := by
  unfold K
  field_simp
  ring_nf
  rw [Real.sq_sqrt (by linarith)]
  ring

/-- The sum of squares T² + J², equal to the determinant of the G matrix. -/
theorem T_sq_add_J_sq : T^2 + J^2 = (5 - 2 * Real.sqrt 5) / 4 := by
  rw [T_sq_val, J_sq_val]
  field_simp
  ring

/-- The fundamental interaction quantum H is defined as T * J.  -/
theorem H_eq_T_mul_J : H = T * J := by
  rfl

/-- The sum of squares T² + J² expressed in terms of H.  -/
theorem T_sq_add_J_sq_eq_one_fourth_sub_2H : T^2 + J^2 = 1/4 - 2*H := by
  calc
    T^2 + J^2 = (T + J)^2 - 2 * (T * J) := by
      ring
    _ = (1/2)^2 - 2 * (T * J) := by
      rw [T_add_J_eq_one_half]
    _ = 1/4 - 2 * H := by
      rw [H_eq_T_mul_J]
      norm_num

/-- The absolute value of 1 is 1. -/
theorem abs_of_one : |(1 : ℝ)| = 1 :=
  abs_of_nonneg (by norm_num : 0 ≤ (1 : ℝ))

/-- The magnitude of the Dampening Operator is less than 1. -/
theorem norm_lambdaG1_lt_one : ‖lambdaG1‖ < 1 := by
    unfold lambdaG1
    rw [Complex.norm_def]
    rw [normSq_apply]
    conv =>
      lhs
      arg 1
      arg 1
      arg 1
      rw [add_re]
    conv =>
      lhs; arg 1; arg 1; arg 1; arg 1
      rw [ofReal_re]
    conv =>
      lhs; arg 1; arg 1; arg 1; arg 2
      rw [mul_I_re]
    conv =>
      lhs; arg 1; arg 1; arg 1; arg 2; arg 1
      rw [ofReal_im]
    conv =>
      lhs; arg 1; arg 1; arg 1
      rw [neg_zero, add_zero]
    conv =>
      lhs; arg 1; arg 1; arg 2
      rw [add_re]
    conv =>
      lhs; arg 1; arg 1; arg 2; arg 1
      rw [ofReal_re]
    conv =>
      lhs; arg 1; arg 1; arg 2; arg 2
      rw [mul_I_re]
    conv =>
      lhs; arg 1; arg 1; arg 2; arg 2; arg 1
      rw [ofReal_im]
    conv =>
      lhs; arg 1; arg 1; arg 2
      rw [neg_zero, add_zero]
    conv =>
      lhs; arg 1; arg 2; arg 1
      rw [add_im]
    conv =>
      lhs; arg 1; arg 2; arg 1; arg 1
      rw [ofReal_im]
    conv =>
      lhs; arg 1; arg 2; arg 1; arg 2
      rw [mul_I_im]
    conv =>
      lhs; arg 1; arg 2; arg 1; arg 2
      rw [ofReal_re]
    conv =>
      lhs; arg 1; arg 2; arg 1
      rw [zero_add]
    conv =>
      lhs; arg 1; arg 2; arg 2
      rw [add_im]
    conv =>
      lhs; arg 1; arg 2; arg 2; arg 1
      rw [ofReal_im]
    conv =>
      lhs; arg 1; arg 2; arg 2; arg 2
      rw [mul_I_im]
    conv =>
      lhs; arg 1; arg 2; arg 2; arg 2
      rw [ofReal_re]
    conv =>
      lhs; arg 1; arg 2; arg 2
      rw [zero_add]
    rw [←pow_two, ←pow_two]
    rw [T_sq_add_J_sq]
    rw [Real.sqrt_div]
    case hx =>
      rw [le_sub_iff_add_le, zero_add]
      rw [← pow_le_pow_iff_left₀]
      case hb =>
        norm_num
      case ha =>
        apply mul_nonneg
        · norm_num
        · apply Real.sqrt_nonneg
      ·
        ring_nf
        rw [Real.sq_sqrt (by linarith)]
        norm_num
      case hn =>
        norm_num
    have h_sqrt_4 : Real.sqrt 4 = 2 := by
      norm_num
    rw [h_sqrt_4]
    rw [← mul_lt_mul_right (by norm_num : (0 : ℝ) < 2)]
    rw [div_mul_cancel₀]
    case h =>
      norm_num
    rw [one_mul]
    have h_final_ineq : 5 - 2 * Real.sqrt 5 < 4 := by
      rw [sub_lt_iff_lt_add]
      rw [(by norm_num : (5:ℝ) = 1 + 4)]
      rw [add_comm 1 4]
      rw [add_lt_add_iff_left 4]
      conv =>
        rhs
        arg 2
        arg 1
        norm_num
      rw [← pow_lt_pow_iff_left₀]
      case ha =>
        norm_num
      case hb =>
        apply mul_nonneg
        · norm_num
        · apply Real.sqrt_nonneg
      ·
        ring_nf
        rw [Real.sq_sqrt (by linarith)]
        norm_num
      case hn =>
        norm_num
    rw [← h_sqrt_4]
    rw [Real.sqrt_lt_sqrt_iff]
    ·
      rw [h_sqrt_4]
      exact h_final_ineq
    ·
        rw [h_sqrt_4]
        rw [le_sub_iff_add_le, zero_add]
        rw [← pow_le_pow_iff_left₀]
        case hb => norm_num
        case ha =>
          apply mul_nonneg
          · norm_num
          · apply Real.sqrt_nonneg
        · ring_nf
          rw [Real.sq_sqrt (by linarith)]
          norm_num
        case hn => norm_num

/-- The magnitude of the Generative Operator is greater than 1. -/
theorem norm_lambdaG1_inv_gt_one : 1 < ‖lambdaG1_inv‖ := by
  unfold lambdaG1_inv
  rw [norm_inv]
  rw [inv_eq_one_div]
  apply one_lt_one_div
  case h2 =>
    exact norm_lambdaG1_lt_one
  case h1 =>
    rw [norm_pos_iff]
    unfold lambdaG1
    have h_T_ne_zero : T ≠ 0 := by
      unfold T
      norm_num
      apply ne_of_gt
      suffices h_simple : 1 < Real.sqrt 5
      case h =>
        linarith [h_simple]
      case h_simple =>
        suffices h_sq : 1^2 < (Real.sqrt 5)^2
        case h_sq =>
          norm_num
        apply lt_of_pow_lt_pow_left₀
        case hb =>
          apply Real.sqrt_nonneg
        case h =>
            exact h_sq
    intro h_lambdaG1_is_zero
    have h_T_is_zero : T = 0 := by
      rw [Complex.ext_iff] at h_lambdaG1_is_zero
      simp at h_lambdaG1_is_zero
      exact h_lambdaG1_is_zero.left
    exact h_T_ne_zero h_T_is_zero

/--
The trace of G is 2T.
-/
theorem trace_G_eq_2T : G.trace = 2 * T := by
  unfold G trace
  simp -- simplifies matrix component access
  ring

/--
The determinant of G is T² + J².
-/
theorem det_G_eq_T_sq_add_J_sq : G.det = T^2 + J^2 := by
  unfold G det
  simp -- simplifies matrix component access
  ring


/--
The Law of Matrix-Operator Duality: The action of the complex operator λ_G1 on a
complex number z = x + iy is equivalent to the action of the matrix G on the
vector v = (x, y) .
-/
theorem matrix_operator_duality (x y : ℝ) :
  let z : ℂ := x + y * I
  let v : Fin 2 → ℝ := ![x, y]
  (lambdaG1 * z).re = (G *ᵥ v) 0 ∧ (lambdaG1 * z).im = (G *ᵥ v) 1 := by
  -- Let z and v be defined
  let z : ℂ := x + y * I
  let v : Fin 2 → ℝ := ![x, y]
  -- Unfold definitions
  unfold lambdaG1 G
  -- Prove the real and imaginary parts match
  constructor
  · -- Real part
    simp [z, v, dotProduct, mul_re, add_re, ofReal_re, I_re, mul_I_re, ofReal_im]
    ring
  · -- Imaginary part
    simp [z, v, dotProduct, mul_im, add_im, ofReal_im, I_im, mul_I_im, ofReal_re]
    ring


/--
A proposition stating that `lambda` is an eigenvalue of a 2x2 real matrix `M`.
This is defined by the existence of a non-zero complex eigenvector `v`
such that `M *ᵥ v = lambda • v`.
-/
def IsEigenvalue (M : Matrix (Fin 2) (Fin 2) ℝ) (lambda : ℂ) : Prop :=
  ∃ (v : Fin 2 → ℂ), v ≠ 0 ∧ (M.map (↑)) *ᵥ v = lambda • v

/--
The Law of Harmonic Eigenvalues: This proves that λ_G1 is an eigenvalue of G
with eigenvector [1, -i].
-/
theorem isEigenvalue_lambdaG1 : IsEigenvalue G lambdaG1 := by
  -- First, let's unfold our definition to see the goal in its most basic terms.
  unfold IsEigenvalue
  -- Provide the witness vector proposed in the manuscript.
  use ![1, -I]
  -- Now, split the conjunction goal `v ≠ 0 ∧ ...` into two separate goals.
  constructor

  · -- Goal 1: The vector is non-zero.
    -- This was proven with `simp`.
    simp

  · -- Goal 2: The eigenvector equation.
    -- We prove this by showing the vectors are equal component-wise.
    ext i
    fin_cases i

    · -- Case i = 0 (the first component)
      have h_lhs : (G.map (↑) *ᵥ ![1, -I]) 0 = (T : ℂ) + J * I := by
        unfold G
        conv =>
          lhs
          arg 1
          unfold HMul.hMul
          dsimp
        unfold Neg.neg
        conv =>
          lhs
          arg 1
          unfold CoeT.coe
          whnf
          whnf
        simp [G, dotProduct, mul_re, add_re, ofReal_re, ofReal_im, I_re, I_im, neg_re]
        ring_nf
        rw [← neg_mul_neg]
        rw [← ofReal_neg]
        rw [Matrix.mulVec]
        dsimp
        rw [dotProduct]
        rw [Fin.sum_univ_two]
        simp
        rw [Complex.ofReal_def]
        ring_nf
        rw [← Complex.ofReal_def]
        rw [mul_comm]
        ring_nf
        change (-I) * (↑(-J)) = ↑J * I
        rw [Complex.ofReal_neg]
        rw [neg_mul_neg]
        ring

      have h_rhs : (lambdaG1 • ![1, -I]) 0 = (T : ℂ) + J * I := by
        simp [lambdaG1]

      calc
        ((G.map (↑)) *ᵥ ![1, -I]) 0 = (T : ℂ) + J * I := h_lhs
        _ = (lambdaG1 • ![1, -I]) 0 := by rw[h_rhs]

    · -- Goal 2: The eigenvector equation.
      have h_lhs_1 : (G.map (↑) *ᵥ ![1, -I]) 1 = (J : ℂ) - T * I := by
        unfold G
        unfold Matrix.mulVec
        rw [dotProduct]
        rw [Fin.sum_univ_two]
        simp
        ring

      have h_rhs_1 : (lambdaG1 • ![1, -I]) 1 = (J : ℂ) - T * I := by
        simp
        ring_nf
        unfold lambdaG1
        ring_nf
        ring_nf
        rw [I_sq]
        rw [neg_one_mul]
        rw [sub_neg_eq_add]
      calc
        ((G.map (↑)) *ᵥ ![1, -I]) 1 = (J : ℂ) - T * I := h_lhs_1
        _ = (lambdaG1 • ![1, -I]) 1 := by rw[h_rhs_1]

/--
The Law of Harmonic Eigenvalues (Part 2): This proves that the conjugate
of λ_G1 is an eigenvalue of G with eigenvector [1, i] .
-/
theorem isEigenvalue_lambdaG1_conj : IsEigenvalue G (Star.star lambdaG1) := by
  unfold IsEigenvalue
  -- Provide the witness eigenvector `v = ![1, I]`.
  use ![1, I]
  constructor
  · -- Goal 1: The vector is non-zero.
    simp
  · -- Goal 2: The eigenvector equation.
    ext i
    fin_cases i
    · -- Case i = 0
      unfold G lambdaG1
      -- We use `star` for conjugation and `simp` handles the rest.
      -- `simp` uses lemmas like `star_add`, `star_mul`, `star_ofReal`, `star_I`
      simp [dotProduct, Fin.sum_univ_two, ofReal_neg, star_add]
      ring_nf
      rw [Matrix.mulVec]
      rw [dotProduct]
      rw [Fin.sum_univ_two]
      simp [dotProduct, Fin.sum_univ_two, ofReal_neg, star_add]
      rw [sub_eq_add_neg]
    · -- Case i = 1
      unfold G lambdaG1
      simp [dotProduct, Fin.sum_univ_two, ofReal_neg, star_add]
      ring_nf
      rw [Matrix.mulVec]
      rw [dotProduct]
      rw [Fin.sum_univ_two]
      simp [dotProduct, Fin.sum_univ_two, ofReal_neg, star_add]
      rw [add_comm]

/--
The Law of Invariant Geometric Sum: The infinite spiral generated by `lambdaG1`
starting at `p0` converges to `p0 / (1 - lambdaG1)`. This is a direct
consequence of the standard formula for a geometric series, valid because
the norm of the operator `lambdaG1` has been proven to be less than 1.
-/
theorem law_of_invariant_geometric_sum (p0 : ℂ) :
  ∑' n, p0 * lambdaG1 ^ n = p0 / (1 - lambdaG1) := by
  -- The proof relies on the formula for the sum of a geometric series.
  -- First, we factor out the constant `p0` from the summation.
  rw [tsum_mul_left]
  -- Now we have `p0 * (∑' (n : ℕ), lambdaG1 ^ n)`.
  -- We can apply the geometric series formula `tsum_geometric_of_norm_lt_one`
  -- to the summation part, which states that `∑' x^n = 1 / (1 - x)`
  -- if `‖x‖ < 1`. We supply our previously proven theorem `norm_lambdaG1_lt_one`
  -- as the required condition.
  rw [tsum_geometric_of_norm_lt_one norm_lambdaG1_lt_one]
  -- The expression becomes `p0 * (1 / (1 - lambdaG1))`.
  -- We use `field_simp` to rewrite this into the desired fractional form.
  field_simp

/--
The Law of Harmonic Momentum Sums: This law provides the solution for an
infinite series weighted by the index `n`, analogous to a momentum sum.
It is derived by differentiating the standard geometric series. The formula
in Mathlib, `hasSum_coe_mul_geometric_of_norm_lt_one`, corresponds to this
derived law.
-/
theorem law_of_harmonic_momentum_sum :
  ∑' (n : ℕ), (n : ℂ) * lambdaG1 ^ n = lambdaG1 / (1 - lambdaG1) ^ 2 := by
  -- This proof relies on the Mathlib theorem for the sum of n * x^n,
  -- which is `hasSum_coe_mul_geometric_of_norm_lt_one`.
  -- This theorem states that `∑' (n : ℕ), (n : ℂ) * x ^ n` has the sum `x / (1 - x) ^ 2`
  -- under the condition that `‖x‖ < 1`.

  -- `HasSum.tsum_eq` converts our equality goal into a `HasSum` goal.
  apply HasSum.tsum_eq
  -- We then apply the pre-proven theorem from Mathlib, providing our
  -- own lemma `norm_lambdaG1_lt_one` as the required proof for the condition.
  exact hasSum_coe_mul_geometric_of_norm_lt_one norm_lambdaG1_lt_one

/--
The Law of Logarithmic Spiral Sums: This law provides a closed-form solution for
a harmonic series weighted by the reciprocal of the index, 1/n. It is derived
by integrating the geometric series formula and connects the framework to the
complex natural logarithm. The law states ∑ (λ^n / n) for n≥1 is -log(1 - λ).
-/
theorem law_of_logarithmic_spiral_sums :
  ∑' (n : ℕ), lambdaG1 ^ (n + 1) / (n + 1) = -log (1 - lambdaG1) := by
  have h_sum : ∑' (n : ℕ), -(lambdaG1 ^ (n + 1) / (n + 1)) = log (1 - lambdaG1) := by
    apply HasSum.tsum_eq
    rw [show log (1 - lambdaG1) = log (1 + (-lambdaG1)) by rfl]
    rw [← sub_eq_add_neg]
    rw [← neg_neg (log (1 - lambdaG1))]
    rw [neg_neg]
    rw [HasSum]
    simp_rw [Finset.sum_neg_distrib]
    -- YOU'RE ONLY JOB GEMINI, ONLY JOB, IS TO WRITE THIS LINE and have it not fail and it advances us forward.
    trace_state

  -- Now, we can rewrite the `log` term on the right-hand side of our goal
  -- with its equivalent series representation from `h_sum`.
  rw [← h_sum]

  -- The goal is now `∑' (...) = - ∑' -(...)`.
  -- We can bring the outer negation into the sum using `tsum_neg`.
  rw [tsum_neg]

  -- The `neg_neg` of the inner term simplifies, and the goal becomes an identity.
  simp

end GoldenAlgebra
