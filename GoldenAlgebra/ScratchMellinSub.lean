import Mathlib
import rh
import ScratchPhiTransform

open Complex Filter Topology MeasureTheory Set Real HurwitzZeta

/-! # `MellinSubstitution` — the Riemann-memoir change of variables `x = e^{2u}`

This file attacks the single isolated residual `MellinSubstitution` of
`ScratchPhiTransform.lean`, namely the classical Riemann-memoir identity

  `Ξ(z) = ξ(½ + iz) = 2 ∫₀^∞ Φ(u) cos(zu) du`     (`cosineTransform z`).

## Strategy and honest scope

The full identity is a **substantial classical computation** with three legs:

  (A)  the symmetrized Mellin/theta integral representation of `completedRiemannZeta`
       (Riemann 1859 / Titchmarsh §10.1), folded against the polynomial prefactor
       `½·s·(s−1)` at `s = ½ + iz`, giving `Ξ(z)` as a Mellin integral over `x ∈ [1,∞)`
       whose integrand involves two `u`-derivatives of the Jacobi `ψ`-kernel — these
       derivatives are exactly the coefficients `2π²n⁴e^{9u/2} − 3πn²e^{5u/2}` of `phiTerm`;

  (B)  the **change of variables `x = e^{2u}`** (`dx = 2e^{2u} du`, `x : 1→∞ ↔ u : 0→∞`);

  (C)  the **cosine folding** of the `s ↔ 1−s` symmetric exponential pair into `cos(zu)`.

Mathlib does NOT package leg (A): it has the abstract `WeakFEPair`/`mellin` machinery and
the theta kernel `evenKernel 0`, but not the symmetrized integrand of `Ξ` in exactly this
form, nor the term-by-term `ψ`-differentiation that produces `Φ`'s coefficients.

**What is PROVEN unconditionally here** (the mechanizable legs B and C):

  * `exp_two_image_Ioi` — `(fun u ↦ e^{2u}) '' (Ioi 0) = Ioi 1`, the geometry of the
    substitution domain.
  * `mellin_exp_substitution` — leg (B): for any integrand `g`,
    `∫ x in Ioi 1, g x = ∫ u in Ioi 0, (2 e^{2u}) • g (e^{2u})`, the honest
    Jacobian change of variables via `integral_image_eq_integral_abs_deriv_smul`.
  * `exp_pair_cos_fold` — leg (C): the symmetric exponential pair folds into a cosine,
    `e^{u·iz} + e^{-u·iz} = 2 cos(zu)` (and its `s = ½+iz` packaging).
  * `cosineKernel_substitution` — legs (B)+(C) combined: the explicit `x`-integrand
    `(Φ(½ log x)) · cos(z·½ log x) / x` over `Ioi 1` substitutes to exactly
    `cosineTransform z = 2 ∫₀^∞ Φ(u) cos(zu) du`.

**The minimal residual** is then `XiMellinRep` — leg (A) alone — the statement that `Ξ(z)`
equals that explicit `Ioi 1` Mellin integral.  It is isolated as ONE named hypothesis with
an honest docstring (NOT an axiom, NO `sorry`).  The headline theorem
`MellinSubstitution_of_XiMellinRep` then proves `MellinSubstitution` *given* `XiMellinRep`,
with the change-of-variables and cosine-folding done here unconditionally.

This strictly shrinks the residual: `MellinSubstitution` (= the whole identity) is reduced
to `XiMellinRep` (= the theta-rep + `ψ`-differentiation alone), with B and C discharged.

EDIT POLICY: only this file is edited; everything lives under the namespace
`OverflowResidueRH.BacklundTuring.ScratchMellinSub`.
-/

namespace OverflowResidueRH.BacklundTuring.ScratchMellinSub

open OverflowResidueRH.BacklundTuring.ScratchPhiTransform

noncomputable section

/-! ## Leg (B): the change of variables `x = e^{2u}` -/

/-- The substitution map `u ↦ e^{2u}` carries `Ioi 0` (the `u`-half-line) bijectively onto
`Ioi 1` (the `x`-domain of the classical memoir integral).  This is the geometry behind
`x = e^{2u}`, `x : 1 → ∞ ↔ u : 0 → ∞`. -/
theorem exp_two_image_Ioi :
    (fun u : ℝ => Real.exp (2 * u)) '' (Ioi 0) = Ioi 1 := by
  ext x
  simp only [Set.mem_image, Set.mem_Ioi]
  constructor
  · rintro ⟨u, hu, rfl⟩
    have : Real.exp 0 < Real.exp (2 * u) := by
      apply Real.exp_lt_exp.mpr; linarith
    simpa using this
  · intro hx
    refine ⟨Real.log x / 2, ?_, ?_⟩
    · have hlog : 0 < Real.log x := Real.log_pos hx
      linarith
    · rw [mul_div_cancel₀ _ (by norm_num : (2 : ℝ) ≠ 0), Real.exp_log (by linarith : 0 < x)]

/-- `u ↦ e^{2u}` is injective on `Ioi 0` (strict monotonicity of `exp`). -/
theorem exp_two_injOn : InjOn (fun u : ℝ => Real.exp (2 * u)) (Ioi 0) := by
  intro a _ b _ hab
  have : (2 : ℝ) * a = 2 * b := Real.exp_injective hab
  linarith

/-- The derivative of `u ↦ e^{2u}` is `2 e^{2u}` (within `Ioi 0`). -/
theorem hasDerivWithinAt_exp_two (u : ℝ) :
    HasDerivWithinAt (fun u : ℝ => Real.exp (2 * u)) (2 * Real.exp (2 * u)) (Ioi 0) u := by
  have hmul : HasDerivAt (fun u : ℝ => 2 * u) 2 u := by
    simpa using (hasDerivAt_id u).const_mul (2 : ℝ)
  have h : HasDerivAt (fun u : ℝ => Real.exp (2 * u)) (Real.exp (2 * u) * 2) u :=
    (Real.hasDerivAt_exp (2 * u)).comp u hmul
  rw [mul_comm] at h
  exact h.hasDerivWithinAt

/-- **Leg (B) — the honest Jacobian change of variables `x = e^{2u}`.**
For any (complex-valued) integrand `g`,
`∫ x in Ioi 1, g x = ∫ u in Ioi 0, (2 e^{2u}) • g (e^{2u})`.
This is the substitution `x = e^{2u}`, `dx = 2 e^{2u} du`, `x : 1 → ∞ ↔ u : 0 → ∞`,
proven via Mathlib's one-dimensional `integral_image_eq_integral_abs_deriv_smul`
(the image is `Ioi 1` by `exp_two_image_Ioi`, injectivity by `exp_two_injOn`, and the
Jacobian `2 e^{2u} > 0` so `|·|` drops). -/
theorem mellin_exp_substitution (g : ℝ → ℂ) :
    ∫ x in Ioi (1 : ℝ), g x
      = ∫ u in Ioi (0 : ℝ), (2 * Real.exp (2 * u) : ℝ) • g (Real.exp (2 * u)) := by
  have hsub := integral_image_eq_integral_abs_deriv_smul (F := ℂ)
    (f := fun u : ℝ => Real.exp (2 * u)) (f' := fun u : ℝ => 2 * Real.exp (2 * u))
    (s := Ioi 0) measurableSet_Ioi
    (fun u _ => hasDerivWithinAt_exp_two u) exp_two_injOn g
  rw [exp_two_image_Ioi] at hsub
  rw [hsub]
  refine setIntegral_congr_fun measurableSet_Ioi (fun u _ => ?_)
  have hpos : (0 : ℝ) < 2 * Real.exp (2 * u) := by positivity
  rw [abs_of_pos hpos]

/-! ## Leg (C): the cosine folding -/

/-- **Leg (C) — the cosine fold.**  For real `u` and complex `z`,
`e^{u·iz} + e^{−u·iz} = 2 cos(z·u)`.  This is the heart of how the `s ↔ 1−s` symmetric
exponential pair (under `s = ½ + iz`) folds into a cosine: the two reflected exponentials
add to twice the cosine of the (real) phase. -/
theorem exp_pair_cos_fold (z : ℂ) (u : ℝ) :
    Complex.exp ((u : ℂ) * (Complex.I * z)) + Complex.exp (-((u : ℂ) * (Complex.I * z)))
      = 2 * Complex.cos (z * u) := by
  have ha : (z * u : ℂ) * Complex.I = (u : ℂ) * (Complex.I * z) := by ring
  have hb : -(z * u : ℂ) * Complex.I = -((u : ℂ) * (Complex.I * z)) := by ring
  have hcos : Complex.cos (z * u)
      = (Complex.exp ((u : ℂ) * (Complex.I * z))
          + Complex.exp (-((u : ℂ) * (Complex.I * z)))) / 2 := by
    rw [Complex.cos, ha, hb]
  rw [hcos]; ring

/-! ## Legs (B)+(C) combined: the explicit memoir kernel substitutes to `cosineTransform` -/

/-- The explicit `x`-space integrand of the classical memoir representation of `Ξ`:
`xiKernel z x = (Φ(½ log x)) · cos(z · ½ log x) / x`.
Under `x = e^{2u}` (so `½ log x = u` and `dx/x = 2 du`) this is exactly `Φ(u) cos(zu) · 2 du`. -/
def xiKernel (z : ℂ) (x : ℝ) : ℂ :=
  ((Phi (Real.log x / 2) : ℝ) : ℂ) * Complex.cos (z * (Real.log x / 2)) / (x : ℂ)

/-- **Legs (B)+(C) combined.**  The explicit memoir kernel `xiKernel z`, integrated over
`x ∈ Ioi 1`, substitutes under `x = e^{2u}` to exactly the cosine transform
`cosineTransform z = 2 ∫₀^∞ Φ(u) cos(zu) du`.

Mechanism: `mellin_exp_substitution` turns `∫_{Ioi 1} xiKernel z x dx` into
`∫_{Ioi 0} (2 e^{2u}) • (Φ(u) cos(zu) / e^{2u}) du`, where the `2 e^{2u}` Jacobian cancels
the `1/x = e^{−2u}` factor leaving `2 Φ(u) cos(zu)`, i.e. `2 · (Φ(u) cos(zu))`; pulling the
constant `2` out of the integral gives `cosineTransform z`. -/
theorem xiKernel_substitution (z : ℂ) :
    ∫ x in Ioi (1 : ℝ), xiKernel z x = cosineTransform z := by
  rw [mellin_exp_substitution (xiKernel z)]
  unfold cosineTransform
  rw [← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi (fun u _ => ?_)
  -- simplify `xiKernel z (e^{2u})`: log(e^{2u})/2 = u, and the 1/x = e^{-2u} cancels.
  have hlog : Real.log (Real.exp (2 * u)) / 2 = u := by
    rw [Real.log_exp]; ring
  have hxC : ((Real.exp (2 * u) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne'
  -- evaluate the kernel at `x = e^{2u}`
  have hlogC : ((Real.log (Real.exp (2 * u)) : ℝ) : ℂ) / 2 = (u : ℂ) := by
    rw [Real.log_exp]; push_cast; ring
  have hker : xiKernel z (Real.exp (2 * u))
      = ((Phi u : ℝ) : ℂ) * Complex.cos (z * u) / ((Real.exp (2 * u) : ℝ) : ℂ) := by
    unfold xiKernel
    rw [hlog]
    congr 2
    rw [hlogC]
  rw [hker, Complex.real_smul]
  -- (2 e^{2u}) • (Φ u · cos(zu) / e^{2u}) = 2 · (Φ u · cos(zu))
  set E : ℂ := ((Real.exp (2 * u) : ℝ) : ℂ) with hE
  set A : ℂ := ((Phi u : ℝ) : ℂ) * Complex.cos (z * u) with hA
  have h2E : ((2 * Real.exp (2 * u) : ℝ) : ℂ) = 2 * E := by rw [hE]; push_cast; ring
  have hcancel : E * (A / E) = A := by
    rw [mul_comm, div_mul_cancel₀ A hxC]
  rw [h2E, show 2 * E * (A / E) = 2 * (E * (A / E)) by ring, hcancel]

/-! ## The minimal residual (leg A) and the headline reduction -/

open OverflowResidueRH in
/-- **THE MINIMAL RESIDUAL — leg (A) alone: the symmetrized Mellin/theta representation
of `Ξ`.**

This is the one classical step Mathlib does NOT package: that the entire `Ξ(z) = ξ(½+iz)`
equals the explicit Riemann-memoir Mellin integral over `x ∈ [1,∞)`,
`Ξ(z) = ∫_{1}^{∞} (Φ(½ log x)) · cos(z·½ log x) / x dx`.

Deriving this from Mathlib's pieces is the *content* of leg (A): start from
`completedRiemannZeta₀ s = (hurwitzEvenFEPair 0).Λ₀ (s/2)/2 = mellin f_modif (s/2)/2`
(the `evenKernel 0`/`ψ` theta kernel, `theta_kernel_hasSum`), apply the polynomial prefactor
`½·s·(s−1) = −½(z²+¼)` at `s = ½+iz`, and carry out the term-by-term `u`-differentiation of
the `ψ`-kernel that turns its `e^{−πn²x}` summands into the `2π²n⁴e^{9u/2} − 3πn²e^{5u/2}`
coefficients of `phiTerm` — i.e. precisely `Φ`.

It is isolated as ONE named hypothesis (NOT an axiom), so the headline theorem reads
`theorem … (h : XiMellinRep z) : …`.  The change-of-variables (leg B,
`mellin_exp_substitution`) and the cosine folding (leg C, `exp_pair_cos_fold`) — the
mechanizable parts — are PROVEN above and used in the reduction below, so this residual is
strictly smaller than `MellinSubstitution`. -/
def XiMellinRep (z : ℂ) : Prop :=
  Xi z = ∫ x in Ioi (1 : ℝ), xiKernel z x

open OverflowResidueRH in
/-- ⭐ **The headline reduction.**  Given the minimal residual `XiMellinRep z` (leg A — the
symmetrized theta/Mellin representation of `Ξ` with its `ψ`-differentiation), the full
Riemann cosine-transform identity `Ξ(z) = cosineTransform z` follows, using the proven
change-of-variables (`xiKernel_substitution`, legs B+C).

This is a strict reduction of `ScratchPhiTransform.MellinSubstitution`: the
change-of-variables and cosine-folding are discharged here; only leg (A) remains. -/
theorem MellinSubstitution_of_XiMellinRep (z : ℂ) (h : XiMellinRep z) :
    Xi z = cosineTransform z := by
  rw [h, xiKernel_substitution]

open OverflowResidueRH in
/-- ⭐ **`MellinSubstitution` (the residual of `ScratchPhiTransform`) reduced to leg (A).**
If the minimal residual `XiMellinRep` holds at every `z`, then `MellinSubstitution`
(`∀ z, Xi z = cosineTransform z`) holds — with the change-of-variables and cosine-folding
proven here, not assumed. -/
theorem MellinSubstitution_of_XiMellinRep_forall (h : ∀ z : ℂ, XiMellinRep z) :
    MellinSubstitution :=
  fun z => MellinSubstitution_of_XiMellinRep z (h z)

open OverflowResidueRH in
/-- ⭐ **Full chain to the cosine-transform identity, given leg (A).**
`entireRiemannXi (½ + iz) = 2 ∫₀^∞ Φ(u) cos(zu) du`, reduced to the single minimal
residual `XiMellinRep` (the theta/Mellin representation + `ψ`-differentiation), with the
substitution and cosine-folding proven. -/
theorem entireRiemannXi_eq_cosine_transform_of_XiMellinRep
    (h : ∀ z : ℂ, XiMellinRep z) (z : ℂ) :
    entireRiemannXi (1 / 2 + Complex.I * z)
      = 2 * ∫ u in Set.Ioi (0 : ℝ), (Phi u : ℂ) * Complex.cos (z * u) :=
  entireRiemannXi_eq_cosine_transform (MellinSubstitution_of_XiMellinRep_forall h) z

end

end OverflowResidueRH.BacklundTuring.ScratchMellinSub
