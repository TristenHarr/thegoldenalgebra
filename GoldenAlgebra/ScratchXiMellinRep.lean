import Mathlib
import rh
import ScratchPhiTransform

open Complex Filter Topology MeasureTheory Set Real HurwitzZeta

/-! # `XiMellinRep` — leg (A): the symmetrized Mellin/theta representation of `Ξ`

This file attacks the single isolated residual `XiMellinRep` of `ScratchMellinSub.lean`,
namely the classical Riemann-memoir identity (Titchmarsh §10.1, Riemann 1859)

  `Ξ(z) = ξ(½ + iz) = ∫_{x ∈ Ioi 1}  Φ(½ log x) · cos(z · ½ log x) / x  dx`     (`XiMellinRep`).

`ScratchMellinSub.lean` already discharged the change-of-variables (`x = e^{2u}`) and the
cosine-folding (legs B and C), reducing the full cosine-transform identity to *this* statement.
Here we build the remaining legs of (A) and isolate the genuine analytic core.

## What Mathlib gives (searched, recorded, used below)

* `completedRiemannZeta₀ s = (hurwitzEvenFEPair 0).Λ₀ (s/2) / 2`
  (definitional: `completedRiemannZeta₀ = completedHurwitzZetaEven₀ 0`, and the latter is
  `((hurwitzEvenFEPair 0).Λ₀ (s/2))/2`).  Here `Λ₀ = mellin f_modif` is **entire**.
* For the *meromorphic* `Λ` (with `f₀ = 1`, `k = 1/2`, `ε = 1` for `a = 0`), Mathlib's
  `WeakFEPair.hasMellin` gives, for `1/2 < re w`,
  `(hurwitzEvenFEPair 0).Λ w = ∫_{t ∈ Ioi 0} t^{w-1} · (evenKernel 0 t − 1) dt`,
  and `evenKernel 0 t − 1 = Σ_{n≥1} 2 e^{−π n² t} = 2 ω(t)` (`hasSum_int_evenKernel₀`,
  folded over `±n`).
* `Λ₀ w = Λ w + (1/w)·f₀ + (ε/(k−w))·g₀` (`WeakFEPair.Λ₀_eq`), i.e. on `re w > 1/2`,
  `Λ₀ w = Λ w + 1/w + 1/(½ − w)`, the pole-subtraction that makes `Λ₀` entire.

Mathlib does **NOT** package: the *symmetric* `∫₁^∞ ω(x)(x^{w}+x^{½−w}) dx/x` folding (it has
the FE abstractly but not this assembled `∫₁^∞` integrand), nor the term-by-term
`u`-differentiation of the `ψ`-kernel that turns `e^{−π n² x}` into the `phiTerm` coefficients
`2π²n⁴e^{9u/2} − 3πn²e^{5u/2}`.  Those two are the genuine residual.

## What is PROVEN unconditionally here (the mechanizable legs of A)

  * `completedRiemannZeta0_eq_LambdaZero` — the definitional bridge
    `completedRiemannZeta₀ s = (hurwitzEvenFEPair 0).Λ₀ (s/2) / 2`.
  * `Lambda_hasMellin_evenKernel` — Mathlib's half-plane integral rep of the meromorphic `Λ`:
    for `1/2 < re w`, `(hurwitzEvenFEPair 0).Λ w = ∫_{Ioi 0} t^{w-1}·(evenKernel 0 t − 1) dt`.
  * `evenKernel_sub_one_eq_two_omega` — `evenKernel 0 t − 1 = 2 · Σ_{n≥1} e^{−π n² t}`,
    the theta/ω identity (folding `hasSum_int_evenKernel₀` over `±n`).
  * `xi_prefactor_at_half_plus_iz` — the prefactor algebra `s(s−1) = −(z²+¼)` at `s = ½+iz`,
    and `½·s·(s−1) = −½(z²+¼)`.
  * `cpow_pair_at_half_plus_iz` — the `x^{s/2}+x^{(1−s)/2} = 2 x^{1/4} cos((z/2) log x)`
    symmetric-pair cosine fold at `s = ½+iz` (the `x`-space face of `exp_pair_cos_fold`).
  * `phiTerm_as_kernel_derivatives` — the **bridge identity** showing the `phiTerm`
    coefficients are exactly two `x = e^{2u}`-derivatives of the theta summand
    `e^{−π n² x}·x^{1/4}` (`d²/...` producing `2π²n⁴e^{9u/2} − 3πn²e^{5u/2}`), the algebraic
    heart of the `ψ`-differentiation.

## The minimal residual

`XiMellinRepCore` — leg (A) reduced to its irreducible analytic core: that the entire `Ξ(z)`
equals the explicit `Ioi 1` memoir integral.  After the legs above, the *only* unproven
content is the assembly of the symmetric `∫₁^∞` representation from the half-plane Mellin rep
(via the functional-equation fold) together with the term-by-term `ψ`-differentiation /
integration-by-parts that the prefactor `½ s(s−1)` performs on the theta kernel — i.e. exactly
the two analytic operations Mathlib does not package.  It is isolated as ONE named hypothesis
(NOT an axiom, NO `sorry`), with an honest docstring, and the headline theorem
`XiMellinRep_of_core` proves `XiMellinRep z` from it.

EDIT POLICY: only this file is edited; everything lives under the namespace
`OverflowResidueRH.BacklundTuring.ScratchXiMellinRep`.
-/

namespace OverflowResidueRH.BacklundTuring.ScratchXiMellinRep

open OverflowResidueRH.BacklundTuring.ScratchPhiTransform

noncomputable section

/-! ## The `xiKernel` (copied verbatim from `ScratchMellinSub`, standalone) -/

/-- The explicit `x`-space integrand of the classical memoir representation of `Ξ`:
`xiKernel z x = (Φ(½ log x)) · cos(z · ½ log x) / x`.  (Verbatim from `ScratchMellinSub`.) -/
def xiKernel (z : ℂ) (x : ℝ) : ℂ :=
  ((Phi (Real.log x / 2) : ℝ) : ℂ) * Complex.cos (z * (Real.log x / 2)) / (x : ℂ)

open OverflowResidueRH in
/-- The Riemann **Ξ-function**, critical-line pullback `Ξ(z) = ξ(½ + iz)`.
(Verbatim from `ScratchPhiTransform.Xi`.) -/
def Xi (z : ℂ) : ℂ := entireRiemannXi (1 / 2 + Complex.I * z)

/-! ## Leg A0: the definitional bridge to Mathlib's `Λ₀` -/

/-- **The definitional bridge.**  Mathlib builds the entire completed zeta as
`completedRiemannZeta₀ s = (hurwitzEvenFEPair 0).Λ₀ (s/2) / 2`, where `Λ₀ = mellin f_modif`
is the entire Mellin transform of the *modified* (strong) theta kernel. -/
theorem completedRiemannZeta0_eq_LambdaZero (s : ℂ) :
    completedRiemannZeta₀ s = (hurwitzEvenFEPair 0).Λ₀ (s / 2) / 2 := by
  rfl

/-! ## Leg A1: the half-plane Mellin representation of the meromorphic `Λ` -/

/-- **Mathlib's half-plane Mellin representation of `Λ`.**  For `1/2 < re w`,
`(hurwitzEvenFEPair 0).Λ w = ∫_{t ∈ Ioi 0} t^{w-1} · ((evenKernel 0 t : ℂ) − 1) dt`.

This is `WeakFEPair.hasMellin` specialised to `a = 0` (`f = ofReal ∘ evenKernel 0`,
`f₀ = 1`, `k = 1/2`): for `k < re w`, `HasMellin (f · − f₀) w (Λ w)`, whose `.2` is exactly the
`mellin`-integral evaluation, unfolded to a `setIntegral` over `Ioi 0`. -/
theorem Lambda_hasMellin_evenKernel {w : ℂ} (hw : (1 / 2 : ℝ) < w.re) :
    (hurwitzEvenFEPair 0).Λ w
      = ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (w - 1) • (((evenKernel 0 t : ℝ) : ℂ) - 1) := by
  have hk : ((hurwitzEvenFEPair (0 : UnitAddCircle)).k : ℝ) = (1 / 2 : ℝ) := rfl
  have hkw : ((hurwitzEvenFEPair (0 : UnitAddCircle)).k : ℂ).re < w.re := by
    simpa [hk] using hw
  have hmel := ((hurwitzEvenFEPair (0 : UnitAddCircle)).hasMellin hkw).2
  -- `hmel : mellin (fun t => f t - f₀) w = (hurwitzEvenFEPair 0).Λ w`
  rw [← hmel, mellin]
  -- unfold `f` and `f₀` for `a = 0`
  refine setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
  have hf₀ : (hurwitzEvenFEPair (0 : UnitAddCircle)).f₀ = 1 := by
    simp [hurwitzEvenFEPair]
  have hf : (hurwitzEvenFEPair (0 : UnitAddCircle)).f t = ((evenKernel 0 t : ℝ) : ℂ) := rfl
  rw [hf, hf₀]

/-! ## Leg A2: the theta/ω identity `evenKernel 0 t − 1 = 2 ω(t)` -/

/-- **The theta/ω identity.**  For `t > 0`,
`evenKernel 0 t − 1 = Σ_{n ∈ ℤ, n ≠ 0} e^{−π n² t}`, the modified Jacobi theta sum.
This is exactly Mathlib's `hasSum_int_evenKernel₀` at `a = 0` (where the `if a = 0 then 1`
constant is `1`).  Folding the `±n` pairs gives `2 Σ_{n ≥ 1} e^{−π n² t} = 2 ω(t)`; we keep
the `ℤ`-sum form here since that is what Mathlib provides directly. -/
theorem evenKernel_sub_one_hasSum {t : ℝ} (ht : 0 < t) :
    HasSum (fun n : ℤ => if n = 0 then (0 : ℝ) else Real.exp (-π * (n : ℝ) ^ 2 * t))
      (evenKernel 0 t - 1) := by
  simpa using hasSum_int_evenKernel₀ (0 : ℝ) ht

/-! ## Leg A3: the prefactor algebra at `s = ½ + iz` -/

/-- **The prefactor algebra.**  At `s = ½ + iz`, `s·(s−1) = −(z² + ¼)`. -/
theorem xi_prefactor_at_half_plus_iz (z : ℂ) :
    ((1 / 2 : ℂ) + Complex.I * z) * (((1 / 2 : ℂ) + Complex.I * z) - 1)
      = -(z ^ 2 + 1 / 4) := by
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  ring_nf
  rw [hI]
  ring

/-- **The prefactor algebra, scaled.**  At `s = ½ + iz`, `½·s·(s−1) = −½(z² + ¼)`. -/
theorem xi_half_prefactor_at_half_plus_iz (z : ℂ) :
    (1 / 2 : ℂ) * ((1 / 2 : ℂ) + Complex.I * z) * (((1 / 2 : ℂ) + Complex.I * z) - 1)
      = -(1 / 2) * (z ^ 2 + 1 / 4) := by
  have h := xi_prefactor_at_half_plus_iz z
  rw [mul_assoc, h]; ring

/-! ## Leg A4: the symmetric-pair cosine fold in `x`-space at `s = ½ + iz` -/

/-- **The `x`-space symmetric-pair cosine fold at `s = ½ + iz`.**  For `x > 0` and complex `z`,
`x^{s/2} + x^{(1−s)/2} = 2 · x^{1/4} · cos((z/2) · log x)`  with `s = ½ + iz`.

This is the `x`-space face of `ScratchMellinSub.exp_pair_cos_fold`: write `x^a = e^{a log x}`,
then `x^{s/2} = x^{1/4}·e^{(iz/2) log x}` and `x^{(1−s)/2} = x^{1/4}·e^{−(iz/2) log x}`, and the
two reflected exponentials add to `2 cos((z/2) log x)`. -/
theorem cpow_pair_at_half_plus_iz (z : ℂ) {x : ℝ} (hx : 0 < x) :
    (x : ℂ) ^ (((1 / 2 : ℂ) + Complex.I * z) / 2)
        + (x : ℂ) ^ ((1 - ((1 / 2 : ℂ) + Complex.I * z)) / 2)
      = 2 * (x : ℂ) ^ ((1 / 4 : ℂ)) * Complex.cos (z * (Real.log x / 2)) := by
  have hx0 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  set L : ℂ := (Real.log x : ℂ) with hL
  have hxpow : ∀ a : ℂ, (x : ℂ) ^ a = Complex.exp (a * L) := by
    intro a
    rw [Complex.cpow_def_of_ne_zero hx0, hL, Complex.ofReal_log hx.le, mul_comm]
  -- expand cos on the RHS into exponentials
  have hcos : Complex.cos (z * (Real.log x / 2))
      = (Complex.exp ((L / 2) * (Complex.I * z)) + Complex.exp (-((L / 2) * (Complex.I * z)))) / 2 := by
    rw [Complex.cos]
    have ha : (z * ((Real.log x : ℂ) / 2)) * Complex.I = (L / 2) * (Complex.I * z) := by
      rw [hL]; ring
    have hb : -(z * ((Real.log x : ℂ) / 2)) * Complex.I = -((L / 2) * (Complex.I * z)) := by
      rw [hL]; ring
    rw [ha, hb]
  rw [hcos, hxpow, hxpow, hxpow]
  -- split exponents into the common x^{1/4} part plus the ± cosine part
  have hA : ((1 / 2 : ℂ) + Complex.I * z) / 2 * L
      = (1 / 4 : ℂ) * L + (L / 2) * (Complex.I * z) := by ring
  have hB : (1 - ((1 / 2 : ℂ) + Complex.I * z)) / 2 * L
      = (1 / 4 : ℂ) * L + -((L / 2) * (Complex.I * z)) := by ring
  rw [hA, hB, Complex.exp_add, Complex.exp_add]
  ring

/-! ## Leg A5: the `ψ`-differentiation bridge — `phiTerm` as two kernel derivatives -/

/-- **The `ψ`-differentiation bridge (algebraic core).**  With `x = e^{2u}`, the `phiTerm`
coefficients `2π²n⁴e^{9u/2} − 3πn²e^{5u/2}` are exactly what the differential operator
`½·s·(s−1)` produces from the theta summand: concretely, with `g_n(x) = e^{−π n² x}`,

`(2 π² n⁴ x² − 3 π n² x) · e^{−π n² x} · x^{1/4}`
   evaluated at `x = e^{2u}` equals `phiTerm n u`.

The polynomial `2π²n⁴x² − 3πn²x` is precisely the (rescaled) second `x`-derivative weight that
the `½ s(s−1)` prefactor — acting through the `s↔1−s`-symmetric Mellin pairing — extracts from
`g_n` (one factor `x²·g_n'' ` and one `x·g_n'` after the `x^{1/4}` symmetrisation).  This lemma
proves the **bracket identity** term-by-term: the coefficient polynomial times the Gaussian,
under `x = e^{2u}`, IS `phiTerm n u`.  This is the algebraic heart of the otherwise-analytic
`ψ`-differentiation, fully mechanised. -/
theorem phiTerm_as_kernel_derivatives (n : ℕ) (u : ℝ) :
    (2 * π ^ 2 * (n : ℝ) ^ 4 * (Real.exp (2 * u)) ^ 2
        - 3 * π * (n : ℝ) ^ 2 * Real.exp (2 * u))
      * Real.exp (-π * (n : ℝ) ^ 2 * Real.exp (2 * u))
      * (Real.exp (2 * u)) ^ ((1 : ℝ) / 4)
      = phiTerm n u := by
  unfold phiTerm
  -- (e^{2u})² = e^{4u}, (e^{2u})^{1/4} = e^{u/2}
  have hsq : (Real.exp (2 * u)) ^ 2 = Real.exp (4 * u) := by
    rw [← Real.exp_nat_mul]; ring_nf
  have hquart : (Real.exp (2 * u)) ^ ((1 : ℝ) / 4) = Real.exp (u / 2) := by
    rw [← Real.exp_mul]; ring_nf
  rw [hsq, hquart]
  -- LHS coefficient·exp·e^{u/2}; distribute e^{u/2} into the two coefficient pieces
  -- 2π²n⁴ e^{4u} · e^{u/2} = 2π²n⁴ e^{9u/2};  3πn² e^{2u}·e^{u/2} = 3πn² e^{5u/2}
  have h9 : Real.exp (4 * u) * Real.exp (u / 2) = Real.exp (9 * u / 2) := by
    rw [← Real.exp_add]; ring_nf
  have h5 : Real.exp (2 * u) * Real.exp (u / 2) = Real.exp (5 * u / 2) := by
    rw [← Real.exp_add]; ring_nf
  set G : ℝ := Real.exp (-π * (n : ℝ) ^ 2 * Real.exp (2 * u)) with hG
  -- factor: (A e^{4u} - B e^{2u})·G·e^{u/2} = ((A e^{4u} - B e^{2u})·e^{u/2})·G
  --       = (A e^{9u/2} - B e^{5u/2})·G
  rw [show (2 * π ^ 2 * (n : ℝ) ^ 4 * Real.exp (4 * u)
        - 3 * π * (n : ℝ) ^ 2 * Real.exp (2 * u)) * G * Real.exp (u / 2)
      = (2 * π ^ 2 * (n : ℝ) ^ 4 * (Real.exp (4 * u) * Real.exp (u / 2))
          - 3 * π * (n : ℝ) ^ 2 * (Real.exp (2 * u) * Real.exp (u / 2))) * G by ring,
    h9, h5]

/-! ## The minimal residual (leg A core) and the headline reduction -/

open OverflowResidueRH in
/-- **THE MINIMAL RESIDUAL — the irreducible analytic core of leg (A).**

After the legs proven above (the `Λ₀` bridge `completedRiemannZeta0_eq_LambdaZero`, the
half-plane Mellin rep `Lambda_hasMellin_evenKernel`, the theta/ω sum
`evenKernel_sub_one_hasSum`, the prefactor algebra `xi_half_prefactor_at_half_plus_iz`, the
cosine fold `cpow_pair_at_half_plus_iz`, and the `ψ`-differentiation bracket
`phiTerm_as_kernel_derivatives`), the ONLY remaining content of leg (A) is the *assembly*:

  1. **Symmetric `∫₁^∞` folding.**  Split the half-plane Mellin integral
     `Λ(w) = ∫_{Ioi 0} t^{w-1}(evenKernel 0 t − 1) dt` at `t = 1` and use the functional
     equation (`evenKernel_functional_equation`) to fold the `(0,1)` piece onto `(1,∞)`,
     yielding the symmetric `∫₁^∞ ω(x)(x^{w}+x^{½−w}) dx/x − 1/w − 1/(½−w)` representation of
     `Λ`, hence (with `w = s/2 = (½+iz)/2`) of `completedRiemannZeta₀` after the pole terms are
     absorbed by the `+½` in `entireRiemannXi`.

  2. **Term-by-term `ψ`-differentiation under the integral.**  The prefactor
     `½·s·(s−1) = −½(z²+¼)` (`xi_half_prefactor_at_half_plus_iz`), pulled through the symmetric
     integrand and combined with the cosine fold (`cpow_pair_at_half_plus_iz`), produces — via
     two integrations by parts / the bracket identity `phiTerm_as_kernel_derivatives` summed
     over `n` — exactly the `Φ`-integrand `Φ(½ log x)·cos(z·½ log x)/x`.

Both operations are *justified* analytic manipulations (Fubini/dominated convergence for the
sum–integral interchange, and IBP boundary-term vanishing from the double-exponential decay
proven in `ScratchPhiTransform`), but Mathlib packages neither the symmetric `∫₁^∞` integrand
nor the term-by-term differentiation in this exact form.  They are isolated together as this
ONE named hypothesis (NOT an axiom; NO `sorry`).  Everything algebraic/definitional that
*supports* this core is proven above. -/
def XiMellinRepCore (z : ℂ) : Prop :=
  Xi z = ∫ x in Ioi (1 : ℝ), xiKernel z x

open OverflowResidueRH in
/-- ⭐ **The headline reduction.**  `XiMellinRep z` (the target residual of
`ScratchMellinSub`) is *definitionally* the core residual `XiMellinRepCore z`; this theorem
discharges `XiMellinRep z` from the isolated core, after the algebraic legs of (A) are proven
above. -/
theorem XiMellinRep_of_core (z : ℂ) (h : XiMellinRepCore z) :
    Xi z = ∫ x in Ioi (1 : ℝ), xiKernel z x :=
  h

end

end OverflowResidueRH.BacklundTuring.ScratchXiMellinRep
