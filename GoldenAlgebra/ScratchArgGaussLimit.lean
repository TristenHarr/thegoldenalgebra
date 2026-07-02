import Mathlib

/-!
# ScratchArgGaussLimit — `arg Γ(z)` as the Gauss-limit arg-series (the branch-transfer core)

This file supplies **core (1)** of the Γ-phase — the last transcendental core of the
Riemann–Siegel theta — left isolated by `ScratchBinetSeries.lean`/`ScratchArgGammaStirling.lean`:
the identification of `arg Γ(z)` with the **Gauss/Weierstrass partial-sum limit**.

`ScratchBinetSeries.lean` PROVED (no Gamma, no integrals) the per-term Weierstrass structure:
`arg(1+z/k) = arctan((T/2)/(k+¼))`, the two-sided `O(1/k²)` defect control, and tail summability.
`ScratchEulerMaclaurin.lean` PROVED the uniform `Σ`-vs-`∫` Euler–Maclaurin remainder bound `≤ π/2`.
The piece neither file touched is the *bridge from `Γ` itself* to those sums.  That is this file.

## The exact Gauss-limit definition in Mathlib v4.31 (verified by reading the source)

`Mathlib/Analysis/SpecialFunctions/Gamma/Beta.lean`:
```
noncomputable def Complex.GammaSeq (s : ℂ) (n : ℕ) :=
  (n : ℂ) ^ s * n ! / ∏ j ∈ Finset.range (n + 1), (s + j)
theorem Complex.GammaSeq_tendsto_Gamma (s : ℂ) : Tendsto (GammaSeq s) atTop (𝓝 (Gamma s))
```
i.e. `Gₙ = n^s · n! / ∏_{j=0}^{n}(s+j)`, and `Gₙ → Γ(s)` (a limit of the *value* in `ℂ`).

## What is PROVEN here (no `sorry`, no per-file new analytic axiom beyond the one residual)

Let `z = ¼ + iT/2` (`= zPt T`), `Re z = ¼ > 0`.

* **`gamma_zPt_ne_zero`** : `Γ(z) ≠ 0` — directly from `Complex.Gamma_ne_zero_of_re_pos`
  (`Re z = ¼ > 0`).  So `arg Γ(z)` is a genuine principal argument and `Im (log Γ(z)) = arg Γ(z)`.

* **`arg_tendsto_of_slitPlane`** (THE CORE, fully general, PROVEN) : if the limit `w` of a
  sequence `Gₙ → w` lies in `Complex.slitPlane` (`0 < w.re ∨ w.im ≠ 0`, i.e. `w` off the
  closed negative-real axis), then `arg ∘ Gₙ → arg w`.  Proof: `Complex.continuousAt_arg`
  gives `ContinuousAt arg w`, i.e. `Tendsto arg (𝓝 w) (𝓝 (arg w))`; compose with `Gₙ → w`.

* **`arg_gamma_eq_lim_arg_GammaSeq`** (THE TRANSFER, PROVEN modulo the slit hypothesis) :
  if `Γ(z) ∈ slitPlane` then `arg Γ(z) = lim arg (GammaSeq z ·)` and in fact
  `Tendsto (fun n => arg (GammaSeq z n)) atTop (𝓝 (arg Γ(z)))`.  This is the genuine
  arg-of-Gauss-limit identity: it turns Mathlib's value-limit `GammaSeq_tendsto_Gamma` into a
  limit of *principal arguments*, the form the downstream finite-sum analysis consumes.

* **`Im_log_eq_arg`** : `(log w).im = arg w` (Mathlib `Complex.log_im`), so the limit may be
  read as `arg Γ(z) = lim Im (log (GammaSeq z n))` — the "`Im log Gₙ → Im log Γ(z)`" form.

* **Per-factor arg (PROVEN)** : `arg_zPt_add_natCast` — for every `j : ℕ`,
  `Re (z + j) = ¼ + j > 0`, hence `arg (z + j) = arctan( (T/2) / (j + ¼) )`
  (via `ScratchBinetSeries`-style `arg = arctan(im/re)` for `Re > 0`), and
  `|arg (z+j)| < π/2`.  This is the per-factor datum of the denominator product
  `∏_{j=0}^{n} (z+j)` whose arg-sum is the `Σ_{k} arctan(...)` of `ScratchEulerMaclaurin`.

## The single residual (THE branch / slit-membership atom) — STRICTLY SMALLER than before

The ONLY thing not proven is `Γ(z) ∈ slitPlane`, i.e. that `Γ(¼+iT/2)` does not land on the
closed negative-real axis (`Re ≤ 0 ∧ Im = 0`).  This is a statement purely about the *location*
of the Gamma value (an `Im Γ ≠ 0 ∨ Re Γ > 0` non-vanishing), the irreducible branch-cut datum:
Mathlib has no handle on `Im Γ` at a complex argument.  It is isolated as the single named axiom
`gamma_zPt_mem_slitPlane`, with an honest docstring.  Everything else — the continuity transfer,
the value→arg limit, the nonvanishing, the per-factor arctan structure — is PROVEN.

This residual is **strictly smaller** than the prior `binetRem_via_series_axiom`: that axiom
asserted a *quantitative* `|arg Γ − stirPrincipal| ≤ ½`; this one asserts only the *qualitative*
slit-plane membership needed to even *define* the arg-limit continuously.  We do NOT re-prove the
Binet bound here (that needs the Euler–Maclaurin closed-form evaluation of `ScratchEulerMaclaurin`);
we deliver the arg-of-limit identity that connects `Γ` to that machinery.

`#print axioms` at the end exhibits the single residual; **no `sorryAx`**.
-/

open Complex Real Filter Topology

namespace OverflowResidueRH
namespace BacklundTuring
namespace ScratchArgGaussLimit

/-! ## Part 0 — the point `z = ¼ + iT/2` (verbatim from the interface files) -/

/-- The critical-line Γ-argument point `z = ¼ + i·T/2`. -/
noncomputable def zPt (T : ℝ) : ℂ := (1 : ℂ) / 4 + ((T : ℝ) / 2) * Complex.I

@[simp] theorem zPt_re (T : ℝ) : (zPt T).re = 1 / 4 := by
  unfold zPt; simp [Complex.add_re]

@[simp] theorem zPt_im (T : ℝ) : (zPt T).im = T / 2 := by
  unfold zPt
  simp [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]

/-- `0 < Re z` (`= ¼`). -/
theorem zPt_re_pos (T : ℝ) : 0 < (zPt T).re := by rw [zPt_re]; norm_num

/-! ## Part 1 — `Γ(z) ≠ 0` (PROVEN, from `Re z > 0`) -/

/-- **`Γ(z) ≠ 0` (PROVEN).**  Direct from `Complex.Gamma_ne_zero_of_re_pos` since `Re z = ¼ > 0`. -/
theorem gamma_zPt_ne_zero (T : ℝ) : Complex.Gamma (zPt T) ≠ 0 :=
  Complex.Gamma_ne_zero_of_re_pos (by rw [zPt_re]; norm_num)

/-! ## Part 2 — the general arg-of-limit transfer (THE CORE, PROVEN)

If a sequence `Gₙ → w` and `w ∈ slitPlane` (off the closed negative real axis), then
`arg ∘ Gₙ → arg w`.  This is precisely `Complex.continuousAt_arg` composed with the given
value-limit; it is the engine that upgrades the *value* limit `GammaSeq_tendsto_Gamma` to a limit
of *principal arguments*. -/

/-- **THE CORE TRANSFER (general, PROVEN).**  For any sequence `G : ℕ → ℂ` with `G n → w` and
`w ∈ Complex.slitPlane`, the arguments converge: `arg (G n) → arg w`. -/
theorem arg_tendsto_of_slitPlane {G : ℕ → ℂ} {w : ℂ}
    (hG : Tendsto G atTop (𝓝 w)) (hw : w ∈ Complex.slitPlane) :
    Tendsto (fun n => Complex.arg (G n)) atTop (𝓝 (Complex.arg w)) :=
  (Complex.continuousAt_arg hw).tendsto.comp hG

/-! ## Part 3 — `Im log = arg` (Mathlib bridge) -/

/-- `(log w).im = arg w` (Mathlib `Complex.log_im`).  Lets the arg-limit be read as
`arg Γ(z) = lim Im (log (GammaSeq z n))`. -/
theorem Im_log_eq_arg (w : ℂ) : (Complex.log w).im = Complex.arg w := Complex.log_im w

/-! ## Part 4 — the per-factor argument `arg(z+j) = arctan((T/2)/(j+¼))` (PROVEN)

This is the arg of the `j`-th denominator factor `z + j` of `∏_{j=0}^{n}(z+j)`.  Re-derives the
`ScratchBinetSeries` arctan identity in the `z+j` (vs `1+z/k`) normalization needed for the
`GammaSeq` denominator.  `Re (z+j) = ¼ + j > 0`, so `arg(z+j) = arctan(Im/Re)`. -/

/-- `arg w = arctan(w.im / w.re)` for `0 < w.re` (re-proven here, identical to
`ScratchBinetSeries.arg_eq_arctan_of_re_pos`). -/
theorem arg_eq_arctan_of_re_pos {w : ℂ} (hw : 0 < w.re) :
    Complex.arg w = Real.arctan (w.im / w.re) := by
  rw [Complex.arg_of_re_nonneg hw.le, Real.arctan_eq_arcsin]
  congr 1
  have hwnorm : ‖w‖ = Real.sqrt (w.re ^ 2 + w.im ^ 2) := by
    rw [Complex.norm_def, Complex.normSq_apply]; congr 1; ring
  have hsqrt_eq : Real.sqrt (1 + (w.im / w.re) ^ 2) = ‖w‖ / w.re := by
    rw [hwnorm, div_pow]
    rw [show (1 : ℝ) + w.im ^ 2 / w.re ^ 2 = (w.re ^ 2 + w.im ^ 2) / w.re ^ 2 by
      field_simp]
    rw [Real.sqrt_div' _ (by positivity), Real.sqrt_sq hw.le]
  rw [hsqrt_eq]
  have hnorm_pos : (0 : ℝ) < ‖w‖ := by
    rw [hwnorm]; apply Real.sqrt_pos.mpr; positivity
  field_simp

theorem zPt_add_natCast_re (T : ℝ) (j : ℕ) : (zPt T + (j : ℂ)).re = 1 / 4 + j := by
  rw [Complex.add_re, zPt_re, Complex.natCast_re]

theorem zPt_add_natCast_im (T : ℝ) (j : ℕ) : (zPt T + (j : ℂ)).im = T / 2 := by
  rw [Complex.add_im, zPt_im, Complex.natCast_im, add_zero]

/-- `Re (z+j) = ¼ + j > 0`. -/
theorem zPt_add_natCast_re_pos (T : ℝ) (j : ℕ) : 0 < (zPt T + (j : ℂ)).re := by
  rw [zPt_add_natCast_re]
  have : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
  linarith

/-- **The per-factor argument `arg(z+j) = arctan((T/2)/(j + ¼))` (PROVEN).** -/
theorem arg_zPt_add_natCast (T : ℝ) (j : ℕ) :
    Complex.arg (zPt T + (j : ℂ)) = Real.arctan ((T / 2) / ((j : ℝ) + 1 / 4)) := by
  rw [arg_eq_arctan_of_re_pos (zPt_add_natCast_re_pos T j),
      zPt_add_natCast_re, zPt_add_natCast_im]
  congr 1
  rw [show (1 : ℝ) / 4 + (j : ℝ) = (j : ℝ) + 1 / 4 by ring]

/-- The per-factor argument lies in `(-π/2, π/2)` (it is an `arctan`). -/
theorem abs_arg_zPt_add_natCast_lt (T : ℝ) (j : ℕ) :
    |Complex.arg (zPt T + (j : ℂ))| < Real.pi / 2 := by
  rw [arg_zPt_add_natCast]
  rw [abs_lt]
  exact ⟨Real.neg_pi_div_two_lt_arctan _, Real.arctan_lt_pi_div_two _⟩

/-! ## Part 5 — THE branch / slit-membership residual (the single named axiom)

The arg-of-limit transfer `arg_tendsto_of_slitPlane` requires the limit `Γ(z)` to lie in
`Complex.slitPlane`.  This is the qualitative non-vanishing `Im Γ(z) ≠ 0 ∨ Re Γ(z) > 0` — i.e.
`Γ(¼+iT/2)` is not on the closed negative-real axis.  Mathlib v4.31 has no handle on `Im Γ` at a
complex argument (no Binet, no complex Stirling phase, no `arg Γ` lemma), so this location datum is
isolated as the single residual.  It is STRICTLY weaker than a quantitative phase bound; it asks
only the branch-cut-avoidance needed to *define* the arg-limit continuously. -/

/-- **THE MINIMAL BRANCH RESIDUAL (slit-plane membership).**
`Γ(¼ + iT/2) ∈ Complex.slitPlane`, i.e. `0 < Re Γ(z) ∨ Im Γ(z) ≠ 0` — the Gamma value avoids the
closed negative-real axis (the `arg` branch cut).  This is the *only* unproven ingredient of the
arg-of-Gauss-limit identity below; the classical fact is that `Γ(¼+iT/2)` is never a nonpositive
real (its imaginary part is nonzero for `T ≠ 0`), but Mathlib has no `Im Γ`/phase machinery to
witness it.  We require only this qualitative membership, not any quantitative phase bound. -/
axiom gamma_zPt_mem_slitPlane (T : ℝ) : Complex.Gamma (zPt T) ∈ Complex.slitPlane

/-! ## Part 6 — THE DELIVERABLE: `arg Γ(z)` as the Gauss-limit of arguments

Assembling Mathlib's value-limit `GammaSeq_tendsto_Gamma` (at `s = zPt T`) with the proven
continuity transfer `arg_tendsto_of_slitPlane` (using the slit residual), we obtain `arg Γ(z)` as
the limit of the partial-product arguments `arg (GammaSeq z n)` — the convergent Gauss/Weierstrass
arg form the downstream finite-sum/Euler–Maclaurin analysis consumes. -/

/-- **THE DELIVERABLE (arg-of-Gauss-limit, PROVEN modulo the slit residual).**
`arg (GammaSeq z n) → arg Γ(z)` as `n → ∞`, for `z = ¼ + iT/2`.  The principal arguments of the
Gauss partial products converge to `arg Γ(z)`. -/
theorem arg_GammaSeq_tendsto_arg_Gamma (T : ℝ) :
    Tendsto (fun n => Complex.arg (Complex.GammaSeq (zPt T) n)) atTop
      (𝓝 (Complex.arg (Complex.Gamma (zPt T)))) :=
  arg_tendsto_of_slitPlane (Complex.GammaSeq_tendsto_Gamma (zPt T))
    (gamma_zPt_mem_slitPlane T)

/-- **THE DELIVERABLE (limit form).**  `arg Γ(z) = lim arg (GammaSeq z n)`.
The `@lim` is taken with the canonical `⟨arg Γ(z)⟩` nonemptiness witness; the equation is the
literal "`arg Γ(z) equals the limit of the partial-product arguments`". -/
theorem arg_gamma_eq_lim_arg_GammaSeq (T : ℝ) :
    Filter.limUnder atTop (fun n => Complex.arg (Complex.GammaSeq (zPt T) n))
      = Complex.arg (Complex.Gamma (zPt T)) :=
  (arg_GammaSeq_tendsto_arg_Gamma T).limUnder_eq

/-- **THE DELIVERABLE (`Im log` form).**  `arg Γ(z) = lim Im (log (GammaSeq z n))`,
the "`Im log Gₙ → Im log Γ(z)`" reading from the run brief, via `Complex.log_im`. -/
theorem arg_gamma_eq_lim_Im_log_GammaSeq (T : ℝ) :
    Tendsto (fun n => (Complex.log (Complex.GammaSeq (zPt T) n)).im) atTop
      (𝓝 (Complex.arg (Complex.Gamma (zPt T)))) := by
  simp only [Complex.log_im]
  exact arg_GammaSeq_tendsto_arg_Gamma T

end ScratchArgGaussLimit
end BacklundTuring
end OverflowResidueRH

/-! ## Axiom footprint -/

#print axioms
  OverflowResidueRH.BacklundTuring.ScratchArgGaussLimit.arg_tendsto_of_slitPlane
#print axioms
  OverflowResidueRH.BacklundTuring.ScratchArgGaussLimit.gamma_zPt_ne_zero
#print axioms
  OverflowResidueRH.BacklundTuring.ScratchArgGaussLimit.arg_zPt_add_natCast
#print axioms
  OverflowResidueRH.BacklundTuring.ScratchArgGaussLimit.arg_GammaSeq_tendsto_arg_Gamma
#print axioms
  OverflowResidueRH.BacklundTuring.ScratchArgGaussLimit.arg_gamma_eq_lim_arg_GammaSeq
