import rh
import Mathlib

open Complex Filter Topology

/-!
# TASK #5 + #6 — Hadamard factorization of ξ and an inhabitant of
`EntireXiClassicalHadamardTheorem`

This file performs the two final assembly steps of the Hadamard program for the
completed Riemann ξ-function (`OverflowResidueRH.entireRiemannXi`), building on
the proven-modulo-residual outputs of the companion scratch files.

It is built on `import rh`, so it uses **rh.lean's own**
`OverflowResidueRH.entireRiemannXi` and `OverflowResidueRH.hadamardGenus1Factor`
directly (the bodies of `hadamardGenus1Factor` and of the scratch `genus1Factor`
are syntactically identical: `(1 - s/ρ)·exp(s/ρ)`). This sidesteps the
namespace bridge `GAP G1` of `ScratchPackage.lean` entirely — every statement is
phrased against the genuine rh ξ.

## STEP 1 — the genus-1 Hadamard factorization (`#5`)

`hadamard_factorization_entireXi` produces

  `∃ C a b : ℂ, C ≠ 0 ∧ ∀ z, entireRiemannXi z = P_mult z · (C · exp (a + b·z))`,

where `P_mult z = ∏' i : XiZeroIndexMult, hadamardGenus1Factor (zeroLocMult i) z`
is the **multiplicity-aware** genus-1 canonical product over the ξ-zeros. The
three deep analytic inputs are carried as **honestly-named hypotheses**, each
matching a proven-modulo-residual output of a companion file:

* `hLU`     — local-uniform multipliability of the genus-1 product over the
              multiplicity index. Companion: `ScratchMultIndex.xiMult_genus1Product_LU hMult`
              (`ScratchMultIndex.lean`, residual `hMult`: with-multiplicity
              inverse-square summability).
* `hOrder`  — the everywhere `analyticOrderAt` match `P_mult ↔ ξ`. Companion:
              `ScratchMultIndex.xiMult_genus1Product_analyticOrderAt htail`
              (`ScratchMultIndex.lean`, residual `htail`: per-point local split).
* `hMinMod` — the genus-1 **minimum-modulus** estimate (Mathlib lacks it).
              Companion: `ScratchQGrowth.quotient_growth_of_factorization`'s
              isolated `hMinMod` (`ScratchQGrowth.lean` / `ScratchMinMod.lean`).

The assembly is: B45 (`entire_quotient_of_analyticOrderAt_eq`) extracts an
entire **zero-free** quotient `Q` with `ξ = P_mult · Q`; the quotient-growth
lemma turns `hMinMod` into `‖Q z‖ ≤ exp(C(1+‖z‖))`; and B43
(`xi_exp_affine_of_zerofree_order_one`, UNCONDITIONAL) recognises the zero-free
order-1 entire `Q` as `C·exp(a+b·z)`.

## STEP 2 — the package (`#6`)

`entireXiClassicalHadamardTheorem_of_quotientData` inhabits
`EntireXiClassicalHadamardTheorem EntireXiNonzeroZeroIndex` via rh.lean's
sharpest smart constructor
`EntireXiClassicalHadamardTheorem.of_canonicalZeros_expAffine_quotient_invSqSummable_normExhaustion`
(rh.lean:81102), which needs only:

* `hC`   : `C ≠ 0`;
* `hinv` : `Summable fun i => (‖zeroLoc i‖²)⁻¹`  — the **distinct-zero**
           inverse-square summability over `EntireXiNonzeroZeroIndex`. Companion:
           `Scratch.xi_zero_invSq_summable` (G3, residual: shell-card bound).
* `hquot`: the **off-zero quotient identity**
           `ξ s / ∏' = C·exp(a+b·s)` for `s` off the indexed (single-index)
           zero set. This is the single-index rephrasing of STEP 1's
           factorization; it is carried as an honest hypothesis here (STEP 1
           produces the multiplicity-index product form, and the single-index
           ⇆ multiplicity-index product bridge is the same RvM/order content
           already isolated upstream).

Everything else in the seven-field bundle — the norm-ball exhaustion, the
locally-uniform product convergence, the log-derivative interchange, the global
factorization, the prefactor data, and the region cover — is discharged
**internally** by the rh.lean constructor.

## Honesty

No `sorry`, no `admit`, no `sorryAx`. Every genuinely-open analytic input is an
explicit, docstring'd hypothesis of the headline theorems; `#print axioms` lists
only the standard kernel axioms (`propext`, `Classical.choice`, `Quot.sound`).
The named hypotheses are *parameters*, so they do not appear as axioms; they are
the proven-modulo-residual deliverables of the companion files.
-/

set_option maxHeartbeats 2000000

namespace OverflowResidueRH.BacklundTuring.ScratchHadamardPackage

open OverflowResidueRH

/-! ## 0. B43 — zero-free entire order-1 ⇒ `C·exp(a+b·z)` (transplanted from `Scratch.lean`).

These four lemmas are copied verbatim from `Scratch.lean` (Bridges 40/41/42/43);
their only Mathlib dependencies are `Complex.norm_deriv_le_of_forall_mem_sphere_norm_le`,
`Differentiable.apply_eq_apply_of_bounded`, `Differentiable.isExactOn_univ`,
`is_const_of_deriv_eq_zero`, and `Complex.borelCaratheodory`. The headline
`xi_exp_affine_of_zerofree_order_one` is UNCONDITIONAL. -/

/-- Cauchy-estimate: linear growth of an entire `f` bounds `‖deriv f‖` by the slope `C`. -/
theorem norm_deriv_le_of_linear_growth
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) {C : ℝ} (hC : 0 ≤ C)
    (hgrow : ∀ z : ℂ, ‖f z‖ ≤ C * (1 + ‖z‖)) :
    ∀ z : ℂ, ‖deriv f z‖ ≤ C := by
  intro z
  have key : ∀ R : ℝ, 0 < R → ‖deriv f z‖ ≤ C * (1 + ‖z‖ + R) / R := by
    intro R hR
    have hsphere : ∀ w ∈ Metric.sphere z R, ‖f w‖ ≤ C * (1 + ‖z‖ + R) := by
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

/-- **B40.** Entire + linear growth ⇒ affine. -/
theorem affine_of_entire_of_linear_growth
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) (C : ℝ)
    (hgrow : ∀ z : ℂ, ‖f z‖ ≤ C * (1 + ‖z‖)) :
    ∃ a b : ℂ, ∀ z, f z = a * z + b := by
  have hC : 0 ≤ C := by
    have := hgrow 0
    simp only [norm_zero, add_zero, mul_one] at this
    exact le_trans (norm_nonneg _) this
  have hbound := norm_deriv_le_of_linear_growth hf hC hgrow
  have hderiv_diff : Differentiable ℂ (deriv f) := by
    have := hf.differentiableOn.deriv isOpen_univ
    rw [differentiableOn_univ] at this
    exact this
  have hconst : ∀ z, deriv f z = deriv f 0 := by
    intro z
    apply hderiv_diff.apply_eq_apply_of_bounded
    rw [isBounded_iff_forall_norm_le]
    exact ⟨C, by rintro x ⟨w, rfl⟩; exact hbound w⟩
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
  linear_combination hz

/-- **B41.** Zero-free entire ⇒ `exp` of an entire function (`ℂ` simply connected). -/
theorem exists_entire_exp_eq {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hne : ∀ z, f z ≠ 0) :
    ∃ g : ℂ → ℂ, Differentiable ℂ g ∧ ∀ z, f z = Complex.exp (g z) := by
  have hlog_diff : Differentiable ℂ (fun z => deriv f z / f z) := by
    have hderiv_diff : Differentiable ℂ (deriv f) := by
      have := hf.differentiableOn.deriv isOpen_univ
      rw [differentiableOn_univ] at this
      exact this
    exact hderiv_diff.div hf (fun z => hne z)
  obtain ⟨g₀, hg₀⟩ := hlog_diff.isExactOn_univ
  have hg₀' : ∀ z, HasDerivAt g₀ (deriv f z / f z) z := fun z => hg₀ z (Set.mem_univ z)
  have hg₀_diff : Differentiable ℂ g₀ := fun z => (hg₀' z).differentiableAt
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
  have hh_diff : Differentiable ℂ h := fun z => (hderiv_h z).differentiableAt
  have hh_deriv0 : ∀ z, deriv h z = 0 := fun z => (hderiv_h z).deriv
  have hh_const : ∀ z, h z = h 0 :=
    fun z => is_const_of_deriv_eq_zero hh_diff hh_deriv0 z 0
  set c : ℂ := h 0 with hc
  have hc_ne : c ≠ 0 := by
    rw [hc, hh]
    exact mul_ne_zero (hne 0) (Complex.exp_ne_zero _)
  set d : ℂ := Complex.log c with hd
  have hcd : Complex.exp d = c := Complex.exp_log hc_ne
  refine ⟨fun z => g₀ z + d, hg₀_diff.add_const d, fun z => ?_⟩
  have hz := hh_const z
  simp only [hh] at hz
  rw [Complex.exp_add, hcd]
  have key : f z = c * Complex.exp (g₀ z) := by
    have hstep : f z * Complex.exp (- g₀ z) * Complex.exp (g₀ z) = c * Complex.exp (g₀ z) := by
      rw [hz]
    rw [mul_assoc, ← Complex.exp_add] at hstep
    simp only [neg_add_cancel, Complex.exp_zero, mul_one] at hstep
    exact hstep
  rw [key]; ring

open Metric in
/-- **B42.** Zero-free entire order-1 ⇒ exp-affine, given the two recognition tools. -/
theorem exp_affine_of_zerofree_order_one
    (liouville : ∀ {f : ℂ → ℂ}, Differentiable ℂ f →
      (∃ C : ℝ, ∀ z, ‖f z‖ ≤ C * (1 + ‖z‖)) → ∃ a b : ℂ, ∀ z, f z = a * z + b)
    (zerofree_exp : ∀ {f : ℂ → ℂ}, Differentiable ℂ f → (∀ z, f z ≠ 0) →
      ∃ g : ℂ → ℂ, Differentiable ℂ g ∧ ∀ z, f z = Complex.exp (g z))
    {Q : ℂ → ℂ} (hQ : Differentiable ℂ Q) (hne : ∀ z, Q z ≠ 0)
    (hgrow : ∃ C : ℝ, ∀ z, ‖Q z‖ ≤ Real.exp (C * (1 + ‖z‖))) :
    ∃ a b : ℂ, ∀ z, Q z = Complex.exp (a + b * z) := by
  obtain ⟨g, hg_diff, hg_eq⟩ := zerofree_exp hQ hne
  obtain ⟨C, hC⟩ := hgrow
  set C₀ : ℝ := max C 0 with hC₀def
  have hC₀nonneg : 0 ≤ C₀ := le_max_right _ _
  have hCC₀ : C ≤ C₀ := le_max_left _ _
  have hRe : ∀ w, (g w).re ≤ C₀ * (1 + ‖w‖) := by
    intro w
    have h1 : ‖Q w‖ = Real.exp (g w).re := by
      rw [hg_eq w, Complex.norm_exp]
    have h2 : Real.exp (g w).re ≤ Real.exp (C * (1 + ‖w‖)) := h1 ▸ hC w
    have h3 : (g w).re ≤ C * (1 + ‖w‖) := Real.exp_le_exp.mp h2
    refine h3.trans ?_
    have : (0:ℝ) ≤ 1 + ‖w‖ := by positivity
    nlinarith [this, hCC₀]
  set C' : ℝ := 7 * C₀ + 4 * ‖g 0‖ + 2 with hC'def
  have hbound : ∀ z, ‖g z‖ ≤ C' * (1 + ‖z‖) := by
    intro z
    set R : ℝ := 2 * (1 + ‖z‖) with hRdef
    have hzn : 0 ≤ ‖z‖ := norm_nonneg z
    have hR0 : 0 < R := by rw [hRdef]; positivity
    have hzR : ‖z‖ < R := by rw [hRdef]; nlinarith [hzn]
    have hzmem : z ∈ Metric.ball (0 : ℂ) R := by
      rw [mem_ball_zero_iff]; exact hzR
    set M : ℝ := C₀ * (1 + R) + 1 with hMdef
    have hM0 : 0 < M := by
      rw [hMdef]
      have : 0 ≤ C₀ * (1 + R) := by positivity
      linarith
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
    have hBC := Complex.borelCaratheodory hM0 hdiffOn hmaps hR0 hzmem
    have hRz : R - ‖z‖ = 2 + ‖z‖ := by rw [hRdef]; ring
    have hRzpos : 0 < R - ‖z‖ := by rw [hRz]; linarith
    refine hBC.trans ?_
    have hM_eq : M = C₀ * (3 + 2 * ‖z‖) + 1 := by
      rw [hMdef, hRdef]; ring
    have hMnn : 0 ≤ M := le_of_lt hM0
    have hterm1 : 2 * M * ‖z‖ / (R - ‖z‖) ≤ 2 * M := by
      rw [hRz, div_le_iff₀ (by linarith : (0:ℝ) < 2 + ‖z‖)]
      nlinarith [hMnn, hzn]
    have hg0 : 0 ≤ ‖g 0‖ := norm_nonneg _
    have hterm2 : ‖g 0‖ * (R + ‖z‖) / (R - ‖z‖) ≤ 3 * ‖g 0‖ := by
      have hRpz : R + ‖z‖ = 2 + 3 * ‖z‖ := by rw [hRdef]; ring
      rw [hRz, hRpz, div_le_iff₀ (by linarith : (0:ℝ) < 2 + ‖z‖)]
      nlinarith [hg0, hzn]
    have hcomb : 2 * M * ‖z‖ / (R - ‖z‖) + ‖g 0‖ * (R + ‖z‖) / (R - ‖z‖)
        ≤ 2 * M + 3 * ‖g 0‖ := by
      linarith [hterm1, hterm2]
    refine hcomb.trans ?_
    rw [hM_eq, hC'def]
    nlinarith [hC₀nonneg, hzn, hg0, mul_nonneg hC₀nonneg hzn]
  obtain ⟨a, b, hab⟩ := liouville hg_diff ⟨C', hbound⟩
  refine ⟨b, a, ?_⟩
  intro z
  rw [hg_eq z, hab z, add_comm]

/-- **B43 — unconditional Hadamard final step** (combines B40, B41, B42). -/
theorem xi_exp_affine_of_zerofree_order_one
    {Q : ℂ → ℂ} (hQ : Differentiable ℂ Q) (hne : ∀ z, Q z ≠ 0)
    (hgrow : ∃ C : ℝ, ∀ z, ‖Q z‖ ≤ Real.exp (C * (1 + ‖z‖))) :
    ∃ a b : ℂ, ∀ z, Q z = Complex.exp (a + b * z) :=
  exp_affine_of_zerofree_order_one
    (fun {_f} hf hCg => affine_of_entire_of_linear_growth hf _ hCg.choose_spec)
    (fun {_f} hf hfne => exists_entire_exp_eq hf hfne)
    hQ hne hgrow

/-! ## 1. B45 — entire quotient with matching zero-orders (transplanted from `ScratchQuotientClose.lean`). -/

/-- **Bridge 45.** Two entire functions vanishing to the same order at every point have a
zero-free entire quotient. -/
theorem entire_quotient_of_analyticOrderAt_eq
    {f P : ℂ → ℂ} (hf : Differentiable ℂ f) (hP : Differentiable ℂ P)
    (hP0 : ∃ z₀, P z₀ ≠ 0)
    (horder : ∀ z, analyticOrderAt f z = analyticOrderAt P z) :
    ∃ Q : ℂ → ℂ, Differentiable ℂ Q ∧ (∀ z, Q z ≠ 0) ∧ ∀ z, f z = P z * Q z := by
  have hfa : ∀ z, AnalyticAt ℂ f z := hf.analyticAt
  have hPa : ∀ z, AnalyticAt ℂ P z := hP.analyticAt
  have hmero : ∀ z, MeromorphicAt (f / P) z := fun z =>
    (hfa z).meromorphicAt.div (hPa z).meromorphicAt
  have hPonNhd : AnalyticOnNhd ℂ P Set.univ := fun z _ => hPa z
  have hPnotTop : ∀ z, analyticOrderAt P z ≠ ⊤ := by
    intro z htop
    obtain ⟨z₀, hz₀⟩ := hP0
    have hev : P =ᶠ[𝓝 z] 0 := analyticOrderAt_eq_top.mp htop
    have : Set.EqOn P 0 Set.univ :=
      hPonNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero
        isPreconnected_univ (Set.mem_univ z) hev
    exact hz₀ (this (Set.mem_univ z₀))
  have horder0 : ∀ z, meromorphicOrderAt (f / P) z = 0 := by
    intro z
    rw [meromorphicOrderAt_div (hfa z).meromorphicAt (hPa z).meromorphicAt,
      (hfa z).meromorphicOrderAt_eq, (hPa z).meromorphicOrderAt_eq, horder z]
    exact LinearOrderedAddCommGroupWithTop.sub_self_eq_zero_of_ne_top
      (by rw [Ne, ENat.map_eq_top_iff]; exact hPnotTop z)
  set Q : ℂ → ℂ := toMeromorphicNFOn (f / P) Set.univ with hQdef
  have hmeroOn : MeromorphicOn (f / P) Set.univ := fun z _ => hmero z
  have hQorder : ∀ z, meromorphicOrderAt Q z = 0 := by
    intro z
    rw [hQdef, meromorphicOrderAt_toMeromorphicNFOn hmeroOn (Set.mem_univ z), horder0 z]
  have hQnf : ∀ z, MeromorphicNFAt Q z := fun z =>
    meromorphicNFOn_toMeromorphicNFOn (f / P) Set.univ (Set.mem_univ z)
  have hQa : ∀ z, AnalyticAt ℂ Q z := by
    intro z
    exact (hQnf z).meromorphicOrderAt_nonneg_iff_analyticAt.mp (by rw [hQorder z])
  have hQdiff : Differentiable ℂ Q := fun z => (hQa z).differentiableAt
  have hQne : ∀ z, Q z ≠ 0 := by
    intro z
    have hAorder : analyticOrderAt Q z = 0 := by
      have hmap := (hQa z).meromorphicOrderAt_eq
      rw [hQorder z] at hmap
      rw [eq_comm, ENat.map_natCast_eq_zero] at hmap
      exact hmap
    exact ((hQa z).analyticOrderAt_eq_zero).mp hAorder
  refine ⟨Q, hQdiff, hQne, ?_⟩
  intro z
  by_cases hPz : P z = 0
  · have hPorderne : analyticOrderAt P z ≠ 0 := (hPa z).analyticOrderAt_ne_zero.mpr hPz
    have hforderne : analyticOrderAt f z ≠ 0 := by rw [horder z]; exact hPorderne
    have hfz : f z = 0 := apply_eq_zero_of_analyticOrderAt_ne_zero hforderne
    rw [hfz, hPz, zero_mul]
  · have hQeq : Q =ᶠ[𝓝[≠] z] (f / P) :=
      hmeroOn.toMeromorphicNFOn_eq_self_on_nhdsNE (Set.mem_univ z)
    have hPne_nhds : ∀ᶠ w in 𝓝 z, P w ≠ 0 :=
      (hPa z).continuousAt.eventually_ne hPz
    have hkey : (fun w => P w * Q w) =ᶠ[𝓝[≠] z] f := by
      filter_upwards [hQeq, hPne_nhds.filter_mono nhdsWithin_le_nhds] with w hw hPw
      rw [hw, Pi.div_apply, mul_div_cancel₀ _ hPw]
    have hcontPQ : ContinuousAt (fun w => P w * Q w) z :=
      ((hPa z).continuousAt).mul ((hQa z).continuousAt)
    have htends_val : Tendsto (fun w => P w * Q w) (𝓝[≠] z) (𝓝 (P z * Q z)) :=
      hcontPQ.continuousWithinAt.tendsto
    have htends_f : Tendsto (fun w => P w * Q w) (𝓝[≠] z) (𝓝 (f z)) :=
      ((hfa z).continuousAt.continuousWithinAt.tendsto).congr' hkey.symm
    exact (tendsto_nhds_unique htends_val htends_f).symm

/-! ## 2. The multiplicity-aware genus-1 product `P_mult`, over rh's `entireRiemannXi`.

The ξ-function and the genus-1 factor are rh.lean's own
`OverflowResidueRH.entireRiemannXi` and `OverflowResidueRH.hadamardGenus1Factor`. -/

theorem differentiable_hadamardGenus1Factor (ρ : ℂ) :
    Differentiable ℂ (hadamardGenus1Factor ρ) :=
  fun s => hadamardGenus1Factor_differentiableAt ρ s

theorem analyticOnNhd_entireRiemannXi :
    AnalyticOnNhd ℂ entireRiemannXi Set.univ :=
  fun z _ => entireRiemannXi_differentiable.analyticAt z

theorem entireRiemannXi_zero_ne : entireRiemannXi 0 ≠ 0 := by
  rw [entireRiemannXi_zero]; norm_num

/-- ξ has finite analytic order at every point (it is not identically zero). -/
theorem analyticOrderAt_entireRiemannXi_ne_top (z : ℂ) :
    analyticOrderAt entireRiemannXi z ≠ ⊤ := by
  have h₀ : analyticOrderAt entireRiemannXi 0 ≠ ⊤ := by
    rw [(analyticOnNhd_entireRiemannXi 0 (Set.mem_univ _)).analyticOrderAt_eq_zero.2
      entireRiemannXi_zero_ne]
    exact (by simp : (0 : ℕ∞) ≠ ⊤)
  exact analyticOnNhd_entireRiemannXi.analyticOrderAt_ne_top_of_isPreconnected
    isPreconnected_univ (Set.mem_univ 0) (Set.mem_univ z) h₀

/-- ξ's zero set. -/
def riemannXiZeros : Set ℂ := entireRiemannXi ⁻¹' {0}

/-- The single-index ξ-zero type (each zero appears once). -/
abbrev XiZeroIndex : Type := riemannXiZeros

def xiZeroLoc (ρ : XiZeroIndex) : ℂ := (ρ : ℂ)

lemma entireRiemannXi_xiZeroLoc (ρ : XiZeroIndex) :
    entireRiemannXi (xiZeroLoc ρ) = 0 := ρ.2

/-- **Multiplicity-aware ξ-zero index**: each zero `ρ` is repeated
`m_ρ = analyticOrderNatAt ξ ρ` times. -/
def XiZeroIndexMult : Type :=
  Σ ρ : XiZeroIndex, Fin (analyticOrderNatAt entireRiemannXi (xiZeroLoc ρ))

/-- Location map of the multiplicity index. -/
def zeroLocMult (i : XiZeroIndexMult) : ℂ := xiZeroLoc i.1

/-- The multiplicity-aware genus-1 Hadamard product `P_mult z = ∏' i, E₁(z/ρᵢ)`. -/
noncomputable def P_mult (z : ℂ) : ℂ :=
  ∏' i : XiZeroIndexMult, hadamardGenus1Factor (zeroLocMult i) z

theorem P_mult_zero_ne : P_mult 0 ≠ 0 := by
  have hone : ∀ i : XiZeroIndexMult, hadamardGenus1Factor (zeroLocMult i) 0 = 1 := by
    intro i; simp [hadamardGenus1Factor]
  have : P_mult 0 = ∏' _i : XiZeroIndexMult, (1 : ℂ) := by
    unfold P_mult; exact tprod_congr hone
  rw [this, tprod_one]; exact one_ne_zero

/-- From local-uniform multipliability of the genus-1 product, `P_mult` is entire. -/
theorem differentiable_P_mult
    (hLU : MultipliableLocallyUniformlyOn
      (fun i : XiZeroIndexMult => fun s => hadamardGenus1Factor (zeroLocMult i) s) Set.univ) :
    Differentiable ℂ P_mult := by
  have hHP : HasProdLocallyUniformlyOn
      (fun i : XiZeroIndexMult => fun s => hadamardGenus1Factor (zeroLocMult i) s)
      (fun s => ∏' i, hadamardGenus1Factor (zeroLocMult i) s) Set.univ :=
    hLU.hasProdLocallyUniformlyOn
  have hTLU : TendstoLocallyUniformlyOn
      (fun (t : Finset XiZeroIndexMult) (s : ℂ) => ∏ i ∈ t, hadamardGenus1Factor (zeroLocMult i) s)
      (fun s => ∏' i, hadamardGenus1Factor (zeroLocMult i) s) atTop Set.univ :=
    (hasProdLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn).mp hHP
  have hdiffOn : ∀ᶠ (t : Finset XiZeroIndexMult) in atTop,
      DifferentiableOn ℂ (fun s => ∏ i ∈ t, hadamardGenus1Factor (zeroLocMult i) s) Set.univ := by
    refine Filter.Eventually.of_forall (fun t => ?_)
    exact DifferentiableOn.fun_finsetProd
      (fun i _ => (differentiable_hadamardGenus1Factor (zeroLocMult i)).differentiableOn)
  have hP_mult_diffOn : DifferentiableOn ℂ
      (fun s => ∏' i, hadamardGenus1Factor (zeroLocMult i) s) Set.univ :=
    hTLU.differentiableOn hdiffOn isOpen_univ
  rw [← differentiableOn_univ]
  exact hP_mult_diffOn

/-! ## 3. Quotient-growth lemma (transplanted from `ScratchQGrowth.lean`).

The single genuinely-missing analytic ingredient is the genus-1 minimum-modulus
estimate `hMinMod`; everything else is elementary. -/

set_option linter.unusedVariables false in
/-- **Quotient-growth lemma**: with `ξ = P·Q`, `Q` entire, and the minimum-modulus estimate
`hMinMod`, the quotient `Q` has order-1 growth `‖Q z‖ ≤ exp(C(1+‖z‖))`. -/
theorem quotient_growth_of_factorization
    {ι : Type*} (loc : ι → ℂ) (Q : ℂ → ℂ)
    (hQ : Differentiable ℂ Q)
    (hMinMod : ∃ C₀ : ℝ, ∀ z : ℂ, 4 ≤ ‖z‖ →
      0 < ‖∏' i, hadamardGenus1Factor (loc i) z‖ ∧
      ‖(∏' i, hadamardGenus1Factor (loc i) z) * Q z‖
        ≤ ‖∏' i, hadamardGenus1Factor (loc i) z‖ * Real.exp (C₀ * (1 + ‖z‖))) :
    ∃ C : ℝ, ∀ z : ℂ, ‖Q z‖ ≤ Real.exp (C * (1 + ‖z‖)) := by
  classical
  set P : ℂ → ℂ := fun z => ∏' i, hadamardGenus1Factor (loc i) z with hP
  obtain ⟨C₀, hC₀⟩ := hMinMod
  have hQcont : Continuous Q := hQ.continuous
  obtain ⟨z₀, _hz₀mem, hz₀max⟩ :=
    (isCompact_closedBall (0 : ℂ) 4).exists_isMaxOn
      (Metric.nonempty_closedBall.2 (by norm_num)) hQcont.norm.continuousOn
  set M : ℝ := ‖Q z₀‖ with hM
  have hM_nonneg : 0 ≤ M := norm_nonneg _
  refine ⟨max C₀ (Real.log (M + 1)), fun z => ?_⟩
  rcases le_or_gt 4 ‖z‖ with hz | hz
  · obtain ⟨hPpos, hkey⟩ := hC₀ z hz
    rw [norm_mul] at hkey
    have hQle : ‖Q z‖ ≤ Real.exp (C₀ * (1 + ‖z‖)) := le_of_mul_le_mul_left hkey hPpos
    refine hQle.trans ?_
    apply Real.exp_le_exp.mpr
    have h1z : (0:ℝ) ≤ 1 + ‖z‖ := by linarith [norm_nonneg z]
    have hCle : C₀ ≤ max C₀ (Real.log (M + 1)) := le_max_left _ _
    nlinarith [h1z, hCle]
  · have hzmem : z ∈ Metric.closedBall (0 : ℂ) 4 := by
      rw [Metric.mem_closedBall, dist_zero_right]; linarith
    have hQz_le_M : ‖Q z‖ ≤ M := hz₀max hzmem
    have hM1_pos : 0 < M + 1 := by linarith
    refine hQz_le_M.trans ?_
    have h1 : M ≤ Real.exp (Real.log (M + 1)) := by
      rw [Real.exp_log hM1_pos]; linarith
    refine h1.trans ?_
    apply Real.exp_le_exp.mpr
    have hlog_le : Real.log (M + 1) ≤ max C₀ (Real.log (M + 1)) := le_max_right _ _
    have hmax_nonneg : 0 ≤ max C₀ (Real.log (M + 1)) :=
      le_trans (Real.log_nonneg (by linarith)) (le_max_right _ _)
    nlinarith [norm_nonneg z, hmax_nonneg, hlog_le]

/-! ## 4. STEP 1 — the Hadamard factorization of ξ (`#5`). -/

/-- **STEP 1 — the genus-1 Hadamard factorization of ξ (TASK #5).**

Combines:
* **B45** `entire_quotient_of_analyticOrderAt_eq` — from `hOrder` (the everywhere
  `analyticOrderAt` match) and `hLU` (giving `Differentiable ℂ P_mult`), extracts an entire
  zero-free `Q` with `ξ = P_mult · Q`;
* the **quotient-growth lemma** — from `hMinMod` (the isolated genus-1 minimum-modulus
  estimate), gives `‖Q z‖ ≤ exp(C(1+‖z‖))`;
* **B43** `xi_exp_affine_of_zerofree_order_one` (unconditional) — recognises the zero-free
  order-1 entire `Q` as `C·exp(a+b·z)` with `C = exp a ≠ 0`.

The three carried hypotheses are exactly the proven-modulo-residual deliverables of the
companion scratch files:
* `hLU`     ← `ScratchMultIndex.xiMult_genus1Product_LU hMult`;
* `hOrder`  ← `ScratchMultIndex.xiMult_genus1Product_analyticOrderAt htail`;
* `hMinMod` ← `ScratchQGrowth.quotient_growth_of_factorization`'s isolated `hMinMod`. -/
theorem hadamard_factorization_entireXi
    (hLU : MultipliableLocallyUniformlyOn
      (fun i : XiZeroIndexMult => fun s => hadamardGenus1Factor (zeroLocMult i) s) Set.univ)
    (hOrder : ∀ z, analyticOrderAt P_mult z = analyticOrderAt entireRiemannXi z)
    (hMinMod : ∃ C₀ : ℝ, ∀ z : ℂ, 4 ≤ ‖z‖ →
      0 < ‖P_mult z‖ ∧
      ‖entireRiemannXi z‖ ≤ ‖P_mult z‖ * Real.exp (C₀ * (1 + ‖z‖))) :
    ∃ (C a b : ℂ), C ≠ 0 ∧
      ∀ z, entireRiemannXi z = P_mult z * (C * Complex.exp (a + b * z)) := by
  -- (a) The Hadamard quotient: B45 with `f := ξ`, `P := P_mult`.
  obtain ⟨Q, hQdiff, hQne, hQfact⟩ :=
    entire_quotient_of_analyticOrderAt_eq
      (f := entireRiemannXi) (P := P_mult)
      entireRiemannXi_differentiable (differentiable_P_mult hLU)
      ⟨0, P_mult_zero_ne⟩ (fun z => (hOrder z).symm)
  -- (b) Quotient growth from the minimum-modulus estimate.
  --     `P_mult` is definitionally `fun z => ∏' i, E₁(zeroLocMult i, z)`, and `ξ = P_mult·Q`
  --     turns `hMinMod` into exactly the shape `quotient_growth_of_factorization` needs.
  have hgrow : ∃ C : ℝ, ∀ z, ‖Q z‖ ≤ Real.exp (C * (1 + ‖z‖)) := by
    refine quotient_growth_of_factorization (loc := zeroLocMult) (Q := Q) hQdiff ?_
    obtain ⟨C₀, hC₀⟩ := hMinMod
    refine ⟨C₀, fun z hz => ?_⟩
    obtain ⟨hPpos, hbound⟩ := hC₀ z hz
    -- `∏' i, E₁ = P_mult z` definitionally; `ξ z = P_mult z · Q z` by `hQfact`.
    rw [hQfact z] at hbound
    exact ⟨hPpos, hbound⟩
  -- (c) B43: zero-free order-1 entire ⇒ exp-affine.
  obtain ⟨a, b, hab⟩ := xi_exp_affine_of_zerofree_order_one hQdiff hQne hgrow
  refine ⟨Complex.exp a, 0, b, Complex.exp_ne_zero a, fun z => ?_⟩
  rw [hQfact z, hab z, zero_add, ← Complex.exp_add]

/-! ## 5. STEP 2 — inhabit `EntireXiClassicalHadamardTheorem` (`#6`).

We use rh.lean's sharpest factorization-facing smart constructor,
`EntireXiClassicalHadamardTheorem.of_canonicalZeros_expAffine_quotient_invSqSummable_normExhaustion`
(rh.lean:81102), which needs ONLY three pieces of data:

* `hC`   : `C ≠ 0`;
* `hinv` : distinct-zero inverse-square summability over `EntireXiNonzeroZeroIndex`;
* `hquot`: the off-zero quotient identity `ξ s / ∏' = C·exp(a+b·s)` for `s` off the
           single-index zero set.

Everything else — the norm-ball exhaustion (`entireXiCanonicalZeroNormProper.normExhaustion`),
the monotone/exhaustive properties, the locally-uniform product convergence, the
log-derivative interchange, the global product factorization, the region cover, and the
prefactor data — is discharged **internally** by the rh.lean constructor.

Both `hinv` (G3) and `hquot` are carried as honest hypotheses:

* `hinv` is the distinct-zero inverse-square summability, the proven-modulo-residual
  output of the RvM/shell-card engine (`Scratch.xi_zero_invSq_summable`, residual: the
  shell-card bound);
* `hquot` is the single-index off-zero quotient identity. It is the single-index
  rephrasing of STEP 1's factorization (STEP 1 gives the multiplicity-index product form;
  the single-index ⇆ multiplicity-index bridge is the same RvM/order content already
  carried by `hOrder`/`hLU` upstream). -/
noncomputable def entireXiClassicalHadamardTheorem_of_quotientData
    {C a b : ℂ} (hC : C ≠ 0)
    (hinv :
      Summable fun i : EntireXiNonzeroZeroIndex =>
        (‖concreteEntireXiZeroSystem.zeroLoc i‖ ^ 2)⁻¹)
    (hquot :
      ∀ s : ℂ,
        (∀ i : EntireXiNonzeroZeroIndex,
          s ≠ concreteEntireXiZeroSystem.zeroLoc i) →
          entireRiemannXi s
              / infiniteHadamardProduct concreteEntireXiZeroSystem.zeroLoc s
            = C * Complex.exp (a + b * s)) :
    EntireXiClassicalHadamardTheorem EntireXiNonzeroZeroIndex :=
  EntireXiClassicalHadamardTheorem.of_canonicalZeros_expAffine_quotient_invSqSummable_normExhaustion
    hC hinv hquot

#print axioms hadamard_factorization_entireXi
#print axioms entireXiClassicalHadamardTheorem_of_quotientData

end OverflowResidueRH.BacklundTuring.ScratchHadamardPackage
