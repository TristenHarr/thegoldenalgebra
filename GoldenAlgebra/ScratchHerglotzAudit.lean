import Mathlib
import rh

/-!
# ScratchHerglotzAudit — the RH-equivalence / honesty certificate

This file is the **audit layer** of the Overflow-Residue programme.  Its job is
NOT to prove RH, but to make the RH-*strength* of the two surviving routes
maximally visible, so that no circularity can hide:

  ROUTE A.  "`Λ[Ξ]` is the Cauchy transform of a positive **real-supported**
            measure" ⟹ the anti-Herglotz target (`XiPullbackAntiHerglotzTarget`).
            The representation existence stays an *unproven core* (`def … : Prop`),
            but the bridge `representation ⟹ anti-Herglotz` is proved here.

  ROUTE B.  "the true-minus-height **displacement** field of every zero exhibits
            no positive upper-imaginary overflow" ⟺ RH.  Here BOTH directions are
            proved: an off-line zero forces overflow (the §4 pole-probe), and
            forbidding overflow is exactly RH.

Everything below reuses the engine of `rh.lean`
(`OverflowResidueRH.PositiveUpperImaginaryEscape`, `AntiHerglotzUHP`,
`logDerivativeResponse`, `XiPullback`, `XiPullbackAntiHerglotzTarget`,
`complex_real_root_residue_imag_nonpos`, the §4 probe arithmetic).  The
displacement field `D_quad` and its imaginary closed form are restated minimally
(self-contained copies of the compiled core of `ScratchDisplacementObstruction.lean`,
which is a scratch file not in the `lake` build).

## Deliverables (all proved, no `sorry`)

ROUTE A
* `realSupportedCauchyTransform`, `harmlessRealAffine`     — the building blocks.
* `realSupportedCauchyTransform_im_nonpos`                 — positive real-supported
  Cauchy transform has `Im ≤ 0` on the UHP (integral of the §2 atom).
* `XiLogDerivRealSupportedCauchy` (`def … : Prop`)        — the unproven core.
* `antiHerglotz_of_realSupportedCauchy`                    — core ⟹ anti-Herglotz target.

ROUTE B
* `D_quad`, `ImDquad`, `Dquad_im_formula`                  — displacement field + Im form.
* `displacement_offline_escape`                           — every off-line config
  (`η ≠ 0`) has positive upper-imaginary escape (uniform witness `⟨γ, |η|/2⟩`).
* `Doff`, `HasOffLineZero`, `DoffNoPositiveOverflow`      — the audit predicates.
* `offLineZero_forces_Doff_positiveOverflow`              — an off-line zero of
  `XiPullback` ⟹ a displacement config with positive overflow (the pole-probe).
* `DoffNoPositiveOverflow_iff_RH`                          — forbidding displacement
  overflow ⟺ RH.  The exact RH-strength, made visible.

TIE-TOGETHER
* `realSupportedCauchy_imp_antiHerglotz` and
  `RH_imp_DoffNoPositiveOverflow` / `DoffNoPositiveOverflow_imp_RH` record that the
  two routes hit the **same wall**.
-/

namespace HerglotzAudit

open Complex MeasureTheory Filter Topology
open OverflowResidueRH

-- =====================================================================
-- ROUTE A.  Real-supported Cauchy / Herglotz representation
-- =====================================================================

/-- **Real-supported Cauchy transform** of a (signed) measure `μ` on `ℝ`:
  `C[μ](z) := ∫_ℝ 1/(z − u) dμ(u)`.
When `μ ≥ 0` this is anti-Herglotz on the UHP (every atom `1/(z−u)` with real
`u` has `Im ≤ 0` there). -/
noncomputable def realSupportedCauchyTransform (μ : Measure ℝ) (z : ℂ) : ℂ :=
  ∫ u : ℝ, (1 : ℂ) / (z - (u : ℂ)) ∂μ

/-- **Harmless real-affine background** `a − b·z` with real `a` and real `b ≥ 0`.
On the UHP its imaginary part is `−b·Im z ≤ 0`, so it never spoils the
anti-Herglotz sign.  (The degrees-of-freedom a Cauchy/Nevanlinna representation
is allowed to carry without changing the sign law.) -/
noncomputable def harmlessRealAffine (a b : ℝ) (z : ℂ) : ℂ :=
  (a : ℂ) - (b : ℂ) * z

/-- `Im(harmlessRealAffine a b z) = −b·Im z ≤ 0` on the UHP when `b ≥ 0`. -/
theorem harmlessRealAffine_im_nonpos (a b : ℝ) (hb : 0 ≤ b) (z : ℂ)
    (hz : 0 < z.im) : (harmlessRealAffine a b z).im ≤ 0 := by
  unfold harmlessRealAffine
  simp only [Complex.sub_im, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, add_zero, zero_sub]
  have : 0 ≤ b * z.im := mul_nonneg hb (le_of_lt hz)
  linarith

/-- 🌟 **PROVED — a positive real-supported Cauchy transform is anti-Herglotz.**
For every UHP `z` with integrable atom family, `Im C[μ](z) = ∫ Im(1/(z−u)) dμ ≤ 0`,
because each atom is `≤ 0` (the §2 atom `complex_real_root_residue_imag_nonpos`)
and `μ ≥ 0`.

The commutation `Im ∘ ∫ = ∫ ∘ Im` is the continuous-linear-map push of
`Complex.imCLM` through the Bochner integral; it needs the integrability of the
atom family, which is part of the representation core below. -/
theorem realSupportedCauchyTransform_im_nonpos
    (μ : Measure ℝ) (z : ℂ) (hz : 0 < z.im)
    (hint : Integrable (fun u : ℝ => (1 : ℂ) / (z - (u : ℂ))) μ) :
    (realSupportedCauchyTransform μ z).im ≤ 0 := by
  unfold realSupportedCauchyTransform
  have hcomm :
      (∫ u : ℝ, (1 : ℂ) / (z - (u : ℂ)) ∂μ).im
        = ∫ u : ℝ, ((1 : ℂ) / (z - (u : ℂ))).im ∂μ := by
    have := ContinuousLinearMap.integral_comp_comm Complex.imCLM hint
    simpa using this.symm
  rw [hcomm]
  apply integral_nonpos
  intro u
  exact complex_real_root_residue_imag_nonpos z u hz

/-- **The Route-A unproven core** — `XiLogDerivRealSupportedCauchy`.
`Λ[Ξ]` equals a positive real-supported Cauchy transform plus a harmless
real-affine background, on the whole open UHP, with the atom family integrable
at each such `z`.  This is the clean "`Λ[Ξ]` is the Cauchy transform of a
positive real-supported measure" characterization; its *existence* is left
unproven, only its *equivalence/sufficiency* for the sign law is the deliverable. -/
def XiLogDerivRealSupportedCauchy : Prop :=
  ∃ (μ : Measure ℝ) (a b : ℝ),
    (0 ≤ b) ∧
    (∀ z : ℂ, 0 < z.im →
        Integrable (fun u : ℝ => (1 : ℂ) / (z - (u : ℂ))) μ) ∧
    (∀ z : ℂ, 0 < z.im →
        logDerivativeResponse XiPullback z
          = realSupportedCauchyTransform μ z + harmlessRealAffine a b z)

/-- 🌟🌟 **PROVED — Route A bridge: real-supported Cauchy ⟹ anti-Herglotz target.**
If `Λ[Ξ]` is a positive real-supported Cauchy transform (+ harmless affine), then
`XiPullbackAntiHerglotzTarget` holds: pointwise on the UHP,
`Im Λ[Ξ] z = Im C[μ] z + Im(affine) ≤ 0`. -/
theorem antiHerglotz_of_realSupportedCauchy
    (h : XiLogDerivRealSupportedCauchy) : XiPullbackAntiHerglotzTarget := by
  obtain ⟨μ, a, b, hb, hint, heq⟩ := h
  intro z hz
  rw [heq z hz, Complex.add_im]
  have h1 : (realSupportedCauchyTransform μ z).im ≤ 0 :=
    realSupportedCauchyTransform_im_nonpos μ z hz (hint z hz)
  have h2 : (harmlessRealAffine a b z).im ≤ 0 :=
    harmlessRealAffine_im_nonpos a b hb z hz
  linarith

-- =====================================================================
-- ROUTE B.  Displacement-pole audit
-- =====================================================================
-- Minimal self-contained restatement of the compiled core of
-- `ScratchDisplacementObstruction.lean` (that scratch file is not in the
-- `lake` build, and its tail does not compile, so we copy only the proven
-- pieces we need).

/-- Imaginary part of `1/(z-w)` for `z = x+iy`, `w = a+ib`. -/
theorem im_recip (x y a b : ℝ) :
    ((1 : ℂ) / ((⟨x, y⟩ : ℂ) - ⟨a, b⟩)).im
      = -(y - b) / ((x - a) ^ 2 + (y - b) ^ 2) := by
  rw [Complex.div_im]
  simp only [Complex.one_re, Complex.one_im, Complex.sub_re, Complex.sub_im,
    Complex.normSq_apply]
  ring_nf

/-- Imaginary part of `1/(z+w)` for `z = x+iy`, `w = a+ib`. -/
theorem im_recip_add (x y a b : ℝ) :
    ((1 : ℂ) / ((⟨x, y⟩ : ℂ) + ⟨a, b⟩)).im
      = -(y + b) / ((x + a) ^ 2 + (y + b) ^ 2) := by
  rw [Complex.div_im]
  simp only [Complex.one_re, Complex.one_im, Complex.add_re, Complex.add_im,
    Complex.normSq_apply]
  ring_nf

/-- Paired Cauchy atom `K_u(z) = 1/(z−u) + 1/(z+u)`. -/
noncomputable def Kpair (u z : ℂ) : ℂ := 1 / (z - u) + 1 / (z + u)

/-- **Quadruple displacement** `D_quad(z,γ,η) =
K_{γ+iη}(z) + K_{γ−iη}(z) − 2·K_γ(z)`: two true paired atoms at the four pullback
points `{±γ ± iη}` minus two real-height atoms at `±γ`.  `D_quad ≡ 0` at `η = 0`. -/
noncomputable def D_quad (z : ℂ) (γ η : ℝ) : ℂ :=
  Kpair ⟨γ, η⟩ z + Kpair ⟨γ, -η⟩ z - 2 * Kpair ⟨γ, 0⟩ z

/-- `D_quad` is **even in `η`** (swapping `η ↦ −η` swaps the two true atoms). -/
theorem D_quad_neg_eta (z : ℂ) (γ η : ℝ) : D_quad z γ (-η) = D_quad z γ η := by
  unfold D_quad
  rw [neg_neg]; ring

/-- The explicit real closed form of `Im D_quad` at `z = x+iy`. -/
noncomputable def ImDquad (x y γ η : ℝ) : ℝ :=
    2 * y / (y ^ 2 + (γ + x) ^ 2)
  + 2 * y / (y ^ 2 + (γ - x) ^ 2)
  + (η - y) / ((η - y) ^ 2 + (γ + x) ^ 2)
  + (η - y) / ((η - y) ^ 2 + (γ - x) ^ 2)
  - (η + y) / ((η + y) ^ 2 + (γ + x) ^ 2)
  - (η + y) / ((η + y) ^ 2 + (γ - x) ^ 2)

/-- **Closed form for `(D_quad ⟨x,y⟩ γ η).im`** — six rational terms. -/
theorem Dquad_im_formula (x y γ η : ℝ) :
    (D_quad (⟨x, y⟩ : ℂ) γ η).im = ImDquad x y γ η := by
  simp only [D_quad, Kpair, Complex.add_im, Complex.sub_im, Complex.mul_im,
    Complex.re_ofNat, Complex.im_ofNat, zero_mul, add_zero,
    im_recip, im_recip_add]
  simp only [ImDquad]
  ring

/-- **PROVED — uniform escape witness for a positive-height off-line config.**
For `η > 0`, the probe `z = ⟨γ, η/2⟩` (the imaginary axis half-way up to the UHP
pole `γ+iη`) gives
  `Im D_quad = 32·(9η⁴+80η²γ²+128γ⁴) / (3η·(η²+16γ²)·(9η²+16γ²)) > 0`,
a manifestly positive rational for every `γ`.  This is the §4 pole-probe in
explicit closed form: the true atom near its UHP pole dominates the bounded
remainder, producing positive upper-imaginary overflow. -/
theorem displacement_pos_escape_witness (γ η : ℝ) (hη : 0 < η) :
    0 < (D_quad (⟨γ, η / 2⟩ : ℂ) γ η).im := by
  rw [Dquad_im_formula]
  have key : ImDquad γ (η / 2) γ η
      = 32 * (9 * η ^ 4 + 80 * η ^ 2 * γ ^ 2 + 128 * γ ^ 4)
          / (3 * η * (η ^ 2 + 16 * γ ^ 2) * (9 * η ^ 2 + 16 * γ ^ 2)) := by
    unfold ImDquad
    rw [show γ - γ = (0 : ℝ) by ring, show η - η / 2 = η / 2 by ring,
        show η + η / 2 = 3 * η / 2 by ring]
    have h1 : (η / 2) ^ 2 + (γ + γ) ^ 2 ≠ 0 := by positivity
    have h2 : (η / 2) ^ 2 + (0 : ℝ) ^ 2 ≠ 0 := by positivity
    have h5 : (3 * η / 2) ^ 2 + (γ + γ) ^ 2 ≠ 0 := by positivity
    have h6 : (3 * η / 2) ^ 2 + (0 : ℝ) ^ 2 ≠ 0 := by positivity
    have hd1 : (η ^ 2 + 16 * γ ^ 2) ≠ 0 := by positivity
    have hd2 : (9 * η ^ 2 + 16 * γ ^ 2) ≠ 0 := by positivity
    have hηne : η ≠ 0 := ne_of_gt hη
    field_simp
    ring
  rw [key]
  apply div_pos
  · nlinarith [sq_nonneg η, sq_nonneg γ, mul_pos hη hη, sq_nonneg (η * γ),
      mul_pos (mul_pos hη hη) (mul_pos hη hη)]
  · positivity

/-- 🌟🌟🌟 **PROVED — every off-line displacement config has positive overflow.**
For `η ≠ 0`, the displacement field `z ↦ D_quad z γ η` satisfies the engine's
`PositiveUpperImaginaryEscape` predicate.  (Sign of `η` is handled by the
`η`-evenness `D_quad_neg_eta`; the positive-height witness then applies.) -/
theorem displacement_offline_escape (γ η : ℝ) (hη : η ≠ 0) :
    PositiveUpperImaginaryEscape (fun z => D_quad z γ η) := by
  rcases lt_or_gt_of_ne hη with hneg | hpos
  · -- η < 0: use evenness to reduce to -η > 0
    have hpos' : 0 < -η := by linarith
    refine ⟨⟨γ, (-η) / 2⟩, ?_, ?_⟩
    · show (0 : ℝ) < (-η) / 2
      linarith
    · show 0 < (D_quad (⟨γ, (-η) / 2⟩ : ℂ) γ η).im
      have := displacement_pos_escape_witness γ (-η) hpos'
      rw [D_quad_neg_eta] at this
      exact this
  · refine ⟨⟨γ, η / 2⟩, ?_, ?_⟩
    · show (0 : ℝ) < η / 2
      linarith
    · exact displacement_pos_escape_witness γ η hpos

-- ---------------------------------------------------------------------
-- The audit predicates, tied to actual zeros of `XiPullback`.
-- ---------------------------------------------------------------------

/-- **`HasOffLineZero f`** — `f` has a zero off the real axis (the failure of RH
for `f`). -/
def HasOffLineZero (f : ℂ → ℂ) : Prop :=
  ∃ ρ : ℂ, f ρ = 0 ∧ ρ.im ≠ 0

/-- **`Doff ρ`** — the true-minus-height displacement field attached to a zero
`ρ` of the pullback: the quadruple displacement of the config `(γ, η) = (Re ρ, Im ρ)`.
Its UHP pole is exactly `ρ` (when `Im ρ > 0`); `Doff ≡ 0` on-line (`Im ρ = 0`). -/
noncomputable def Doff (ρ : ℂ) : ℂ → ℂ :=
  fun z => D_quad z ρ.re ρ.im

/-- **The Route-B audit predicate.** No off-line zero of `XiPullback` produces a
displacement field with positive upper-imaginary overflow.  Equivalently (proved
below): RH. -/
def DoffNoPositiveOverflow : Prop :=
  ¬ ∃ ρ : ℂ, XiPullback ρ = 0 ∧ ρ.im ≠ 0 ∧ PositiveUpperImaginaryEscape (Doff ρ)

/-- 🌟🌟🌟 **PROVED — pole-probe: an off-line zero forces displacement overflow.**
If `XiPullback` has an off-line zero `ρ`, then its displacement field `Doff ρ`
has a non-real Cauchy pole at `ρ` and therefore exhibits positive upper-imaginary
overflow.  This is the §4 pole-probe applied to the displacement field:
the witness `⟨Re ρ, |Im ρ|/2⟩` makes the overflow explicit. -/
theorem offLineZero_forces_Doff_positiveOverflow
    (h : HasOffLineZero XiPullback) :
    ∃ ρ : ℂ, XiPullback ρ = 0 ∧ ρ.im ≠ 0 ∧ PositiveUpperImaginaryEscape (Doff ρ) := by
  obtain ⟨ρ, hρ0, hρim⟩ := h
  exact ⟨ρ, hρ0, hρim, displacement_offline_escape ρ.re ρ.im hρim⟩

/-- 🌟🌟🌟🌟 **PROVED — the exact RH-strength: forbidding displacement overflow ⟺ RH.**
`DoffNoPositiveOverflow ↔ (∀ ρ, XiPullback ρ = 0 → ρ.im = 0)`.

* `←` (RH ⟹ no overflow): if every zero is real there is no off-line zero, so the
  existential defining the overflow is empty.
* `→` (no overflow ⟹ RH): contrapositive of the pole-probe.  An off-line zero
  would, by `displacement_offline_escape`, supply exactly the forbidden overflow.

This records that the displacement gate is **not weaker** than RH — it IS RH. -/
theorem DoffNoPositiveOverflow_iff_RH :
    DoffNoPositiveOverflow ↔ (∀ ρ : ℂ, XiPullback ρ = 0 → ρ.im = 0) := by
  unfold DoffNoPositiveOverflow
  constructor
  · -- no overflow ⟹ RH
    intro hno ρ hρ0
    by_contra hρim
    exact hno ⟨ρ, hρ0, hρim, displacement_offline_escape ρ.re ρ.im hρim⟩
  · -- RH ⟹ no overflow
    intro hRH ⟨ρ, hρ0, hρim, _hesc⟩
    exact hρim (hRH ρ hρ0)

/-- **Convenience direction — RH ⟹ no displacement overflow.** -/
theorem RH_imp_DoffNoPositiveOverflow
    (hRH : ∀ ρ : ℂ, XiPullback ρ = 0 → ρ.im = 0) :
    DoffNoPositiveOverflow :=
  DoffNoPositiveOverflow_iff_RH.mpr hRH

/-- **Convenience direction — no displacement overflow ⟹ RH.** -/
theorem DoffNoPositiveOverflow_imp_RH
    (h : DoffNoPositiveOverflow) :
    ∀ ρ : ℂ, XiPullback ρ = 0 → ρ.im = 0 :=
  DoffNoPositiveOverflow_iff_RH.mp h

-- =====================================================================
-- TIE-TOGETHER.  Both routes hit the same wall.
-- =====================================================================

/-- **Route A summary.** The real-supported Cauchy representation core is
*sufficient* for the anti-Herglotz target (hence, with the engine's
pole-witness + Schwarz symmetry, for RH).  Restatement of
`antiHerglotz_of_realSupportedCauchy` for the audit index. -/
theorem realSupportedCauchy_imp_antiHerglotz :
    XiLogDerivRealSupportedCauchy → XiPullbackAntiHerglotzTarget :=
  antiHerglotz_of_realSupportedCauchy

/-- 🌟 **PROVED — the two routes are the same wall.**
Route B's audit predicate `DoffNoPositiveOverflow` is *equivalent* to RH; and RH
is what Route A's anti-Herglotz target delivers (through the engine's
`AbstractXiOverflowPackage.zeros_real`).  Concretely: if one assumes the engine's
own RH conclusion `RH_concl` (the shared target both routes aim at), then the
displacement audit predicate holds.  This pins both routes to the single wall
"all zeros of `XiPullback` are real". -/
theorem routes_share_wall
    (RH_concl : ∀ ρ : ℂ, XiPullback ρ = 0 → ρ.im = 0) :
    DoffNoPositiveOverflow ∧
      (XiLogDerivRealSupportedCauchy → XiPullbackAntiHerglotzTarget) :=
  ⟨RH_imp_DoffNoPositiveOverflow RH_concl, realSupportedCauchy_imp_antiHerglotz⟩

end HerglotzAudit

-- =====================================================================
-- Axiom audit.
-- =====================================================================

#print axioms HerglotzAudit.antiHerglotz_of_realSupportedCauchy
#print axioms HerglotzAudit.offLineZero_forces_Doff_positiveOverflow
#print axioms HerglotzAudit.DoffNoPositiveOverflow_iff_RH
#print axioms HerglotzAudit.displacement_offline_escape
#print axioms HerglotzAudit.routes_share_wall
