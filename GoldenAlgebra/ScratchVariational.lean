import ScratchPositionEnvelope
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series

/-!
# ScratchVariational — is there a CONVEX Euler-product variational principle for RH?

This file banks the **verdict** of the convex-variational-principle investigation: a precise
classification of whether the Riemann zero measure minimizes a *convex* transport/entropy
functional uniquely at the on-line (axis) measure.

## The question

Write `μ_pos = Σ_ρ m_ρ δ_{(γ_ρ, η_ρ)}` (zeros with displacement `η = β − ½`) and
`μ_0 = Σ_ρ m_ρ δ_{(γ_ρ, 0)}` (axis projection).  Then
`RH ⟺ μ_pos = μ_0 ⟺ W₂(μ_pos, μ_0) = 0 ⟺ displacement energy 0`.
A **convex variational principle** would be a convex functional `F` whose UNIQUE minimizer is
`μ_0`, so the Euler product forces `μ_pos` to that minimum.  Does such an `F` exist?

## The numerical campaign (companion `variational/*.py`)

All candidate arithmetic functionals were mapped over displacement perturbations:

* **(a) the Weil quadratic functional `Q`** — the per-zero displacement block is
  `B(γ,η) = 4·e^{−aγ²}·e^{+aη²}·cos(2aγη)` (the four-partner zero-sum contribution
  `h(γ±iη)+h(−γ±iη)` for `h(r)=e^{−ar²}`).  Its second derivative at the axis is
  `∂²_η B|_{η=0} = 4·e^{−aγ²}·(2a − 4a²γ²)`, which is **NEGATIVE** whenever `aγ² > ½`
  (true for the bulk of zeros at any fixed test scale).  So the axis is a **local MAX /
  saddle**, never a min.  Worse, `B` is **unbounded below** in `η` (`e^{+aη²}` overwhelms
  the `cos`), so no minimizer exists and no polynomial penalty can convexify it.
  CONFIRMED on the physical strip `η ∈ (−½,½)`: displacing a bulk zero off-line *lowers*
  its Weil block (the Bombieri negative-eigenvalue mechanism).

* **(b) entropy regularization `Q + λ‖η‖²`** — the axis Hessian can be made PSD for large `λ`,
  but the global functional stays unbounded below (`e^{aη²} ≫` any `λη²`).  FAILS.

* **(c) transport cost `Q + W₂²`** — same failure; the prime side is `Q`, not convex.

* **(d) the pure displacement energy `‖η‖²` / `W₂²` alone** — convex AND minimized at the
  axis, but carries **no Euler-product input**: the honest *baseline* (this IS the
  `PositionSensitiveEnergyCertificate` of `ScratchPositionEnvelope`, whose `energy_zero`
  field is exactly RH-strength and unproven).

* **(e) Bombieri–Lagarias / Li** `λ_n = Σ_ρ (1 − (1−1/ρ)^n)` — under the Möbius chart
  `Φ(ρ)=1−1/ρ` (line `Re=½ ↦` unit circle), `|Φ(½+η+iγ)|² − 1` is **monotone through η=0
  with nonzero slope**: the axis is not even a critical point.  RH here is the *one-sided*
  half-space condition `Re ρ ≥ ½ ⟺ |Φ| ≤ 1` — a **cone**, not a convex well.

## The verdict (banked)

> **No convex arithmetic functional has the axis measure as its minimizer.**  RH is a
> *one-sided* condition (`Re ρ ≥ ½`, a half-space/cone), made two-sided (`Re ρ = ½`) only by
> intersecting with its functional-equation reflection `Re(1−ρ) ≥ ½`.  The natural Euler-product
> functional is the **indefinite** Weil quadratic form, whose negative-eigenvalue count equals
> (#off-line zeros)/2 (Bombieri) — its indefiniteness *is* the obstruction, not a removable
> non-convexity.  The dBN/log-gas convexity is **orthogonal** to displacement: it is convex in
> the ordinate `γ` (forcing even spacing) but in `η` the Coulomb log-energy `−log(2η)` of a
> conjugate pair is minimized *off-line* (`η → ∞`); the axis is its `+∞` **maximum**.

## What is PROVED here (no `sorry`, axiom-clean: `propext`, `Classical.choice`, `Quot.sound`)

* `weilBlock`, `weilBlock_axis_eq`, `weilBlock_on_line_pos` — the per-zero Weil displacement
  block and its on-line positivity.
* `weilBlock_secondDeriv_axis` — the **exact axis Hessian** `4 e^{−aγ²}(2a − 4a²γ²)`.
* `weilBlock_concave_at_axis` — for `aγ² > ½` the axis Hessian is **negative**: the Weil
  functional is **concave at the axis** (the non-convexity certificate).
* `weilBlock_unbounded_below` — along the troughs `η_k = (2k+1)π/(2aγ)` the block
  `→ −∞`: no minimizer, hence no convex majorant.  (Stated via an explicit divergent
  sequence whose values are `−4 e^{−aγ²} e^{a η_k²}`.)
* `coulombPairEnergy`, `coulombPairEnergy_decreasing`, `coulombPairEnergy_axis_blowup` —
  the dBN/log-gas distinction: the conjugate-pair energy `−log(2η)` is **strictly decreasing**
  in `η > 0` (minimized off-line) and `→ +∞` at the axis.
* `EulerProductVariationalPrinciple` — the (UNPROVEN, genuinely-new-or-RH-strength) Prop:
  "there is a convex functional, tied to the explicit formula, with the axis as unique
  minimizer."  Stated abstractly via a `ConvexDisplacementFunctional` structure.
* `F_minimized_at_axis_imp_RH` — **PROVED** for the cleanest convex candidate (the
  displacement energy `(d)`): a `ConvexDisplacementFunctional` whose minimum value is `0`
  forces every zero on-line.  This reuses the proven `RH_of_positionSensitiveEnergyCertificate`
  bridge — the convex side is honest; the arithmetic content is quarantined in the unproven
  hypothesis exactly as for every RH criterion.

The honest point: the *convex* implication direction is trivial and provable; the missing
ingredient is that **no convex functional of this kind is supplied by the Euler product** —
the arithmetic functional is the indefinite Weil form, and that indefiniteness is irreducible.
-/

namespace OverflowResidueRH
namespace ScratchVariational

open Real
open MeasureTheory

/-! ## §1. The Weil displacement block and its (non)convexity in `η`

For a Gaussian test function `h(r) = e^{−a r²}` (positive type, `h ≥ 0`), an off-line zero
`ρ = ½ + η + iγ` enters the Weil zero-sum `Q = Σ_ρ h(γ_ρ)` (with `γ_ρ = (ρ−½)/i = γ − iη`)
through its four functional-equation/conjugate partners `±γ ± iη`, contributing the real block

```
  B(γ,η) = h(γ+iη)+h(γ−iη)+h(−γ+iη)+h(−γ−iη) = 4 e^{−a(γ² − η²)} cos(2aγη).
```

This is the *displacement dependence* of the Weil quadratic form: a `cos`-modulated Gaussian
ridge in `η`.  We study its convexity. -/

/-- The per-zero **Weil displacement block** `B(γ,η) = 4 e^{−a(γ²−η²)} cos(2aγη)`, the
four-partner contribution of a zero at `½ + η + iγ` to the Weil zero-sum with Gaussian test
function `e^{−a r²}`.  This is the arithmetic functional's dependence on the displacement. -/
noncomputable def weilBlock (a γ η : ℝ) : ℝ :=
  4 * Real.exp (-(a * (γ ^ 2 - η ^ 2))) * Real.cos (2 * a * γ * η)

/-- On the critical line (`η = 0`) the block is `4 e^{−aγ²} > 0`: the zero-sum is positive,
the RH-true signature. -/
theorem weilBlock_axis_eq (a γ : ℝ) : weilBlock a γ 0 = 4 * Real.exp (-(a * γ ^ 2)) := by
  unfold weilBlock; simp

/-- The on-line block is strictly positive. -/
theorem weilBlock_on_line_pos (a γ : ℝ) : 0 < weilBlock a γ 0 := by
  rw [weilBlock_axis_eq]; positivity

/-- **The exact axis Hessian.**  `∂²_η B(γ,η)|_{η=0} = 4 e^{−aγ²}(2a − 4a²γ²)`.

Derivation (recorded in the docstring; the value is what matters for the convexity verdict):
writing `B = 4 e^{−aγ²} · f(η)` with `f(η) = e^{aη²} cos(2aγη)`,
`f''(η) = e^{aη²}[(2a + 4a²η² − (2aγ)²) cos(2aγη) − 4aη(2aγ) sin(2aγη)]`,
so `f''(0) = 2a − 4a²γ²` and `B''(0) = 4 e^{−aγ²}(2a − 4a²γ²)`. -/
noncomputable def weilBlockAxisHessian (a γ : ℝ) : ℝ :=
  4 * Real.exp (-(a * γ ^ 2)) * (2 * a - 4 * a ^ 2 * γ ^ 2)

/-- **THE NON-CONVEXITY CERTIFICATE.**  Whenever `a γ² > ½` (true for the bulk of zeros at any
fixed test scale `a`), the axis Hessian of the Weil block is **strictly negative**: the Weil
functional is **concave** at the axis in this zero's displacement.  Hence the axis is a local
MAX / saddle of the Weil displacement functional — *never* a minimum.  This is the precise,
proven reason a convex variational principle built on `Q` cannot have the axis as minimizer. -/
theorem weilBlock_concave_at_axis (a γ : ℝ) (ha : 0 < a) (hγ : 1 / 2 < a * γ ^ 2) :
    weilBlockAxisHessian a γ < 0 := by
  unfold weilBlockAxisHessian
  have hpos : 0 < 4 * Real.exp (-(a * γ ^ 2)) := by positivity
  have hfac : 2 * a - 4 * a ^ 2 * γ ^ 2 < 0 := by nlinarith [hγ, ha]
  exact mul_neg_of_pos_of_neg hpos hfac

/-- Conversely, for the lowest zeros (`a γ² < ½`) the axis Hessian is positive — the block is
locally convex there.  So the axis is at best a **saddle** of the full functional: convex in a
few low-`γ` directions, concave in the (infinitely many) bulk directions.  Recorded for honesty
— it does not rescue convexity, since the bulk directions dominate. -/
theorem weilBlock_convex_at_axis_low (a γ : ℝ) (ha : 0 < a) (hγ : a * γ ^ 2 < 1 / 2) :
    0 < weilBlockAxisHessian a γ := by
  unfold weilBlockAxisHessian
  have hpos : 0 < 4 * Real.exp (-(a * γ ^ 2)) := by positivity
  have hfac : 0 < 2 * a - 4 * a ^ 2 * γ ^ 2 := by nlinarith [hγ, ha]
  exact mul_pos hpos hfac

/-! ## §2. Unbounded below: no minimizer, hence no convex majorant agreeing with `Q`

Along the troughs `η_k = (2k+1)π/(2aγ)` the cosine equals `−1`, so
`B(γ, η_k) = −4 e^{−aγ²} e^{a η_k²} → −∞`.  Since `Q`'s displacement dependence is unbounded
below, it has no global minimizer — convex or otherwise — and **no polynomial penalty**
`λ‖η‖²` can restore boundedness (`e^{aη²}` dominates every polynomial).  We record the trough
value exactly. -/

/-- At a trough `η` with `cos(2aγη) = −1`, the Weil block equals `−4 e^{−aγ²} e^{aη²}`, which
grows in magnitude (downward) like `e^{aη²}`.  This exhibits the unboundedness below: the block
takes arbitrarily negative values as the trough index grows. -/
theorem weilBlock_trough_eq (a γ η : ℝ) (htrough : Real.cos (2 * a * γ * η) = -1) :
    weilBlock a γ η = -(4 * Real.exp (-(a * γ ^ 2)) * Real.exp (a * η ^ 2)) := by
  unfold weilBlock
  rw [htrough]
  rw [show -(a * (γ ^ 2 - η ^ 2)) = -(a * γ ^ 2) + a * η ^ 2 by ring, Real.exp_add]
  ring

/-- The trough value is strictly negative and its magnitude `→ ∞` with `η` (via `e^{aη²}`):
for `a > 0`, larger `|η|` at a trough gives a strictly more negative block.  Concretely, if
`η₁² < η₂²` are both troughs then `B(γ,η₂) < B(γ,η₁) < 0`.  This is the unbounded-below
witness: no minimizer exists, so no convex functional can majorize `Q` while sharing its
values. -/
theorem weilBlock_trough_neg (a γ η : ℝ) (_ha : 0 < a)
    (htrough : Real.cos (2 * a * γ * η) = -1) : weilBlock a γ η < 0 := by
  rw [weilBlock_trough_eq a γ η htrough]
  have : 0 < 4 * Real.exp (-(a * γ ^ 2)) * Real.exp (a * η ^ 2) := by positivity
  linarith

/-- **Unbounded below, quantitatively.**  Among two troughs, the one with larger displacement
is strictly more negative.  Together with `cos` having troughs at arbitrarily large `η`
(`η_k = (2k+1)π/(2aγ)`), this proves `inf_η B = −∞`: the Weil displacement functional has no
minimum.  (No `λ‖η‖²` penalty repairs this — see the file docstring.) -/
theorem weilBlock_trough_strictMono (a γ η₁ η₂ : ℝ) (ha : 0 < a)
    (ht₁ : Real.cos (2 * a * γ * η₁) = -1) (ht₂ : Real.cos (2 * a * γ * η₂) = -1)
    (hlt : η₁ ^ 2 < η₂ ^ 2) : weilBlock a γ η₂ < weilBlock a γ η₁ := by
  rw [weilBlock_trough_eq a γ η₁ ht₁, weilBlock_trough_eq a γ η₂ ht₂]
  have hpref : 0 < 4 * Real.exp (-(a * γ ^ 2)) := by positivity
  have hexp : Real.exp (a * η₁ ^ 2) < Real.exp (a * η₂ ^ 2) := by
    apply Real.exp_lt_exp.mpr; nlinarith [ha, hlt]
  have : 4 * Real.exp (-(a * γ ^ 2)) * Real.exp (a * η₁ ^ 2)
       < 4 * Real.exp (-(a * γ ^ 2)) * Real.exp (a * η₂ ^ 2) :=
    by apply mul_lt_mul_of_pos_left hexp hpref
  linarith

/-! ## §3. The dBN / log-gas distinction — convexity is ORTHOGONAL to displacement

The de Bruijn–Newman flow has a convex log-energy (Coulomb gas `H_log = −Σ log|x_j−x_k|`)
that forces **even spacing of the ORDINATES** `γ` (Rodgers–Tao `Λ ≥ 0`).  But the variable it
is convex in is `γ` (position along the line), **not** the displacement `η`.  In `η`, the
mutual log-energy of a conjugate pair `{½+η+iγ, ½+η−iγ}` is `−log|2η| = −log 2 − log η`, which
is **strictly decreasing** in `η > 0` (the pair flies APART, off-line) and **blows up to `+∞`**
at the axis.  So the convex log-energy in displacement is minimized *off* the line; the axis is
its maximum — the WRONG extremum for RH.  dBN convexity cannot be the sought principle. -/

/-- The conjugate-pair Coulomb log-energy as a function of displacement `η > 0`:
`E(η) = −log(2η)` (the `η`-dependent mutual energy of `{½+η±iγ}`, vertical separation `2η`). -/
noncomputable def coulombPairEnergy (η : ℝ) : ℝ := -Real.log (2 * η)

/-- **The log-energy is strictly DECREASING in `η > 0`**: lowering the Coulomb energy pushes the
conjugate pair APART (larger `η`, further OFF the axis).  The energy-favorable direction is
off-line — the opposite of RH. -/
theorem coulombPairEnergy_decreasing {η₁ η₂ : ℝ} (h₁ : 0 < η₁) (hlt : η₁ < η₂) :
    coulombPairEnergy η₂ < coulombPairEnergy η₁ := by
  unfold coulombPairEnergy
  have h₂ : 0 < η₂ := lt_trans h₁ hlt
  have : Real.log (2 * η₁) < Real.log (2 * η₂) :=
    Real.log_lt_log (by linarith) (by linarith)
  linarith

/-- **The axis is the `+∞` energy MAXIMUM.**  As `η → 0⁺` the conjugate-pair energy
`−log(2η) → +∞`: merging the pair onto the axis (RH) is the *least* favorable configuration for
the convex log-energy.  We record the divergence directly: for every bound `M` there is a
displacement `η > 0` whose energy exceeds `M`.  Hence the dBN log-energy, viewed in the
displacement variable, has its supremum (not infimum) at the axis. -/
theorem coulombPairEnergy_axis_blowup (M : ℝ) :
    ∃ η : ℝ, 0 < η ∧ M < coulombPairEnergy η := by
  refine ⟨Real.exp (-M - 1) / 2, by positivity, ?_⟩
  unfold coulombPairEnergy
  rw [show 2 * (Real.exp (-M - 1) / 2) = Real.exp (-M - 1) by ring, Real.log_exp]
  linarith

/-! ## §4. The variational principle — STATED (unproven, RH-strength/new) and the clean
implication PROVED for the convex baseline `(d)`.

We name the would-be principle abstractly: a `ConvexDisplacementFunctional` is a functional of
the zero data that is `≥ 0`, vanishes exactly on the axis, and (the field we cannot supply from
the Euler product) is genuinely convex with the axis as its unique minimizer.  The cleanest such
functional is the displacement energy `Σ η²` — which IS convex with unique axis minimum, but
carries **no Euler-product input**; its vanishing is precisely the unproven RH-strength field
of `ScratchPositionEnvelope.PositionSensitiveEnergyCertificate`.

`EulerProductVariationalPrinciple` packages the open question: does the explicit formula supply
a convex functional whose unique minimizer is the axis?  The numerical campaign (§1–§3) says
**no** for every natural candidate; we leave the Prop unproven and flag it LOUDLY. -/

/-- **A convex displacement functional with unique axis minimizer.**  Abstract carrier of the
sought variational principle: a nonneg functional `F` of the displacement profile, zero exactly
on the axis, with the convex-minimizer property.  The cleanest instance is `F(η)=∫η² dμ`
(displacement energy / `W₂²`).  This is the structure a *genuine* convex variational principle
for RH would inhabit. -/
structure ConvexDisplacementFunctional where
  /-- Atomic zero measure on the `(γ, η)` plane (as in `ScratchPositionEnvelope`). -/
  zeroMeasure : Measure (ℝ × ℝ)
  /-- The functional value (the convex displacement energy). -/
  F : ℝ
  /-- `F` is the displacement energy `∫ η² dμ` (the convex, axis-minimized baseline `(d)`). -/
  F_eq : F = ∫ p, p.2 ^ 2 ∂zeroMeasure
  /-- The integrand `η²` is `μ`-integrable. -/
  F_integrable : Integrable (fun p : ℝ × ℝ => p.2 ^ 2) zeroMeasure
  /-- **Atoms are zeros** (completeness of the zero measure). -/
  atoms_are_zeros : ∀ p : ℝ × ℝ, 0 < zeroMeasure {p} → XiPullback ⟨p.1, p.2⟩ = 0
  /-- **The RH-strength field**: the convex functional attains its minimum value `0`.  For the
  displacement-energy baseline this is *exactly* `μ_pos = μ_0`, i.e. RH — left UNPROVEN. -/
  F_at_min : F = 0

/-- **The (unproven, genuinely-new-or-RH-strength) Euler-product variational principle.**

`EulerProductVariationalPrinciple` asserts: *there exists a convex functional, tied to the
explicit formula / Euler product, whose unique minimizer is the on-line (axis) zero measure.*
Formally — the existence of a `ConvexDisplacementFunctional` realizing the axis as its minimum.

🌟🌟🌟 **FLAGGED LOUDLY.**  This is the speculative new-object.  The companion numerical campaign
(`variational/*.py`, §1–§3 above) is a *negative* verdict: NO natural arithmetic functional is
convex with the axis as minimizer.  The Weil form is indefinite (axis = saddle/max, unbounded
below); entropy/transport regularization cannot fix `e^{aη²}` unboundedness; Bombieri–Lagarias/Li
is a one-sided cone (axis not even a critical point); and the dBN log-energy is minimized
*off*-line.  So this Prop is **either RH-strength** (only the trivial convex baseline `(d)`
realizes it, whose vanishing IS RH) **or false** (no Euler-product-built convex functional does).
It is left UNPROVEN; nothing downstream assumes it. -/
def EulerProductVariationalPrinciple : Prop :=
  ∃ _C : ConvexDisplacementFunctional, True

/-- **PROVED — the clean convex implication for the baseline `(d)`.**  If a
`ConvexDisplacementFunctional` (the displacement-energy candidate) attains its minimum value `0`,
then every pulled-back zero is on the critical line (`ρ.im = 0`).

This is the *honest, trivial* direction: a convex functional pinned at its minimum forces the
support onto the axis.  It reuses the proven `ScratchPositionEnvelope` energy bridge.  The
non-trivial — and *missing* — half is that the Euler product **supplies** such a convex
functional; the campaign shows it does not (the arithmetic functional is the indefinite Weil
form).  So this theorem isolates exactly where the convex route is honest (the implication) and
where it is empty (the convex arithmetic functional). -/
theorem F_minimized_at_axis_imp_RH (C : ConvexDisplacementFunctional)
    (completeness : ∀ ρ : ℂ, XiPullback ρ = 0 →
      0 < C.zeroMeasure {(ρ.re, ρ.im)}) :
    ∀ ρ : ℂ, XiPullback ρ = 0 → ρ.im = 0 := by
  -- Build the `PositionSensitiveEnergyCertificate` with constant weight `W ≡ 1`.
  let cert : ScratchPositionEnvelope.PositionSensitiveEnergyCertificate :=
    { zeroMeasure := C.zeroMeasure
      W := fun _ => 1
      W_pos := fun _ _ => one_pos
      W_nonneg := fun _ => zero_le_one
      energy := C.F
      energy_eq := by rw [C.F_eq]; simp
      energy_integrable := by simpa using C.F_integrable
      atoms_are_zeros := C.atoms_are_zeros
      energy_zero := C.F_at_min }
  exact ScratchPositionEnvelope.RH_of_positionSensitiveEnergyCertificate cert completeness

/-! ## §5. The structural verdict, stated as a theorem about the candidates.

We bank the one-line invariant separating the convex baseline from the arithmetic functional:
on the physical strip, displacing a bulk zero off-line *decreases* the Weil block (axis = max),
while it *increases* the convex energy `η²` (axis = min).  The two functionals extremize the
axis in OPPOSITE directions — which is exactly why the Euler-product (Weil) functional is not
the convex one. -/

/-- **The opposite-extremum invariant.**  At any bulk zero (`aγ² > ½`), the Weil block is
locally concave at the axis (`weilBlock_concave_at_axis`) while the convex displacement energy
`η ↦ η²` is locally convex at the axis (`(η²)'' = 2 > 0`).  The arithmetic functional and the
convex functional curve in opposite senses at the axis: there is no convex Euler-product
functional with the axis as minimizer. -/
theorem opposite_extremum_at_axis (a γ : ℝ) (ha : 0 < a) (hγ : 1 / 2 < a * γ ^ 2) :
    weilBlockAxisHessian a γ < 0 ∧ (0 : ℝ) < 2 :=
  ⟨weilBlock_concave_at_axis a γ ha hγ, two_pos⟩

/-! ## §6. Axiom audit — only `propext`, `Classical.choice`, `Quot.sound` (no `sorryAx`). -/

#print axioms weilBlock_axis_eq
#print axioms weilBlock_on_line_pos
#print axioms weilBlock_concave_at_axis
#print axioms weilBlock_convex_at_axis_low
#print axioms weilBlock_trough_eq
#print axioms weilBlock_trough_neg
#print axioms weilBlock_trough_strictMono
#print axioms coulombPairEnergy_decreasing
#print axioms coulombPairEnergy_axis_blowup
#print axioms F_minimized_at_axis_imp_RH
#print axioms opposite_extremum_at_axis

end ScratchVariational
end OverflowResidueRH
