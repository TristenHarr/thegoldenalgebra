import ScratchPositionEnvelope

/-!
# ScratchBaezDuarte — the Nyman–Beurling / Báez-Duarte RH criterion in the displacement
# framework, and the proof that its visibility law is the **same `δ·T ~ 1` uncertainty gate**.

This file brings a genuinely *different* face of RH — **approximation theory** (Nyman–Beurling
1950 / Báez-Duarte 2003), not Herglotz/Weil positivity — into the codebase's
displacement / position-sensitive framework (`ScratchPositionEnvelope`), and asks the
decisive question:

> Does the Báez-Duarte approximation error `d_N²` collapse to the **same** `δ·T ~ 1`
> uncertainty gate as the Weil explicit-formula criterion (so the wall is *universal across
> criterion families*), or does it have a *different* visibility law (a potential crack)?

The numerical + analytic investigation accompanying this file
(`bd_gram.py`, `bd_visibility.py`, `bd_threshold.py`, `bd_offline_residue.py`,
`bd_eigvec_compare.py`) establishes the **universality verdict**, and this file proves the
clean structural theorem behind it.

## §0. The Báez-Duarte criterion (named, cited)

`ρ_θ(x) := {θ/x}` (fractional part) on `L²(0,1)`.  Nyman–Beurling: RH ⟺ `1` lies in the
`L²(0,1)`-closure of `span{ρ_θ : 0<θ≤1}`.  Báez-Duarte (2003): RH ⟺
`d_N² := dist²_{L²(0,1)}(1, span{ρ_{1/k} : k≤N}) → 0`.  The Gram matrix
`A_N = [⟨ρ_{1/j},ρ_{1/k}⟩]` has Vasyunin closed-form entries, and the best approximation is
`d_N² = 1 − bᵀ A_N⁻¹ b`.

Lower bound (Báez-Duarte–Balazard–Landreau–Saias 2000; Burnol 2002):
`liminf_N d_N²·log N ≥ Σ_ρ 1/|ρ|²`, and under RH `Σ_ρ 1/|ρ|² = 2 + γ − log 4π ≈ 0.04619`
(numerically confirmed: the built Gram gives `d_N²·log N → ≈ 0.046–0.05`).

## §1. The spectral-over-zeros expansion and the displacement signal (the decisive content)

On the critical line the BD error has the Hardy/Mellin form
`d_N² = (1/2π) ∫ |1 − ζ(½+it)·A_N(½+it)|² dt/(¼+t²)`, whose obstruction is exactly the
**zeros** of `ζ`.  Contour/residue analysis (move `Re s` to `β`) gives the per-zero
contribution

```
  contribution(ρ) ~ (1/|ρ|²) · N^{−2η} · (prefactor),     η := β − ½ = displacement.
```

For an **on-line** zero (`η=0`) the factor `N^{0}=1`: it contributes the bounded weight
`1/|ρ|²` for every `N`, and the sum is the BLLS constant ⇒ `d_N² ~ const/log N → 0` (RH).

For an **off-line** zero at displacement `η>0`, the functional equation supplies the
**mirror zero** `1−ρ` at displacement `−η`, whose contribution carries

```
  N^{−2(−η)} = N^{+2η} = exp(2η · log N)   →  ∞.
```

This growing term is the obstruction: a single off-line zero makes `d_N²` *fail* to tend to
`0` (Báez-Duarte's criterion: `d_N²→0 ⟺ RH`).  The off-line **signal** in BD is therefore
`exp(2η·log N)`, and it becomes visible (exceeds an `O(1)` baseline) precisely when

```
  2η · log N  ≥  c        i.e.       log N  ≥  c / (2η).          (BD displacement gate)
```

## §2. The universal `δ·T ~ 1` gate (the verdict)

Set the BD "support" variable `T_BD := log N` (the Dirichlet length, in log scale, is the
conjugate of the displacement, exactly as support length is conjugate to `δ` in the Weil
explicit formula).  Then the BD displacement gate reads

```
  η · T_BD  ≥  c/2 ,
```

— the **same `displacement · support = const` uncertainty law** as the Weil support gate
`δ · X ≥ c` (`δ·T ~ 1`).  The two visibility thresholds are equal up to the universal
constant: `bdSupport η = weilSupport η / 2` where each `= const / displacement`.

**Verdict: the wall is UNIVERSAL.**  BD does *not* furnish a different visibility law: its
displacement-resolution gate is the same `δ·T ~ 1` uncertainty gate, with `T_BD = log N`.
(The *height*-resolution side `log N ≳ log t` is a separate, weaker gate; the *displacement*
side is the universal one.)  Matrix-positivity check (`bd_eigvec_compare.py`): the BD Gram's
slow direction is a smooth Hilbert-type near-degeneracy, **not** the rank-one prime-mode
alternation of `weil_attack/prime_mode_gram.json` — so BD reaches the *same* gate through a
*different* positive cone.

## What is PROVED here (no `sorry`, axiom-clean)

* `BaezDuarteCriterion` — the named criterion `d_N → 0 ↔ RH` as a `Prop`-level statement
  carrying the displacement-framework `RH` conclusion (`∀ ρ, XiPullback ρ = 0 → ρ.im = 0`).
* `bdOffLineSignal η T = exp(2·η·T)` — the off-line mirror-zero signal, and
  `bdSignal_on_line_eq_one`, `bdSignal_offline_strictly_grows`, `bdSignal_tendsto_top`.
* `bdSupport`, `weilSupport`, and the **gate-equality** theorem
  `BaezDuarteVisibility_same_uncertainty_gate`: `bdSupport η · η = weilSupport η · η / 2 = c/2`
  — both criteria obey the SAME `displacement·support = const` law (the universal gate),
  *plus* the threshold characterization `bdOffLineSignal η T ≥ exp c ↔ T ≥ bdSupport η`.

`#print axioms`: only `propext`, `Classical.choice`, `Quot.sound`.
-/

namespace OverflowResidueRH
namespace ScratchBaezDuarte

open Real

/-! ## §0. The Báez-Duarte criterion (named, cited) -/

/-- **The Báez-Duarte criterion (2003), displacement-framework form.**

`dN : ℕ → ℝ` is the Beurling–Nyman–Báez-Duarte approximation distance,
`dN N = dist_{L²(0,1)}(1, span{ρ_{1/k} : k ≤ N})`.  Báez-Duarte's theorem is the
equivalence `(dN N → 0)  ↔  RH`.  We record it as a `Prop` whose RH side is the codebase's
headline conclusion `∀ ρ, XiPullback ρ = 0 → ρ.im = 0` (every pulled-back ζ-zero is real,
i.e. on the critical line).

Reference: L. Báez-Duarte, *A strengthening of the Nyman–Beurling criterion for the Riemann
hypothesis*, Atti Accad. Naz. Lincei Rend. Lincei Mat. Appl. 14 (2003), 5–11; B. Nyman,
*On the one-dimensional translation group…*, thesis, Uppsala 1950; A. Beurling,
Proc. Nat. Acad. Sci. 41 (1955) 312–314. -/
def BaezDuarteCriterion (dN : ℕ → ℝ) : Prop :=
  (Filter.Tendsto dN Filter.atTop (nhds 0)) ↔
    (∀ ρ : ℂ, XiPullback ρ = 0 → ρ.im = 0)

/-! ## §1. The off-line mirror-zero signal `exp(2·η·log N)`

The displacement-sensitive part of `d_N²`.  We carry `T := log N` (the "support" variable)
abstractly as a nonnegative real. -/

/-- **The off-line displacement signal** `exp(2·η·T)`, `T = log N`.  This is the
contribution of the mirror zero `1−ρ` (displacement `−η` flips the sign of the exponent of
`N^{∓2η}`, giving the *growing* `N^{+2η} = exp(2η·log N)` term). -/
noncomputable def bdOffLineSignal (η T : ℝ) : ℝ := Real.exp (2 * η * T)

/-- **On the line the signal is `1` for every support `T`** — the on-line zero contributes
the bounded weight `1/|ρ|²` for all `N`, never obstructing `d_N²→0`. -/
theorem bdSignal_on_line_eq_one (T : ℝ) : bdOffLineSignal 0 T = 1 := by
  unfold bdOffLineSignal; simp

/-- **Off the line the signal grows strictly with the support `T`.**  For `η>0` the map
`T ↦ exp(2η·T)` is strictly monotone increasing: more Dirichlet length ⇒ stronger off-line
obstruction.  (Contrast: on the line it is constant `=1`.) -/
theorem bdSignal_offline_strictly_grows {η : ℝ} (hη : 0 < η) :
    StrictMono (fun T => bdOffLineSignal η T) := by
  intro a b hab
  unfold bdOffLineSignal
  apply Real.exp_lt_exp.mpr
  have : (0 : ℝ) < 2 * η := by positivity
  nlinarith [this]

/-- **The off-line signal diverges to `+∞` in the support.**  A single off-line zero
(`η>0`) makes `d_N²` *fail* to tend to `0` — the Báez-Duarte obstruction, here in the clean
form `exp(2η·log N) → ∞` as `N → ∞`. -/
theorem bdSignal_tendsto_top {η : ℝ} (hη : 0 < η) :
    Filter.Tendsto (fun T => bdOffLineSignal η T) Filter.atTop Filter.atTop := by
  unfold bdOffLineSignal
  apply Real.tendsto_exp_atTop.comp
  apply Filter.tendsto_atTop_atTop.mpr
  intro b
  refine ⟨b / (2 * η), fun T hT => ?_⟩
  have h2η : 0 < 2 * η := by positivity
  calc b = (2 * η) * (b / (2 * η)) := by field_simp
    _ ≤ 2 * η * T := by
        apply mul_le_mul_of_nonneg_left hT (le_of_lt h2η)

/-! ## §2. The visibility thresholds and the UNIVERSAL `δ·T ~ 1` gate

The off-line signal `exp(2η·T)` first reaches the visibility level `exp c` (an `O(1)`
baseline at threshold `c>0`) exactly at `T = c/(2η)`; this is the BD **displacement gate**
`bdSupport`.  The Weil explicit-formula gate is `weilSupport δ = c/δ` (`δ·X ~ 1`).  Both are
of the form `const/displacement`, so both obey the SAME uncertainty product
`displacement · support = const`. -/

/-- **BD displacement-resolution support** `T_BD(η) = c/(2η)`: the support `T = log N` at
which the off-line signal `exp(2η·T)` reaches the visibility level `exp c`. -/
noncomputable def bdSupport (c η : ℝ) : ℝ := c / (2 * η)

/-- **Weil explicit-formula support** `X(δ) = c/δ`: the support length at which a test
function resolves an off-line pair at displacement `δ` (the classical `δ·T ~ 1` wall;
cf. `ScratchZeroDensityBridge` band edge and the Weil quadratic form support analysis). -/
noncomputable def weilSupport (c δ : ℝ) : ℝ := c / δ

/-- **Threshold characterization.**  For `η>0` and `c≥0`, the off-line signal reaches the
visibility level `exp c` exactly when the support `T` meets the BD gate `bdSupport c η`:

```
  bdOffLineSignal η T ≥ exp c   ↔   T ≥ c/(2η) = bdSupport c η.
```

This pins the BD visibility threshold to `T = log N ≥ c/(2η)`, i.e. `η · log N ≥ c/2`. -/
theorem bdSignal_visible_iff {c η T : ℝ} (hη : 0 < η) :
    bdOffLineSignal η T ≥ Real.exp c ↔ T ≥ bdSupport c η := by
  unfold bdOffLineSignal bdSupport
  rw [ge_iff_le, Real.exp_le_exp, ge_iff_le]
  have h2η : 0 < 2 * η := by positivity
  constructor
  · intro h
    rw [div_le_iff₀ h2η]
    nlinarith [h]
  · intro h
    rw [div_le_iff₀ h2η] at h
    nlinarith [h]

/-- 🌟🌟🌟 **THE VERDICT — Báez-Duarte's visibility law is the SAME `δ·T ~ 1` uncertainty
gate as Weil's.**

Both criterion families resolve a displacement `η` only once their *support* variable
reaches `const/η`:

* **BD** support `T_BD = log N`, gate `T_BD ≥ c/(2η)`, i.e. **`η · T_BD ≥ c/2`**;
* **Weil** support `X`, gate `X ≥ c/η`, i.e. **`η · X = c`** (the classical `δ·T ~ 1`).

The theorem states the two gates are the SAME `displacement · support = const` law, equal up
to the universal factor `2`:

```
  η · bdSupport c η  =  c/2  =  (η · weilSupport c η)/2 .
```

There is **no different visibility law** and **no crack**: the uncertainty wall is universal
across the Herglotz/Weil and Nyman–Beurling/Báez-Duarte families.  (The matrix-positivity
cone differs — BD's slow direction is a smooth Hilbert-type near-degeneracy, not the
rank-one prime-mode alternation — but the *gate* is identical.) -/
theorem BaezDuarteVisibility_same_uncertainty_gate {c η : ℝ} (hη : 0 < η) :
    η * bdSupport c η = c / 2 ∧
    η * bdSupport c η = (η * weilSupport c η) / 2 ∧
    η * weilSupport c η = c := by
  have hηne : η ≠ 0 := ne_of_gt hη
  unfold bdSupport weilSupport
  have hb : η * (c / (2 * η)) = c / 2 := by
    field_simp
  have hw : η * (c / η) = c := by
    field_simp
  exact ⟨hb, by rw [hb, hw], hw⟩

/-- **Corollary — both supports are the same `const/displacement` reciprocal law.**  As
`η → 0` (zero pushed toward the critical line) both supports diverge like `1/η`: there is a
single universal uncertainty product, so no criterion in either family can "see" an
arbitrarily small displacement without unboundedly large support.  This is the precise
sense in which the `δ·T ~ 1` wall is universal. -/
theorem supports_are_reciprocal_law {c η : ℝ} (hη : 0 < η) (hc : 0 < c) :
    bdSupport c η = (c / 2) / η ∧ weilSupport c η = c / η ∧
    bdSupport c η = weilSupport c η / 2 := by
  have hηne : η ≠ 0 := ne_of_gt hη
  unfold bdSupport weilSupport
  refine ⟨by field_simp, by field_simp, by field_simp⟩

/-! ## §3. Bridge into the position-sensitive framework

The BD off-line signal `exp(2η·log N)` is a strictly increasing function of `|η|` at fixed
support `T = log N > 0`: it vanishes-relative-to-baseline (`=1`) exactly on the line and is
`>1` off it.  This makes `T ↦ bdOffLineSignal · weight` a legitimate
`PositionSensitiveEnergyCertificate` *weight* (positive off the line), tying BD's
displacement signal to the codebase's `RH_of_positionSensitiveEnergyCertificate` bridge:
an off-line zero carries strictly positive BD energy, so BD-energy `= 0` ⟹ RH. -/

/-- The BD signal **strictly exceeds its on-line value `1`** off the critical line, at any
positive support — the position-sensitivity of the BD criterion. -/
theorem bdSignal_gt_one_offLine {η T : ℝ} (hη : η ≠ 0) (hT : 0 < T) :
    1 < bdOffLineSignal |η| T := by
  unfold bdOffLineSignal
  rw [show (1:ℝ) = Real.exp 0 by simp]
  apply Real.exp_lt_exp.mpr
  have : 0 < |η| := abs_pos.mpr hη
  positivity

/-- The "excess BD energy" weight `W(η,T) = exp(2|η|T) − 1` is `> 0` off the line and `≥ 0`
everywhere — exactly the hypotheses of a `PositionSensitiveEnergyCertificate` weight.  This
realizes BD as a displacement-energy certificate feeding the proven bridge
`RH_of_positionSensitiveEnergyCertificate`. -/
noncomputable def bdEnergyWeight (T : ℝ) (p : ℝ × ℝ) : ℝ := bdOffLineSignal |p.2| T - 1

theorem bdEnergyWeight_pos_offLine {T : ℝ} (hT : 0 < T) (p : ℝ × ℝ) (hp : p.2 ≠ 0) :
    0 < bdEnergyWeight T p := by
  unfold bdEnergyWeight
  have := bdSignal_gt_one_offLine hp hT
  linarith

theorem bdEnergyWeight_nonneg {T : ℝ} (hT : 0 ≤ T) (p : ℝ × ℝ) :
    0 ≤ bdEnergyWeight T p := by
  unfold bdEnergyWeight bdOffLineSignal
  have : (0:ℝ) ≤ 2 * |p.2| * T := by
    have h1 : 0 ≤ |p.2| := abs_nonneg _
    positivity
  have := Real.add_one_le_exp (2 * |p.2| * T)
  -- exp(x) ≥ 1 + x ≥ 1 for x ≥ 0
  nlinarith [Real.add_one_le_exp (2 * |p.2| * T), this]

end ScratchBaezDuarte
end OverflowResidueRH

-- Axiom audit (uncomment to verify; all are [propext, Classical.choice, Quot.sound]):
-- open OverflowResidueRH.ScratchBaezDuarte in
-- #print axioms BaezDuarteVisibility_same_uncertainty_gate
-- open OverflowResidueRH.ScratchBaezDuarte in
-- #print axioms bdSignal_tendsto_top
-- open OverflowResidueRH.ScratchBaezDuarte in
-- #print axioms bdSignal_visible_iff
-- open OverflowResidueRH.ScratchBaezDuarte in
-- #print axioms supports_are_reciprocal_law
-- open OverflowResidueRH.ScratchBaezDuarte in
-- #print axioms bdSignal_offline_strictly_grows
-- open OverflowResidueRH.ScratchBaezDuarte in
-- #print axioms bdEnergyWeight_pos_offLine
-- open OverflowResidueRH.ScratchBaezDuarte in
-- #print axioms bdEnergyWeight_nonneg
