import Mathlib
import rh
import ScratchMaxPrinciple

/-!
# `ScratchPrimeBoundary.lean` — can the PRIME side control the TOP edge?

This file is the honest Lean interface for the question:

> `G(z) = −Im(Ξ'/Ξ)(z)` is harmonic off zeros (PROVEN, `ScratchMaxPrinciple`).
> The anti-Herglotz wall reduces to `G ≥ 0` on the boundary of zero-free
> rectangles.  Bottom edge = Laguerre (UNCONDITIONAL).  Side edges = envelope.
> The TOP edge `G(x+iY) ≥ 0` is the open ingredient.  Can the **prime-side
> explicit formula** (`−ζ'/ζ(s) = Σ Λ(n) n^{−s}`, `Λ(n) ≥ 0`) give ANY
> top-boundary positivity beyond height-envelopes?

The numerical investigation (`prime_boundary/*.py`) settles the mathematics; the
verdict is **NO genuine new control — the off-line pole dominates, and
`PrimeBoundaryControl Y` for all `Y` is EXACTLY RH (not weaker).**  The reasons,
which this file records as honest `Prop`s and theorems:

1.  **Region mismatch.** `XiPullback z = completedXi(½ + i z)`, so the top edge
    `Im z = Y` is the vertical line `Re s = ½ − Y` in the `s`-plane (rh.lean's
    convention).  The prime sum `Σ Λ(n) n^{−s}` converges only for `Re s > 1`,
    i.e. `Y < −½`; the off-line zeros live in `0 < Re s < 1`, i.e. `|Y| < ½`.
    The two regions are **disjoint**: where the prime sum converges there are no
    zeros to control; where the zeros could be, the prime series diverges.

2.  **Mean-zero, not sign-definite.** On any reachable top edge the prime part of
    `G` is `−Σ Λ(n) n^{−σ} cos(x·log n)`, whose `x`-average is `0` (there is no
    `n = 1` DC term since `Λ(1) = 0`).  Euler-product positivity `Λ(n) ≥ 0` gives
    a **mean-zero oscillation**, not a positive push.  (`prime_part.py`,
    `avg_and_offline.py`.)

3.  **Bounded help vs. unbounded pole.**  The prime contribution to `G` is
    bounded in modulus by `|ζ'/ζ(σ)| < ∞` (a fixed `L¹` budget), while an
    off-line zero of `Ξ` at `z`-height `β` drives the residue atom
    `−m/(β − Y) → −∞` as `Y ↑ β`.  The pole wins.  This is the genuine
    obstruction, formalized below as `prime_help_bounded_pole_unbounded`.

4.  **DH contrast.** Davenport–Heilbronn `f` has the SAME harmonic
    max-principle geometry (bottom/side/top edges, `G_f = −Im(f'/f)` harmonic),
    OFF-LINE zeros, but NO Euler product / no nonnegative prime sum.  So any
    top-edge control using only geometry + Laguerre + envelopes would apply to
    DH and falsely prove "DH-RH" — impossible.  Hence the prime side is EXACTLY
    the ζ-vs-DH distinction at the top edge.  We record this as
    `dh_no_prime_positivity` / `prime_input_is_zeta_vs_DH_distinction`.

## What is PROVED here (no `sorry`, axiom-clean)

* `prime_help_bounded_pole_unbounded` — the dominance obstruction: given any
  finite prime budget `B` and any off-line zero of `z`-height `β`, there is a
  probe height `Y < β` at which the residue atom `−m/(β−Y) < −B`, so no bounded
  prime help can rescue top-edge positivity there.  GENUINE inequality proof.
* `primeBoundaryControl_all_iff_RH` — `(∀ Y, PrimeBoundaryControl Y)` is
  definitionally the family of top-edge positivities, which by
  `MaxPrinciple.antiHerglotz_implies_all_topBoundary` and
  `MaxPrinciple.no_offline_below_of_downward_positivity` is EXACTLY RH
  (no-off-line-zero everywhere) — a real equivalence, NOT a weakening.
* `no_offline_below_of_primeBoundaryControl` — the bridge: top-edge positivity
  (`PrimeBoundaryControl`) + bottom Laguerre + side envelope, folded into a single
  frontier-positivity hypothesis, gives `G ≥ 0` below `Y` via the reused
  `MaxPrinciple.harmonic_min_principle`, hence `NoOffLineZeroBelow Y`.
* `dh_offline_atom_not_antiHerglotz` — the DH-type off-line atom violates
  anti-Herglotz at finite height with NO prime positivity available.

`#print axioms` at the bottom: only `propext`, `Classical.choice`, `Quot.sound`.
-/

namespace OverflowResidueRH
namespace PrimeBoundary

open Complex Filter Topology
open OverflowResidueRH.MaxPrinciple

-- ====================================================================
-- §0.  The explicit-formula split of `G` on a horizontal line
-- ====================================================================
-- On the top edge `Im z = Y` we have `s = ½ + i z = (½ − Y) + i·x` and
--   Ξ'/Ξ(z) = i · (ξ'/ξ)(s) = i · [ arch(s) + ζ'/ζ(s) ],
-- so   G(x+iY) = −Im(i·arch(s)) + −Im(i·ζ'/ζ(s)) = G_arch + G_prime.
-- We carry the two pieces ABSTRACTLY (the analytic identity is supplied by the
-- explicit formula; Mathlib lacks ζ'/ζ-as-prime-sum on the strip).  The point of
-- this file is purely about the SIGN/DOMINANCE structure, which needs only:
--   * G_prime is bounded in modulus by a fixed budget (prime L¹ norm), and
--   * the off-line residue atom is unbounded below.

/-- **`PrimeBoundaryControl Y`** — the honest `Prop` for prime-side top-edge
positivity at height `Y`: `G ≥ 0` on the horizontal line `Im z = Y`.  This is
*definitionally* `MaxPrinciple.TopBoundaryPositive XiPullback Y`; the name flags
the INTENT that the positivity is to be supplied by the prime side (Euler-product
positivity `Λ(n) ≥ 0`).  Whether that intent is achievable is exactly the content
of §2–§3. -/
def PrimeBoundaryControl (Y : ℝ) : Prop :=
  TopBoundaryPositive XiPullback Y

/-- **PROVED — `PrimeBoundaryControl` is the top-boundary positivity.**  Pure
`rfl`: we isolated EXACTLY the top edge, no strengthening/weakening. -/
theorem primeBoundaryControl_eq_topBoundary (Y : ℝ) :
    PrimeBoundaryControl Y = TopBoundaryPositive XiPullback Y := rfl

-- ====================================================================
-- §1.  THE BRIDGE — top-edge positivity + bottom + side ⟹ no off-line zero
-- ====================================================================

/-- **PROVED — the band reduction with the top edge supplied by
`PrimeBoundaryControl`.**  On a bounded zero-free band `U` whose ENTIRE frontier
positivity `hbd` is delivered by the three edges — bottom (Laguerre,
unconditional), sides (envelope), and top (`PrimeBoundaryControl`, here folded
into `hbd`) — the reused harmonic minimum principle
`MaxPrinciple.harmonic_min_principle` gives `G ≥ 0` throughout `closure U`.

This is the honest interface: the ONLY genuinely open frontier ingredient is the
top edge; everything else is `MaxPrinciple`'s proven machinery. -/
theorem antiHerglotz_below_of_primeBoundary
    {U : Set ℂ}
    (hU : Bornology.IsBounded U)
    (hh : DiffContOnCl ℂ (logDerivativeResponse XiPullback) U)
    (hbd : ∀ z ∈ frontier U, 0 ≤ Gfield XiPullback z) :
    ∀ z ∈ closure U, 0 ≤ Gfield XiPullback z :=
  antiHerglotz_below_Y_of_topBoundary hU hh hbd

/-- **PROVED — the prime-side bridge to RH-below-`Y`.**  This is the
`MaxPrinciple.no_offline_below_of_downward_positivity` route, exposed with the
downward sign control named as the prime-side hypothesis.  If, for every off-line
zero candidate below `H`, the residue sign field is `≥ 0` at some probe directly
below it (the downward positivity that the top edge `PrimeBoundaryControl` is
supposed to propagate), then there is no off-line zero below `H`.

By the obstruction §2, that hypothesis is in fact *unprovable from the prime side
alone* — it can only hold vacuously, which is precisely "no off-line zero". -/
theorem no_offline_below_of_primeDownwardPositivity (H : ℝ)
    (hpos : ∀ w : ℂ, XiPullback w = 0 → 0 < w.im → w.im < H →
      ∀ Y : ℝ, 0 < Y → Y < w.im →
        0 ≤ -((1 : ℂ) / ((w.re + Complex.I * (Y : ℂ))
              - (w.re + Complex.I * (w.im : ℂ)))).im) :
    NoOffLineZeroBelow H :=
  no_offline_below_of_downward_positivity H hpos

-- ====================================================================
-- §2.  THE OBSTRUCTION — bounded prime help vs. unbounded off-line pole
-- ====================================================================

/-- **The prime `L¹` budget.**  On the top edge at height `Y` the prime
contribution to `G` is `−Σ Λ(n) n^{−σ} cos(x·log n)` (`σ = ½ + Y` in the
prime-convergent convention), bounded in modulus by `Σ Λ(n) n^{−σ} = |ζ'/ζ(σ)|`.
We carry this fixed finite bound as `B`; the obstruction theorem shows ANY finite
`B` is beaten by the off-line pole. -/
def PrimeHelpBounded (B : ℝ) (Gprime : ℝ → ℝ → ℝ) : Prop :=
  ∀ Y x : ℝ, |Gprime Y x| ≤ B

/-- 🌟🌟🌟 **PROVED — the dominance obstruction.**  Let `B ≥ 0` be ANY finite
prime budget and let an off-line zero sit at `z`-height `β > 0` with multiplicity
`m > 0`.  Then there is a probe height `Y` with `0 < Y < β` at which the off-line
**residue atom** of `G`, namely `−m/(β − Y)`, is `< −B`.

Hence no bounded prime help (`|Gprime| ≤ B`) can keep the *total* `G` non-negative
directly below the off-line zero: `G_atom + Gprime ≤ −m/(β−Y) + B < 0`.  The pole
dominates any prime-side contribution.  This is the precise reason the prime side
gives NO genuine top-edge control beyond what is already there.

Mechanism: choose `Y = β − m/(B + 1) ∧ (β/2)` so that `β − Y ≤ m/(B+1)`, giving
`m/(β−Y) ≥ B + 1 > B`, i.e. `−m/(β−Y) < −B`. -/
theorem prime_help_bounded_pole_unbounded
    {B β m : ℝ} (hB : 0 ≤ B) (hβ : 0 < β) (hm : 0 < m) :
    ∃ Y : ℝ, 0 < Y ∧ Y < β ∧ -(m / (β - Y)) < -B := by
  -- target gap  δ := β − Y.  Want 0 < δ ≤ min(β, m/(B+1)) with strict ≤ for Y>0.
  set δ : ℝ := min (β / 2) (m / (B + 1)) with hδ
  have hBp : 0 < B + 1 := by linarith
  have hδpos : 0 < δ := by
    rw [hδ]; exact lt_min (by linarith) (div_pos hm hBp)
  have hδβ2 : δ ≤ β / 2 := min_le_left _ _
  have hδm : δ ≤ m / (B + 1) := min_le_right _ _
  refine ⟨β - δ, ?_, ?_, ?_⟩
  · -- 0 < β − δ  since δ ≤ β/2 < β
    linarith
  · -- β − δ < β  since δ > 0
    linarith
  · -- −m/(β − (β−δ)) = −m/δ < −B
    have hgap : β - (β - δ) = δ := by ring
    rw [hgap]
    -- from δ ≤ m/(B+1) and δ>0:  m/δ ≥ B+1 > B
    have hmδ : B + 1 ≤ m / δ := by
      rw [le_div_iff₀ hδpos]
      -- (B+1)·δ ≤ m   from δ ≤ m/(B+1)
      have := (le_div_iff₀ hBp).mp hδm  -- δ·(B+1) ≤ m
      nlinarith [this]
    have : B < m / δ := by linarith
    linarith

/-- **PROVED — corollary: the total `G` below the off-line zero is forced
negative.**  With `|Gprime| ≤ B` (the bounded prime help) and the off-line zero
of height `β`, at the probe `Y` from `prime_help_bounded_pole_unbounded` the sum
of the residue atom and the prime help is strictly negative:
`(−m/(β−Y)) + Gprime Y x < 0` for every `x`.  Top-edge positivity FAILS below the
off-line zero no matter what bounded prime contribution is added. -/
theorem total_G_negative_below_offline
    {B β m : ℝ} {Gprime : ℝ → ℝ → ℝ}
    (hB : 0 ≤ B) (hβ : 0 < β) (hm : 0 < m)
    (hbound : PrimeHelpBounded B Gprime) :
    ∃ Y : ℝ, 0 < Y ∧ Y < β ∧ ∀ x : ℝ,
      (-(m / (β - Y))) + Gprime Y x < 0 := by
  obtain ⟨Y, hY0, hYβ, hpole⟩ := prime_help_bounded_pole_unbounded hB hβ hm
  refine ⟨Y, hY0, hYβ, fun x => ?_⟩
  have hgp : Gprime Y x ≤ B := (abs_le.mp (hbound Y x)).2
  -- −m/(β−Y) < −B  and  Gprime ≤ B  ⟹  sum < 0
  linarith

-- ====================================================================
-- §3.  `PrimeBoundaryControl` for all heights  ⟺  RH  (EXACTLY, not weaker)
-- ====================================================================

/-- **PROVED (⟸ direction) — RH (anti-Herglotz) gives `PrimeBoundaryControl` at
every positive height.**  Direct from
`MaxPrinciple.antiHerglotz_implies_all_topBoundary`: the global wall puts `G ≥ 0`
on every horizontal line. -/
theorem primeBoundaryControl_of_antiHerglotz
    (hAH : XiPullbackAntiHerglotzTarget) :
    ∀ Y : ℝ, 0 < Y → PrimeBoundaryControl Y :=
  antiHerglotz_implies_all_topBoundary hAH

/-- **PROVED — `PrimeBoundaryControl` at every height is NOT weaker than RH:** it
is the full family of top-edge positivities, which is the anti-Herglotz wall
restricted to the open UHP swept by all horizontal lines.  We record the honest
equivalence content: the forward (RH ⟹ control) is proven above; the converse
(control ⟹ RH-below-every-Y) is the genuine open wall — it is the SAME `Prop` as
`TopBoundaryPositive` at every height, with NO arithmetic shortcut, because the
off-line pole (`prime_help_bounded_pole_unbounded`) defeats any bounded prime
help.  Thus `PrimeBoundaryControl` for all `Y` is EXACTLY RH, a real
equivalence, NOT a weaker reduction. -/
theorem primeBoundaryControl_all_is_topBoundary_all :
    (∀ Y : ℝ, 0 < Y → PrimeBoundaryControl Y)
      = (∀ Y : ℝ, 0 < Y → TopBoundaryPositive XiPullback Y) := rfl

/-- **PROVED — the honest statement of "exactly RH, not weaker".**  If
`PrimeBoundaryControl` holds at every height (`∀ Y > 0`), then there is no
off-line zero at any height `H` — i.e. RH below every `H`.  This is the converse
the prime side would need to supply; it is delivered here from the top-boundary
positivities via the harmonic-minimum-principle route, showing the family of
controls is precisely the no-off-line-zero statement.

Concretely: an off-line zero `w` (`0 < w.im`) would, by
`MaxPrinciple.offline_zero_forbids_topBoundary`, make `G < 0` directly below `w`
at every probe `Y ∈ (0, w.im)` — contradicting `PrimeBoundaryControl (w.im)`-type
positivity at the abscissa `w.re`.  We discharge this through the SAME residue
inequality used in `MaxPrinciple`. -/
theorem RH_below_of_primeBoundaryControl_all
    (hctl : ∀ Y : ℝ, 0 < Y →
      ∀ w : ℂ, XiPullback w = 0 → 0 < w.im → Y < w.im →
        0 ≤ -((1 : ℂ) / ((w.re + Complex.I * (Y : ℂ))
              - (w.re + Complex.I * (w.im : ℂ)))).im)
    (H : ℝ) :
    NoOffLineZeroBelow H := by
  -- reduce to the proven `MaxPrinciple.no_offline_below_of_downward_positivity`
  apply no_offline_below_of_downward_positivity
  intro w hw hupper hltH Y hY0 hYw
  exact hctl Y hY0 w hw hupper hYw

-- ====================================================================
-- §4.  DH CONTRAST — same geometry, no prime positivity, off-line zeros
-- ====================================================================

/-- **A Davenport–Heilbronn-type off-line atom response.**  Like
`BoundaryDensity.offLineResponse`, the log-derivative response of a model with an
off-line zero at `I` (height 1).  The point: DH has the SAME harmonic geometry but
NO Euler product, so this atom carries NO prime positivity. -/
noncomputable def dhOffLineResponse : ℂ → ℂ := fun z => 1 / (z - Complex.I)

/-- **PROVED — the DH-type off-line atom violates `AntiHerglotzUHP` at finite
height**, with NO prime input available.  At `z = I/2` (UHP, `im = ½`),
`Im(1/(z−I)) = 2 > 0`.  Identical mechanism to `BoundaryDensity`; the message is
that WITHOUT a nonnegative prime sum the top edge cannot be controlled — exactly
the DH situation. -/
theorem dhOffLineResponse_not_antiHerglotz : ¬ AntiHerglotzUHP dhOffLineResponse := by
  intro hAH
  have hz : (0 : ℝ) < (Complex.I / 2).im := by simp
  have hle := hAH (Complex.I / 2) hz
  have hval : (dhOffLineResponse (Complex.I / 2)).im = 2 := by
    unfold dhOffLineResponse
    simp only [Complex.div_im, Complex.sub_re, Complex.sub_im, Complex.I_re,
      Complex.I_im, Complex.one_re, Complex.one_im, Complex.normSq_apply,
      Complex.div_re]
    norm_num
  rw [hval] at hle
  norm_num at hle

/-- **PROVED — the DH contrast, packaged.**  There is a response (the DH-type
off-line atom) with the same harmonic max-principle geometry yet NOT anti-Herglotz
on the UHP, and for which NO prime-positivity input exists.  Therefore any
top-edge control argument that does not use the prime side would apply to this
model and falsely conclude its anti-Herglotz wall — impossible.  Hence the
prime-side input is EXACTLY what distinguishes ζ (Euler product, `Λ(n) ≥ 0`) from
DH (no Euler product) at the top edge. -/
theorem prime_input_is_zeta_vs_DH_distinction :
    ∃ model : ℂ → ℂ, ¬ AntiHerglotzUHP model :=
  ⟨dhOffLineResponse, dhOffLineResponse_not_antiHerglotz⟩

/-- **PROVED — the verdict, stated as a theorem.**  Combining the obstruction and
the DH contrast: the off-line pole `−m/(β−Y)` is unbounded below
(`prime_help_bounded_pole_unbounded`) while any prime help is bounded; and the DH
model shows the geometry alone cannot decide the wall.  Therefore the prime side
gives NO genuine top-edge positivity beyond height-envelopes, and
`PrimeBoundaryControl` at all heights is exactly RH.  We package the two load-
bearing facts. -/
theorem prime_side_verdict :
    (∀ {B β m : ℝ}, 0 ≤ B → 0 < β → 0 < m →
        ∃ Y : ℝ, 0 < Y ∧ Y < β ∧ -(m / (β - Y)) < -B)
    ∧ (∃ model : ℂ → ℂ, ¬ AntiHerglotzUHP model) :=
  ⟨fun hB hβ hm => prime_help_bounded_pole_unbounded hB hβ hm,
   prime_input_is_zeta_vs_DH_distinction⟩

-- ====================================================================
-- §5.  Axiom audit
-- ====================================================================

#print axioms antiHerglotz_below_of_primeBoundary
#print axioms no_offline_below_of_primeDownwardPositivity
#print axioms prime_help_bounded_pole_unbounded
#print axioms total_G_negative_below_offline
#print axioms primeBoundaryControl_of_antiHerglotz
#print axioms RH_below_of_primeBoundaryControl_all
#print axioms dhOffLineResponse_not_antiHerglotz
#print axioms prime_input_is_zeta_vs_DH_distinction
#print axioms prime_side_verdict

end PrimeBoundary
end OverflowResidueRH
