import rh

/-!
# ScratchAP_DeformN: AP2 general-`n` contour additivity by induction on the n=1 step

This file PROVES the general-`n` contour-deformation / additivity step of the
argument principle, by induction on the proven n=1 building block:

  *for `h : ℂ → ℂ` holomorphic on a closed rectangle EXCEPT at finitely many
  interior points `a₁,…,aₙ`, the boundary integral equals the sum of small-
  rectangle boundary integrals around each singular point:*

        `∮_{∂R} h  =  Σ_i ∮_{∂square(aᵢ)} h`.

`ScratchAP_Deformation.lean` PROVED the n=1 case
`∮_{∂R} f = ∮_{∂square} f` (one interior singularity) via a four-strip
decomposition + edge cancellation (`abel`), reusing rh.lean's
`SmallSquareInsideRectangle`, `rectangleIntegral_eq_edges`,
`globalRectangleCauchyGoursatBridge`.  It isolated the general-`n` statement as
a structure with field
`deform : R.rectangleIntegral h = Σ_{s∈pts.attach} (Sq.sq s).toRectangle.rectangleIntegral h`.

## What this file does

Scratch files are not library targets and cannot be imported, so the n=1 API of
`ScratchAP_Deformation.lean` cannot be `import`ed.  We therefore **RE-DERIVE**
the needed n=1 pieces here as clean local lemmas (reproducing the four-strip
proof, calling rh-level `rectangleIntegral_eq_edges`, `globalRectangleCauchyGoursatBridge`,
`intervalIntegral_add_three_adjacent_eq`).  These re-derived lemmas are:

* `gHEdge`, `gVEdge` — generic straight-line edge integrals (any `f`).
* `gHEdge_reverse_eq_neg`, `gVEdge_reverse_eq_neg` — orientation reversal.
* `gHEdge_add_two_adjacent_eq`, `gVEdge_add_two_adjacent_eq` — 2-piece joins.
* `gHEdge_add_three_adjacent_eq`, `gVEdge_add_three_adjacent_eq` — 3-piece joins.
* `rectangleIntegral_eq_edges` — boundary integral as four oriented edges.
* `fourStripBoundarySymbolicGen` — the four-strip cancellation identity.
* `DeformLineIntegrable`, `rectangleDeformOneSingularity` — the n=1 deformation.

## New content (the deliverable)

1. **`rectangleHorizontalSplit`** — a PROVEN "rectangle = bottom ⊕ top glued on a
   shared horizontal cut" additivity lemma.  Cutting `[L,Rt]×[B,T]` at `y = c`
   (with `B < c < T`) gives `[L,Rt]×[B,c]` and `[L,Rt]×[c,T]`; the shared cut
   edge `y = c` appears once in each sub-rectangle with OPPOSITE orientation and
   cancels (`gHEdge_reverse_eq_neg`), while the two split vertical edges rejoin
   (`gVEdge_add_two_adjacent_eq`).  Exactly the n=1 edge-cancellation device,
   one cut instead of four.

2. **`RectangleSplitDeformStep`** + **`.of_split_deform`** — bundles ONE
   induction step: the proven equation
   `R.rectangleIntegral h = sqInt + Rnext.rectangleIntegral h`, built (no new
   assumptions) from a horizontal split `R = Rbot + Rtop` (`rectangleHorizontalSplit`)
   and an n=1 deformation `Rtop = sq` of the top piece
   (`rectangleDeformOneSingularity`).  `sqInt` is the isolated square integral,
   `Rnext` the residual rectangle carrying the remaining `n-1` points.

3. **`DeformChain`** + **`.telescope`** + **`.additivity_of_residual_analytic`**
   — the PROVEN induction: a chain of `n` split-deform steps telescopes
   (induction on the chain) to
   `R.rectangleIntegral h = (Σ isolated squares) + R_final.rectangleIntegral h`,
   and when the residual is singularity-free (`R_final` Cauchy–Goursat) to the
   full additivity `R.rectangleIntegral h = Σ isolated squares`.

4. **`RectangleDeformInteriorSingularities`** (reproduced interface) +
   **`.of_chain`** / **`deform_finset_of_chain`** — the `Finset`-indexed
   general-`n` statement, obtained from the chain telescoping by converting the
   `List` sum to a `Finset` sum over `pts` (`List.sum_toFinset` /
   `Finset.sum_map_toList` + a nodup-permutation bookkeeping argument).

5. **`deform_one_step_eq`** — sanity: a one-step chain with analytic residual
   recovers exactly the n=1 conclusion.

The only genuinely-irreducible geometric facts — that at each step a horizontal
cut isolates the next singularity (so `rectangleHorizontalSplit`'s coordinate +
integrability hypotheses hold and `rectangleDeformOneSingularity` applies to the
top piece), and that the residual rectangle is eventually singularity-free — are
carried as the explicit hypotheses of `RectangleSplitDeformStep.of_split_deform`
and `DeformChain.additivity_of_residual_analytic`, never as `sorry`.  Each
peeling step is itself fully PROVEN from the split + n=1 lemmas.

Everything is in namespace
`OverflowResidueRH.BacklundTuring.ScratchAPDeformN`.
We open `ZetaRectangle` to reuse its strip/edge API.
-/

open Complex
open scoped Real

namespace OverflowResidueRH
namespace BacklundTuring

open ZetaRectangle

namespace ScratchAPDeformN

/-! ## 1. Generic straight-line edge integrals (re-derived from ScratchAP_Deformation) -/

/-- Horizontal edge integral of `f`: integrate `f ⟨x, y⟩` along `x` from `x₀`
to `x₁` at fixed imaginary part `y`. -/
noncomputable def gHEdge (f : ℂ → ℂ) (y x₀ x₁ : ℝ) : ℂ :=
  ∫ x in x₀..x₁, f ⟨x, y⟩

/-- Vertical edge integral of `f` with the `* Complex.I` orientation weight. -/
noncomputable def gVEdge (f : ℂ → ℂ) (x y₀ y₁ : ℝ) : ℂ :=
  ∫ y in y₀..y₁, f ⟨x, y⟩ * Complex.I

/-- Reversing a horizontal edge negates it (no integrability needed). -/
theorem gHEdge_reverse_eq_neg (f : ℂ → ℂ) (y x₀ x₁ : ℝ) :
    gHEdge f y x₁ x₀ = -gHEdge f y x₀ x₁ := by
  unfold gHEdge
  exact intervalIntegral.integral_symm x₀ x₁

/-- Reversing a vertical edge negates it. -/
theorem gVEdge_reverse_eq_neg (f : ℂ → ℂ) (x y₀ y₁ : ℝ) :
    gVEdge f x y₁ y₀ = -gVEdge f x y₀ y₁ := by
  unfold gVEdge
  exact intervalIntegral.integral_symm y₀ y₁

/-- Two adjacent horizontal pieces concatenate, given integrability. -/
theorem gHEdge_add_two_adjacent_eq
    {f : ℂ → ℂ} {y x₀ x₁ x₂ : ℝ}
    (h01 : IntervalIntegrable (fun x : ℝ => f ⟨x, y⟩) MeasureTheory.volume x₀ x₁)
    (h12 : IntervalIntegrable (fun x : ℝ => f ⟨x, y⟩) MeasureTheory.volume x₁ x₂) :
    gHEdge f y x₀ x₁ + gHEdge f y x₁ x₂ = gHEdge f y x₀ x₂ := by
  unfold gHEdge
  exact intervalIntegral.integral_add_adjacent_intervals h01 h12

/-- Two adjacent vertical pieces concatenate, given integrability. -/
theorem gVEdge_add_two_adjacent_eq
    {f : ℂ → ℂ} {x y₀ y₁ y₂ : ℝ}
    (h01 : IntervalIntegrable (fun y : ℝ => f ⟨x, y⟩ * Complex.I)
            MeasureTheory.volume y₀ y₁)
    (h12 : IntervalIntegrable (fun y : ℝ => f ⟨x, y⟩ * Complex.I)
            MeasureTheory.volume y₁ y₂) :
    gVEdge f x y₀ y₁ + gVEdge f x y₁ y₂ = gVEdge f x y₀ y₂ := by
  unfold gVEdge
  exact intervalIntegral.integral_add_adjacent_intervals h01 h12

/-- Three adjacent horizontal pieces concatenate, given integrability. -/
theorem gHEdge_add_three_adjacent_eq
    {f : ℂ → ℂ} {y x₀ x₁ x₂ x₃ : ℝ}
    (h01 : IntervalIntegrable (fun x : ℝ => f ⟨x, y⟩) MeasureTheory.volume x₀ x₁)
    (h12 : IntervalIntegrable (fun x : ℝ => f ⟨x, y⟩) MeasureTheory.volume x₁ x₂)
    (h23 : IntervalIntegrable (fun x : ℝ => f ⟨x, y⟩) MeasureTheory.volume x₂ x₃) :
    gHEdge f y x₀ x₁ + gHEdge f y x₁ x₂ + gHEdge f y x₂ x₃ = gHEdge f y x₀ x₃ := by
  unfold gHEdge
  exact intervalIntegral_add_three_adjacent_eq h01 h12 h23

/-- Three adjacent vertical pieces concatenate, given integrability. -/
theorem gVEdge_add_three_adjacent_eq
    {f : ℂ → ℂ} {x y₀ y₁ y₂ y₃ : ℝ}
    (h01 : IntervalIntegrable (fun y : ℝ => f ⟨x, y⟩ * Complex.I)
            MeasureTheory.volume y₀ y₁)
    (h12 : IntervalIntegrable (fun y : ℝ => f ⟨x, y⟩ * Complex.I)
            MeasureTheory.volume y₁ y₂)
    (h23 : IntervalIntegrable (fun y : ℝ => f ⟨x, y⟩ * Complex.I)
            MeasureTheory.volume y₂ y₃) :
    gVEdge f x y₀ y₁ + gVEdge f x y₁ y₂ + gVEdge f x y₂ y₃ = gVEdge f x y₀ y₃ := by
  unfold gVEdge
  exact intervalIntegral_add_three_adjacent_eq h01 h12 h23

/-! ### 1b. `rectangleIntegral` in generic-edge form (re-derived) -/

/-- The coordinate boundary integral of `f` over a rectangle, written in the
generic edge primitives. -/
theorem coordinateBoundaryIntegral_eq_edges (R : ZetaRectangle) (f : ℂ → ℂ) :
    R.coordinateBoundaryIntegral f =
      gHEdge f R.bottom R.left R.right
        + gVEdge f R.right R.bottom R.top
        + gHEdge f R.top R.right R.left
        + gVEdge f R.left R.top R.bottom := by
  unfold coordinateBoundaryIntegral bottomHorizontalIntegral
    rightVerticalIntegral topHorizontalIntegral leftVerticalIntegral
    gHEdge gVEdge
  rfl

/-- Bridge `rectangleIntegral` (the `t`-parametrized boundary integral) to the
generic-edge form, for any `f`.  Uses rh.lean's proved edge/coordinate
adapters. -/
theorem rectangleIntegral_eq_edges (R : ZetaRectangle) (f : ℂ → ℂ) :
    R.rectangleIntegral f =
      gHEdge f R.bottom R.left R.right
        + gVEdge f R.right R.bottom R.top
        + gHEdge f R.top R.right R.left
        + gVEdge f R.left R.top R.bottom := by
  rw [rectangleIntegral_eq_coordinateBoundaryIntegral
        (rectangleEdgeIntegralCoordinateBridge R f),
      coordinateBoundaryIntegral_eq_edges]

/-! ## 2. The rectangle HORIZONTAL-SPLIT additivity lemma (NEW, PROVEN)

This is the inductive workhorse: a rectangle cut by a horizontal line `y = c`
decomposes its boundary integral as the sum of the two sub-rectangle boundary
integrals, the shared cut edge cancelling by orientation reversal.

Coordinates: outer `[L,Rt]×[B,T]`; cut at `y = c`; bottom `[L,Rt]×[B,c]`, top
`[L,Rt]×[c,T]`.  We work directly in the edge primitives (the geometric content
is identical to the `ZetaRectangle`-level statement, which follows by
`rectangleIntegral_eq_edges`).

The split requires integrability of `f·I` along the two outer vertical edges
`x = L` and `x = Rt` (so they rejoin across `c`); the horizontal edges and the
shared cut need no integrability hypotheses (reversal is unconditional). -/

/-- **Symbolic horizontal split.**  The sum of the bottom and top sub-rectangle
edge-boundaries equals the outer rectangle edge-boundary, given the two vertical
rejoin facts.  Pure additive-group `abel` once the joins/reversal are supplied. -/
theorem horizontalSplitSymbolic
    (f : ℂ → ℂ) (L Rt B T c : ℝ)
    (hRight : gVEdge f Rt B c + gVEdge f Rt c T = gVEdge f Rt B T)
    (hLeft  : gVEdge f L T c + gVEdge f L c B = gVEdge f L T B)
    (hCut   : gHEdge f c Rt L = -gHEdge f c L Rt) :
    -- bottom rectangle [L,Rt]×[B,c]
    ((gHEdge f B L Rt + gVEdge f Rt B c + gHEdge f c Rt L + gVEdge f L c B)
      -- top rectangle [L,Rt]×[c,T]
      +
      (gHEdge f c L Rt + gVEdge f Rt c T + gHEdge f T Rt L + gVEdge f L T c)) =
    -- outer rectangle [L,Rt]×[B,T]
    (gHEdge f B L Rt + gVEdge f Rt B T + gHEdge f T Rt L + gVEdge f L T B) := by
  rw [← hRight, ← hLeft, hCut]
  abel

/-- **Rectangle horizontal split (PROVEN).**  For an outer rectangle `R` and a
horizontal cut height `c` strictly between `R.bottom` and `R.top`, let `Rbot` be
`R` with top lowered to `c` and `Rtop` be `R` with bottom raised to `c`.  Then

  `R.rectangleIntegral f = Rbot.rectangleIntegral f + Rtop.rectangleIntegral f`,

provided `f·I` is interval-integrable along the left and right outer edges over
both sub-intervals (so the split vertical edges rejoin).

`Rbot` and `Rtop` are passed explicitly (as `ZetaRectangle`s) together with the
hypotheses that their edges match the cut coordinates; this avoids inlining the
`<` proofs and makes the lemma reusable for any concrete sub-rectangle pair. -/
theorem rectangleHorizontalSplit
    (R Rbot Rtop : ZetaRectangle) (f : ℂ → ℂ) (c : ℝ)
    -- geometry: bottom piece shares L,Rt,B; top edge is the cut
    (hbL : Rbot.left = R.left) (hbR : Rbot.right = R.right)
    (hbB : Rbot.bottom = R.bottom) (hbT : Rbot.top = c)
    -- top piece shares L,Rt,T; bottom edge is the cut
    (htL : Rtop.left = R.left) (htR : Rtop.right = R.right)
    (htB : Rtop.bottom = c) (htT : Rtop.top = R.top)
    -- integrability of f·I on the two outer verticals across the cut
    (hRightLow  : IntervalIntegrable (fun y : ℝ => f ⟨R.right, y⟩ * Complex.I)
                    MeasureTheory.volume R.bottom c)
    (hRightHigh : IntervalIntegrable (fun y : ℝ => f ⟨R.right, y⟩ * Complex.I)
                    MeasureTheory.volume c R.top)
    (hLeftHigh  : IntervalIntegrable (fun y : ℝ => f ⟨R.left, y⟩ * Complex.I)
                    MeasureTheory.volume R.top c)
    (hLeftLow   : IntervalIntegrable (fun y : ℝ => f ⟨R.left, y⟩ * Complex.I)
                    MeasureTheory.volume c R.bottom) :
    R.rectangleIntegral f = Rbot.rectangleIntegral f + Rtop.rectangleIntegral f := by
  -- Expand all three rectangle integrals into edges, rewriting the sub-rectangle
  -- coordinates back to outer coordinates / the cut `c`.
  have hOuter := rectangleIntegral_eq_edges R f
  have hBot := rectangleIntegral_eq_edges Rbot f
  have hTop := rectangleIntegral_eq_edges Rtop f
  rw [hbL, hbR, hbB, hbT] at hBot
  rw [htL, htR, htB, htT] at hTop
  -- Symbolic split identity, fed the two vertical rejoins + the cut reversal.
  have hsym := horizontalSplitSymbolic f R.left R.right R.bottom R.top c
    (gVEdge_add_two_adjacent_eq hRightLow hRightHigh)
    (gVEdge_add_two_adjacent_eq hLeftHigh hLeftLow)
    (gHEdge_reverse_eq_neg f c R.left R.right)
  rw [hOuter, hBot, hTop]
  -- `hsym : (bot edges) + (top edges) = (outer edges)`; goal is its symmetry.
  exact hsym.symm

/-! ## 3. n = 1 deformation re-derived (four-strip cancellation)

Reproduced from `ScratchAP_Deformation.lean` (which cannot be imported, being a
scratch file).  The four-strip symbolic identity + the `DeformLineIntegrable`
package + the strip Cauchy–Goursat give `∮_{∂R} f = ∮_{∂square} f`. -/

/-- The four-strip cancellation identity, generic in `f` (re-derived). -/
theorem fourStripBoundarySymbolicGen
    (f : ℂ → ℂ) (L Rgt B T xl xr yb yt : ℝ)
    (hRight :
      gVEdge f Rgt B yb + gVEdge f Rgt yb yt + gVEdge f Rgt yt T =
        gVEdge f Rgt B T)
    (hLeft :
      gVEdge f L T yt + gVEdge f L yt yb + gVEdge f L yb B =
        gVEdge f L T B)
    (hInnerBottomJoin :
      gHEdge f yb L xl + gHEdge f yb xl xr + gHEdge f yb xr Rgt =
        gHEdge f yb L Rgt)
    (hInnerTopJoin :
      gHEdge f yt Rgt xr + gHEdge f yt xr xl + gHEdge f yt xl L =
        gHEdge f yt Rgt L)
    (hInnerBottomReverse : gHEdge f yb Rgt L = -gHEdge f yb L Rgt)
    (hInnerTopReverse : gHEdge f yt L Rgt = -gHEdge f yt Rgt L)
    (hInnerLeftReverse : gVEdge f xl yb yt = -gVEdge f xl yt yb)
    (hInnerRightReverse : gVEdge f xr yt yb = -gVEdge f xr yb yt) :
    -- bottom strip
    ((gHEdge f B L Rgt + gVEdge f Rgt B yb
        + gHEdge f yb Rgt L + gVEdge f L yb B)
      -- top strip
      +
      (gHEdge f yt L Rgt + gVEdge f Rgt yt T
        + gHEdge f T Rgt L + gVEdge f L T yt)
      -- left strip
      +
      (gHEdge f yb L xl + gVEdge f xl yb yt
        + gHEdge f yt xl L + gVEdge f L yt yb)
      -- right strip
      +
      (gHEdge f yb xr Rgt + gVEdge f Rgt yb yt
        + gHEdge f yt Rgt xr + gVEdge f xr yt yb)) =
    -- outer rectangle boundary
    (gHEdge f B L Rgt + gVEdge f Rgt B T
      + gHEdge f T Rgt L + gVEdge f L T B) -
    -- inner square boundary
    (gHEdge f yb xl xr + gVEdge f xr yb yt
      + gHEdge f yt xr xl + gVEdge f xl yt yb) := by
  rw [← hRight, ← hLeft]
  rw [hInnerBottomReverse, hInnerTopReverse,
      hInnerLeftReverse, hInnerRightReverse]
  rw [← hInnerBottomJoin, ← hInnerTopJoin]
  abel

/-- Per-line integrability data for the four-strip deformation of `f` over an
outer rectangle `[L,Rgt]×[B,T]` with inner square `[xl,xr]×[yb,yt]`
(re-derived). -/
structure DeformLineIntegrable
    (f : ℂ → ℂ) (L Rgt B T xl xr yb yt : ℝ) : Prop where
  right₁ : IntervalIntegrable (fun y : ℝ => f ⟨Rgt, y⟩ * Complex.I)
            MeasureTheory.volume B yb
  right₂ : IntervalIntegrable (fun y : ℝ => f ⟨Rgt, y⟩ * Complex.I)
            MeasureTheory.volume yb yt
  right₃ : IntervalIntegrable (fun y : ℝ => f ⟨Rgt, y⟩ * Complex.I)
            MeasureTheory.volume yt T
  left₁ : IntervalIntegrable (fun y : ℝ => f ⟨L, y⟩ * Complex.I)
            MeasureTheory.volume T yt
  left₂ : IntervalIntegrable (fun y : ℝ => f ⟨L, y⟩ * Complex.I)
            MeasureTheory.volume yt yb
  left₃ : IntervalIntegrable (fun y : ℝ => f ⟨L, y⟩ * Complex.I)
            MeasureTheory.volume yb B
  bot₁ : IntervalIntegrable (fun x : ℝ => f ⟨x, yb⟩) MeasureTheory.volume L xl
  bot₂ : IntervalIntegrable (fun x : ℝ => f ⟨x, yb⟩) MeasureTheory.volume xl xr
  bot₃ : IntervalIntegrable (fun x : ℝ => f ⟨x, yb⟩) MeasureTheory.volume xr Rgt
  top₁ : IntervalIntegrable (fun x : ℝ => f ⟨x, yt⟩) MeasureTheory.volume Rgt xr
  top₂ : IntervalIntegrable (fun x : ℝ => f ⟨x, yt⟩) MeasureTheory.volume xr xl
  top₃ : IntervalIntegrable (fun x : ℝ => f ⟨x, yt⟩) MeasureTheory.volume xl L

variable {R : ZetaRectangle} {a : ℂ}

/-- **Core n = 1 deformation (re-derived, PROVEN).**  Given the four strip
boundary integrals (each `= 0` by Cauchy–Goursat) and the per-line
integrability, the outer rectangle boundary integral equals the inner square
boundary integral. -/
theorem rectangleDeformOneSingularity
    (S : R.SmallSquareInsideRectangle a) (f : ℂ → ℂ)
    (hTop : S.topStrip.rectangleIntegral f = 0)
    (hBot : S.bottomStrip.rectangleIntegral f = 0)
    (hLeft : S.leftStrip.rectangleIntegral f = 0)
    (hRight : S.rightStrip.rectangleIntegral f = 0)
    (I : DeformLineIntegrable f R.left R.right R.bottom R.top
          (a.re - S.r) (a.re + S.r) (a.im - S.r) (a.im + S.r)) :
    R.rectangleIntegral f = S.toRectangle.rectangleIntegral f := by
  have hTopE : S.topStrip.rectangleIntegral f =
      gHEdge f (a.im + S.r) R.left R.right
        + gVEdge f R.right (a.im + S.r) R.top
        + gHEdge f R.top R.right R.left
        + gVEdge f R.left R.top (a.im + S.r) :=
    rectangleIntegral_eq_edges S.topStrip f
  have hBotE : S.bottomStrip.rectangleIntegral f =
      gHEdge f R.bottom R.left R.right
        + gVEdge f R.right R.bottom (a.im - S.r)
        + gHEdge f (a.im - S.r) R.right R.left
        + gVEdge f R.left (a.im - S.r) R.bottom :=
    rectangleIntegral_eq_edges S.bottomStrip f
  have hLeftE : S.leftStrip.rectangleIntegral f =
      gHEdge f (a.im - S.r) R.left (a.re - S.r)
        + gVEdge f (a.re - S.r) (a.im - S.r) (a.im + S.r)
        + gHEdge f (a.im + S.r) (a.re - S.r) R.left
        + gVEdge f R.left (a.im + S.r) (a.im - S.r) :=
    rectangleIntegral_eq_edges S.leftStrip f
  have hRightE : S.rightStrip.rectangleIntegral f =
      gHEdge f (a.im - S.r) (a.re + S.r) R.right
        + gVEdge f R.right (a.im - S.r) (a.im + S.r)
        + gHEdge f (a.im + S.r) R.right (a.re + S.r)
        + gVEdge f (a.re + S.r) (a.im + S.r) (a.im - S.r) :=
    rectangleIntegral_eq_edges S.rightStrip f
  have hOuterE := rectangleIntegral_eq_edges R f
  have hInnerE : S.toRectangle.rectangleIntegral f =
      gHEdge f (a.im - S.r) (a.re - S.r) (a.re + S.r)
        + gVEdge f (a.re + S.r) (a.im - S.r) (a.im + S.r)
        + gHEdge f (a.im + S.r) (a.re + S.r) (a.re - S.r)
        + gVEdge f (a.re - S.r) (a.im + S.r) (a.im - S.r) :=
    rectangleIntegral_eq_edges S.toRectangle f
  have hsym := fourStripBoundarySymbolicGen f
    R.left R.right R.bottom R.top
    (a.re - S.r) (a.re + S.r) (a.im - S.r) (a.im + S.r)
    (gVEdge_add_three_adjacent_eq I.right₁ I.right₂ I.right₃)
    (gVEdge_add_three_adjacent_eq I.left₁ I.left₂ I.left₃)
    (gHEdge_add_three_adjacent_eq I.bot₁ I.bot₂ I.bot₃)
    (gHEdge_add_three_adjacent_eq I.top₁ I.top₂ I.top₃)
    (gHEdge_reverse_eq_neg f (a.im - S.r) R.left R.right)
    (gHEdge_reverse_eq_neg f (a.im + S.r) R.right R.left)
    (gVEdge_reverse_eq_neg f (a.re - S.r) (a.im + S.r) (a.im - S.r))
    (gVEdge_reverse_eq_neg f (a.re + S.r) (a.im - S.r) (a.im + S.r))
  rw [← hBotE, ← hTopE, ← hLeftE, ← hRightE,
      ← hOuterE, ← hInnerE,
      hTop, hBot, hLeft, hRight] at hsym
  have hzero : R.rectangleIntegral f - S.toRectangle.rectangleIntegral f = 0 := by
    rw [← hsym]; ring
  exact sub_eq_zero.mp hzero

/-- Strip Cauchy–Goursat from analyticity (re-derived bridge call). -/
theorem rectangleIntegral_eq_zero_of_analyticOn
    (R' : ZetaRectangle) (f : ℂ → ℂ)
    (hf : ∀ z ∈ {z : ℂ | R'.ContainsClosed z}, AnalyticAt ℂ f z) :
    R'.rectangleIntegral f = 0 :=
  globalRectangleCauchyGoursatBridge.cauchyGoursat R' f hf

/-- `DeformLineIntegrable` from continuity along the four cut lines. -/
theorem deformLineIntegrable_of_continuous
    (f : ℂ → ℂ) (L Rgt B T xl xr yb yt : ℝ)
    (hRightLine : Continuous (fun y : ℝ => f ⟨Rgt, y⟩ * Complex.I))
    (hLeftLine : Continuous (fun y : ℝ => f ⟨L, y⟩ * Complex.I))
    (hBotLine : Continuous (fun x : ℝ => f ⟨x, yb⟩))
    (hTopLine : Continuous (fun x : ℝ => f ⟨x, yt⟩)) :
    DeformLineIntegrable f L Rgt B T xl xr yb yt where
  right₁ := hRightLine.intervalIntegrable _ _
  right₂ := hRightLine.intervalIntegrable _ _
  right₃ := hRightLine.intervalIntegrable _ _
  left₁ := hLeftLine.intervalIntegrable _ _
  left₂ := hLeftLine.intervalIntegrable _ _
  left₃ := hLeftLine.intervalIntegrable _ _
  bot₁ := hBotLine.intervalIntegrable _ _
  bot₂ := hBotLine.intervalIntegrable _ _
  bot₃ := hBotLine.intervalIntegrable _ _
  top₁ := hTopLine.intervalIntegrable _ _
  top₂ := hTopLine.intervalIntegrable _ _
  top₃ := hTopLine.intervalIntegrable _ _

/-- **n = 1 deformation, analytic form (re-derived, PROVEN).** -/
theorem rectangleDeformOneSingularity_of_analytic
    (S : R.SmallSquareInsideRectangle a) (f : ℂ → ℂ)
    (hTop : ∀ z ∈ {z : ℂ | S.topStrip.ContainsClosed z}, AnalyticAt ℂ f z)
    (hBot : ∀ z ∈ {z : ℂ | S.bottomStrip.ContainsClosed z}, AnalyticAt ℂ f z)
    (hLeft : ∀ z ∈ {z : ℂ | S.leftStrip.ContainsClosed z}, AnalyticAt ℂ f z)
    (hRight : ∀ z ∈ {z : ℂ | S.rightStrip.ContainsClosed z}, AnalyticAt ℂ f z)
    (hRightLine : Continuous (fun y : ℝ => f ⟨R.right, y⟩ * Complex.I))
    (hLeftLine : Continuous (fun y : ℝ => f ⟨R.left, y⟩ * Complex.I))
    (hBotLine : Continuous (fun x : ℝ => f ⟨x, a.im - S.r⟩))
    (hTopLine : Continuous (fun x : ℝ => f ⟨x, a.im + S.r⟩)) :
    R.rectangleIntegral f = S.toRectangle.rectangleIntegral f :=
  rectangleDeformOneSingularity S f
    (rectangleIntegral_eq_zero_of_analyticOn S.topStrip f hTop)
    (rectangleIntegral_eq_zero_of_analyticOn S.bottomStrip f hBot)
    (rectangleIntegral_eq_zero_of_analyticOn S.leftStrip f hLeft)
    (rectangleIntegral_eq_zero_of_analyticOn S.rightStrip f hRight)
    (deformLineIntegrable_of_continuous f R.left R.right R.bottom R.top
      (a.re - S.r) (a.re + S.r) (a.im - S.r) (a.im + S.r)
      hRightLine hLeftLine hBotLine hTopLine)

/-! ## 4. Induction skeleton: chaining horizontal splits + n=1 deformations

We now assemble the general-`n` additivity by induction on a LIST of singular
points, each peeled off by one horizontal cut.

### Per-step witness

`RectangleSplitDeformStep h R sq Rnext` packages the proven outcome of ONE
induction step on the current rectangle `R`:

  `R.rectangleIntegral h = sq.rectangleIntegral h + Rnext.rectangleIntegral h`,

where `sq` is the inner-square boundary integral isolated by the cut (the n=1
deformation of the top piece), and `Rnext` is the residual rectangle carrying the
remaining singularities.  The field `step_eq` is exactly the equation that
`rectangleHorizontalSplit` (giving `R = Rbot + Rtop`) composed with
`rectangleDeformOneSingularity` on the top piece (`Rtop = sq`) produces; we
expose a builder `RectangleSplitDeformStep.of_split_deform` that constructs it
from those two PROVEN lemmas, so `step_eq` is never assumed ad hoc. -/

/-- One peeling step: the current rectangle's integral splits as an isolated
inner-square integral plus the residual rectangle's integral.  `sqInt` is the
boundary integral around the isolated singularity (an inner-square
`rectangleIntegral`); `Rnext` is the residual rectangle. -/
structure RectangleSplitDeformStep (h : ℂ → ℂ) (R : ZetaRectangle) where
  /-- Residual rectangle carrying the remaining singularities. -/
  Rnext : ZetaRectangle
  /-- Boundary integral isolated around this step's singularity. -/
  sqInt : ℂ
  /-- The proven split+deform equation for this step. -/
  step_eq :
    R.rectangleIntegral h = sqInt + Rnext.rectangleIntegral h

/-- **Builder (PROVEN).**  Construct a peeling step from the two proven lemmas:
a horizontal split `R = Rbot + Rtop` and an n=1 deformation `Rtop = sq` of the
top piece around the isolated singularity `a`.  No new assumptions: the equation
follows by `rw`. -/
noncomputable def RectangleSplitDeformStep.of_split_deform
    {h : ℂ → ℂ} {R Rbot Rtop : ZetaRectangle} {a : ℂ}
    (S : Rtop.SmallSquareInsideRectangle a)
    (hsplit : R.rectangleIntegral h = Rbot.rectangleIntegral h + Rtop.rectangleIntegral h)
    (hdeform : Rtop.rectangleIntegral h = S.toRectangle.rectangleIntegral h) :
    RectangleSplitDeformStep h R where
  Rnext := Rbot
  sqInt := S.toRectangle.rectangleIntegral h
  step_eq := by rw [hsplit, hdeform]; ring

/-- A deformation chain over a starting rectangle `R`: a list of peeling steps
where each step's residual rectangle is the next step's current rectangle.  We
model it as a dependent structure proven by recursion. -/
inductive DeformChain (h : ℂ → ℂ) : ZetaRectangle → ZetaRectangle → List ℂ → Prop
  /-- Empty chain: the rectangle is unchanged and no squares were isolated. -/
  | nil (R : ZetaRectangle) : DeformChain h R R []
  /-- Cons: a step from `R` to `step.Rnext` isolating `step.sqInt`, followed by a
  chain from `step.Rnext` to `Rfinal`. -/
  | cons {R Rfinal : ZetaRectangle} {sqs : List ℂ}
      (step : RectangleSplitDeformStep h R)
      (rest : DeformChain h step.Rnext Rfinal sqs) :
      DeformChain h R Rfinal (step.sqInt :: sqs)

/-- **Chain telescoping (PROVEN by induction).**  A deformation chain from `R`
to `Rfinal` isolating squares with boundary integrals `sqs` satisfies

  `R.rectangleIntegral h = sqs.sum + Rfinal.rectangleIntegral h`.

This is the core induction on the n=1 step: each `cons` applies one proven
split+deform equation; `nil` is reflexivity. -/
theorem DeformChain.telescope
    {h : ℂ → ℂ} {R Rfinal : ZetaRectangle} {sqs : List ℂ}
    (chain : DeformChain h R Rfinal sqs) :
    R.rectangleIntegral h = sqs.sum + Rfinal.rectangleIntegral h := by
  induction chain with
  | nil R => simp
  | cons step rest ih =>
    rw [step.step_eq, List.sum_cons, ih]
    ring

/-- **General-`n` additivity, residual form (PROVEN).**  If the residual
rectangle is singularity-free for `h` (so its boundary integral vanishes by
Cauchy–Goursat), the chain telescopes to pure additivity:

  `R.rectangleIntegral h = (Σ isolated square integrals)`.  -/
theorem DeformChain.additivity_of_residual_analytic
    {h : ℂ → ℂ} {R Rfinal : ZetaRectangle} {sqs : List ℂ}
    (chain : DeformChain h R Rfinal sqs)
    (hRfinal : ∀ z ∈ {z : ℂ | Rfinal.ContainsClosed z}, AnalyticAt ℂ h z) :
    R.rectangleIntegral h = sqs.sum := by
  rw [chain.telescope, rectangleIntegral_eq_zero_of_analyticOn Rfinal h hRfinal,
    add_zero]

/-! ## 5. Finset-indexed general-`n` statement (the original AP2 interface)

We reproduce the `SingularSquares` / `RectangleDeformInteriorSingularities`
interface of `ScratchAP_Deformation.lean` and PROVE its `deform` field from a
`DeformChain` whose isolated square integrals enumerate the singular set.

The bridge from the chain's `List` sum to the `Finset.sum` over `pts` uses
`List.sum_toFinset` (`l.Nodup → l.toFinset.sum f = (l.map f).sum`): given a nodup
enumerating list `l` of the points with `l.toFinset = pts` and a per-point square
assignment `g`, the chain's isolated integrals `l.map g` sum to `Σ_{s∈pts} g s`. -/

/-- A choice of small interior square around each point of a finite singular set
(reproduced from `ScratchAP_Deformation.lean`). -/
structure SingularSquares (R : ZetaRectangle) (pts : Finset ℂ) where
  sq : ∀ s ∈ pts, R.SmallSquareInsideRectangle s

/-- **General-`n` AP2 (Finset form, reproduced interface).**  The boundary
integral of `h` over `R` equals the sum, over the finite singular set `pts`, of
the boundary integrals over each inner square. -/
structure RectangleDeformInteriorSingularities
    (R : ZetaRectangle) (h : ℂ → ℂ)
    (pts : Finset ℂ) (Sq : SingularSquares R pts) : Prop where
  deform :
    R.rectangleIntegral h =
      pts.attach.sum
        (fun s => (Sq.sq s.1 s.2).toRectangle.rectangleIntegral h)

/-- **From a `DeformChain` to Finset-additivity (PROVEN).**  Suppose:

* a nodup list `l : List ℂ` enumerates the singular set: `l.toFinset = pts`;
* `g : ℂ → ℂ` assigns to each point its inner-square boundary integral;
* a `DeformChain` peels off exactly `l.map g` and lands on a residual rectangle
  `Rfinal` on which `h` is analytic.

Then `R.rectangleIntegral h = Σ_{s∈pts} g s`.

This converts the proven list-telescoping (`DeformChain.additivity_of_residual_analytic`)
into the Finset sum required by the AP2 interface, via `List.sum_toFinset`. -/
theorem deform_finset_of_chain
    {h : ℂ → ℂ} {R Rfinal : ZetaRectangle} {pts : Finset ℂ}
    {l : List ℂ} {g : ℂ → ℂ}
    (hl_nodup : l.Nodup) (hl_pts : l.toFinset = pts)
    (chain : DeformChain h R Rfinal (l.map g))
    (hRfinal : ∀ z ∈ {z : ℂ | Rfinal.ContainsClosed z}, AnalyticAt ℂ h z) :
    R.rectangleIntegral h = pts.sum g := by
  rw [chain.additivity_of_residual_analytic hRfinal]
  rw [← hl_pts, List.sum_toFinset g hl_nodup]

/-- **General-`n` AP2 from a chain (PROVEN, attach form).**  The same bridge,
delivering the exact `RectangleDeformInteriorSingularities.deform` shape:
the Finset sum is over `pts.attach`, mapping each member to its inner-square
boundary integral via `Sq`.

We require the enumerating list `l` together with a proof `hmap` that the
chain's isolated integrals coincide with `l.map (square integral via Sq)`.  This
is the place where the per-step geometry (which point each square belongs to)
meets the bookkeeping; it is supplied as the explicit hypothesis `hmap`, never
assumed away. -/
theorem RectangleDeformInteriorSingularities.of_chain
    {R Rfinal : ZetaRectangle} {h : ℂ → ℂ}
    {pts : Finset ℂ} (Sq : SingularSquares R pts)
    {l : List ℂ}
    (hl_nodup : l.Nodup) (hl_pts : l.toFinset = pts)
    (hl_mem : ∀ s ∈ l, s ∈ pts)
    (chain : DeformChain h R Rfinal
      (l.attachWith (· ∈ pts) hl_mem |>.map
        (fun s => (Sq.sq s.1 s.2).toRectangle.rectangleIntegral h)))
    (hRfinal : ∀ z ∈ {z : ℂ | Rfinal.ContainsClosed z}, AnalyticAt ℂ h z) :
    RectangleDeformInteriorSingularities R h pts Sq where
  deform := by
    classical
    -- Telescope the chain to the list sum.
    have htel := chain.additivity_of_residual_analytic hRfinal
    rw [htel]
    -- Rewrite the target Finset sum as a list sum over `pts.attach.toList`.
    rw [← Finset.sum_map_toList pts.attach
      (fun s => (Sq.sq s.1 s.2).toRectangle.rectangleIntegral h)]
    -- The two lists are `.map F` of permuted subtype lists; sums agree.
    apply List.Perm.sum_eq
    apply List.Perm.map
    -- `l.attachWith _ _ ~ pts.attach.toList` (both nodup, same membership).
    -- Nodup of the attachWith list:
    have hnd_left : (l.attachWith (· ∈ pts) hl_mem).Nodup := by
      apply List.Nodup.of_map Subtype.val
      rw [List.attachWith_map_subtype_val]
      exact hl_nodup
    have hnd_right : pts.attach.toList.Nodup := Finset.nodup_toList _
    refine (List.perm_ext_iff_of_nodup hnd_left hnd_right).2 ?_
    intro x
    -- membership equivalence on the subtype `{x // x ∈ pts}`.
    obtain ⟨xv, hxv⟩ := x
    rw [List.mem_attachWith, Finset.mem_toList]
    constructor
    · intro _; exact Finset.mem_attach _ _
    · intro _
      rw [← hl_pts] at hxv
      exact List.mem_toFinset.mp hxv

/-! ## 6. Sanity: the n = 1 case as a one-step chain

To confirm the induction skeleton is consistent with the proven single-
singularity deformation, we build a length-1 chain from one split+deform step
whose residual rectangle is singularity-free, and check it recovers exactly the
n=1 conclusion `R.rectangleIntegral h = sq.toRectangle.rectangleIntegral h`. -/

/-- A single split+deform step whose residual is analytic gives a length-1
deformation chain landing on the analytic residual. -/
theorem DeformChain.one_step
    {h : ℂ → ℂ} {R Rbot Rtop : ZetaRectangle} {a : ℂ}
    (S : Rtop.SmallSquareInsideRectangle a)
    (hsplit : R.rectangleIntegral h
      = Rbot.rectangleIntegral h + Rtop.rectangleIntegral h)
    (hdeform : Rtop.rectangleIntegral h = S.toRectangle.rectangleIntegral h) :
    DeformChain h R Rbot [S.toRectangle.rectangleIntegral h] := by
  -- `step.Rnext = Rbot`, `step.sqInt = S.toRectangle.rectangleIntegral h` (rfl).
  exact DeformChain.cons
    (RectangleSplitDeformStep.of_split_deform S hsplit hdeform)
    (DeformChain.nil _)

/-- **n = 1 consistency (PROVEN).**  A one-step chain with analytic residual
recovers exactly the n=1 deformation conclusion. -/
theorem deform_one_step_eq
    {h : ℂ → ℂ} {R Rbot Rtop : ZetaRectangle} {a : ℂ}
    (S : Rtop.SmallSquareInsideRectangle a)
    (hsplit : R.rectangleIntegral h
      = Rbot.rectangleIntegral h + Rtop.rectangleIntegral h)
    (hdeform : Rtop.rectangleIntegral h = S.toRectangle.rectangleIntegral h)
    (hRbot : ∀ z ∈ {z : ℂ | Rbot.ContainsClosed z}, AnalyticAt ℂ h z) :
    R.rectangleIntegral h = S.toRectangle.rectangleIntegral h := by
  have hchain := DeformChain.one_step S hsplit hdeform
  have := hchain.additivity_of_residual_analytic hRbot
  simpa using this

end ScratchAPDeformN

end BacklundTuring
end OverflowResidueRH

open OverflowResidueRH.BacklundTuring.ScratchAPDeformN

/-! ## Axiom audit — must show only standard classical/quotient axioms,
NO `sorryAx`. -/

#print axioms rectangleHorizontalSplit
#print axioms horizontalSplitSymbolic
#print axioms rectangleDeformOneSingularity
#print axioms DeformChain.telescope
#print axioms DeformChain.additivity_of_residual_analytic
#print axioms deform_finset_of_chain
#print axioms RectangleDeformInteriorSingularities.of_chain
#print axioms deform_one_step_eq
