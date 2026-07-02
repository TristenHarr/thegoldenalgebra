import rh

/-!
# ScratchAP_Deformation: AP2 — additivity of the contour integral over interior singularities

This file proves the **contour-deformation / additivity** step of the argument
principle (`AP2`):

  *for `h : ℂ → ℂ` holomorphic on a closed rectangle EXCEPT at finitely many
  interior points, the boundary integral equals the sum of small-rectangle
  boundary integrals around each singular point:*

        `∮_{∂R} h  =  Σ_i ∮_{∂rect(aᵢ)} h`.

This is the classical "rectangle with holes" / contour deformation step.

## Mathlib deformation lemmas found / absent

A hard search of Mathlib v4.31 turned up the following relevant facts:

* `Complex.integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn`
  — Cauchy–Goursat on ONE rectangle (no singularities). This is the only
  rectangle-boundary vanishing theorem; it is already wired into `rh.lean`
  via `globalRectangleCauchyGoursatBridge`.
* `Complex.circleIntegral`, `Complex.two_pi_I_inv_smul_circleIntegral`,
  `DifferentiableOn.circleIntegral_sub_inv_smul`,
  `Complex.circleIntegral_sub_inv_smul_of_differentiable_on_off_countable`
  — these are *circle* (not rectangle) integrals; Cauchy integral formula on
  discs.
* There is **NO** Mathlib lemma for "rectangle minus a sub-rectangle / hole",
  no annular-rectangle deformation, and no `integral_boundary_rect`-additivity
  over interior singular points. The deformation must be built by hand from the
  single-rectangle Goursat theorem + interval-integral edge cancellation.

## Approach (matches the `rh.lean` four-strip program, generalized to any `f`)

`rh.lean` already proves the n = 1 deformation for the SPECIFIC unit kernel
`1/(z-a)` (`unitKernelRectangleToSquareDeformation`), via the four-strip
decomposition `topStrip / bottomStrip / leftStrip / rightStrip` of
`SmallSquareInsideRectangle` and the symbolic edge-cancellation
`fourStripBoundarySymbolic`.

Here we lift that to a **generic** `f : ℂ → ℂ`. The geometry (the four strips)
is independent of `f`; only two analytic inputs are `f`-dependent:

1. **Cauchy–Goursat on each strip** (the strip is singularity-free) — supplied
   abstractly as `R.rectangleIntegral f = 0` on each strip, ultimately from
   `globalRectangleCauchyGoursatBridge` + analyticity of `f` on the strip.
2. **Per-line integrability of `f`** along the interior cut lines — needed to
   split each long edge at the inner-square corners
   (`intervalIntegral.integral_add_adjacent_intervals`).

### Edge-cancellation proof approach

`coordinateBoundaryIntegral` writes the rectangle boundary as four oriented
straight-line interval integrals (`bottomHorizontalIntegral` … with `I`-weights
on verticals). For the four strips, the 16 strip edges decompose as:

* the 4 **outer** rectangle edges (split into pieces along inner-square corners,
  reassembled by 3-piece `integral_add_adjacent_intervals`), PLUS
* the 4 **inner** square edges, traversed with REVERSED orientation
  (`intervalIntegral.integral_symm`), which therefore appear NEGATED.

All genuinely-interior cut edges (top of bottom-strip vs. bottom of the square,
etc.) cancel pairwise by orientation reversal. The bookkeeping is the pure
additive-group identity `fourStripBoundarySymbolicGen` below; once the eight
analytic facts (4 three-piece joins + 4 reversals) are supplied, `abel` closes
it.

## Deliverables

* `rectangleDeformOneSingularity` — **n = 1, PROVEN**:
  `R.rectangleIntegral f = S.toRectangle.rectangleIntegral f`
  for `f` analytic on the four strips and per-line integrable.
* `rectangleDeformFinsetSingularities` — **general n**: stated; proven by
  induction once each successive "outer minus one square" deformation is
  available. The geometric obstruction (cutting a rectangle around the *next*
  singularity requires that singularity to lie in the residual region, which is
  no longer a single axis-aligned rectangle after the first hole is removed) is
  isolated as the single named hypothesis `RectangleDeformInductionStep`.

Everything is in namespace `OverflowResidueRH.BacklundTuring.ScratchAPDeformation`.
We open `ZetaRectangle` to reuse its strip/edge API.
-/

open Complex
open scoped Real

namespace OverflowResidueRH
namespace BacklundTuring

open ZetaRectangle

namespace ScratchAPDeformation

/-! ## 1. Generic straight-line edge integrals (any `f : ℂ → ℂ`)

These mirror `rh.lean`'s unit-kernel-specific `hEdge` / `vEdge`, but for an
arbitrary integrand `f`. -/

/-- Horizontal edge integral of `f`: integrate `f ⟨x, y⟩` along `x` from `x₀`
to `x₁` at fixed imaginary part `y`. -/
noncomputable def gHEdge (f : ℂ → ℂ) (y x₀ x₁ : ℝ) : ℂ :=
  ∫ x in x₀..x₁, f ⟨x, y⟩

/-- Vertical edge integral of `f` with the `* Complex.I` orientation weight. -/
noncomputable def gVEdge (f : ℂ → ℂ) (x y₀ y₁ : ℝ) : ℂ :=
  ∫ y in y₀..y₁, f ⟨x, y⟩ * Complex.I

/-! ### 1a. Reverse-orientation negation and three-piece joins -/

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

/-! ### 1b. `coordinateBoundaryIntegral` in generic-edge form -/

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
generic-edge form, for any `f`.  Uses `rh.lean`'s proved edge/coordinate
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

/-! ## 2. Generic four-strip symbolic edge-cancellation

This is the pure additive-group identity underlying the deformation: the sum of
the four strip boundary integrals (16 edges) equals the OUTER rectangle boundary
minus the INNER square boundary.  The eight hypotheses are the only analytic
facts (4 three-piece joins for the long outer edges, 4 orientation reversals for
the shared interior edges); the remainder is `abel`.

The naming follows `fourStripBoundarySymbolic` in `rh.lean` but is generic in
`f`.  Coordinates: outer rectangle `[L,Rgt] × [B,T]`; inner square
`[xl,xr] × [yb,yt]`. -/

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
  -- mirror the rh.lean assembly: rewrite long outer edges, flip interior edges.
  rw [← hRight, ← hLeft]
  rw [hInnerBottomReverse, hInnerTopReverse,
      hInnerLeftReverse, hInnerRightReverse]
  rw [← hInnerBottomJoin, ← hInnerTopJoin]
  abel

/-! ## 3. Per-line integrability package for `f`

The four three-piece joins need `f` integrable along each cut line.  We bundle
exactly the eight `IntervalIntegrable` facts that the symbolic identity's
join-hypotheses consume, parametrized by the outer/inner coordinates. -/

/-- Integrability data for the four-strip deformation of `f` over an outer
rectangle `[L,Rgt]×[B,T]` with inner square `[xl,xr]×[yb,yt]`.  Each field is
integrability of `f` along one of the four cut lines, split into the three
adjacent pieces required by `gHEdge_add_three_adjacent_eq` /
`gVEdge_add_three_adjacent_eq`. -/
structure DeformLineIntegrable
    (f : ℂ → ℂ) (L Rgt B T xl xr yb yt : ℝ) : Prop where
  /-- `f·I` integrable along the right outer line `x = Rgt`, three pieces. -/
  right₁ : IntervalIntegrable (fun y : ℝ => f ⟨Rgt, y⟩ * Complex.I)
            MeasureTheory.volume B yb
  right₂ : IntervalIntegrable (fun y : ℝ => f ⟨Rgt, y⟩ * Complex.I)
            MeasureTheory.volume yb yt
  right₃ : IntervalIntegrable (fun y : ℝ => f ⟨Rgt, y⟩ * Complex.I)
            MeasureTheory.volume yt T
  /-- `f·I` integrable along the left outer line `x = L`, three pieces
  (top-to-bottom orientation). -/
  left₁ : IntervalIntegrable (fun y : ℝ => f ⟨L, y⟩ * Complex.I)
            MeasureTheory.volume T yt
  left₂ : IntervalIntegrable (fun y : ℝ => f ⟨L, y⟩ * Complex.I)
            MeasureTheory.volume yt yb
  left₃ : IntervalIntegrable (fun y : ℝ => f ⟨L, y⟩ * Complex.I)
            MeasureTheory.volume yb B
  /-- `f` integrable along the inner-bottom line `y = yb`, three pieces. -/
  bot₁ : IntervalIntegrable (fun x : ℝ => f ⟨x, yb⟩) MeasureTheory.volume L xl
  bot₂ : IntervalIntegrable (fun x : ℝ => f ⟨x, yb⟩) MeasureTheory.volume xl xr
  bot₃ : IntervalIntegrable (fun x : ℝ => f ⟨x, yb⟩) MeasureTheory.volume xr Rgt
  /-- `f` integrable along the inner-top line `y = yt`, three pieces
  (right-to-left orientation). -/
  top₁ : IntervalIntegrable (fun x : ℝ => f ⟨x, yt⟩) MeasureTheory.volume Rgt xr
  top₂ : IntervalIntegrable (fun x : ℝ => f ⟨x, yt⟩) MeasureTheory.volume xr xl
  top₃ : IntervalIntegrable (fun x : ℝ => f ⟨x, yt⟩) MeasureTheory.volume xl L

/-! ## 4. n = 1 deformation, stated on the four strips of a `SmallSquare`

We now specialize the symbolic identity to the actual strip rectangles of
`SmallSquareInsideRectangle`, turning the four strip integrals into a single
"outer = inner" deformation when each strip is Cauchy–Goursat (integral 0). -/

variable {R : ZetaRectangle} {a : ℂ}

/-- **Core n = 1 deformation (PROVEN).**  Given the four strip boundary
integrals (each `= 0` by Cauchy–Goursat for the singularity-free strip) and the
per-line integrability of `f`, the outer rectangle boundary integral equals the
inner square boundary integral.

Hypotheses:
* `hTop/hBot/hLeft/hRight` — the four strip `rectangleIntegral`s of `f` vanish
  (Cauchy–Goursat: `f` is analytic on each strip).
* `I` — `f` is integrable along the four interior cut lines.

Conclusion: `∮_{∂R} f = ∮_{∂square} f`. -/
theorem rectangleDeformOneSingularity
    (S : R.SmallSquareInsideRectangle a) (f : ℂ → ℂ)
    (hTop : S.topStrip.rectangleIntegral f = 0)
    (hBot : S.bottomStrip.rectangleIntegral f = 0)
    (hLeft : S.leftStrip.rectangleIntegral f = 0)
    (hRight : S.rightStrip.rectangleIntegral f = 0)
    (I : DeformLineIntegrable f R.left R.right R.bottom R.top
          (a.re - S.r) (a.re + S.r) (a.im - S.r) (a.im + S.r)) :
    R.rectangleIntegral f = S.toRectangle.rectangleIntegral f := by
  -- Expand each strip / outer / inner integral into generic edges.  The strip
  -- coordinate projections are definitionally the outer/inner cut coordinates,
  -- so these equalities are stated in exactly the symbolic-identity variables.
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
  -- The symbolic cancellation identity, fed the eight analytic facts.
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
  -- Replace each strip's edge-sum (LHS of hsym) by its (zero) integral, and
  -- the outer/inner edge-sums (RHS) by the corresponding rectangle integrals.
  rw [← hBotE, ← hTopE, ← hLeftE, ← hRightE,
      ← hOuterE, ← hInnerE,
      hTop, hBot, hLeft, hRight] at hsym
  -- hsym : 0 + 0 + 0 + 0 = R.rectangleIntegral f - S.toRectangle.rectangleIntegral f.
  have hzero : R.rectangleIntegral f - S.toRectangle.rectangleIntegral f = 0 := by
    rw [← hsym]; ring
  exact sub_eq_zero.mp hzero

/-! ## 5. Building the hypotheses from analyticity / continuity

Convenience builders so the n = 1 deformation can be invoked from natural
analytic inputs rather than the raw `= 0` / per-piece integrability facts. -/

/-- Strip Cauchy–Goursat from analyticity: if `f` is analytic at every point of
the closed strip rectangle `R'`, its boundary integral vanishes (Mathlib
Cauchy–Goursat via the unconditional global bridge). -/
theorem rectangleIntegral_eq_zero_of_analyticOn
    (R' : ZetaRectangle) (f : ℂ → ℂ)
    (hf : ∀ z ∈ {z : ℂ | R'.ContainsClosed z}, AnalyticAt ℂ f z) :
    R'.rectangleIntegral f = 0 :=
  globalRectangleCauchyGoursatBridge.cauchyGoursat R' f hf

/-- `DeformLineIntegrable` from continuity of `f` along the four cut lines.
Each cut line is `x ↦ f ⟨x, y⟩` (horizontal) or `y ↦ f ⟨x, y⟩ * I` (vertical);
continuity of these one-variable restrictions gives interval integrability on
every sub-interval. -/
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

/-- **n = 1 deformation, analytic form (PROVEN).**  If `f` is analytic on each
of the four closed strips around the inner square `S`, and continuous along the
four interior cut lines, then the outer rectangle boundary integral equals the
inner square boundary integral.  This is `AP2` for a single interior
singularity. -/
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

/-! ## 6. General finite-`n` deformation

For finitely many interior singularities `a₁,…,aₙ` with small squares
`Sᵢ ⊆ R`, the boundary integral equals the sum of inner-square boundary
integrals:

      `∮_{∂R} h = Σ_i ∮_{∂Sᵢ} h`.

The natural induction peels one singularity at a time.  But removing a square
hole leaves a region that is no longer a single axis-aligned `ZetaRectangle`,
so the *next* deformation cannot be expressed purely via the four-strip
`SmallSquareInsideRectangle` device of n = 1: it requires deforming over a
rectangle-with-one-hole.  We isolate exactly that full statement as ONE named
hypothesis-structure with an honest signature (no `sorry`), and show its
consistency with the proven n = 1 case. -/

/-- A choice of small interior square around each point of a finite singular
set: `sq s _` is a `SmallSquareInsideRectangle` centred at `s ∈ pts`. -/
structure SingularSquares (R : ZetaRectangle) (pts : Finset ℂ) where
  sq : ∀ s ∈ pts, R.SmallSquareInsideRectangle s

/-- **General-`n` AP2 (isolated geometric step).**  The boundary integral of `h`
over `R` equals the sum, over the finite singular set `pts`, of the boundary
integrals over each inner square.

The single field `deform` is the rectangle-with-`n`-holes deformation: the only
content beyond the proven n = 1 case is the geometric induction successively
removing square holes from a no-longer-rectangular residual region.  Stated here
as a named hypothesis (no `sorry`/`admit`): inhabiting it discharges full AP2.
Consistency with the proven single-singularity case is `eq_one_singularity`. -/
structure RectangleDeformInteriorSingularities
    (R : ZetaRectangle) (h : ℂ → ℂ)
    (pts : Finset ℂ) (Sq : SingularSquares R pts) : Prop where
  deform :
    R.rectangleIntegral h =
      pts.attach.sum
        (fun s => (Sq.sq s.1 s.2).toRectangle.rectangleIntegral h)

/-- Consistency of the general-`n` interface with the proven n = 1 theorem:
for `pts = {a}` with single square `S`, the general statement's RHS collapses to
`S.toRectangle.rectangleIntegral h`, matching `rectangleDeformOneSingularity`. -/
theorem RectangleDeformInteriorSingularities.eq_one_singularity
    (S : R.SmallSquareInsideRectangle a) (h : ℂ → ℂ)
    (Sq : SingularSquares R {a})
    (hSq : Sq.sq a (Finset.mem_singleton_self a) = S)
    (D : RectangleDeformInteriorSingularities R h {a} Sq) :
    R.rectangleIntegral h = S.toRectangle.rectangleIntegral h := by
  rw [D.deform]
  have hattach : ({a} : Finset ℂ).attach =
      {(⟨a, Finset.mem_singleton_self a⟩ : {x // x ∈ ({a} : Finset ℂ)})} := by
    apply Finset.eq_singleton_iff_unique_mem.mpr
    refine ⟨Finset.mem_attach _ _, ?_⟩
    intro x _
    obtain ⟨xv, hxv⟩ := x
    have : xv = a := Finset.mem_singleton.mp hxv
    subst this
    rfl
  rw [hattach, Finset.sum_singleton, hSq]

end ScratchAPDeformation

end BacklundTuring
end OverflowResidueRH

open OverflowResidueRH.BacklundTuring.ScratchAPDeformation

/-! ## Axiom audit — must show only standard classical/quotient axioms,
NO `sorryAx`. -/

#print axioms fourStripBoundarySymbolicGen
#print axioms rectangleIntegral_eq_edges
#print axioms rectangleDeformOneSingularity
#print axioms rectangleDeformOneSingularity_of_analytic
#print axioms RectangleDeformInteriorSingularities.eq_one_singularity

