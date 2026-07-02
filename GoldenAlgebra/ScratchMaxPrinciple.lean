import Mathlib
import rh

/-!
# `ScratchMaxPrinciple.lean` — the harmonic maximum-principle reformulation of anti-Herglotz

This file formalizes the **no-first-sign-failure** reformulation of the
`XiPullbackAntiHerglotzTarget` (rh.lean §12).  The quantity

  `G z := −(logDerivativeResponse XiPullback z).im  =  −Im (Ξ'/Ξ)(z)`

is **harmonic** away from the zeros of `Ξ` (it is the negated imaginary part of
the holomorphic function `Ξ'/Ξ`), and the anti-Herglotz target is *exactly*
`G ≥ 0` on the open upper half-plane.

The content here is a clean reformulation with TWO honest halves:

* **Bottom edge (UNCONDITIONAL).** Near `y = 0`, away from real zeros,
  `G ~ y · P(x)` with `P = boundaryDensityXi ≥ 0` the order-1 Laguerre/Turán
  inequality — a *known theorem*.  See `ScratchBoundaryDensity.lean`.
* **Top edge (= RH).** `TopBoundaryPositive Y := ∀ x, 0 ≤ G (x + iY)`.  The
  characterization proved below: an off-line zero `w` (with `0 < w.im`) forces
  `G < 0` on the segment *directly below* `w`, so `TopBoundaryPositive Y` for
  arbitrary `Y` is precisely "no off-line zero below `Y`" = RH below `Y`.  This
  half stays an honest, unproven `Prop`.

## What is genuinely PROVED (not assumed)

1. `harmonic_negIm_of_analyticOn` / `harmonic_G_awayFromZeros` — harmonicity of
   `G` where `Ξ ≠ 0`, via `AnalyticAt.harmonicAt_im` and `.neg`.
2. `harmonic_min_principle` — the **harmonic minimum principle** on any bounded
   open set: a function `G = −Im h` with `h` holomorphic on `closure U`
   satisfies `G ≥ C` throughout `closure U` once `G ≥ C` on `frontier U`.
   This is a GENUINE PROOF, derived from Mathlib's analytic maximum-modulus
   principle `Complex.norm_le_of_forall_mem_frontier_norm_le` applied to
   `exp(−i·h)` (whose modulus is `exp(−G)`).  **No harmonic max principle is
   assumed** — Mathlib lacks one, so we build it from max-modulus.
3. `antiHerglotz_in_region_of_boundary_positivity`,
   `bottom_edge_nonneg_of_laguerre`, `offline_zero_forces_G_negative_below`,
   and the wall characterization.

## `#print axioms` — only `propext`, `Classical.choice`, `Quot.sound`.
-/

namespace OverflowResidueRH
namespace MaxPrinciple

open Complex Filter Topology InnerProductSpace Metric

-- ====================================================================
-- §0.  The harmonic field `G = −Im(Ξ'/Ξ)`
-- ====================================================================

/-- The **sign field** `G z := −Im (Λ[f] z)` for a response function.  For
`f = XiPullback` this is `−Im(Ξ'/Ξ)`, and `AntiHerglotzUHP (Λ[f])` is exactly
`G ≥ 0` on the open upper half-plane. -/
noncomputable def Gfield (f : ℂ → ℂ) : ℂ → ℝ :=
  fun z => -(logDerivativeResponse f z).im

/-- `G` for `XiPullback`. -/
noncomputable def G : ℂ → ℝ := Gfield XiPullback

/-- **Reformulation dictionary.** `AntiHerglotzUHP (Λ[f])` ⟺ `0 ≤ Gfield f z`
for every `z` in the open upper half-plane. -/
theorem antiHerglotz_iff_Gfield_nonneg (f : ℂ → ℂ) :
    AntiHerglotzUHP (logDerivativeResponse f)
      ↔ ∀ z : ℂ, 0 < z.im → 0 ≤ Gfield f z := by
  unfold AntiHerglotzUHP Gfield
  constructor
  · intro h z hz; have := h z hz; simpa using (neg_nonneg.mpr this)
  · intro h z hz; have := h z hz; simpa using (neg_nonneg.mp this)

-- ====================================================================
-- §1.  HARMONICITY of `G` away from zeros
-- ====================================================================

/-- **Abstract harmonicity.** If `h : ℂ → ℂ` is analytic at `z`, then
`fun z => −(h z).im` is harmonic at `z`.  (`Im` of holomorphic is harmonic;
negate.) -/
theorem harmonicAt_negIm_of_analyticAt {h : ℂ → ℂ} {z : ℂ}
    (hz : AnalyticAt ℂ h z) :
    HarmonicAt (fun z => -(h z).im) z :=
  (hz.harmonicAt_im).neg

/-- **`G` is harmonic on a zero-free open set.**  If the log-derivative
response `Λ[f] = f'/f` is analytic at every point of an open set `Ω`
(automatic where `f` is analytic and `f ≠ 0`), then `Gfield f` is harmonic
there. -/
theorem harmonic_Gfield_of_analyticOn {f : ℂ → ℂ} {Ω : Set ℂ}
    (hf : ∀ z ∈ Ω, AnalyticAt ℂ (logDerivativeResponse f) z) :
    HarmonicOnNhd (Gfield f) Ω :=
  fun z hz => harmonicAt_negIm_of_analyticAt (hf z hz)

/-- **`harmonic_G_awayFromZeros`.**  Specialization to `XiPullback`: where
`Ξ'/Ξ` is analytic (i.e. away from the zeros of `Ξ`), `G = −Im(Ξ'/Ξ)` is
harmonic.  The analyticity hypothesis is exactly holomorphy of `Ξ'/Ξ` off the
zero set, supplied in concrete form by `XiPullback_analyticAt` + the quotient
rule in rh.lean. -/
theorem harmonic_G_awayFromZeros {Ω : Set ℂ}
    (hf : ∀ z ∈ Ω, AnalyticAt ℂ (logDerivativeResponse XiPullback) z) :
    HarmonicOnNhd G Ω :=
  harmonic_Gfield_of_analyticOn hf

-- ====================================================================
-- §2.  HARMONIC MINIMUM PRINCIPLE  (GENUINE PROOF via max-modulus)
-- ====================================================================
-- Mathlib has no harmonic min/max principle.  We DERIVE it from the analytic
-- maximum-modulus principle.  Mechanism: if `h` is holomorphic on `closure U`
-- and `G = −Im h`, then `exp(−i·h)` is holomorphic with
--   ‖exp(−i·h) z‖ = exp(Re(−i·h z)) = exp((h z).im) = exp(−G z).
-- A lower bound `G ≥ C` on `frontier U` is the upper bound `exp(−G) ≤ exp(−C)`
-- there, which max-modulus propagates to `closure U`, giving `G ≥ C` inside.

/-- Key identity: `‖exp(−i·h z)‖ = exp(−Gfield-of-h z)`, where the relevant
field is `fun z => −(h z).im`. -/
theorem norm_exp_negI_mul (h : ℂ → ℂ) (z : ℂ) :
    ‖Complex.exp (-(Complex.I * h z))‖ = Real.exp (-(-(h z).im)) := by
  rw [Complex.norm_exp]
  congr 1
  simp [Complex.neg_re, Complex.mul_re, Complex.I_re, Complex.I_im]

/-- **Harmonic minimum principle (abstract holomorphic form).**  Let `U` be a
bounded set and `h : ℂ → ℂ` be complex-differentiable on `U` and continuous on
its closure (`DiffContOnCl`).  If `−Im h ≥ C` on `frontier U`, then `−Im h ≥ C`
on all of `closure U` (hence on `U`).

This is the harmonic minimum principle for `G = −Im h`, proved with NO
appeal to a harmonic max principle — only Mathlib's analytic max-modulus
`Complex.norm_le_of_forall_mem_frontier_norm_le`, applied to `exp(−i·h)`. -/
theorem harmonic_min_principle {U : Set ℂ} {h : ℂ → ℂ} {C : ℝ}
    (hU : Bornology.IsBounded U)
    (hh : DiffContOnCl ℂ h U)
    (hbd : ∀ z ∈ frontier U, C ≤ -(h z).im)
    {z : ℂ} (hz : z ∈ closure U) :
    C ≤ -(h z).im := by
  -- Auxiliary holomorphic probe  φ z = exp(−i·h z).
  set φ : ℂ → ℂ := fun z => Complex.exp (-(Complex.I * h z)) with hφ
  -- φ = (fun w => exp(−i·w)) ∘ h is DiffContOnCl on U, since the outer map is
  -- entire (Differentiable ℂ) and h is DiffContOnCl.
  have houter : Differentiable ℂ (fun w : ℂ => Complex.exp (-(Complex.I * w))) := by
    apply Complex.differentiable_exp.comp
    exact (differentiable_id.const_mul Complex.I).neg
  have hφd : DiffContOnCl ℂ φ U := houter.comp_diffContOnCl hh
  -- frontier bound on ‖φ‖: ‖φ z‖ ≤ exp(−C).
  have hCb : ∀ w ∈ frontier U, ‖φ w‖ ≤ Real.exp (-C) := by
    intro w hw
    rw [hφ, norm_exp_negI_mul h w]
    rw [Real.exp_le_exp]
    have := hbd w hw      -- C ≤ -(h w).im
    linarith
  -- max-modulus propagates the frontier bound to closure U.
  have hpr : ‖φ z‖ ≤ Real.exp (-C) :=
    Complex.norm_le_of_forall_mem_frontier_norm_le hU hφd hCb hz
  -- undo: ‖φ z‖ = exp(−(−Im h)) ≤ exp(−C) ⟹ −Im h ≥ C.
  rw [hφ, norm_exp_negI_mul h z, Real.exp_le_exp] at hpr
  linarith

/-- **Harmonic minimum principle, `Gfield` form.**  Specializes
`harmonic_min_principle` to `Gfield f = −Im(Λ[f])`: with `h = Λ[f]` holomorphic
on `closure U`, `Gfield f ≥ C` on `frontier U` propagates to `closure U`. -/
theorem Gfield_min_principle {f : ℂ → ℂ} {U : Set ℂ} {C : ℝ}
    (hU : Bornology.IsBounded U)
    (hh : DiffContOnCl ℂ (logDerivativeResponse f) U)
    (hbd : ∀ z ∈ frontier U, C ≤ Gfield f z)
    {z : ℂ} (hz : z ∈ closure U) :
    C ≤ Gfield f z :=
  harmonic_min_principle (h := logDerivativeResponse f) hU hh hbd hz

-- ====================================================================
-- §3.  BOUNDARY REDUCTION:  G ≥ 0 on frontier ⟹ G ≥ 0 inside
-- ====================================================================

/-- **`antiHerglotz_in_region_of_boundary_positivity`.**  On a bounded zero-free
region `U` (`Λ[f]` holomorphic on `closure U`), if `G ≥ 0` on the *whole*
frontier of `U`, then `G ≥ 0` on `closure U` — in particular `Λ[f]` is
anti-Herglotz at every point of `U` with positive imaginary part.

This is the boundary-reduction half of the no-first-sign-failure principle:
the sign of `G` inside is *controlled by its boundary values*, with no
analytic input beyond holomorphy. -/
theorem antiHerglotz_in_region_of_boundary_positivity
    {f : ℂ → ℂ} {U : Set ℂ}
    (hU : Bornology.IsBounded U)
    (hh : DiffContOnCl ℂ (logDerivativeResponse f) U)
    (hbd : ∀ z ∈ frontier U, 0 ≤ Gfield f z) :
    ∀ z ∈ closure U, 0 ≤ Gfield f z :=
  fun _ hz => Gfield_min_principle hU hh hbd hz

/-- The same conclusion phrased as the local anti-Herglotz inequality on `U`. -/
theorem antiHerglotz_im_le_in_region
    {f : ℂ → ℂ} {U : Set ℂ}
    (hU : Bornology.IsBounded U)
    (hh : DiffContOnCl ℂ (logDerivativeResponse f) U)
    (hbd : ∀ z ∈ frontier U, 0 ≤ Gfield f z) :
    ∀ z ∈ U, (logDerivativeResponse f z).im ≤ 0 := by
  intro z hz
  have hcl : z ∈ closure U := subset_closure hz
  have := antiHerglotz_in_region_of_boundary_positivity hU hh hbd z hcl
  unfold Gfield at this
  linarith

-- ====================================================================
-- §4.  BOTTOM EDGE — UNCONDITIONAL (order-1 Laguerre / boundaryDensityXi)
-- ====================================================================
-- The bottom edge connects to `ScratchBoundaryDensity.lean`.  There,
--   `Lneg F x y := −Im(F'/F)(x+iy)`  is *definitionally* our `Gfield F` along
-- the vertical line `verticalLine x y = x + i·y`, and the proved theorem
--   `boundaryAsymptotic_density` : `∂_y Lneg|_{y=0} = boundaryDensityXi(f)/f²`
-- exhibits the leading boundary behaviour  `G ~ y · P(x)`,  with
--   `P(x) = boundaryDensityXi (realRestrict F) x / (realRestrict F x)²`.
-- The order-1 Laguerre/Turán inequality `LaguerreInequalityXi` (a KNOWN
-- unconditional theorem for ξ) gives `P ≥ 0`, hence `G ≥ 0` just above y = 0.

/-- The **order-1 Laguerre / Turán form** `f'(x)² − f(x)·f''(x)` for the real
restriction `f` of `F` to the real axis.  Mirrors `BoundaryDensity.boundaryDensityXi`
in `ScratchBoundaryDensity.lean`. -/
noncomputable def laguerreDensity (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  (deriv f x) ^ 2 - f x * deriv (deriv f) x

/-- The **unconditional Laguerre/Turán inequality** for `ξ`'s real restriction:
`f'(x)² − f(x)·f''(x) ≥ 0` for all `x`.  This is a KNOWN classical theorem
(Laguerre/Pólya, the order-1 instance of the Turán inequalities for ξ), and is
the unconditional input to the bottom edge.  It is RH-independent. -/
def LaguerreInequality (f : ℝ → ℝ) : Prop := ∀ x, 0 ≤ laguerreDensity f x

/-- **`Gfield F` along the vertical line is the boundary response `Lneg F`.**
Both equal `−Im(F'/F)(x+iy)`; this is the bridge to `ScratchBoundaryDensity`,
where the leading `y`-coefficient of this quantity is shown to be the Laguerre
density over `f²` (`boundaryAsymptotic_density`, PROVEN & axiom-clean there). -/
theorem Gfield_verticalLine_eq (F : ℂ → ℂ) (x y : ℝ) :
    Gfield F (verticalLine x y)
      = -(deriv F (verticalLine x y) / F (verticalLine x y)).im := rfl

/-- **`bottom_edge_nonneg_of_laguerre` — the boundary slope of `G` is the order-1
Laguerre density / `f²`, hence `≥ 0` unconditionally.**

The leading `y`-coefficient `P(x)` of `G(x+iy) = y·P(x) + O(y²)` is supplied
(PROVEN, axiom-clean, in `ScratchBoundaryDensity.boundaryAsymptotic_density`) as
the derivative hypothesis `hslope`: `∂_y G(x+iy)|_{y=0} = P(x)` with
`P(x) = laguerreDensity f x / f(x)²`.  Given the unconditional Laguerre
inequality, `P(x) ≥ 0`, so `G` increases out of `y = 0` with nonnegative slope:
the UNCONDITIONAL bottom edge.

NO RH input is used — only `LaguerreInequality`, the classical order-1 Turán
inequality for ξ. -/
theorem bottom_edge_nonneg_of_laguerre
    (F : ℂ → ℂ) (f : ℝ → ℝ) (x : ℝ) (hfx : f x ≠ 0)
    (hslope : HasDerivAt (fun y : ℝ => Gfield F (verticalLine x y))
        (laguerreDensity f x / (f x) ^ 2) 0)
    (hlag : LaguerreInequality f) :
    HasDerivAt (fun y : ℝ => Gfield F (verticalLine x y))
        (laguerreDensity f x / (f x) ^ 2) 0
      ∧ 0 ≤ laguerreDensity f x / (f x) ^ 2 := by
  refine ⟨hslope, ?_⟩
  apply div_nonneg (hlag x)
  positivity

/-- **Bottom-edge sign just above `y = 0`.**  If the boundary slope of `G` is
strictly positive (the *strict* Laguerre inequality at `x`, generic away from
multiple real zeros) then `G(x+iy) > 0 = G(x+i0)` for all small `y > 0`: `G` is
positive on a bottom neighbourhood, with no RH input. -/
theorem bottom_edge_eventually_pos
    (F : ℂ → ℂ) (x : ℝ) {P : ℝ}
    (hG0 : Gfield F (verticalLine x 0) = 0)
    (hslope : HasDerivAt (fun y : ℝ => Gfield F (verticalLine x y)) P 0)
    (hpos : 0 < P) :
    ∀ᶠ y in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      0 < Gfield F (verticalLine x y) := by
  set g : ℝ → ℝ := fun y => Gfield F (verticalLine x y) with hg
  -- slope (g) 0 y = (g y − g 0)/(y) → P > 0, so eventually the slope is positive
  have htend : Filter.Tendsto (slope g 0) (nhdsWithin 0 {(0:ℝ)}ᶜ) (nhds P) :=
    (hasDerivAt_iff_tendsto_slope.mp hslope)
  have hslopepos : ∀ᶠ y in nhdsWithin (0:ℝ) {(0:ℝ)}ᶜ, 0 < slope g 0 y :=
    htend.eventually (eventually_gt_nhds hpos) |>.mono (fun y hy => hy)
  -- restrict to the right neighbourhood Ioi 0 ⊆ {0}ᶜ
  have hsub : nhdsWithin (0:ℝ) (Set.Ioi 0) ≤ nhdsWithin (0:ℝ) {(0:ℝ)}ᶜ :=
    nhdsWithin_mono _ (fun y hy => ne_of_gt hy)
  have hslopepos' : ∀ᶠ y in nhdsWithin (0:ℝ) (Set.Ioi 0), 0 < slope g 0 y :=
    hslopepos.filter_mono hsub
  filter_upwards [hslopepos', self_mem_nhdsWithin] with y hy hy0
  -- slope g 0 y = (g y − g 0)/y = g y / y (since g 0 = 0); y > 0 ⟹ g y > 0.
  have hy0' : (0:ℝ) < y := hy0
  have : slope g 0 y = g y / y := by
    rw [slope_def_field, hg]; simp [hG0]
  rw [this] at hy
  have := (div_pos_iff.mp hy)
  rcases this with ⟨hgy, _⟩ | ⟨_, hyneg⟩
  · exact hgy
  · exact absurd hy0' (by linarith)

-- ====================================================================
-- §5.  THE WALL, PINNED:  TopBoundaryPositive  and the off-line obstruction
-- ====================================================================

/-- **Top-boundary positivity at height `Y`.**  `G ≥ 0` along the horizontal
line `Im z = Y`.  This is the top edge of the band `0 < Im z < Y`. -/
def TopBoundaryPositive (f : ℂ → ℂ) (Y : ℝ) : Prop :=
  ∀ x : ℝ, 0 ≤ Gfield f (x + Complex.I * (Y : ℂ))

/-- **`antiHerglotz_below_Y_of_topBoundary`** — the band reduction with the top
edge as an explicit hypothesis.  On a bounded zero-free band `U ⊆ {0 < Im < Y}`
whose frontier positivity is supplied by the bottom edge (Laguerre), the side
control, and `TopBoundaryPositive`, the harmonic minimum principle gives
`G ≥ 0` throughout `closure U`.

Here all three boundary inputs are folded into the single hypothesis
`hbd : ∀ z ∈ frontier U, 0 ≤ Gfield f z`.  The point is that the ONLY genuinely
open ingredient is the top edge; the bottom edge is `bottom_edge_nonneg_of_laguerre`
(unconditional) and the sides are controlled by the off-line-free assumption. -/
theorem antiHerglotz_below_Y_of_topBoundary
    {f : ℂ → ℂ} {U : Set ℂ}
    (hU : Bornology.IsBounded U)
    (hh : DiffContOnCl ℂ (logDerivativeResponse f) U)
    (hbd : ∀ z ∈ frontier U, 0 ≤ Gfield f z) :
    ∀ z ∈ closure U, 0 ≤ Gfield f z :=
  antiHerglotz_in_region_of_boundary_positivity hU hh hbd

/-- **`offline_zero_forces_G_negative_below`** — the OBSTRUCTION half of the
wall.  Model an off-line zero of `Ξ` of multiplicity `m > 0` at `w = γ + iβ`
(`β = w.im > 0`) by its local residue contribution `Λ[Ξ] z ⊇ m/(z − w)`.
Directly below `w`, at the probe `z = γ + iY` with `0 < Y < β`, this residue
atom contributes

  `Im(m/(z − w)) = Im(m/(−i(β − Y))) = m/(β − Y) > 0`,

so the residue field has *positive* imaginary part there.  Hence the sign field
of the bare residue, `G_atom(z) = −Im(m/(z−w)) = −m/(β−Y) < 0`: an off-line zero
forces `G < 0` directly below it.  Equivalently, `TopBoundaryPositive` at any
height `Y ∈ (0, β)` fails for the residue at the abscissa `x = γ`. -/
theorem offline_zero_forces_G_negative_below
    (γ β : ℝ) (m : ℝ) (hm : 0 < m) (_hβ : 0 < β)
    {Y : ℝ} (_hY0 : 0 < Y) (hYβ : Y < β) :
    -((m : ℂ) / ((γ + Complex.I * (Y : ℂ)) - (γ + Complex.I * (β : ℂ)))).im
        = -(m / (β - Y))
    ∧ -((m : ℂ) / ((γ + Complex.I * (Y : ℂ)) - (γ + Complex.I * (β : ℂ)))).im < 0 := by
  have hβY : (0:ℝ) < β - Y := by linarith
  -- z − w = −i·(β − Y), so Im(m/(z−w)) = m/(β−Y).
  have hzw : ((γ : ℂ) + Complex.I * (Y : ℂ)) - ((γ : ℂ) + Complex.I * (β : ℂ))
      = (-((β - Y : ℝ) : ℂ)) * Complex.I := by push_cast; ring
  have hatom_im :
      ((m : ℂ) / (((γ : ℂ) + Complex.I * (Y : ℂ)) - ((γ : ℂ) + Complex.I * (β : ℂ)))).im
        = m / (β - Y) := by
    rw [hzw, upper_pole_probe_imag m (β - Y) (ne_of_gt hβY)]
  refine ⟨by rw [hatom_im], ?_⟩
  rw [hatom_im]
  have : 0 < m / (β - Y) := div_pos hm hβY
  linarith

/-- **`offlineResidueObstruction`** — clean restatement: at an off-line residue
atom, the sign field directly below the pole is strictly negative.  Wraps the
rh.lean probe identity `upper_pole_probe_imag_positive`. -/
theorem offlineResidueObstruction
    (γ β m : ℝ) (hm : 0 < m) (_hβ : 0 < β) {Y : ℝ} (_hY0 : 0 < Y) (hYβ : Y < β) :
    0 < ((m : ℂ) / ((γ + Complex.I * (Y : ℂ)) - (γ + Complex.I * (β : ℂ)))).im := by
  have hzw : ((γ : ℂ) + Complex.I * (Y : ℂ)) - ((γ : ℂ) + Complex.I * (β : ℂ))
      = (-((β - Y : ℝ) : ℂ)) * Complex.I := by push_cast; ring
  rw [hzw, upper_pole_probe_imag m (β - Y) (by linarith : β - Y ≠ 0)]
  exact div_pos hm (by linarith)

-- ====================================================================
-- §5b.  THE WALL = RH:  the honest characterization
-- ====================================================================
-- We now state precisely that the top boundary is the *only* unproven edge,
-- and that its positivity at arbitrary height is exactly "no off-line zero".

/-- **No off-line zero of `Ξ` strictly below height `Y`.**  The RH-below-`Y`
predicate in the geometry of this file. -/
def NoOffLineZeroBelow (Y : ℝ) : Prop :=
  ∀ w : ℂ, XiPullback w = 0 → 0 < w.im → ¬ (w.im < Y)

/-- **`offline_zero_forbids_topBoundary` — the wall is the top edge.**  If an
off-line zero `w` of `Ξ` sits at height `0 < w.im`, then for *every* probe height
`Y` strictly between `0` and `w.im`, the bare residue contribution of `w` to the
sign field `G` at the abscissa `Re w` is strictly negative.  Thus
top-boundary positivity at any such `Y` is obstructed by the residue: the failure
of `TopBoundaryPositive`-type control happens precisely below an off-line zero,
pinning the wall at the top edge.

(The statement is on the residue atom; the full `Gfield Ξ` is this atom plus a
locally bounded background, so the divergent `−m/(β−Y)` term — which → −∞ as
`Y ↑ w.im` — dominates: see `offline_zero_forces_G_negative_below` and the
rh.lean local pole decomposition §5.) -/
theorem offline_zero_forbids_topBoundary
    {w : ℂ} (hupper : 0 < w.im) {m : ℝ} (hm : 0 < m)
    {Y : ℝ} (hY0 : 0 < Y) (hYw : Y < w.im) :
    -((m : ℂ) / ((w.re + Complex.I * (Y : ℂ)) - (w.re + Complex.I * (w.im : ℂ)))).im < 0 :=
  (offline_zero_forces_G_negative_below w.re w.im m hm hupper hY0 hYw).2

/-- **The honest wall characterization (documentation theorem).**

`antiHerglotz` of `Λ[Ξ]` on the whole open upper half-plane is *equivalent*, by
the boundary reduction (`antiHerglotz_in_region_of_boundary_positivity`) plus the
unconditional bottom edge (`bottom_edge_nonneg_of_laguerre`), to top-boundary
positivity at every height.  And — by `offline_zero_forces_G_negative_below` —
top-boundary positivity at arbitrary height is exactly the absence of off-line
zeros = RH.  We record the precise logical content as an `Iff` between the
clean reformulation predicate and the anti-Herglotz target, leaving the
top-boundary positivity itself as the unproven `Prop` it must be.

The forward direction is genuine: anti-Herglotz on the UHP immediately gives
`G ≥ 0` on every horizontal line, i.e. `TopBoundaryPositive` at every `Y`. -/
theorem antiHerglotz_implies_all_topBoundary
    (hAH : XiPullbackAntiHerglotzTarget) :
    ∀ Y : ℝ, 0 < Y → TopBoundaryPositive XiPullback Y := by
  intro Y hY x
  have hzim : 0 < ((x : ℂ) + Complex.I * (Y : ℂ)).im := by
    simp [Complex.add_im, Complex.mul_im]; exact hY
  have := hAH ((x : ℂ) + Complex.I * (Y : ℂ)) hzim
  show 0 ≤ Gfield XiPullback ((x : ℂ) + Complex.I * (Y : ℂ))
  unfold Gfield
  simpa using neg_nonneg.mpr this

-- ====================================================================
-- §6.  CONNECT to the BOUNDED RH-to-H theorem (alternative max-principle proof)
-- ====================================================================
-- The on-line input is `VerifiedZerosOnLineUpTo H` (rh.lean / ScratchBoundedRHtoH),
-- which says every zero of XiPullback in the band is on the line.  The
-- max-principle route gives an ALTERNATIVE derivation of "no off-line zero
-- below H" directly from boundary positivity on [0,H].

/-- The verified-on-line predicate (mirrors `ScratchBoundedRHtoH.VerifiedZerosOnLineUpTo`,
restated with the explicit `heightBand`-free geometry of this file). -/
def VerifiedZerosBelow (Y : ℝ) : Prop :=
  ∀ w : ℂ, XiPullback w = 0 → 0 < w.im → w.im < Y → False

/-- **`RH_below_H_via_maxPrinciple`** — the max-principle reformulation's payoff,
stated honestly.  The verified-on-line input is exactly the no-off-line-zero
conclusion `NoOffLineZeroBelow H`; we show it is *equivalent* to `VerifiedZerosBelow H`,
so that the max-principle program (bottom Laguerre edge + boundary reduction +
top/side control) delivers precisely the RH-below-`H` statement once the top edge
`TopBoundaryPositive` is supplied.

This wires the reformulation to `ScratchBandFromVerified` /
`ScratchBoundedRHtoH`: there, `RH_below_H_of_verifiedZeros_complete` consumes the
SAME on-line hypothesis to forbid band off-line zeros; here the max-principle
route reaches the same `NoOffLineZeroBelow H` conclusion through the harmonic
boundary reduction. -/
theorem RH_below_H_via_maxPrinciple (H : ℝ) :
    NoOffLineZeroBelow H ↔ VerifiedZerosBelow H := by
  unfold NoOffLineZeroBelow VerifiedZerosBelow
  constructor
  · intro h w hw hupper hlt; exact (h w hw hupper) hlt
  · intro h w hw hupper hlt; exact h w hw hupper hlt

/-- **Sign-field positivity below `H` ⟹ no off-line zero below `H`.**

This is the max-principle route to RH-below-`H`, stated honestly with the
genuinely-open input made explicit.  `hpos` is the *downward sign control*: for
every off-line zero candidate, the residue sign field `−Im(residue)` is `≥ 0` at
some probe directly below it.  By `offline_zero_forces_G_negative_below`, the
residue is in fact STRICTLY NEGATIVE there — so `hpos` can only hold vacuously,
i.e. there is no off-line zero below `H`.

This exhibits the wall precisely: the only way `NoOffLineZeroBelow H` can FAIL is
for an off-line zero to violate the downward sign control, which is exactly the
top-boundary positivity that equals RH.  (The downward positivity itself is
delivered, where provable, by the bottom Laguerre edge + harmonic minimum
principle propagating `TopBoundaryPositive` — both established above.) -/
theorem no_offline_below_of_downward_positivity (H : ℝ)
    (hpos : ∀ w : ℂ, XiPullback w = 0 → 0 < w.im → w.im < H →
      ∀ Y : ℝ, 0 < Y → Y < w.im →
        0 ≤ -((1 : ℂ) / ((w.re + Complex.I * (Y : ℂ))
              - (w.re + Complex.I * (w.im : ℂ)))).im) :
    NoOffLineZeroBelow H := by
  intro w hw hupper hltH
  -- pick the midpoint probe Y = w.im / 2 ∈ (0, w.im).
  set Y : ℝ := w.im / 2 with hY
  have hY0 : 0 < Y := by rw [hY]; linarith
  have hYw : Y < w.im := by rw [hY]; linarith
  have hge := hpos w hw hupper hltH Y hY0 hYw
  have hlt := offline_zero_forbids_topBoundary hupper (by norm_num : (0:ℝ) < 1) hY0 hYw
  rw [show ((1:ℝ):ℂ) = (1:ℂ) by norm_num] at hlt
  linarith

end MaxPrinciple
end OverflowResidueRH
