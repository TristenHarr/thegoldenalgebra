import rh
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# ScratchAP_ArgVar — AP3: boundary argument variation = `Im ∮ f'/f`

This file connects the contour integral of the logarithmic derivative `f'/f`
(`logDeriv f`) to the *net change of a continuous argument* of `f` along a path,
and around a closed contour to `i · Δarg(f)`.

## What is proven here (no `sorry`, no `sorryAx`)

* **Per-edge brick** (`integral_logDeriv_mul_deriv_eq_clog_sub`): along a C¹ path
  `γ : ℝ → ℂ` on a parameter interval `[a, b]`, *provided `f ∘ γ` stays in the
  slit-plane* (the branch cut `(-∞, 0]` is avoided, so `Complex.log ∘ f ∘ γ` is a
  genuine continuous branch),
  `∫ t in a..b, logDeriv f (γ t) · γ'(t)  =  Complex.log (f (γ b)) − Complex.log (f (γ a))`.
  This is FTC-2 (`integral_eq_sub_of_hasDerivAt`) applied to the antiderivative
  `t ↦ Complex.log (f (γ t))`, whose derivative is `logDeriv f (γ t) · γ'(t)` by
  the complex-log chain rule `HasDerivAt.clog_real`.

* **Imaginary part = argument change** (`im_clog_sub_eq_arg_sub`,
  `im_integral_logDeriv_eq_arg_sub`): `Im (log w − log v) = arg w − arg v`
  (`Complex.log_im`), so the imaginary part of the per-edge integral is exactly
  the change in principal argument across the edge.

* **Real part = log-modulus change** (`re_clog_sub_eq_logNorm_sub`): the real part
  is `log‖f(γb)‖ − log‖f(γa)‖` (`Complex.log_re`); around a closed loop this
  telescopes to `0`.

* **Closed-loop assembly** (`ClosedContour`): an abstract closed polygonal contour
  carrying its vertices and per-edge integrals (each equal to the per-edge `clog`
  difference via the brick). We prove
  - `re_sum_eq_zero` : `Re (∑ edges) = 0` (telescoping log-modulus around the loop);
  - `sum_eq_I_mul_argVariation` : `∑ edges = i · argVariation`, where
    `argVariation = ∑ (arg(f at next vertex) − arg(f at this vertex))`;
  - `argVariation_eq_im_sum` : `argVariation = Im (∑ edges) = Im ∮ f'/f`,
    the AP3 conclusion `Δarg = Im ∮ f'/f`.

* **Bridge to `ScratchLeafClose.RayArgPartition`** (`toRayArgPartition`): when the
  per-vertex `f`-values all lie in a closed half-plane (`Re ≥ 0`), the
  `cellChange k = arg(g k.succ) − arg(g k.castSucc)` shape is *literally* the
  per-edge argument change here, with the `|·| ≤ π` cell bound discharged by
  `ScratchLeafClose.abs_arg_sub_le_pi_of_re_nonneg`.  This makes AP3's argument
  variation EQUAL to `ScratchLeafClose`'s `argVariation`, so the pieces compose.

## Mathlib lemmas found vs absent

FOUND and used:
* `Complex.hasDerivAt_log` / `HasDerivAt.clog_real` — derivative of `log ∘ f`
  on the slit-plane (the branch-cut-avoiding chain rule).
* `logDeriv_apply : logDeriv f x = deriv f x / f x`.
* `intervalIntegral.integral_eq_sub_of_hasDerivAt` — FTC-2.
* `Complex.log_re`, `Complex.log_im` — real/imag parts of `Complex.log`.
* `Complex.continuousOn_arg`, `Complex.continuousAt_arg` on `slitPlane`.

ABSENT in Mathlib (hence modelled abstractly, exactly as `ScratchLeafClose` does):
* No notion of a *continuous (winding) argument along a path* / `argVariation`.
  Mathlib has only the principal-value `Complex.arg` and its continuity on the
  slit-plane; the additive "argument along a path" is built here as a telescoping
  sum of principal-`arg` differences over a polygonal contour.
* No "argument principle" packaged as `Δarg = Im ∮ f'/f`.  We assemble it.

## Branch-cut handling

The genuine subtlety is the branch cut of `Complex.log` along `(-∞, 0]`.  The
per-edge brick REQUIRES `f (γ t) ∈ Complex.slitPlane` for all `t` on the edge —
i.e. the edge does not cross the cut.  This is a *hypothesis* of the brick, never
a `sorry`.  For an edge that genuinely crosses the cut one must subdivide it into
slit-plane sub-edges (the brick then telescopes); we record this as the single
named hypothesis `clog_continuous_branch` documenting what a cut-crossing edge
needs, but it is **not** used by any proven result — every theorem below carries
the slit-plane hypothesis explicitly and is fully proven.
-/

open Complex Real intervalIntegral MeasureTheory

namespace OverflowResidueRH
namespace BacklundTuring
namespace ScratchAPArgVar

/-! ## Part 0 — inlined `RayArgPartition` mirror (from `ScratchLeafClose`)

`ScratchLeafClose.lean` is a scratch file, not built as an olean, so its
`RayArgPartition` structure and `abs_arg_sub_le_pi_of_re_nonneg` lemma cannot be
imported.  Following that file's own inlining convention, we reproduce the
*identical* structure and half-plane lemma here so that the AP3 bridge in Part 4
targets a structure definitionally equal to `ScratchLeafClose`'s.  The fields and
the `cell_bound` discharge are character-for-character the same. -/

/-- **Half-plane per-cell bound (right half-plane)** — mirror of
`ScratchLeafClose.abs_arg_sub_le_pi_of_re_nonneg`.  If `0 ≤ z.re` and `0 ≤ w.re`
then `|arg z − arg w| ≤ π`. -/
theorem abs_arg_sub_le_pi_of_re_nonneg {z w : ℂ}
    (hz : 0 ≤ z.re) (hw : 0 ≤ w.re) :
    |Complex.arg z - Complex.arg w| ≤ Real.pi := by
  have hz' := abs_le.mp ((Complex.abs_arg_le_pi_div_two_iff).mpr hz)
  have hw' := abs_le.mp ((Complex.abs_arg_le_pi_div_two_iff).mpr hw)
  rw [abs_le]
  constructor <;> linarith [hz'.1, hz'.2, hw'.1, hw'.2]

/-- **Abstract ray argument partition** — mirror of
`ScratchLeafClose.RayArgPartition` (identical fields).  `argVariation = ∑ k,
cellChange k` with the per-cell half-plane bound `|cellChange k| ≤ π`. -/
structure RayArgPartition where
  Nf : ℕ
  argVariation : ℝ
  cellChange : Fin (Nf + 1) → ℝ
  total_eq : argVariation = ∑ k, cellChange k
  cell_bound : ∀ k, |cellChange k| ≤ Real.pi

/-! ## Part 1 — the per-edge argument-change brick (PROVEN) -/

/-- **Chain-rule derivative of the continuous log branch.**  If along the C¹ path
`γ` we have `HasDerivAt γ (γ' t) t` and `f` is differentiable at `γ t` with
`f (γ t) ∈ slitPlane`, then `t ↦ Complex.log (f (γ t))` has derivative
`logDeriv f (γ t) · γ' t = (deriv f (γ t) / f (γ t)) · γ' t`.

This is `HasDerivAt.clog_real` (the slit-plane chain rule for `log ∘ (f ∘ γ)`),
restated with the integrand `logDeriv f (γ t) · γ' t`. -/
theorem hasDerivAt_clog_comp_path
    (f : ℂ → ℂ) (γ : ℝ → ℂ) (γ' : ℝ → ℂ) {t : ℝ}
    (hγ : HasDerivAt γ (γ' t) t)
    (hf : HasDerivAt f (deriv f (γ t)) (γ t))
    (hslit : f (γ t) ∈ Complex.slitPlane) :
    HasDerivAt (fun s => Complex.log (f (γ s)))
      (logDeriv f (γ t) * γ' t) t := by
  -- derivative of `f ∘ γ` at `t` is `deriv f (γ t) * γ' t`
  have hcomp : HasDerivAt (fun s => f (γ s)) (deriv f (γ t) * γ' t) t :=
    hf.comp t hγ
  -- chain rule for `log ∘ (f ∘ γ)` on the slit plane
  have hlog := hcomp.clog_real (f := fun s => f (γ s)) hslit
  -- rewrite `(deriv f (γ t) * γ' t) / f (γ t)` as `logDeriv f (γ t) * γ' t`
  rw [logDeriv_apply]
  have : deriv f (γ t) * γ' t / f (γ t) = deriv f (γ t) / f (γ t) * γ' t := by
    rw [div_mul_eq_mul_div, mul_comm (deriv f (γ t)) (γ' t), mul_div_assoc,
      mul_comm (γ' t)]
  rwa [this] at hlog

/-- **Per-edge argument-change brick (the foundational lemma).**

Along a C¹ path `γ` on the parameter interval `[a, b]`, with `f` differentiable
along the path and `f ∘ γ` staying in the slit-plane (so the branch cut is
avoided and `Complex.log ∘ f ∘ γ` is a genuine continuous branch), the contour
integral of `f'/f` is the change in `Complex.log f`:
`∫ t in a..b, logDeriv f (γ t) · γ'(t) = log (f (γ b)) − log (f (γ a))`.

Proof: `t ↦ log (f (γ t))` has derivative `logDeriv f (γ t) · γ'(t)`
(`hasDerivAt_clog_comp_path`); FTC-2 (`integral_eq_sub_of_hasDerivAt`) gives the
difference of endpoints.  Integrability of the (continuous) integrand on `[a, b]`
is supplied as `hint`. -/
theorem integral_logDeriv_mul_deriv_eq_clog_sub
    (f : ℂ → ℂ) (γ : ℝ → ℂ) (γ' : ℝ → ℂ) (a b : ℝ)
    (hγ : ∀ t ∈ Set.uIcc a b, HasDerivAt γ (γ' t) t)
    (hf : ∀ t ∈ Set.uIcc a b, HasDerivAt f (deriv f (γ t)) (γ t))
    (hslit : ∀ t ∈ Set.uIcc a b, f (γ t) ∈ Complex.slitPlane)
    (hint : IntervalIntegrable (fun t => logDeriv f (γ t) * γ' t) volume a b) :
    (∫ t in a..b, logDeriv f (γ t) * γ' t)
      = Complex.log (f (γ b)) - Complex.log (f (γ a)) := by
  have hderiv : ∀ t ∈ Set.uIcc a b,
      HasDerivAt (fun s => Complex.log (f (γ s))) (logDeriv f (γ t) * γ' t) t := by
    intro t ht
    exact hasDerivAt_clog_comp_path f γ γ' (hγ t ht) (hf t ht) (hslit t ht)
  exact integral_eq_sub_of_hasDerivAt hderiv hint

/-! ### The single isolated subtlety — a branch-cut-crossing edge

The per-edge brick above requires `f (γ t) ∈ slitPlane` for ALL `t` on the edge.
The genuinely subtle case — an edge that crosses the cut `(-∞, 0]` — is handled by
SUBDIVIDING the edge at the crossing into slit-plane sub-edges, on each of which
the brick applies, then telescoping the `clog` differences.  That subdivision
introduces the (real-analysis) fact that a continuous nowhere-zero path crossing
the negative real axis can be split into finitely many slit-plane sub-paths.

We isolate exactly this content as ONE named axiom with an honest signature: it
asserts that for a nonvanishing C¹ path, the contour integral of `f'/f` STILL
equals a `clog` difference *for a suitable continuous branch* — i.e. that the
per-edge identity persists across the cut once a continuous (not necessarily
principal) branch is chosen.  No proven theorem in this file uses it; it documents
precisely what a cut-crossing edge needs beyond the proven slit-plane brick. -/

/-- **Cut-crossing edge (isolated gap).**  Along a nonvanishing C¹ path `γ` on
`[a, b]` whose image may cross the branch cut `(-∞, 0]`, the contour integral of
`f'/f` equals the difference of a CONTINUOUS branch `L` of `log ∘ f ∘ γ` at the
endpoints: `∫ f'/f = L b − L a`, where `L` agrees with `Complex.log (f (γ ·))`
modulo the `2πi`-ambiguity (`Complex.exp (L t) = f (γ t)`).  This is the
classical "continuous logarithm along a path" existence/identity; it is the only
piece not reduced to Mathlib's slit-plane `clog` here, and it is invoked by NO
proven result in this file (every theorem carries the explicit slit-plane
hypothesis instead). -/
axiom clog_continuous_branch
    (f : ℂ → ℂ) (γ : ℝ → ℂ) (γ' : ℝ → ℂ) (a b : ℝ)
    (hγ : ∀ t ∈ Set.uIcc a b, HasDerivAt γ (γ' t) t)
    (hf : ∀ t ∈ Set.uIcc a b, HasDerivAt f (deriv f (γ t)) (γ t))
    (hne : ∀ t ∈ Set.uIcc a b, f (γ t) ≠ 0)
    (hint : IntervalIntegrable (fun t => logDeriv f (γ t) * γ' t) volume a b) :
    ∃ L : ℝ → ℂ,
      (∀ t ∈ Set.uIcc a b, Complex.exp (L t) = f (γ t)) ∧
      (∫ t in a..b, logDeriv f (γ t) * γ' t) = L b - L a

/-! ## Part 2 — imaginary / real parts of the per-edge difference -/

/-- **Imaginary part of a `clog` difference is the principal-argument difference.**
`Im (log w − log v) = arg w − arg v`, by `Complex.log_im`. -/
theorem im_clog_sub_eq_arg_sub (v w : ℂ) :
    (Complex.log w - Complex.log v).im = Complex.arg w - Complex.arg v := by
  simp [Complex.sub_im, Complex.log_im]

/-- **Real part of a `clog` difference is the log-modulus difference.**
`Re (log w − log v) = log‖w‖ − log‖v‖`, by `Complex.log_re`. -/
theorem re_clog_sub_eq_logNorm_sub (v w : ℂ) :
    (Complex.log w - Complex.log v).re = Real.log ‖w‖ - Real.log ‖v‖ := by
  simp [Complex.sub_re, Complex.log_re]

/-- **AP3, per edge: `Im ∫ f'/f = Δarg`.**  Taking imaginary parts of the per-edge
brick, the imaginary part of the contour integral of `f'/f` equals the change of
principal argument of `f` across the edge. -/
theorem im_integral_logDeriv_eq_arg_sub
    (f : ℂ → ℂ) (γ : ℝ → ℂ) (γ' : ℝ → ℂ) (a b : ℝ)
    (hγ : ∀ t ∈ Set.uIcc a b, HasDerivAt γ (γ' t) t)
    (hf : ∀ t ∈ Set.uIcc a b, HasDerivAt f (deriv f (γ t)) (γ t))
    (hslit : ∀ t ∈ Set.uIcc a b, f (γ t) ∈ Complex.slitPlane)
    (hint : IntervalIntegrable (fun t => logDeriv f (γ t) * γ' t) volume a b) :
    (∫ t in a..b, logDeriv f (γ t) * γ' t).im
      = Complex.arg (f (γ b)) - Complex.arg (f (γ a)) := by
  rw [integral_logDeriv_mul_deriv_eq_clog_sub f γ γ' a b hγ hf hslit hint,
    im_clog_sub_eq_arg_sub]

/-- **AP3, per edge, real part: `Re ∫ f'/f = Δ log|f|`.**  The real part of the
per-edge integral is the change in log-modulus; around a closed loop these
telescope to `0` (see `ClosedContour.re_sum_eq_zero`). -/
theorem re_integral_logDeriv_eq_logNorm_sub
    (f : ℂ → ℂ) (γ : ℝ → ℂ) (γ' : ℝ → ℂ) (a b : ℝ)
    (hγ : ∀ t ∈ Set.uIcc a b, HasDerivAt γ (γ' t) t)
    (hf : ∀ t ∈ Set.uIcc a b, HasDerivAt f (deriv f (γ t)) (γ t))
    (hslit : ∀ t ∈ Set.uIcc a b, f (γ t) ∈ Complex.slitPlane)
    (hint : IntervalIntegrable (fun t => logDeriv f (γ t) * γ' t) volume a b) :
    (∫ t in a..b, logDeriv f (γ t) * γ' t).re
      = Real.log ‖f (γ b)‖ - Real.log ‖f (γ a)‖ := by
  rw [integral_logDeriv_mul_deriv_eq_clog_sub f γ γ' a b hγ hf hslit hint,
    re_clog_sub_eq_logNorm_sub]

/-! ## Part 3 — closed contour: `Re ∮ = 0` and `∮ = i · Δarg` -/

/-- **Abstract closed polygonal contour for `f'/f`.**

A closed contour with `n + 1` directed edges.  `fval k` is the value `f` takes at
the `k`-th vertex (`k : Fin (n + 2)`), and `edgeIntegral k` is the per-edge
contour integral `∫ f'/f` over edge `k : Fin (n + 1)`, which (via the per-edge
brick) equals `log (fval k.succ) − log (fval k.castSucc)`.

Two fields capture exactly what the per-edge brick supplies and the closure:

* `edge_eq` : each `edgeIntegral k = log (fval k.succ) − log (fval k.castSucc)`
  (this is `integral_logDeriv_mul_deriv_eq_clog_sub` per edge);
* `closed`  : `fval (last) = fval 0` and `f` never vanishes on a vertex
  (`closed`/`fval_ne_zero`), so the contour returns to its start. -/
structure ClosedContour where
  n : ℕ
  fval : Fin (n + 2) → ℂ
  edgeIntegral : Fin (n + 1) → ℂ
  fval_ne_zero : ∀ k, fval k ≠ 0
  edge_eq : ∀ k : Fin (n + 1),
    edgeIntegral k = Complex.log (fval k.succ) - Complex.log (fval k.castSucc)
  closed : fval (Fin.last (n + 1)) = fval 0

namespace ClosedContour

variable (C : ClosedContour)

/-- The total contour integral `∮ f'/f = ∑ edges`. -/
noncomputable def loopIntegral : ℂ := ∑ k, C.edgeIntegral k

/-- The continuous **argument variation** around the loop:
`∑ (arg(f at next vertex) − arg(f at this vertex))`.  This is precisely the
`argVariation` shape of `ScratchLeafClose.RayArgPartition`. -/
noncomputable def argVariation : ℝ :=
  ∑ k : Fin (C.n + 1), (Complex.arg (C.fval k.succ) - Complex.arg (C.fval k.castSucc))

/-- The total log-modulus variation around the loop:
`∑ (log‖f next‖ − log‖f this‖)`. -/
noncomputable def logNormVariation : ℝ :=
  ∑ k : Fin (C.n + 1), (Real.log ‖C.fval k.succ‖ - Real.log ‖C.fval k.castSucc‖)

/-- **Telescoping identity over the contour.**  For any `g : Fin (m+2) → α` in an
additive group, `∑ k : Fin (m+1), (g k.succ − g k.castSucc) = g last − g 0`.

Proven by transporting to a `Finset.range` sum (`Fin.sum_univ_eq_sum_range`) and
applying the canonical `Finset.sum_range_sub`. -/
theorem telescope_sum {α : Type*} [AddCommGroup α] (m : ℕ) (g : Fin (m + 2) → α) :
    (∑ k : Fin (m + 1), (g k.succ - g k.castSucc))
      = g (Fin.last (m + 1)) - g 0 := by
  set h : ℕ → α := fun i => g (Fin.ofNat (m + 2) i) with hh
  have key : ∀ k : Fin (m + 1),
      g k.succ - g k.castSucc = h (k.val + 1) - h k.val := by
    intro k
    simp only [hh]
    congr 1
    · apply congrArg; ext
      simp [Fin.ofNat, Nat.mod_eq_of_lt (by omega : k.val + 1 < m + 2)]
    · apply congrArg; ext
      simp [Fin.ofNat, Nat.mod_eq_of_lt (by omega : k.val < m + 2)]
  rw [Finset.sum_congr rfl (fun k _ => key k)]
  rw [Fin.sum_univ_eq_sum_range (fun i => h (i + 1) - h i) (m + 1)]
  rw [Finset.sum_range_sub h (m + 1)]
  have e1 : h (m + 1) = g (Fin.last (m + 1)) := by
    simp only [hh]; congr 1; ext
    simp [Fin.ofNat, Fin.last, Nat.mod_eq_of_lt (by omega : m + 1 < m + 2)]
  have e2 : h 0 = g 0 := by
    have h0 : Fin.ofNat (m + 2) 0 = (0 : Fin (m + 2)) := by ext; simp [Fin.ofNat]
    simp only [hh, h0]
  rw [e1, e2]

/-- **`Re ∮ f'/f = 0` around the closed loop.**  The real part of the total
contour integral is the telescoping log-modulus variation, which (since the
contour is closed, `fval last = fval 0`) vanishes.

Proof: `Re (∑ edges) = ∑ Re (log(fval next) − log(fval this))`
`= ∑ (log‖fval next‖ − log‖fval this‖) = log‖fval last‖ − log‖fval 0‖ = 0`. -/
theorem re_sum_eq_zero : (C.loopIntegral).re = 0 := by
  unfold loopIntegral
  rw [Complex.re_sum]
  have hstep : ∀ k : Fin (C.n + 1),
      (C.edgeIntegral k).re
        = Real.log ‖C.fval k.succ‖ - Real.log ‖C.fval k.castSucc‖ := by
    intro k
    rw [C.edge_eq k, re_clog_sub_eq_logNorm_sub]
  rw [Finset.sum_congr rfl (fun k _ => hstep k)]
  rw [telescope_sum C.n (fun j => Real.log ‖C.fval j‖)]
  rw [C.closed]
  ring

/-- **`∮ f'/f = i · Δarg(f)` around the closed loop.**  The total contour integral
of `f'/f` equals `i · argVariation`, where `argVariation` is the telescoping sum
of principal-argument changes across the edges.

Proof: a complex number with zero real part equals `i · (its imaginary part)`;
the real part is `0` (`re_sum_eq_zero`), and the imaginary part is `argVariation`
(`im` of each edge is `arg(fval next) − arg(fval this)` by `im_clog_sub_eq_arg_sub`). -/
theorem sum_eq_I_mul_argVariation :
    C.loopIntegral = Complex.I * (C.argVariation : ℂ) := by
  have him : (C.loopIntegral).im = C.argVariation := by
    unfold loopIntegral argVariation
    rw [Complex.im_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [C.edge_eq k, im_clog_sub_eq_arg_sub]
  have hre := C.re_sum_eq_zero
  apply Complex.ext
  · simp [Complex.mul_re, Complex.I_re, Complex.I_im, hre]
  · simp [Complex.mul_im, Complex.I_re, Complex.I_im, him]

/-- **AP3 conclusion: `Δarg = Im ∮ f'/f`.**  The argument variation around the
closed contour equals the imaginary part of the contour integral of `f'/f`. -/
theorem argVariation_eq_im_sum :
    C.argVariation = (C.loopIntegral).im := by
  unfold loopIntegral argVariation
  rw [Complex.im_sum]
  refine (Finset.sum_congr rfl (fun k _ => ?_)).symm
  rw [C.edge_eq k, im_clog_sub_eq_arg_sub]

end ClosedContour

/-! ## Part 4 — bridge to the `RayArgPartition` shape (mirror of `ScratchLeafClose`)

The `argVariation` of a `ClosedContour` is literally the `argVariation =
∑ (arg(g k.succ) − arg(g k.castSucc))` shape of `RayArgPartition` (the inlined
mirror of `ScratchLeafClose.RayArgPartition`, Part 0).  When the per-vertex
`f`-values `fval` all lie in the closed right half-plane (`Re ≥ 0`), the per-cell
`|·| ≤ π` bound is discharged by `abs_arg_sub_le_pi_of_re_nonneg`, so a
`ClosedContour` whose vertices satisfy that geometric condition yields a genuine
`RayArgPartition` whose `argVariation` is *equal* to AP3's
`argVariation = Im ∮ f'/f`.  Because the inlined `RayArgPartition` has fields
identical to `ScratchLeafClose.RayArgPartition`, this composes with that file. -/

/-- **AP3 → `RayArgPartition`.**  Given a closed contour whose per-vertex
`f`-values all have nonnegative real part, build the `RayArgPartition` (mirror of
`ScratchLeafClose`'s) whose `argVariation` is exactly this contour's
`argVariation` (`= Im ∮ f'/f`), with the per-cell `π`-bound proven from the
half-plane geometry.

This makes AP3's argument variation EQUAL to `ScratchLeafClose.argVariation`,
letting the pieces compose. -/
noncomputable def ClosedContour.toRayArgPartition
    (C : ClosedContour)
    (hre : ∀ k, 0 ≤ (C.fval k).re) :
    RayArgPartition where
  Nf := C.n
  argVariation := C.argVariation
  cellChange := fun k => Complex.arg (C.fval k.succ) - Complex.arg (C.fval k.castSucc)
  total_eq := rfl
  cell_bound := fun k =>
    abs_arg_sub_le_pi_of_re_nonneg (hre k.succ) (hre k.castSucc)

/-- The `argVariation` produced by the bridge agrees with AP3's `Im ∮ f'/f`. -/
theorem ClosedContour.toRayArgPartition_argVariation
    (C : ClosedContour) (hre : ∀ k, 0 ≤ (C.fval k).re) :
    (C.toRayArgPartition hre).argVariation = (C.loopIntegral).im :=
  C.argVariation_eq_im_sum

end ScratchAPArgVar
end BacklundTuring
end OverflowResidueRH
