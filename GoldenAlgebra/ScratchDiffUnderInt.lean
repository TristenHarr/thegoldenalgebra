import Mathlib
import rh
import ScratchEnergyKernel
import ScratchKernelForm

/-!
# `DiffUnderDoubleIntegral` — differentiation under the double integral on `[0,A]²`

This scratch file discharges the **single remaining residual** of the
`KernelForm` route from `ScratchKernelForm.lean`: the differentiation-under-the-
integral interchange

```
∂_y ∫₀^A ∫₀^A Φ(u)Φ(v)·cosKer u v (verticalLine x y) du dv
  = ∫₀^A ∫₀^A Φ(u)Φ(v)·(∂_y cosKer u v (verticalLine x y)) du dv
```

for continuous `Φ` and finite `A ≥ 0`.  This is standard differentiation under
the integral sign on the **compact** square `[0,A]²`.

## Strategy

We use the interval-integral version of Mathlib's parametric differentiation
lemma, `intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le`,
applied **twice** (nested): once for the inner `∫_v` (for each fixed `u`) and
once for the outer `∫_u`.

The closed form of the integrand in `yy` (from `cosKer_closedForm`) is
```
cosKer u v (verticalLine x yy)
  = cos(xu)cos(xv)·cosh(u·yy)cosh(v·yy) + sin(xu)sin(xv)·sinh(u·yy)sinh(v·yy),
```
a smooth function of `yy` whose `yy`-derivative is explicit:
```
Dy u v x yy
  = cos(xu)cos(xv)·(u·sinh(u·yy)cosh(v·yy) + cosh(u·yy)·v·sinh(v·yy))
  + sin(xu)sin(xv)·(u·cosh(u·yy)sinh(v·yy) + sinh(u·yy)·v·cosh(v·yy)).
```
On the compact box `u,v ∈ [0,A]` and `yy` in the neighborhood `Icc (y-1) (y+1)`,
every factor is bounded, so the integrand derivative is dominated by a constant
(times `|Φ(u)|·|Φ(v)|`), and the domination hypotheses are met with an
**interval-integrable (indeed continuous) constant bound**.

## Result

`diffUnderDoubleIntegral` proves `DiffUnderDoubleIntegral Phi A x y` for any
continuous `Φ` and `0 ≤ A`.  This closes the `KernelForm` residual entirely.

#print axioms: only `propext`, `Classical.choice`, `Quot.sound` (no `sorryAx`).
-/

namespace OverflowResidueRH
namespace BacklundTuring
namespace ScratchDiffUnderInt

open Complex MeasureTheory Filter Set
open scoped Topology

open OverflowResidueRH.XiDoubleKernel
open OverflowResidueRH.BacklundTuring.ScratchEnergyKernel
open OverflowResidueRH.BacklundTuring.ScratchKernelForm

set_option maxHeartbeats 1000000

/-! ## §1. The closed form of the integrand in `yy`, and its `yy`-derivative -/

/-- The integrand `cosKer u v (verticalLine x ·)` as an explicit function of `yy`,
in its `cos`/`sin`/`cosh`/`sinh` closed form. -/
noncomputable def cosKerForm (u v x yy : ℝ) : ℝ :=
    Real.cos (x*u) * Real.cosh (yy*u) * (Real.cos (x*v) * Real.cosh (yy*v))
  + Real.sin (x*u) * Real.sinh (yy*u) * (Real.sin (x*v) * Real.sinh (yy*v))

theorem cosKer_verticalLine_eq (u v x yy : ℝ) :
    cosKer u v (verticalLine x yy) = cosKerForm u v x yy :=
  cosKer_closedForm u v x yy

/-- The explicit `yy`-derivative of `cosKerForm u v x ·`. -/
noncomputable def Dy (u v x yy : ℝ) : ℝ :=
    Real.cos (x*u) * (u * Real.sinh (yy*u)) * (Real.cos (x*v) * Real.cosh (yy*v))
  + Real.cos (x*u) * Real.cosh (yy*u) * (Real.cos (x*v) * (v * Real.sinh (yy*v)))
  + (Real.sin (x*u) * (u * Real.cosh (yy*u)) * (Real.sin (x*v) * Real.sinh (yy*v))
     + Real.sin (x*u) * Real.sinh (yy*u) * (Real.sin (x*v) * (v * Real.cosh (yy*v))))

/-- `cosh (yy * u)` has `yy`-derivative `u * sinh (yy * u)`. -/
theorem hasDerivAt_cosh_lin (c : ℝ) (yy : ℝ) :
    HasDerivAt (fun ww : ℝ => Real.cosh (ww * c)) (c * Real.sinh (yy * c)) yy := by
  have h1 : HasDerivAt (fun ww : ℝ => ww * c) c yy := by
    simpa using (hasDerivAt_id yy).mul_const c
  have h2 := (Real.hasDerivAt_cosh (yy * c)).comp yy h1
  -- h2 : HasDerivAt (Real.cosh ∘ fun ww => ww * c) (Real.sinh (yy*c) * c) yy
  have h3 : HasDerivAt (fun ww : ℝ => Real.cosh (ww * c)) (Real.sinh (yy * c) * c) yy := h2
  rw [mul_comm]; exact h3

/-- `sinh (yy * u)` has `yy`-derivative `u * cosh (yy * u)`. -/
theorem hasDerivAt_sinh_lin (c : ℝ) (yy : ℝ) :
    HasDerivAt (fun ww : ℝ => Real.sinh (ww * c)) (c * Real.cosh (yy * c)) yy := by
  have h1 : HasDerivAt (fun ww : ℝ => ww * c) c yy := by
    simpa using (hasDerivAt_id yy).mul_const c
  have h2 := (Real.hasDerivAt_sinh (yy * c)).comp yy h1
  have h3 : HasDerivAt (fun ww : ℝ => Real.sinh (ww * c)) (Real.cosh (yy * c) * c) yy := h2
  rw [mul_comm]; exact h3

/-- The closed-form integrand has `yy`-derivative `Dy u v x yy`. -/
theorem hasDerivAt_cosKerForm (u v x yy : ℝ) :
    HasDerivAt (fun ww : ℝ => cosKerForm u v x ww) (Dy u v x yy) yy := by
  -- Build the derivative termwise from the cosh/sinh linear chain rules.
  -- Term 1: cos(xu)·cosh(u·yy) · (cos(xv)·cosh(v·yy))
  have hc_u : HasDerivAt (fun ww : ℝ => Real.cosh (ww * u))
      (u * Real.sinh (yy * u)) yy := hasDerivAt_cosh_lin u yy
  have hc_v : HasDerivAt (fun ww : ℝ => Real.cosh (ww * v))
      (v * Real.sinh (yy * v)) yy := hasDerivAt_cosh_lin v yy
  have hs_u : HasDerivAt (fun ww : ℝ => Real.sinh (ww * u))
      (u * Real.cosh (yy * u)) yy := hasDerivAt_sinh_lin u yy
  have hs_v : HasDerivAt (fun ww : ℝ => Real.sinh (ww * v))
      (v * Real.cosh (yy * v)) yy := hasDerivAt_sinh_lin v yy
  -- factor A := cos(xu)·cosh(u·yy)
  have hA : HasDerivAt (fun ww : ℝ => Real.cos (x*u) * Real.cosh (ww * u))
      (Real.cos (x*u) * (u * Real.sinh (yy * u))) yy := hc_u.const_mul _
  have hB : HasDerivAt (fun ww : ℝ => Real.cos (x*v) * Real.cosh (ww * v))
      (Real.cos (x*v) * (v * Real.sinh (yy * v))) yy := hc_v.const_mul _
  have hC : HasDerivAt (fun ww : ℝ => Real.sin (x*u) * Real.sinh (ww * u))
      (Real.sin (x*u) * (u * Real.cosh (yy * u))) yy := hs_u.const_mul _
  have hD : HasDerivAt (fun ww : ℝ => Real.sin (x*v) * Real.sinh (ww * v))
      (Real.sin (x*v) * (v * Real.cosh (yy * v))) yy := hs_v.const_mul _
  -- term1 = A·B, term2 = C·D
  have ht1 := hA.mul hB
  have ht2 := hC.mul hD
  have hsum := ht1.add ht2
  -- Reconcile the function (definitionally `cosKerForm`) and the derivative value.
  have hfun : (fun ww : ℝ => cosKerForm u v x ww)
      = (fun ww : ℝ =>
          (Real.cos (x*u) * Real.cosh (ww * u)) * (Real.cos (x*v) * Real.cosh (ww * v))
          + (Real.sin (x*u) * Real.sinh (ww * u)) * (Real.sin (x*v) * Real.sinh (ww * v))) := by
    funext ww; simp only [cosKerForm]
  rw [hfun]
  have hval : Dy u v x yy
      = (Real.cos (x*u) * (u * Real.sinh (yy * u))) * (Real.cos (x*v) * Real.cosh (yy * v))
        + (Real.cos (x*u) * Real.cosh (yy * u)) * (Real.cos (x*v) * (v * Real.sinh (yy * v)))
        + ((Real.sin (x*u) * (u * Real.cosh (yy * u))) * (Real.sin (x*v) * Real.sinh (yy * v))
           + (Real.sin (x*u) * Real.sinh (yy * u)) * (Real.sin (x*v) * (v * Real.cosh (yy * v)))) := by
    simp only [Dy]
  rw [hval]
  exact hsum

/-- `deriv` corollary: the `yy`-derivative of `cosKer u v (verticalLine x ·)` is `Dy`. -/
theorem deriv_cosKer_verticalLine (u v x yy : ℝ) :
    deriv (fun ww : ℝ => cosKer u v (verticalLine x ww)) yy = Dy u v x yy := by
  have hfun : (fun ww : ℝ => cosKer u v (verticalLine x ww))
      = (fun ww : ℝ => cosKerForm u v x ww) := by
    funext ww; exact cosKer_verticalLine_eq u v x ww
  rw [hfun]
  exact (hasDerivAt_cosKerForm u v x yy).deriv

/-! ## §2. Uniform bounds for domination -/

/-- `|Real.sinh t| ≤ Real.cosh t`. -/
theorem abs_sinh_le_cosh (t : ℝ) : |Real.sinh t| ≤ Real.cosh t := by
  rw [abs_le]
  constructor
  · -- -cosh t ≤ sinh t  ↔  0 ≤ cosh t + sinh t = exp t
    have : Real.cosh t + Real.sinh t = Real.exp t := Real.cosh_add_sinh t
    nlinarith [Real.exp_pos t, this]
  · -- sinh t ≤ cosh t  ↔  0 ≤ cosh t - sinh t = exp (-t)
    have : Real.cosh t - Real.sinh t = Real.exp (-t) := Real.cosh_sub_sinh t
    nlinarith [Real.exp_pos (-t), this]

/-- On the box `|c| ≤ A`, `yy ∈ [y-1, y+1]`, both `|cosh(yy·c)|` and `|sinh(yy·c)|`
are bounded by `Ch x y A := cosh ((|y|+1)·A)` (assuming `0 ≤ A`). -/
noncomputable def Ch (y A : ℝ) : ℝ := Real.cosh ((|y| + 1) * A)

theorem cosh_lin_le {c yy y A : ℝ} (hA : 0 ≤ A) (hc : |c| ≤ A)
    (hyy : yy ∈ Set.Icc (y - 1) (y + 1)) :
    Real.cosh (yy * c) ≤ Ch y A := by
  rw [Ch]
  rw [Real.cosh_le_cosh]
  -- |yy * c| ≤ (|y|+1) * A
  rw [abs_mul]
  have hyy' : |yy| ≤ |y| + 1 := by
    obtain ⟨h1, h2⟩ := hyy
    rw [abs_le]; constructor <;>
      [nlinarith [abs_nonneg y, le_abs_self y, neg_abs_le y];
       nlinarith [abs_nonneg y, le_abs_self y, neg_abs_le y]]
  have hcA : |c| ≤ A := hc
  have hAabs : |(|y| + 1) * A| = (|y| + 1) * A := by
    rw [abs_of_nonneg]; positivity
  rw [hAabs]
  calc |yy| * |c| ≤ (|y| + 1) * A :=
        mul_le_mul hyy' hcA (abs_nonneg c) (by positivity)

theorem abs_sinh_lin_le {c yy y A : ℝ} (hA : 0 ≤ A) (hc : |c| ≤ A)
    (hyy : yy ∈ Set.Icc (y - 1) (y + 1)) :
    |Real.sinh (yy * c)| ≤ Ch y A :=
  le_trans (abs_sinh_le_cosh (yy * c)) (cosh_lin_le hA hc hyy)

theorem abs_cosh_lin_le {c yy y A : ℝ} (hA : 0 ≤ A) (hc : |c| ≤ A)
    (hyy : yy ∈ Set.Icc (y - 1) (y + 1)) :
    |Real.cosh (yy * c)| ≤ Ch y A := by
  rw [abs_of_nonneg (le_of_lt (Real.cosh_pos _))]
  exact cosh_lin_le hA hc hyy

theorem Ch_nonneg (y A : ℝ) : 0 ≤ Ch y A := le_of_lt (Real.cosh_pos _)

/-- **Uniform bound on `Dy`.** For `|u| ≤ A`, `|v| ≤ A`, `yy ∈ [y-1,y+1]`, `0 ≤ A`,
`|Dy u v x yy| ≤ 4 · A · (Ch y A)²`. -/
theorem abs_Dy_le {u v x yy y A : ℝ} (hA : 0 ≤ A)
    (hu : |u| ≤ A) (hv : |v| ≤ A)
    (hyy : yy ∈ Set.Icc (y - 1) (y + 1)) :
    |Dy u v x yy| ≤ 4 * A * (Ch y A) ^ 2 := by
  have hC := Ch_nonneg y A
  -- bounds on each factor
  have hcu : Real.cosh (yy * u) ≤ Ch y A := cosh_lin_le hA hu hyy
  have hcv : Real.cosh (yy * v) ≤ Ch y A := cosh_lin_le hA hv hyy
  have hsu : |Real.sinh (yy * u)| ≤ Ch y A := abs_sinh_lin_le hA hu hyy
  have hsv : |Real.sinh (yy * v)| ≤ Ch y A := abs_sinh_lin_le hA hv hyy
  have hcua : |Real.cosh (yy * u)| ≤ Ch y A := abs_cosh_lin_le hA hu hyy
  have hcva : |Real.cosh (yy * v)| ≤ Ch y A := abs_cosh_lin_le hA hv hyy
  have hcos_xu : |Real.cos (x*u)| ≤ 1 := Real.abs_cos_le_one _
  have hcos_xv : |Real.cos (x*v)| ≤ 1 := Real.abs_cos_le_one _
  have hsin_xu : |Real.sin (x*u)| ≤ 1 := Real.abs_sin_le_one _
  have hsin_xv : |Real.sin (x*v)| ≤ 1 := Real.abs_sin_le_one _
  have huA : |u| ≤ A := hu
  have hvA : |v| ≤ A := hv
  set Chb := Ch y A with hChb
  -- A generic 4-factor bound: |s · (m · h) · (s' · h')| ≤ A · Chb² where
  --   |s|,|s'| ≤ 1, |m| ≤ A, |h|,|h'| ≤ Chb.
  -- We bound via `abs_mul` then `mul_le_mul` chains.
  have key : ∀ s m h s' h' : ℝ, |s| ≤ 1 → |m| ≤ A → |h| ≤ Chb → |s'| ≤ 1 → |h'| ≤ Chb →
      |s * (m * h) * (s' * h')| ≤ A * Chb ^ 2 := by
    intro s m h s' h' hs hm hh hs' hh'
    have h1 : |s| * (|m| * |h|) * (|s'| * |h'|) ≤ 1 * (A * Chb) * (1 * Chb) := by
      have e2 : |m| * |h| ≤ A * Chb :=
        mul_le_mul hm hh (abs_nonneg h) (le_trans (abs_nonneg m) hm)
      have e4 : |s'| * |h'| ≤ 1 * Chb :=
        mul_le_mul hs' hh' (abs_nonneg h') zero_le_one
      have e1 : |s| * (|m| * |h|) ≤ 1 * (A * Chb) :=
        mul_le_mul hs e2 (mul_nonneg (abs_nonneg m) (abs_nonneg h)) zero_le_one
      exact mul_le_mul e1 e4
        (mul_nonneg (abs_nonneg s') (abs_nonneg h'))
        (by positivity)
    calc |s * (m * h) * (s' * h')|
        = |s| * (|m| * |h|) * (|s'| * |h'|) := by
          rw [abs_mul, abs_mul, abs_mul, abs_mul]
      _ ≤ 1 * (A * Chb) * (1 * Chb) := h1
      _ = A * Chb ^ 2 := by ring
  have hT1 : |Real.cos (x*u) * (u * Real.sinh (yy*u)) * (Real.cos (x*v) * Real.cosh (yy*v))|
      ≤ A * Chb^2 := key _ _ _ _ _ hcos_xu huA hsu hcos_xv hcva
  have hT2 : |Real.cos (x*v) * (v * Real.sinh (yy*v)) * (Real.cos (x*u) * Real.cosh (yy*u))|
      ≤ A * Chb^2 := key _ _ _ _ _ hcos_xv hvA hsv hcos_xu hcua
  have hT3 : |Real.sin (x*u) * (u * Real.cosh (yy*u)) * (Real.sin (x*v) * Real.sinh (yy*v))|
      ≤ A * Chb^2 := key _ _ _ _ _ hsin_xu huA hcua hsin_xv hsv
  have hT4 : |Real.sin (x*v) * (v * Real.cosh (yy*v)) * (Real.sin (x*u) * Real.sinh (yy*u))|
      ≤ A * Chb^2 := key _ _ _ _ _ hsin_xv hvA hcva hsin_xu hsu
  -- Reorder T2,T4 to match the literal Dy summands.
  rw [show Real.cos (x*v) * (v * Real.sinh (yy*v)) * (Real.cos (x*u) * Real.cosh (yy*u))
        = Real.cos (x*u) * Real.cosh (yy*u) * (Real.cos (x*v) * (v * Real.sinh (yy*v))) by ring] at hT2
  rw [show Real.sin (x*v) * (v * Real.cosh (yy*v)) * (Real.sin (x*u) * Real.sinh (yy*u))
        = Real.sin (x*u) * Real.sinh (yy*u) * (Real.sin (x*v) * (v * Real.cosh (yy*v))) by ring] at hT4
  -- Combine: Dy = T1 + T2 + (T3 + T4), triangle inequality
  unfold Dy
  calc |Real.cos (x*u) * (u * Real.sinh (yy*u)) * (Real.cos (x*v) * Real.cosh (yy*v))
        + Real.cos (x*u) * Real.cosh (yy*u) * (Real.cos (x*v) * (v * Real.sinh (yy*v)))
        + (Real.sin (x*u) * (u * Real.cosh (yy*u)) * (Real.sin (x*v) * Real.sinh (yy*v))
           + Real.sin (x*u) * Real.sinh (yy*u) * (Real.sin (x*v) * (v * Real.cosh (yy*v))))|
      ≤ |Real.cos (x*u) * (u * Real.sinh (yy*u)) * (Real.cos (x*v) * Real.cosh (yy*v))|
        + |Real.cos (x*u) * Real.cosh (yy*u) * (Real.cos (x*v) * (v * Real.sinh (yy*v)))|
        + (|Real.sin (x*u) * (u * Real.cosh (yy*u)) * (Real.sin (x*v) * Real.sinh (yy*v))|
           + |Real.sin (x*u) * Real.sinh (yy*u) * (Real.sin (x*v) * (v * Real.cosh (yy*v)))|) := by
        refine le_trans (abs_add_le _ _) ?_
        gcongr <;> exact abs_add_le _ _
    _ ≤ A * Chb^2 + A * Chb^2 + (A * Chb^2 + A * Chb^2) := by
        gcongr
    _ = 4 * A * Chb^2 := by ring

/-! ## §3. Continuity of the integrands -/

/-- For fixed `u, x, yy`, `v ↦ Dy u v x yy` is continuous. -/
theorem continuous_Dy_in_v (u x yy : ℝ) :
    Continuous (fun v : ℝ => Dy u v x yy) := by
  unfold Dy; fun_prop

/-- For fixed `u, x, yy`, `v ↦ cosKerForm u v x yy` is continuous. -/
theorem continuous_cosKerForm_in_v (u x yy : ℝ) :
    Continuous (fun v : ℝ => cosKerForm u v x yy) := by
  unfold cosKerForm; fun_prop

/-- For fixed `u, yy`, the inner integrand `v ↦ Φu·Φv·cosKer u v (vL x yy)` is continuous. -/
theorem continuous_inner_value {Phi : ℝ → ℝ} (hPhi : Continuous Phi)
    (x u yy : ℝ) :
    Continuous (fun v : ℝ => Phi u * Phi v * cosKer u v (verticalLine x yy)) := by
  have hcc : Continuous (fun v : ℝ => Phi u * Phi v * cosKerForm u v x yy) :=
    (continuous_const.mul hPhi).mul (continuous_cosKerForm_in_v u x yy)
  simpa only [cosKer_verticalLine_eq] using hcc

/-- For fixed `u, yy`, the inner derivative integrand `v ↦ Φu·Φv·Dy u v x yy` is continuous. -/
theorem continuous_inner_deriv {Phi : ℝ → ℝ} (hPhi : Continuous Phi)
    (x u yy : ℝ) :
    Continuous (fun v : ℝ => Phi u * Phi v * Dy u v x yy) :=
  (continuous_const.mul hPhi).mul (continuous_Dy_in_v u x yy)

/-- The `yy`-derivative of the scaled integrand `Φu·Φv·cosKer u v (vL x ·)`. -/
theorem hasDerivAt_scaled (Phi : ℝ → ℝ) (x u v yy : ℝ) :
    HasDerivAt (fun ww : ℝ => Phi u * Phi v * cosKer u v (verticalLine x ww))
      (Phi u * Phi v * Dy u v x yy) yy := by
  have hfun : (fun ww : ℝ => cosKer u v (verticalLine x ww))
      = (fun ww : ℝ => cosKerForm u v x ww) := by
    funext ww; exact cosKer_verticalLine_eq u v x ww
  have hbase : HasDerivAt (fun ww : ℝ => cosKer u v (verticalLine x ww)) (Dy u v x yy) yy := by
    rw [hfun]; exact hasDerivAt_cosKerForm u v x yy
  simpa using hbase.const_mul (Phi u * Phi v)

/-! ## §4. Inner-integral differentiation under the integral sign -/

/-- **Inner interval-integral derivative.**  For continuous `Φ`, `0 ≤ A`, fixed
`u` with `|u| ≤ A`, the `yy`-derivative of `yy ↦ ∫₀^A Φu·Φv·cosKer u v (vL x yy) dv`
equals `∫₀^A Φu·Φv·Dy u v x y dv`, by `intervalIntegral`'s parametric
differentiation lemma with the constant-times-`|Φ|` dominating bound. -/
theorem hasDerivAt_inner {Phi : ℝ → ℝ} (hPhi : Continuous Phi)
    {A : ℝ} (hA : 0 ≤ A) (x y : ℝ) {u : ℝ} (hu : |u| ≤ A) :
    HasDerivAt
      (fun yy : ℝ => ∫ v in (0:ℝ)..A, Phi u * Phi v * cosKer u v (verticalLine x yy))
      (∫ v in (0:ℝ)..A, Phi u * Phi v * Dy u v x y) y := by
  set s : Set ℝ := Set.Icc (y - 1) (y + 1) with hs_def
  -- The bound function of `v`.
  set C : ℝ := 4 * A * (Ch y A) ^ 2 with hC_def
  set bound : ℝ → ℝ := fun v => |Phi u| * |Phi v| * C with hbound_def
  have hs : s ∈ 𝓝 y := by
    rw [hs_def]; exact Icc_mem_nhds (by linarith) (by linarith)
  -- measurability of F yy (continuous in v) eventually
  have hF_meas : ∀ᶠ yy in 𝓝 y,
      AEStronglyMeasurable
        (fun v => Phi u * Phi v * cosKer u v (verticalLine x yy))
        (volume.restrict (Set.uIoc (0:ℝ) A)) :=
    Filter.Eventually.of_forall fun yy =>
      (continuous_inner_value hPhi x u yy).aestronglyMeasurable.restrict
  -- F y integrable
  have hF_int : IntervalIntegrable
      (fun v => Phi u * Phi v * cosKer u v (verticalLine x y)) volume 0 A :=
    (continuous_inner_value hPhi x u y).intervalIntegrable 0 A
  -- F' y measurable
  have hF'_meas : AEStronglyMeasurable
      (fun v => Phi u * Phi v * Dy u v x y)
      (volume.restrict (Set.uIoc (0:ℝ) A)) :=
    (continuous_inner_deriv hPhi x u y).aestronglyMeasurable.restrict
  -- bound integrable (continuous in v)
  have hbound_int : IntervalIntegrable bound volume 0 A := by
    have : Continuous bound := by
      rw [hbound_def]; fun_prop
    exact this.intervalIntegrable 0 A
  -- the domination bound
  have h_bound : ∀ᵐ v ∂volume, v ∈ Set.uIoc (0:ℝ) A →
      ∀ yy ∈ s, ‖Phi u * Phi v * Dy u v x yy‖ ≤ bound v := by
    refine Filter.Eventually.of_forall ?_
    intro v hv yy hyy
    rw [Set.uIoc_of_le hA] at hv
    have hvA : |v| ≤ A := by
      rw [abs_of_pos hv.1]; exact hv.2
    rw [Real.norm_eq_abs, hbound_def]
    simp only
    rw [abs_mul, abs_mul]
    -- |Φu|·|Φv|·|Dy| ≤ |Φu|·|Φv|·C
    have hDy : |Dy u v x yy| ≤ C := abs_Dy_le hA hu hvA hyy
    gcongr
  -- differentiability at each yy ∈ s
  have h_diff : ∀ᵐ v ∂volume, v ∈ Set.uIoc (0:ℝ) A →
      ∀ yy ∈ s, HasDerivAt
        (fun ww => Phi u * Phi v * cosKer u v (verticalLine x ww))
        (Phi u * Phi v * Dy u v x yy) yy := by
    refine Filter.Eventually.of_forall ?_
    intro v _ yy _
    exact hasDerivAt_scaled Phi x u v yy
  exact (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    hs hF_meas hF_int hF'_meas h_bound hbound_int h_diff).2

/-! ## §5. Joint `(u,v)`-continuity for the outer integral -/

/-- Joint continuity in `(u, v)` of the value integrand. -/
theorem continuous_value_uv {Phi : ℝ → ℝ} (hPhi : Continuous Phi) (x yy : ℝ) :
    Continuous (fun p : ℝ × ℝ => Phi p.1 * Phi p.2 * cosKer p.1 p.2 (verticalLine x yy)) := by
  have hck : Continuous (fun p : ℝ × ℝ => cosKerForm p.1 p.2 x yy) := by
    unfold cosKerForm; fun_prop
  have : Continuous (fun p : ℝ × ℝ => Phi p.1 * Phi p.2 * cosKerForm p.1 p.2 x yy) := by
    fun_prop
  simpa only [cosKer_verticalLine_eq] using this

/-- Joint continuity in `(u, v)` of the derivative integrand. -/
theorem continuous_deriv_uv {Phi : ℝ → ℝ} (hPhi : Continuous Phi) (x yy : ℝ) :
    Continuous (fun p : ℝ × ℝ => Phi p.1 * Phi p.2 * Dy p.1 p.2 x yy) := by
  have hd : Continuous (fun p : ℝ × ℝ => Dy p.1 p.2 x yy) := by
    unfold Dy; fun_prop
  fun_prop

/-- `u ↦ ∫ v in 0..A, Φu·Φv·cosKer u v (vL x yy) dv` is continuous. -/
theorem continuous_outer_value {Phi : ℝ → ℝ} (hPhi : Continuous Phi) (x yy A : ℝ) :
    Continuous (fun u : ℝ => ∫ v in (0:ℝ)..A, Phi u * Phi v * cosKer u v (verticalLine x yy)) :=
  intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (continuous_value_uv hPhi x yy) 0 A

/-- `u ↦ ∫ v in 0..A, Φu·Φv·Dy u v x yy dv` is continuous. -/
theorem continuous_outer_deriv {Phi : ℝ → ℝ} (hPhi : Continuous Phi) (x yy A : ℝ) :
    Continuous (fun u : ℝ => ∫ v in (0:ℝ)..A, Phi u * Phi v * Dy u v x yy) :=
  intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (continuous_deriv_uv hPhi x yy) 0 A

/-! ## §6. Outer-integral differentiation and the final result -/

/-- **Outer interval-integral derivative.**  For continuous `Φ`, `0 ≤ A`, the
`yy`-derivative of `yy ↦ ∫₀^A ∫₀^A Φu·Φv·cosKer u v (vL x yy) dv du` equals
`∫₀^A ∫₀^A Φu·Φv·Dy u v x y dv du`.  Second application of `intervalIntegral`'s
parametric differentiation lemma, the bound `bound u := |Φu|·(C·∫₀^A|Φv|dv)`. -/
theorem hasDerivAt_outer {Phi : ℝ → ℝ} (hPhi : Continuous Phi)
    {A : ℝ} (hA : 0 ≤ A) (x y : ℝ) :
    HasDerivAt
      (fun yy : ℝ => ∫ u in (0:ℝ)..A, ∫ v in (0:ℝ)..A,
        Phi u * Phi v * cosKer u v (verticalLine x yy))
      (∫ u in (0:ℝ)..A, ∫ v in (0:ℝ)..A, Phi u * Phi v * Dy u v x y) y := by
  set s : Set ℝ := Set.Icc (y - 1) (y + 1) with hs_def
  set C : ℝ := 4 * A * (Ch y A) ^ 2 with hC_def
  set I0 : ℝ := ∫ v in (0:ℝ)..A, |Phi v| with hI0_def
  set bound : ℝ → ℝ := fun u => |Phi u| * (C * I0) with hbound_def
  have hCnn : 0 ≤ C := by rw [hC_def]; positivity
  have hI0nn : 0 ≤ I0 := by
    rw [hI0_def]
    apply intervalIntegral.integral_nonneg hA
    intro v _; exact abs_nonneg _
  have hs : s ∈ 𝓝 y := by
    rw [hs_def]; exact Icc_mem_nhds (by linarith) (by linarith)
  -- measurability of the F yy (outer integrand) eventually
  have hF_meas : ∀ᶠ yy in 𝓝 y,
      AEStronglyMeasurable
        (fun u => ∫ v in (0:ℝ)..A, Phi u * Phi v * cosKer u v (verticalLine x yy))
        (volume.restrict (Set.uIoc (0:ℝ) A)) :=
    Filter.Eventually.of_forall fun yy =>
      (continuous_outer_value hPhi x yy A).aestronglyMeasurable.restrict
  have hF_int : IntervalIntegrable
      (fun u => ∫ v in (0:ℝ)..A, Phi u * Phi v * cosKer u v (verticalLine x y)) volume 0 A :=
    (continuous_outer_value hPhi x y A).intervalIntegrable 0 A
  have hF'_meas : AEStronglyMeasurable
      (fun u => ∫ v in (0:ℝ)..A, Phi u * Phi v * Dy u v x y)
      (volume.restrict (Set.uIoc (0:ℝ) A)) :=
    (continuous_outer_deriv hPhi x y A).aestronglyMeasurable.restrict
  have hbound_int : IntervalIntegrable bound volume 0 A := by
    have : Continuous bound := by rw [hbound_def]; fun_prop
    exact this.intervalIntegrable 0 A
  -- the domination bound, using the inner norm-le-integral estimate
  have h_bound : ∀ᵐ u ∂volume, u ∈ Set.uIoc (0:ℝ) A →
      ∀ yy ∈ s,
        ‖∫ v in (0:ℝ)..A, Phi u * Phi v * Dy u v x yy‖ ≤ bound u := by
    refine Filter.Eventually.of_forall ?_
    intro u hu yy hyy
    rw [Set.uIoc_of_le hA] at hu
    have huA : |u| ≤ A := by rw [abs_of_pos hu.1]; exact hu.2
    -- pointwise: ‖Φu·Φv·Dy‖ ≤ |Φu|·|Φv|·C =: gv
    have hptwise : ∀ᵐ v ∂volume, v ∈ Set.Ioc (0:ℝ) A →
        ‖Phi u * Phi v * Dy u v x yy‖ ≤ |Phi u| * |Phi v| * C := by
      refine Filter.Eventually.of_forall ?_
      intro v hv
      have hvA : |v| ≤ A := by rw [abs_of_pos hv.1]; exact hv.2
      rw [Real.norm_eq_abs, abs_mul, abs_mul]
      have hDy : |Dy u v x yy| ≤ C := abs_Dy_le hA huA hvA hyy
      gcongr
    -- g is interval integrable
    have hg_int : IntervalIntegrable (fun v => |Phi u| * |Phi v| * C) volume 0 A := by
      have : Continuous (fun v => |Phi u| * |Phi v| * C) := by fun_prop
      exact this.intervalIntegrable 0 A
    have hnorm := intervalIntegral.norm_integral_le_of_norm_le hA hptwise hg_int
    -- ∫ |Φu|·|Φv|·C dv = |Φu|·(C·I0)
    have heval : (∫ v in (0:ℝ)..A, |Phi u| * |Phi v| * C) = bound u := by
      rw [hbound_def]
      simp only
      rw [show (fun v => |Phi u| * |Phi v| * C) = (fun v => (|Phi u| * C) * |Phi v|) by
        funext v; ring]
      rw [intervalIntegral.integral_const_mul]
      rw [hI0_def]; ring
    rw [heval] at hnorm
    exact hnorm
  -- differentiability of the inner integral in yy, at each u ∈ Ι 0 A
  have h_diff : ∀ᵐ u ∂volume, u ∈ Set.uIoc (0:ℝ) A →
      ∀ yy ∈ s, HasDerivAt
        (fun ww => ∫ v in (0:ℝ)..A, Phi u * Phi v * cosKer u v (verticalLine x ww))
        (∫ v in (0:ℝ)..A, Phi u * Phi v * Dy u v x yy) yy := by
    refine Filter.Eventually.of_forall ?_
    intro u hu yy _
    rw [Set.uIoc_of_le hA] at hu
    have huA : |u| ≤ A := by rw [abs_of_pos hu.1]; exact hu.2
    exact hasDerivAt_inner hPhi hA x yy huA
  exact (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    hs hF_meas hF_int hF'_meas h_bound hbound_int h_diff).2

/-! ## §7. `DiffUnderDoubleIntegral` -/

/-- **PROVED — `DiffUnderDoubleIntegral` for continuous `Φ` and `0 ≤ A`.**
The differentiation-under-the-double-integral interchange on the compact square
`[0,A]²`, the last residual of the `KernelForm` route.  The outer interval
integral's `yy`-derivative is computed by `hasDerivAt_outer`, and
`deriv (fun ww => cosKer u v (verticalLine x ww)) y = Dy u v x y`. -/
theorem diffUnderDoubleIntegral {Phi : ℝ → ℝ} (hPhi : Continuous Phi)
    {A : ℝ} (hA : 0 ≤ A) (x y : ℝ) :
    DiffUnderDoubleIntegral Phi A x y := by
  unfold DiffUnderDoubleIntegral
  rw [(hasDerivAt_outer hPhi hA x y).deriv]
  -- replace `deriv (cosKer …) y` by `Dy …`
  refine intervalIntegral.integral_congr ?_
  intro u _
  refine intervalIntegral.integral_congr ?_
  intro v _
  simp only [deriv_cosKer_verticalLine]

/-- **PROVED — `KernelForm` for continuous `Φ` and `0 ≤ A`, unconditionally.**
The `KernelForm` residual of `ScratchKernelForm` is now fully discharged: its
last analytic input `DiffUnderDoubleIntegral` is proven (`diffUnderDoubleIntegral`),
so `KernelForm Phi A x y` holds for any continuous `Φ` and `0 ≤ A` with no
remaining hypothesis. -/
theorem kernelForm_of_continuous' {Phi : ℝ → ℝ} (hPhi : Continuous Phi)
    {A : ℝ} (hA : 0 ≤ A) (x y : ℝ) :
    KernelForm Phi A x y :=
  kernelForm_of_continuous hPhi hA x y (diffUnderDoubleIntegral hPhi hA x y)
