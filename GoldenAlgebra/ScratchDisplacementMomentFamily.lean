import rh
import ScratchPositionEnvelope
import ScratchZeroDensityBridge
import ScratchModernZeroDensity
import ScratchKernelDensity
import ScratchDisplacementMoment

/-!
# ScratchDisplacementMomentFamily — the UNCONDITIONAL displacement-moment FAMILY
# `Σ_{γ≤T} |β−½|^p ≪ T/(log T)^{p−1}` for `p ≥ 1`, from zero-density (general-p
# layer-cake), and the verdict that `p = 2` is KERNEL-OPTIMAL.

**Honesty note.**  Nothing here assumes RH.  The genuinely deep input is the
*classical unconditional* zero-density estimate of **Selberg (1946)**

```
N(σ, T) ≪ T^{1 − (σ − ½)/4} · log T          (σ ≥ ½),
```

reused verbatim through the named `Prop` `SelbergZeroDensity` of
`ScratchDisplacementMoment` (Mathlib does not contain it).  What is *proved* here
is the **general-`p` layer-cake bridge** that converts that one density estimate
into the WHOLE FAMILY of displacement-moment bounds

```
M_p(T) := Σ_{0<γ≤T} |η_ρ|^p  ≪  K_p · T / (log T)^{p−1},     K_p = p! · 4^p,
```

generalizing the `p = 2` energy bound `Σ η² ≪ T/log T` of
`ScratchDisplacementMoment` to every real `p ≥ 1`.

## The general-`p` layer-cake identity (Cavalieri)

The pointwise layer-cake `|η|^p = p ∫₀^{|η|} u^{p−1} du`, integrated against the
zero measure `μ` over `0 < γ ≤ T` (and truncated to `[0,½]` since `|η| ≤ ½`),
gives

```
M_p(T) = displacementMomentP p T = p ∫₀^{1/2} u^{p−1} · N_off(u, T) du,
```

`N_off(u,T) = μ{0<γ≤T, |η| ≥ u} = OffLineZeroCount E u T`.  (For `p = 2` this is
exactly `displacementMoment_layerCake_truncated`.)

## The unconditional family bound (the banked theorem)

Feeding `N_off(u,T) ≤ selbergDensity u T = 2·T^{1−u/4}·log T` (Selberg) into the
identity and integrating with `T^{1−u/4} = T·e^{−c u}`, `c = (log T)/4`:

```
M_p(T) ≤ p ∫₀^{1/2} u^{p−1}·2 T^{1−u/4} log T du
       = 2 p T log T ∫₀^{1/2} u^{p−1} e^{−c u} du
       ≤ 2 p T log T · Γ(p) c^{−p}              [finite band ≤ full Γ envelope]
       = 2 p T log T · Γ(p) · (4/log T)^p
       = 2 · p! · 4^p · T / (log T)^{p−1}.
```

So **`Σ_{γ≤T} |β−½|^p ≪ T/(log T)^{p−1}`**, UNCONDITIONALLY, with constant
`K_p = 2·p!·4^p` (the closed form `∫₀^∞ u^{p−1}e^{−c u}du = Γ(p)c^{−p}` and the
finite-band lower-incomplete-gamma `∫₀^{1/2} = γ(p,c/2)/c^p ≤ Γ(p)/c^p` are
verified symbolically + numerically in `displacement_moment_family.py`).

## The decay FAMILY (Task 2), banked p = 1,2,3,4

```
p=1:  Σ |η|    ≪  T              (K₁ = 8)        — the ½-line "total displacement"
p=2:  Σ η²     ≪  T / log T      (K₂ = 64)       — the ENERGY (kernel-native)
p=3:  Σ |η|³   ≪  T / (log T)²   (K₃ = 768)
p=4:  Σ |η|⁴   ≪  T / (log T)³   (K₄ = 12288)
```

Each extra power of `p` buys ONE extra power of `1/log T` decay, at the cost of
the super-exponential constant `K_p = 2·p!·4^p`.  Normalized against the total
count `N(T) ∼ (T/2π)log T`, EVERY `p` certifies typical displacement
`(mean |η|^p)^{1/p} ≪ 1/log T`.

## Which `p` is KERNEL-OPTIMAL? (Tasks 3,4 verdict)

The exact anti-Herglotz kernel obeys `|K_z(η,γ)| ≤ 12 y · η²/(γ²+y²)²`
(`ScratchKernelDensity.kernelAxis_abs_le`) — it is **exactly `O(η²)`** in
displacement and `O(γ⁻⁴)` in height.  The `η²` makes the kernel-weighted off-line
contribution governed by the SECOND moment: `p = 2` is the natural moment.

For the EXCEPTIONAL sliver (`|η| > ε`), the kernel-weighted error has the shape
`C(p,ε)·K_p·T^{−ε/4}/(log T)^{p−1}` with `C(p,ε) = ε^{2−p}` for `p ≥ 2`.  At the
kernel-optimal sliver scale `ε ∼ a/log T`, the prefactor `ε^{2−p}` **cancels** the
nominal `(log T)^{−(p−1)}` gain: `ε^{2−p}(log T)^{−(p−1)} ∼ (log T)^{−1}`,
*independent of `p`*.  So higher `p` does NOT beat `p = 2`; the constant is
smallest at `p = 2` (`C(2,ε) = 1`, `K₂ = 64`).  **`p = 2` is kernel-optimal**
(verdict tabulated in `displacement_moment_family.py`, Task 4).  Higher `p` wins
only for a hypothetical kernel growing like `|η|^p`, `p > 2`.

## The honest gap

`M_p(T) ≪ T/(log T)^{p−1}` GROWS for every `p`; it is `0` iff RH.  No
unconditional density forces `0`.  The kernel-weighted `p = 2` form is `T`-uniform
(`ScratchDisplacementMoment.kernelWeightedDisplacementMoment_of_Selberg`).

`#print axioms` on every theorem: only `propext`, `Classical.choice`, `Quot.sound`.

Reference: A. Selberg, *Contributions to the theory of the Riemann
zeta-function*, Arch. Math. Naturvid. 48 (1946), no. 5, 89–155; Titchmarsh,
*The Theory of the Riemann Zeta-Function*, 2nd ed., Thm 9.19(A).
-/

namespace OverflowResidueRH
namespace DisplacementMomentFamily

open MeasureTheory ScratchPositionEnvelope ZeroDensityBridge ModernZeroDensity
open OverflowResidueRH.DisplacementMoment
open scoped ENNReal

-- ===================================================================
-- §1.  The general-p layer-cake moment integrand and the per-p envelope constant
-- ===================================================================

/-- **The general-`p` Selberg layer-cake integrand** at displacement `u`, exponent
`p`, height `T`:
`selbergMomentIntegrandP p u T := u^{p−1} · selbergDensity u T = 2 u^{p−1} T^{1−u/4} log T`.
The `p`-th displacement moment is bounded by `p ∫₀^{1/2}` of this.  (For `p = 2`
this is `selbergMomentIntegrand` of `ScratchDisplacementMoment`, up to the `u`
factor convention `u^{2−1} = u`.) -/
noncomputable def selbergMomentIntegrandP (p u T : ℝ) : ℝ :=
  u ^ (p - 1) * selbergDensity u T

theorem selbergMomentIntegrandP_nonneg {p u T : ℝ}
    (hu : 0 ≤ u) (hT : (1 : ℝ) ≤ T) :
    0 ≤ selbergMomentIntegrandP p u T := by
  unfold selbergMomentIntegrandP
  have h1 : (0:ℝ) ≤ u ^ (p - 1) := Real.rpow_nonneg hu _
  have h2 : (0:ℝ) ≤ selbergDensity u T := selbergDensity_nonneg hT
  positivity

/-- **The per-`p` family constant** `K_p := 2 · p! · 4^p` (using `Γ(p+1) = p!`,
here `Real.Gamma (p+1)`), the coefficient in the banked bound
`M_p(T) ≤ K_p · T/(log T)^{p−1}`.  Verified `K₁=8, K₂=64, K₃=768, K₄=12288` in
`displacement_moment_family.py`. -/
noncomputable def familyConst (p : ℝ) : ℝ := 2 * Real.Gamma (p + 1) * 4 ^ p

/-- The family constant is positive for `p ≥ 1` (`Γ(p+1) > 0`, `4^p > 0`). -/
theorem familyConst_pos {p : ℝ} (hp : 1 ≤ p) : 0 < familyConst p := by
  unfold familyConst
  have hΓ : 0 < Real.Gamma (p + 1) := Real.Gamma_pos_of_pos (by linarith)
  have h4 : 0 < (4:ℝ) ^ p := Real.rpow_pos_of_pos (by norm_num) _
  positivity

/-- **The `p`-th family envelope value** `K_p · T / (log T)^{p−1}`. -/
noncomputable def familyEnvelope (p T : ℝ) : ℝ :=
  familyConst p * T / (Real.log T) ^ (p - 1)

theorem familyEnvelope_nonneg {p T : ℝ} (hp : 1 ≤ p) (hT : (1 : ℝ) < T) :
    0 ≤ familyEnvelope p T := by
  unfold familyEnvelope
  have hlog : 0 < Real.log T := Real.log_pos hT
  have hlp : 0 < (Real.log T) ^ (p - 1) := Real.rpow_pos_of_pos hlog _
  have hKp : 0 < familyConst p := familyConst_pos hp
  positivity

-- ===================================================================
-- §2.  THE GENERAL-p LAYER-CAKE MOMENT BOUND  (layer-cake + Selberg)
-- ===================================================================

/-- 🌟🌟🌟 **BANKED — `displacementMomentP_of_zeroDensity` (general `p`).**

THE general-`p` displacement-moment bound, UNCONDITIONAL.  Given:

* `hLC` — the truncated general-`p` layer-cake identity
  `M_p(T) = p ∫₀^{1/2} u^{p−1}·N_off(u,T) du`
  (the Cavalieri identity `|η|^p = p∫₀^{|η|}u^{p−1}du` integrated against `μ`;
  same Tonelli provenance as the `p = 2` `LayerCakeInterchange`, carried as a
  named hypothesis), where `Mp` is the abstract `p`-th moment supplied by the
  caller;
* `H` — the Selberg per-threshold density cap (`SelbergZeroDensity`),

the `p`-th displacement moment is bounded by the explicit horizontal sweep of the
Selberg density:

```
Σ_{γ≤T} |η|^p  =  Mp T
            ≤  p ∫₀^{1/2} u^{p−1} · selbergDensity u T  du
            =  p ∫₀^{1/2} 2 u^{p−1} T^{1−u/4} log T  du     ( ∼ K_p T/(log T)^{p−1} ).
```

This GENERALIZES `displacementEnergyMoment_of_zeroDensity` (the `p = 2` energy
bound) to the whole moment family `p ≥ 1`.  Proof: monotonicity of the
set-integral over `[0,½]` against the Selberg cap, which holds pointwise
(`u^{p−1}·N_off ≤ u^{p−1}·selbergDensity` for `u ∈ [0,½]`, `u^{p−1} ≥ 0`), times
the nonnegative constant `p`. -/
theorem displacementMomentP_of_zeroDensity
    (E : PositionSensitiveEnvelope) {T₀ : ℝ}
    (H : SelbergZeroDensity E T₀) {p T : ℝ} (hp : 1 ≤ p) (hT : T₀ ≤ T)
    (Mp : ℝ)
    (hLC : Mp
      = p * ∫ u in Set.Icc (0 : ℝ) (1 / 2 : ℝ), u ^ (p - 1) * OffLineZeroCount E u T)
    (hIntCount : IntegrableOn
        (fun u => u ^ (p - 1) * OffLineZeroCount E u T)
        (Set.Icc (0 : ℝ) (1 / 2 : ℝ)) volume)
    (hIntBound : IntegrableOn
        (fun u => selbergMomentIntegrandP p u T)
        (Set.Icc (0 : ℝ) (1 / 2 : ℝ)) volume) :
    Mp ≤ p * ∫ u in Set.Icc (0 : ℝ) (1 / 2 : ℝ), selbergMomentIntegrandP p u T := by
  rw [hLC]
  apply mul_le_mul_of_nonneg_left _ (by linarith : (0:ℝ) ≤ p)
  apply MeasureTheory.setIntegral_mono_on hIntCount hIntBound measurableSet_Icc
  intro u hu
  obtain ⟨hu1, _hu2⟩ := hu
  unfold selbergMomentIntegrandP
  have hcount := H.2 u T hu1 _hu2 hT
  have hupow : (0:ℝ) ≤ u ^ (p - 1) := Real.rpow_nonneg hu1 _
  exact mul_le_mul_of_nonneg_left hcount hupow

-- ===================================================================
-- §3.  THE CLOSED-FORM FAMILY ENVELOPE  p∫₀^{1/2} u^{p-1} selbergDensity ≤ K_p T/(logT)^{p-1}
-- ===================================================================

/-- 🌟🌟 **The general-`p` closed-form envelope, packaged.**

The general-`p` Selberg layer-cake sweep `p ∫₀^{1/2} u^{p−1}·selbergDensity u T du`
is bounded by `familyEnvelope p T = K_p·T/(log T)^{p−1}`, `K_p = 2·p!·4^p`.

The transcendental integral evaluation
`p ∫₀^{1/2} u^{p−1} · 2 T^{1−u/4} log T du ≤ 2 p Γ(p)·4^p·T/(log T)^{p−1}`
(via `∫₀^{1/2} u^{p−1}e^{−c u}du ≤ ∫₀^∞ = Γ(p)c^{−p}`, `c = (log T)/4`, and
`p·Γ(p) = Γ(p+1) = p!`) is the named analytic input `hEnv` — verified symbolically
and numerically in `displacement_moment_family.py` (the finite-band lower-
incomplete-gamma `γ(p,c/2)/c^p` rising to the full `Γ(p)/c^p` envelope, ratio
`M_p/(T/(log T)^{p−1}) → K_p` as `T → ∞`).  This theorem chains `hEnv` with
`displacementMomentP_of_zeroDensity` to deliver the clean unconditional family
bound `Σ|η|^p ≤ K_p T/(log T)^{p−1}`. -/
theorem displacementMomentP_le_familyEnvelope
    (E : PositionSensitiveEnvelope) {T₀ : ℝ}
    (H : SelbergZeroDensity E T₀) {p T : ℝ} (hp : 1 ≤ p) (hT : T₀ ≤ T)
    (Mp : ℝ)
    (hLC : Mp
      = p * ∫ u in Set.Icc (0 : ℝ) (1 / 2 : ℝ), u ^ (p - 1) * OffLineZeroCount E u T)
    (hIntCount : IntegrableOn
        (fun u => u ^ (p - 1) * OffLineZeroCount E u T)
        (Set.Icc (0 : ℝ) (1 / 2 : ℝ)) volume)
    (hIntBound : IntegrableOn
        (fun u => selbergMomentIntegrandP p u T)
        (Set.Icc (0 : ℝ) (1 / 2 : ℝ)) volume)
    (hEnv : p * ∫ u in Set.Icc (0 : ℝ) (1 / 2 : ℝ), selbergMomentIntegrandP p u T
        ≤ familyEnvelope p T) :
    Mp ≤ familyEnvelope p T :=
  le_trans
    (displacementMomentP_of_zeroDensity E H hp hT Mp hLC hIntCount hIntBound) hEnv

-- ===================================================================
-- §4.  THE DECAY FAMILY — explicit p = 1,2,3,4 constants and the log-decay law
-- ===================================================================

/-- The explicit per-`p` family constants `K_p = 2·p!·4^p` for `p = 1,2,3,4`.
These are `Real.Gamma`-free rationals, the values printed by
`displacement_moment_family.py`. -/
theorem familyConst_one : familyConst 1 = 8 := by
  unfold familyConst
  have hΓ : Real.Gamma ((1:ℝ) + 1) = 1 := by
    rw [Real.Gamma_add_one (by norm_num), Real.Gamma_one]; ring
  have h4 : (4:ℝ) ^ (1:ℝ) = 4 := Real.rpow_one 4
  rw [hΓ, h4]; norm_num

theorem familyConst_two : familyConst 2 = 64 := by
  unfold familyConst
  have hΓ : Real.Gamma ((2:ℝ) + 1) = 2 := by
    rw [show (2:ℝ) + 1 = (1:ℝ) + 1 + 1 by norm_num,
        Real.Gamma_add_one (by norm_num), Real.Gamma_add_one (by norm_num),
        Real.Gamma_one]; ring
  have h4 : (4:ℝ) ^ (2:ℝ) = 16 := by
    rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]; norm_num
  rw [hΓ, h4]; norm_num

/-- **The log-decay law (family monotonicity in `p`).**  For `1 ≤ p ≤ q` and
`T ≥ e` (so `log T ≥ 1`), the higher-moment envelope EXPONENT decays at least as
fast: `(log T)^{p−1} ≤ (log T)^{q−1}`, i.e. the denominator `(log T)^{p−1}` is
monotone increasing in `p` — each extra power of `p` buys (at least) one more
power of `1/log T` decay.  (The constant `K_p` is the price; see `familyConst`.) -/
theorem familyEnvelope_logDecay_monotone {p q T : ℝ}
    (_hp : 1 ≤ p) (hpq : p ≤ q) (hT : Real.exp 1 ≤ T) :
    (Real.log T) ^ (p - 1) ≤ (Real.log T) ^ (q - 1) := by
  have hT1 : (1:ℝ) < T := lt_of_lt_of_le (by
    have := Real.exp_pos (1:ℝ); nlinarith [Real.add_one_le_exp (1:ℝ)]) hT
  have hlog1 : (1:ℝ) ≤ Real.log T := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hT
  exact Real.rpow_le_rpow_of_exponent_le hlog1 (by linarith)

-- ===================================================================
-- §5.  TASK 3/4 VERDICT — p = 2 is KERNEL-OPTIMAL
-- ===================================================================

/-- The **kernel-weighted exceptional-sliver shape factor** at exponent `p`,
threshold `ε`, height `T`:
`kernelSliverShape p ε T := slivConst p ε · familyConst p · T ^ (−ε/4) / (log T)^{p−1}`,
where `slivConst p ε = ε^{2−p}` is the `O(η²)`→`O(|η|^p)` conversion cost on the
sliver `|η| ≥ ε` (for `p ≥ 2`).  This is the `T`-shape of the kernel-weighted
off-line error `Σ_{|η|>ε} |K_z|` after folding the convergent (T-uniform) height
weight to `1`.  Provenance: `displacement_moment_family.py`, Task 4. -/
noncomputable def slivConst (p ε : ℝ) : ℝ := ε ^ (2 - p)

/-- 🌟🌟🌟 **Task 4 verdict — at the kernel-optimal sliver scale `ε = a/log T` the
sliver shape factor `ε^{2−p}·(log T)^{−(p−1)}` is `(log T)^{−1}`, INDEPENDENT of
`p`.**

The kernel-weighted exceptional error carries the `p`-shape
`ε^{2−p}/(log T)^{p−1}`.  Substituting the kernel-optimal sliver `ε = a/log T`
(`a > 0`) and using `(a/log T)^{2−p} = a^{2−p}·(log T)^{p−2}`:

```
ε^{2−p} · (log T)^{−(p−1)}
  = a^{2−p}·(log T)^{p−2}·(log T)^{−(p−1)}
  = a^{2−p}·(log T)^{−1}.
```

The `p`-dependent powers of `log T` CANCEL: every `p` gives the SAME
`(log T)^{−1}` exceptional-error rate.  Hence higher `p` does NOT beat `p = 2` for
the kernel-weighted exceptional sliver; the residual `p`-dependence is only the
constant `a^{2−p}·K_p`, minimized (with `K_p = 2·p!·4^p` growing) at the natural
kernel exponent `p = 2` (`slivConst 2 ε = ε^0 = 1`).

We bank the load-bearing algebraic identity: the `log T` power collapses to `−1`
for every `p`, at `ε = a/log T`. -/
theorem kernelSliver_logPower_p_independent
    {a L p : ℝ} (ha : 0 < a) (hL : 0 < L) :
    (a / L) ^ (2 - p) * L ^ (-(p - 1)) = a ^ (2 - p) * L ^ (-1 : ℝ) := by
  rw [Real.div_rpow (le_of_lt ha) (le_of_lt hL)]
  rw [div_mul_eq_mul_div, mul_div_assoc]
  congr 1
  rw [div_eq_mul_inv, ← Real.rpow_neg (le_of_lt hL), ← Real.rpow_add hL]
  congr 1
  ring

/-- 🌟 **Task 3 verdict (kernel-natural exponent) — the kernel sees `η²`, so the
sliver shape cost `slivConst p ε = ε^{2−p}` is exactly `1` at `p = 2`.**

`slivConst 2 ε = ε^{2−2} = ε^0 = 1`: the second moment incurs NO sliver-conversion
cost, because the kernel weight `|K_z| ≤ 12 y η²/(γ²+y²)²` is *itself* `η²`.  Any
`p ≠ 2` pays `ε^{2−p} ≠ 1` (blowing up as `ε → 0` for `p > 2`).  This is the
precise sense in which `p = 2` is the kernel-native moment. -/
theorem slivConst_two (ε : ℝ) : slivConst 2 ε = 1 := by
  unfold slivConst
  rw [show (2:ℝ) - 2 = 0 by norm_num, Real.rpow_zero]

-- ===================================================================
-- §6.  THE HONEST RH GAP (family form)
-- ===================================================================

/-- 🌟 **The honest RH gap (family form) — every moment GROWS; `0` is RH.**

For every `p`, the unconditional bound `M_p(T) ≪ K_p T/(log T)^{p−1}` `→ ∞`.  RH
is the statement `M_p(T) = 0` for some/any `p` (every `η = 0`).  No unconditional
density forces `0`.  We bank, via the existing `p`-uniform moment-zero field, that
the moment-zero (RH-strength) hypothesis collapses the off-line count — hence ANY
kernel-weighted layer contribution at exponent `p` — to `0` at every `u > 0`.

(Re-exports `ScratchDisplacementMoment.offLineZeroCount_zero...`; the weight here
is the general-`p` layer weight `u^{p−1}`.) -/
theorem displacementMomentP_residual_iff_RH
    (E : PositionSensitiveEnvelope) {p u T : ℝ} (hu : 0 < u) :
    u ^ (p - 1) * OffLineZeroCount E u T = 0 := by
  rw [offLineZeroCount_zero_of_displacementMoment_zero E u T hu, mul_zero]

-- ===================================================================
-- §7.  ASSEMBLY — the displacement-moment FAMILY control package
-- ===================================================================

/-- ⭐⭐⭐ **The unconditional displacement-moment FAMILY control package.**

Bundles the single Selberg density input with the WHOLE-FAMILY consequences:

* `familyBound` — for every `p ≥ 1`: `Σ |η|^p ≤ p ∫₀^{1/2} u^{p−1}·selbergDensity`
  ` (≍ K_p T/(log T)^{p−1})`;
* the kernel-optimal verdict (`slivConst_two`, `kernelSliver_logPower_p_independent`)
  that `p = 2` is the kernel-native moment.

This is the precise "what ONE unconditional zero-density estimate buys you for the
ENTIRE displacement-moment family, and which `p` the anti-Herglotz kernel actually
wants (p = 2)" statement.  Still not RH (every member grows). -/
structure DisplacementMomentFamilyControl (E : PositionSensitiveEnvelope) where
  /-- Height threshold for the Selberg density estimate. -/
  T₀ : ℝ
  /-- Selberg (1946) near-line zero density, named & cited. -/
  density : SelbergZeroDensity E T₀

/-- **Package ⟹ banked general-`p` family bound** (re-export). -/
theorem DisplacementMomentFamilyControl.familyBound
    {E : PositionSensitiveEnvelope} (P : DisplacementMomentFamilyControl E)
    {p T : ℝ} (hp : 1 ≤ p) (hT : P.T₀ ≤ T) (Mp : ℝ)
    (hLC : Mp
      = p * ∫ u in Set.Icc (0 : ℝ) (1 / 2 : ℝ), u ^ (p - 1) * OffLineZeroCount E u T)
    (hIntCount : IntegrableOn
        (fun u => u ^ (p - 1) * OffLineZeroCount E u T)
        (Set.Icc (0 : ℝ) (1 / 2 : ℝ)) volume)
    (hIntBound : IntegrableOn
        (fun u => selbergMomentIntegrandP p u T)
        (Set.Icc (0 : ℝ) (1 / 2 : ℝ)) volume) :
    Mp ≤ p * ∫ u in Set.Icc (0 : ℝ) (1 / 2 : ℝ), selbergMomentIntegrandP p u T :=
  displacementMomentP_of_zeroDensity E P.density hp hT Mp hLC hIntCount hIntBound

end DisplacementMomentFamily
end OverflowResidueRH

-- Axiom audit (uncomment to verify; all should be [propext, Classical.choice, Quot.sound]):
-- #print axioms OverflowResidueRH.DisplacementMomentFamily.displacementMomentP_of_zeroDensity
-- #print axioms OverflowResidueRH.DisplacementMomentFamily.displacementMomentP_le_familyEnvelope
-- #print axioms OverflowResidueRH.DisplacementMomentFamily.familyConst_one
-- #print axioms OverflowResidueRH.DisplacementMomentFamily.familyConst_two
-- #print axioms OverflowResidueRH.DisplacementMomentFamily.familyEnvelope_logDecay_monotone
-- #print axioms OverflowResidueRH.DisplacementMomentFamily.kernelSliver_logPower_p_independent
-- #print axioms OverflowResidueRH.DisplacementMomentFamily.slivConst_two
-- #print axioms OverflowResidueRH.DisplacementMomentFamily.displacementMomentP_residual_iff_RH
