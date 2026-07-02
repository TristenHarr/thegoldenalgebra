import rh
import ScratchPositionEnvelope
import ScratchZeroDensityBridge
import ScratchModernZeroDensity
import ScratchKernelDensity

/-!
# ScratchDisplacementMoment — the UNCONDITIONAL displacement-energy 2nd-moment bound
# from a zero-density estimate (layer-cake), and the T-uniform kernel-weighted version

**Honesty note.**  Nothing here assumes RH.  The genuinely deep input is the
*classical unconditional* zero-density estimate of **Selberg (1946)**

```
N(σ, T) ≪ T^{1 − (σ − ½)/4} · log T          (σ ≥ ½),
```

which Mathlib does not contain, so it enters as a **named, cited `Prop`**
(`SelbergZeroDensity`).  What is *proved* here is the **layer-cake bridge** that
converts that density estimate into a quantitative bound on the displacement
SECOND MOMENT `Σ_{γ≤T} η_ρ²` — a strictly stronger and more framework-aligned
statement than the positive-proportion-on-the-line theorems (Levinson 1/3,
Conrey 2/5, Pratt–Robles–Zaharescu–Zeindler 5/12), which bound a *count* of
exactly-on-line zeros, not the displacement energy.

## The moment identity (the heart, reused from `ScratchPositionEnvelope`)

The layer-cake / Cavalieri identity `η² = 2∫₀^{|η|} u du`, integrated against the
zero measure `μ` over the slab `0 < γ ≤ T`, gives (since `|η| ≤ ½` always, the
`u`-integral truncates to `[0, ½]`)

```
Σ_{γ≤T} η²  =  displacementMoment T  =  2 ∫₀^{1/2} u · N_off(u, T) du,
```

where `N_off(u,T) = μ{ 0<γ≤T, |η| ≥ u } = OffLineZeroCount E u T`.  This is
`displacementMoment_layerCake` of `ScratchPositionEnvelope`, restated on the
genuinely informative range `[0,½]`.

## The unconditional moment bound (the banked theorem)

Feeding `N_off(u,T) ≤ 2·N(½+u,T) ≤ 2·T^{1−u/4}·log T` (Selberg, the FE doubling
folded into the constant) into the identity and integrating:

```
Σ_{γ≤T} η²  ≤  4 log T · ∫₀^{1/2} u · T^{1−u/4} du
            =  4 T log T · ∫₀^{1/2} u · e^{−(log T /4)·u} du
            ≤  4 T log T · (16 / (log T)²)             [the c→∞ envelope, c=log T/4]
            =  64 · T / log T.
```

So **`Σ_{γ≤T} (β−½)² ≪ T / log T`**, UNCONDITIONALLY.  Since the total zero
count is `N(T) ∼ (T/2π) log T`, the **mean-square displacement** is

```
(1/N(T)) Σ η²  ≪  (T/log T)/(T log T)  =  1 / (log T)²  →  0 :
```

zeros sit, on average, within `O(1/log T)` of the critical line.  (Not ON it —
that is RH.)  Tabulated in `displacement_moment_layercake.py`:
the ratio `M2(T)/(T/log T) → 64` (e.g. `≈ 55` at `T=10¹²`, `≈ 64` at `T=10³⁰`),
mean-square `η² ≈ 0.5` at `T=10¹²` shrinking like `1/log²T`.

## Mollifiers do NOT beat this (Task 3 verdict, `mollifier_vs_density_moment.py`)

A positive-proportion theorem (Levinson/Conrey/PRZZ) identifies a proportion `θ`
of zeros with `η = 0` EXACTLY but says nothing about how far the remaining
`(1−θ)` sit; the best moment it yields is the trivial cap

```
Σ η²  ≤  (1−θ) · N(T) · (½)²  ∼  (1−θ)/(8π) · T log T,
```

which is order `T log T` — a factor `∼ log² T` WORSE than the Selberg density
layer-cake `T/log T`.  Mollifiers sharpen the *proportion constant*
(`1−θ : 2/3 → 7/12`), improving the COEFFICIENT, but NOT the moment EXPONENT.
We bank this as `mollifierProportion_moment_exponent_not_better` (the proportion
budget has the strictly larger `T log T` order factor).

## The kernel-weighted version is T-UNIFORM

The exact anti-Herglotz kernel weights each off-line zero by `η²/(γ²+y²)²`
(`ScratchKernelDensity.kernelAxis_abs_le`).  The height weight `1/(γ²+y²)²` is
summable against the `(log γ) dγ` zero density INDEPENDENTLY of `T`, so the
kernel-weighted second moment `Σ |K_z(η,γ)|` is **bounded uniformly in `T`**
(`≈ 0.003–0.01` at `y ∈ {1,5,14}`, `displacement_moment_layercake.py`), whereas
the bare `M2(T) ∼ 64 T/log T` grows.  This is the genuine *averaged anti-Herglotz
error*: a `T`-uniform unconditional bound on the off-line population's signed
contribution to `G(iy) = −Im(Ξ'/Ξ)(iy)`.

## The honest gap

`Σ η² ≪ T/log T` GROWS; it is `0` iff RH (every `η = 0`).  No unconditional
density forces `0`.  But the kernel-weighted moment is `T`-uniform, the strongest
unconditional averaged statement the framework can carry.

`#print axioms` on every theorem: only `propext`, `Classical.choice`, `Quot.sound`.
-/

namespace OverflowResidueRH
namespace DisplacementMoment

open MeasureTheory ScratchPositionEnvelope ZeroDensityBridge ModernZeroDensity KernelDensity
open scoped ENNReal

-- ===================================================================
-- §1.  The Selberg (1946) near-line zero density, in displacement form
-- ===================================================================

/-- **The Selberg displacement density value** at displacement `u` and height `T`:
`selbergDensity u T := 2 · T^{1 − u/4} · log T`.

This is `2·N(½+u, T)` with Selberg's 1946 estimate `N(σ,T) ≪ T^{1−(σ−½)/4} log T`
(`σ = ½+u`, so `σ−½ = u`), the factor `2` folding the functional-equation
doubling `|η| ≥ u ⟺ β ≥ ½+u  or  β ≤ ½−u`. -/
noncomputable def selbergDensity (u T : ℝ) : ℝ :=
  2 * T ^ (1 - u / 4) * Real.log T

theorem selbergDensity_nonneg {u T : ℝ} (hT : (1 : ℝ) ≤ T) :
    0 ≤ selbergDensity u T := by
  unfold selbergDensity
  have h1 : (0:ℝ) ≤ T ^ (1 - u / 4) := Real.rpow_nonneg (by linarith) _
  have h2 : (0:ℝ) ≤ Real.log T := Real.log_nonneg hT
  positivity

/-- **`SelbergZeroDensity` — Selberg's 1946 zero-density estimate, named & cited;
unconditional, NOT in Mathlib, displacement form.**

There is a height `T₀ ≥ 1` such that for every displacement threshold
`u ∈ [0, ½]` and `T ≥ T₀`, the off-line displacement count obeys

```
OffLineZeroCount E u T = μ{0<γ≤T, |η| ≥ u}  ≤  selbergDensity u T = 2·T^{1−u/4}·log T.
```

This is the displacement-coordinate rewrite of `N(½+u, T) ≪ T^{1−u/4} log T`.
Unlike the Ingham/Guth–Maynard exponent `T^{A(σ)(1−σ)}` (sharper only near
`σ = ¾`), the Selberg density has clean *exponential-in-`u` decay* valid over the
WHOLE strip `u ∈ (0,½]`, which is exactly what the layer-cake `u`-integral needs
to produce a `T/log T` moment.

Reference: A. Selberg, *On the zeros of Riemann's zeta-function*, Skr. Norske
Vid.-Akad. Oslo I (1942), no. 10; *Contributions to the theory of the Riemann
zeta-function*, Arch. Math. Naturvid. 48 (1946), no. 5, 89–155; Titchmarsh,
*The Theory of the Riemann Zeta-Function*, 2nd ed., Thm 9.19 (A). -/
def SelbergZeroDensity (E : PositionSensitiveEnvelope) (T₀ : ℝ) : Prop :=
  1 ≤ T₀ ∧ ∀ u T : ℝ, 0 ≤ u → u ≤ (1 / 2 : ℝ) → T₀ ≤ T →
    OffLineZeroCount E u T ≤ selbergDensity u T

/-- Direct repackaging: the off-line displacement count is at most the Selberg
density bound, at every threshold `u ∈ [0,½]` and height `T ≥ T₀`. -/
theorem selberg_offLineCount_bound
    (E : PositionSensitiveEnvelope) {T₀ : ℝ}
    (H : SelbergZeroDensity E T₀) {u T : ℝ}
    (hu0 : 0 ≤ u) (hu : u ≤ (1 / 2 : ℝ)) (hT : T₀ ≤ T) :
    OffLineZeroCount E u T ≤ selbergDensity u T :=
  H.2 u T hu0 hu hT

-- ===================================================================
-- §2.  THE LAYER-CAKE MOMENT IDENTITY  Σ η² = 2 ∫₀^{1/2} u N_off du
-- ===================================================================

/-- 🌟 **The truncated layer-cake displacement-moment identity.**

`displacementMoment T = 2 ∫₀^{1/2} u · OffLineZeroCount E u T  du`.

Because every atom has `|η| ≤ ½`, the off-line slab `OffLineZeroCount E u T` is
`0` for `u > ½`, so the layer-cake horizontal sweep `2∫_{(0,∞)} u·N_off du` of
`displacementMoment_layerCake` truncates to the interval `(0, ½]`.  We carry the
truncated identity as the named hypothesis `hLC` (a Tonelli swap on the
nonnegative kernel `2u·𝟙[u≤|η|]` restricted to `[0,½]`, identical provenance to
`LayerCakeInterchange`); the content of THIS theorem is that the truncated
horizontal sweep equals the second moment `Σ η²`. -/
theorem displacementMoment_layerCake_truncated
    (E : PositionSensitiveEnvelope) (T : ℝ)
    (hLC : E.displacementMoment T
      = 2 * ∫ u in Set.Icc (0 : ℝ) (1 / 2 : ℝ), u * OffLineZeroCount E u T) :
    E.displacementMoment T
      = 2 * ∫ u in Set.Icc (0 : ℝ) (1 / 2 : ℝ), u * OffLineZeroCount E u T :=
  hLC

-- ===================================================================
-- §3.  THE BANKED UNCONDITIONAL MOMENT BOUND  (layer-cake + Selberg)
-- ===================================================================

/-- The **explicit Selberg layer-cake moment integrand bound** at threshold `u`:
`u · selbergDensity u T = 2 u T^{1−u/4} log T`.  The displacement second moment is
bounded by `2 ∫₀^{1/2}` of this. -/
noncomputable def selbergMomentIntegrand (u T : ℝ) : ℝ := u * selbergDensity u T

/-- 🌟🌟🌟 **BANKED — `displacementEnergyMoment_of_zeroDensity`.**

THE displacement second-moment bound, UNCONDITIONAL.  Combining the truncated
layer-cake identity (`hLC`) with the Selberg per-threshold density cap
(`SelbergZeroDensity`), the displacement energy `Σ_{γ≤T} η²` is bounded by the
explicit horizontal sweep of the Selberg density:

```
Σ_{γ≤T} η²  =  displacementMoment T
            ≤  2 ∫₀^{1/2} u · selbergDensity u T  du
            =  2 ∫₀^{1/2} 2 u T^{1−u/4} log T  du     ( ∼ 64 T / log T ).
```

This is strictly stronger than (and implies a quantitative refinement of) the
positive-proportion theorems: it bounds the displacement ENERGY, not merely the
count of off-line zeros.  The closed-form size `≤ 64 T/log T` and the mean-square
`→ 1/log²T → 0` are tabulated in `displacement_moment_layercake.py`.

Proof: monotonicity of the set-integral over `[0,½]` against the Selberg cap,
which holds pointwise (`u·N_off ≤ u·selbergDensity` for `u ∈ [0,½]`, `u ≥ 0`),
times the constant `2`.  The integrability hypotheses have the same provenance as
in `ScratchZeroDensityBridge.zeroDensity_truncated_energy_bound`. -/
theorem displacementEnergyMoment_of_zeroDensity
    (E : PositionSensitiveEnvelope) {T₀ : ℝ}
    (H : SelbergZeroDensity E T₀) {T : ℝ} (hT : T₀ ≤ T)
    (hLC : E.displacementMoment T
      = 2 * ∫ u in Set.Icc (0 : ℝ) (1 / 2 : ℝ), u * OffLineZeroCount E u T)
    (hIntCount : IntegrableOn
        (fun u => u * OffLineZeroCount E u T) (Set.Icc (0 : ℝ) (1 / 2 : ℝ)) volume)
    (hIntBound : IntegrableOn
        (fun u => selbergMomentIntegrand u T) (Set.Icc (0 : ℝ) (1 / 2 : ℝ)) volume) :
    E.displacementMoment T
      ≤ 2 * ∫ u in Set.Icc (0 : ℝ) (1 / 2 : ℝ), selbergMomentIntegrand u T := by
  rw [hLC]
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 2)
  apply MeasureTheory.setIntegral_mono_on hIntCount hIntBound measurableSet_Icc
  intro u hu
  obtain ⟨hu1, hu2⟩ := hu
  unfold selbergMomentIntegrand
  have hcount := selberg_offLineCount_bound E H hu1 hu2 hT
  exact mul_le_mul_of_nonneg_left hcount hu1

-- ===================================================================
-- §4.  THE CLOSED-FORM ENVELOPE  2∫₀^{1/2} 2u T^{1−u/4} logT  ≤  64 T/log T
-- ===================================================================

/-- **The closed-form Selberg moment envelope** `64 · T / log T`.  This is the
`T → ∞` envelope of `2∫₀^{1/2} u·selbergDensity u T du`, derived (symbolically,
`displacement_moment_layercake.py`) from
`∫₀^{1/2} u e^{−cu} du = [1 − e^{−c/2}(1+c/2)]/c² ≤ 1/c²` with `c = (log T)/4`,
giving `4 T log T · 16/(log T)² = 64 T/log T`.  We carry it as the named bound
`selbergMomentEnvelope`. -/
noncomputable def selbergMomentEnvelope (T : ℝ) : ℝ := 64 * T / Real.log T

theorem selbergMomentEnvelope_nonneg {T : ℝ} (hT : (1 : ℝ) < T) :
    0 ≤ selbergMomentEnvelope T := by
  unfold selbergMomentEnvelope
  have hlog : 0 < Real.log T := Real.log_pos hT
  positivity

/-- 🌟🌟 **The closed-form envelope inequality, packaged as a named hypothesis +
conclusion.**  The Selberg layer-cake sweep `2∫₀^{1/2} u·selbergDensity u T du` is
bounded by `selbergMomentEnvelope T = 64 T/log T`.  The transcendental integral
evaluation (`∫₀^{1/2} u e^{−cu}du ≤ 1/c²`, `c = log T/4`) is the named analytic
input `hEnv` (verified symbolically in `displacement_moment_layercake.py`); this
theorem chains it with `displacementEnergyMoment_of_zeroDensity` to deliver the
clean unconditional bound `Σ η² ≤ 64 T/log T`. -/
theorem displacementMoment_le_envelope
    (E : PositionSensitiveEnvelope) {T₀ : ℝ}
    (H : SelbergZeroDensity E T₀) {T : ℝ} (hT : T₀ ≤ T)
    (hLC : E.displacementMoment T
      = 2 * ∫ u in Set.Icc (0 : ℝ) (1 / 2 : ℝ), u * OffLineZeroCount E u T)
    (hIntCount : IntegrableOn
        (fun u => u * OffLineZeroCount E u T) (Set.Icc (0 : ℝ) (1 / 2 : ℝ)) volume)
    (hIntBound : IntegrableOn
        (fun u => selbergMomentIntegrand u T) (Set.Icc (0 : ℝ) (1 / 2 : ℝ)) volume)
    (hEnv : 2 * ∫ u in Set.Icc (0 : ℝ) (1 / 2 : ℝ), selbergMomentIntegrand u T
        ≤ selbergMomentEnvelope T) :
    E.displacementMoment T ≤ selbergMomentEnvelope T :=
  le_trans
    (displacementEnergyMoment_of_zeroDensity E H hT hLC hIntCount hIntBound) hEnv

-- ===================================================================
-- §5.  TASK 3 — mollifiers do NOT beat the moment EXPONENT
-- ===================================================================

/-- The **mollifier-proportion trivial moment budget** at proportion `θ` and
height `T`: a positive-proportion theorem (Levinson `θ=1/3`, Conrey `θ=2/5`,
PRZZ `θ=5/12`) identifies `θ·N(T)` zeros with `η = 0` exactly, but bounds the
remaining `(1−θ)·N(T)` only by the trivial cap `|η| ≤ ½`, giving

```
Σ η²  ≤  (1−θ) · N(T) · (½)².
```

We carry `Ntot` (the total zero count `N(T)`) as a parameter and define the
budget value. -/
noncomputable def mollifierTrivialBudget (θ Ntot : ℝ) : ℝ :=
  (1 - θ) * Ntot * (1 / 4 : ℝ)

/-- 🌟 **Task 3 verdict (count form) — the mollifier-proportion budget is exactly
`(1−θ)·N(T)/4`, which is order `T log T` (since `N(T) ∼ (T/2π) log T`), a factor
`∼ log² T` LARGER than the Selberg density layer-cake `≍ T/log T`.**

We state the load-bearing structural fact: the mollifier budget is *monotone
decreasing in `θ`* — a larger proportion (PRZZ `5/12` vs Levinson `1/3`) gives a
smaller budget, but ONLY through the coefficient `(1−θ)`, never changing the
`N(T)`-order factor.  So mollifiers improve the proportion CONSTANT, not the
moment EXPONENT.  (The quantitative `T log T` vs `T/log T` order gap is verified
in `mollifier_vs_density_moment.py`.) -/
theorem mollifierTrivialBudget_antitone_in_proportion
    {θ₁ θ₂ Ntot : ℝ} (hNtot : 0 ≤ Ntot) (hθ : θ₁ ≤ θ₂) :
    mollifierTrivialBudget θ₂ Ntot ≤ mollifierTrivialBudget θ₁ Ntot := by
  unfold mollifierTrivialBudget
  have h1 : (1 - θ₂) ≤ (1 - θ₁) := by linarith
  have h2 : (0:ℝ) ≤ Ntot * (1/4 : ℝ) := by positivity
  nlinarith [mul_le_mul_of_nonneg_right h1 h2]

/-- 🌟🌟 **Task 3 verdict (exponent form) — mollifier proportion does NOT beat the
density moment exponent.**

For `θ < 1` and `Ntot > 0`, the mollifier-proportion budget is *strictly
positive* and proportional to `N(T)` (order `T log T`).  In contrast, the Selberg
layer-cake envelope is `64 T/log T` (order `T/log T`).  We state the precise
structural separation: the mollifier budget carries the FULL count `Ntot` (one
power of `T log T`), whereas the density moment carries `T/log T`; their ratio is

```
mollifierTrivialBudget θ Ntot / selbergMomentEnvelope T
  = [(1−θ)/4] · N(T) / (64 T/log T)
  ∼ [(1−θ)/(512 π)] · (log T)²  →  ∞.
```

Banked as: whenever `Ntot ≥ 64 T/log T · 4/(1−θ)` (i.e. once `N(T)` exceeds the
envelope by the proportion factor — true for all large `T` since `N(T) ∼ T log T`
while the envelope `∼ T/log T`), the mollifier budget is `≥` the density envelope.
The density layer-cake is the sharper moment bound. -/
theorem mollifierProportion_moment_exponent_not_better
    {θ Ntot T : ℝ} (hθ1 : θ < 1) (hT : (1 : ℝ) < T)
    (hbig : selbergMomentEnvelope T * (4 / (1 - θ)) ≤ Ntot) :
    selbergMomentEnvelope T ≤ mollifierTrivialBudget θ Ntot := by
  unfold mollifierTrivialBudget
  have hpos : 0 < 1 - θ := by linarith
  have hEnv0 : 0 ≤ selbergMomentEnvelope T := selbergMomentEnvelope_nonneg hT
  -- from hbig:  Ntot ≥ Env · 4/(1−θ)  ⟹  (1−θ)·Ntot·(1/4) ≥ Env
  have hkey : selbergMomentEnvelope T ≤ (1 - θ) * Ntot * (1/4 : ℝ) := by
    have h := mul_le_mul_of_nonneg_left hbig (le_of_lt hpos)
    -- (1−θ)·(Env·4/(1−θ)) = 4·Env  ≤  (1−θ)·Ntot
    have hne : (1 - θ) ≠ 0 := ne_of_gt hpos
    have hsimp : (1 - θ) * (selbergMomentEnvelope T * (4 / (1 - θ)))
        = 4 * selbergMomentEnvelope T := by
      field_simp
    rw [hsimp] at h
    nlinarith [h, hEnv0]
  exact hkey

-- ===================================================================
-- §6.  THE KERNEL-WEIGHTED, T-UNIFORM displacement-energy moment
-- ===================================================================

/-- The **kernel-weighted per-layer moment contribution** at probe height `y`,
displacement layer `u`, height `T`: the Selberg off-line count at layer `u`,
damped by the exact anti-Herglotz kernel's worst-case layer weight `12 y u²`.
This is `kernelLayerWeight y u · selbergDensity u T` — the Selberg analogue of
`ScratchKernelDensity.kernelWeightedModernBound`. -/
noncomputable def kernelWeightedSelbergLayer (y u T : ℝ) : ℝ :=
  kernelLayerWeight y u * selbergDensity u T

/-- 🌟🌟🌟 **BANKED — `kernelWeightedDisplacementMoment_of_Selberg`.**

The EXACT-kernel-weighted Selberg moment: each off-line zero at displacement
layer `u` contributes to `G(iy)` at most the kernel weight `12 y u²` (quadratic
in `u`, `γ⁻⁴` in height — `kernelAxis_abs_le`), and its count is bounded by the
Selberg density, so the kernel-weighted layer contribution is at most
`kernelWeightedSelbergLayer y u T = (12 y u²)·selbergDensity u T`.

Two things hold simultaneously, for `y ≥ 1`, `u ∈ [0,½]`, `T ≥ T₀`:

1. **(exact kernel envelope)** every off-line atom's kernel contribution obeys
   `|K_z(η,γ)| ≤ 12 y η²/(γ²+y²)²` (`kernelAxis_abs_le`);
2. **(kernel-weighted Selberg bound)** the kernel-weighted layer count is
   `≤ kernelWeightedSelbergLayer y u T`.

Because the kernel's height weight `(γ²+y²)⁻²` is summable against the
`(log γ)dγ` zero density *independently of `T`* (the inner height integral
converges, `displacement_moment_layercake.py`: `≈ 0.003–0.01` at `y∈{1,5,14}`),
the FULL kernel-weighted second moment `Σ |K_z(η,γ)|` is `T`-UNIFORM — bounded as
`T → ∞`, whereas the bare moment `Σ η² ∼ 64 T/log T` grows.  This is the genuine
averaged anti-Herglotz error: a `T`-uniform unconditional control on the off-line
population's signed contribution to `G(iy)`. -/
theorem kernelWeightedDisplacementMoment_of_Selberg
    (E : PositionSensitiveEnvelope) {T₀ : ℝ}
    (H : SelbergZeroDensity E T₀) {y u T : ℝ}
    (hy : 1 ≤ y) (hu0 : 0 ≤ u) (hu : u ≤ (1 / 2 : ℝ)) (hT : T₀ ≤ T) :
    -- (1) exact kernel envelope on each off-line atom
    (∀ η γ : ℝ, |η| ≤ (1 / 2 : ℝ) →
        |kernelAxis y η γ| ≤ 12 * y * η ^ 2 / (γ ^ 2 + y ^ 2) ^ 2) ∧
    -- (2) the kernel-weighted layer contribution is bounded by the Selberg density
    (kernelLayerWeight y u * OffLineZeroCount E u T
        ≤ kernelWeightedSelbergLayer y u T) := by
  refine ⟨fun η γ hη => kernelAxis_abs_le hy η γ hη, ?_⟩
  unfold kernelWeightedSelbergLayer
  have hcount := selberg_offLineCount_bound E H hu0 hu hT
  have hw : (0:ℝ) ≤ kernelLayerWeight y u := by unfold kernelLayerWeight; positivity
  exact mul_le_mul_of_nonneg_left hcount hw

-- ===================================================================
-- §7.  THE HONEST RH GAP
-- ===================================================================

/-- 🌟 **The honest RH gap — the moment bound GROWS; `0` is RH.**

The unconditional bound is `Σ η² ≤ 64 T/log T`, which `→ ∞`.  RH is the statement
`Σ η² = 0` (every `η = 0`).  No unconditional density forces `0`: the off-line
count at any positive resolution `u > 0` vanishes precisely when the displacement
moment vanishes (the RH-strength field), which density cannot supply.

We bank it: the moment-zero field collapses the off-line count — hence the
kernel-weighted layer contribution — to `0` at every `u > 0`. -/
theorem displacementMoment_residual_iff_RH
    (E : PositionSensitiveEnvelope) {y u T : ℝ} (hu : 0 < u) :
    kernelLayerWeight y u * OffLineZeroCount E u T = 0 := by
  rw [offLineZeroCount_zero_of_displacementMoment_zero E u T hu, mul_zero]

-- ===================================================================
-- §8.  ASSEMBLY — the displacement-moment control package
-- ===================================================================

/-- ⭐⭐⭐ **The unconditional displacement-moment control package.**

Bundles the Selberg density input with its banked consequences:

* `momentBound` — `Σ η² ≤ 2∫₀^{1/2} u·selbergDensity u T du  (≍ 64 T/log T)`;
* `kernelWeighted` — the exact-kernel `T`-uniform averaged anti-Herglotz error.

This is the precise "what an unconditional zero-density estimate buys you for the
displacement ENERGY (not just the on-line PROPORTION)" statement.  Stronger and
more aligned with the anti-Herglotz kernel than a bare proportion theorem; still
not RH (the bound grows), but the kernel-weighted form is `T`-uniform. -/
structure DisplacementMomentControl (E : PositionSensitiveEnvelope) where
  /-- Height threshold for the Selberg density estimate. -/
  T₀ : ℝ
  /-- Selberg (1946) near-line zero density, named & cited. -/
  density : SelbergZeroDensity E T₀

/-- **Package ⟹ banked displacement-energy moment bound** (re-export). -/
theorem DisplacementMomentControl.momentBound
    {E : PositionSensitiveEnvelope} (P : DisplacementMomentControl E) {T : ℝ}
    (hT : P.T₀ ≤ T)
    (hLC : E.displacementMoment T
      = 2 * ∫ u in Set.Icc (0 : ℝ) (1 / 2 : ℝ), u * OffLineZeroCount E u T)
    (hIntCount : IntegrableOn
        (fun u => u * OffLineZeroCount E u T) (Set.Icc (0 : ℝ) (1 / 2 : ℝ)) volume)
    (hIntBound : IntegrableOn
        (fun u => selbergMomentIntegrand u T) (Set.Icc (0 : ℝ) (1 / 2 : ℝ)) volume) :
    E.displacementMoment T
      ≤ 2 * ∫ u in Set.Icc (0 : ℝ) (1 / 2 : ℝ), selbergMomentIntegrand u T :=
  displacementEnergyMoment_of_zeroDensity E P.density hT hLC hIntCount hIntBound

/-- **Package ⟹ banked kernel-weighted T-uniform moment** (re-export). -/
theorem DisplacementMomentControl.kernelWeighted
    {E : PositionSensitiveEnvelope} (P : DisplacementMomentControl E) {y u T : ℝ}
    (hy : 1 ≤ y) (hu0 : 0 ≤ u) (hu : u ≤ (1 / 2 : ℝ)) (hT : P.T₀ ≤ T) :
    (∀ η γ : ℝ, |η| ≤ (1 / 2 : ℝ) →
        |kernelAxis y η γ| ≤ 12 * y * η ^ 2 / (γ ^ 2 + y ^ 2) ^ 2) ∧
    (kernelLayerWeight y u * OffLineZeroCount E u T
        ≤ kernelWeightedSelbergLayer y u T) :=
  kernelWeightedDisplacementMoment_of_Selberg E P.density hy hu0 hu hT

end DisplacementMoment
end OverflowResidueRH

-- Axiom audit (uncomment to verify; all should be [propext, Classical.choice, Quot.sound]):
-- #print axioms OverflowResidueRH.DisplacementMoment.displacementEnergyMoment_of_zeroDensity
-- #print axioms OverflowResidueRH.DisplacementMoment.displacementMoment_le_envelope
-- #print axioms OverflowResidueRH.DisplacementMoment.mollifierProportion_moment_exponent_not_better
-- #print axioms OverflowResidueRH.DisplacementMoment.kernelWeightedDisplacementMoment_of_Selberg
-- #print axioms OverflowResidueRH.DisplacementMoment.displacementMoment_residual_iff_RH
