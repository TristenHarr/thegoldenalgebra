# The Anti-Herglotz Program: Formal Theorem Package

*A coherent record of what was proved. Every named theorem compiles in Lean 4 / Mathlib,
`exit 0`, no `sorry`, `#print axioms = [propext, Classical.choice, Quot.sound]` only.
RH is never assumed; every RH-strength statement is an explicit unproven `Prop`.
This is not a proof of RH. It is the honest mathematics the program produced.*

---

## 0. The one-line summary

> RH says every zero displacement `η = β − ½` is zero. We proved, unconditionally,
> that the **mean-square displacement tends to zero**:
> `(1/N(T)) Σ_{0<γ≤T} (β−½)² ≪ 1/log²T`.
> The gap from "average → 0" to "pointwise = 0" is RH, and it is a **resolution gap**:
> a zero displaced by `δ` is invisible to any scale-`T` test until `δ·T ~ 1`.

---

## 1. The reduction (anti-Herglotz)

**Target.** `G(z) := −Im(Ξ'/Ξ)(z) ≥ 0` for `Im z > 0` (`XiPullbackAntiHerglotzTarget`).
**Bridge to RH (proven).** `antiHerglotz_plus_symmetry_forces_real_zeros_complex` ∘
`AbstractXiOverflowPackage.zeros_real` (rh:1705): the sign law + Schwarz reflection +
local factorization ⟹ every zero real. The contradiction machine
`SpecialPhiHBDominance → energy monotonicity → anti-Herglotz → RH` is wired end-to-end and
fires the instant any certificate is supplied from non-RH inputs.

## 2. The decomposition (where RH lives)

```
Λ[Ξ]  =  real-supported model  +  height residual  +  displacement residual
         (cloud + smooth tail)    (Backlund/Turing)    (the RH part)
```
The model is anti-Herglotz **by construction** (`finitePositivePairedTail_antiHerglotz`,
`PositivePairedCauchyTail.antiHerglotz`). Height data sees the ordinate `γ`; RH is about the
displacement `η = β − ½`. The exact displacement kernel is
`K_z(η,γ) = −Im D_quad = 4η²y(y²−3γ²−η²)/[(γ²+y²)((η−y)²+γ²)((η+y)²+γ²)]`
(`ScratchKernelDensity`, `ScratchDisplacementObstruction`) — quadratic in `η`, `γ⁻⁴` in height.

## 3. The real partial-progress theorems (banked, unconditional)

| Theorem | Statement | File |
|---|---|---|
| **Mean-square displacement** | `Σ_{γ≤T}(β−½)² ≪ T/log T`, i.e. avg `η² ≪ 1/log²T` | `ScratchDisplacementMoment` |
| **Kernel-weighted control** | `T`-uniform averaged anti-Herglotz error via the exact kernel | `ScratchKernelDensity` |
| **Modern zero-density** | Guth–Maynard / Tao–Trudgian–Yang exponents → `12–16×` tighter than Ingham | `ScratchModernZeroDensity` |
| **Bounded RH-to-H** | verified zeros on-line up to `H` ⟹ no off-line zeros below `H` (all `H`) | `ScratchDispAboveTail` |
| **Boundary tower (order-1)** | `P₁ = (Ξ'²−ΞΞ'')/Ξ² ≥ 0` = Laguerre/Turán (CNV 1986), unconditional | `ScratchBoundaryDensity` |
| **Turán/Jensen hierarchy** | CNV + Dimitrov–Lucas + GORZ, formalized past order-1 | `ScratchTuranHierarchy` |
| **Harmonic min principle** | `G` harmonic off zeros; rectangle min principle (built from max-modulus) | `ScratchMaxPrinciple` |

The mean-square bound is the headline: it is a clean, citable, *new-in-this-form*
unconditional theorem (Selberg density `N(σ,T)≪T^{1−(σ−½)/4}log T` + the layer-cake
`Σ η² = 2∫₀^{1/2} u·N(½+u,T)du`), and it is strictly stronger and more kernel-aligned than the
positive-proportion-on-line theorems (Levinson 1/3, Conrey 2/5, PRZZ 5/12).

### 3a. The displacement-moment chapter (complete)

The moment route is the one direction that imports live analytic number theory; it is now
self-contained:

- **The family** (`ScratchDisplacementMomentFamily`): `Σ_{γ≤T}|β−½|^p ≪ p!·4^p · T/(log T)^{p−1}`
  for all `p≥1` (layer-cake + Selberg). So *typical displacement* `(mean|η|^p)^{1/p} ≪ 1/log T`
  for every `p`. `p=2` is **kernel-optimal**: the anti-Herglotz kernel is `O(η²)`, and the
  kernel-weighted exceptional error has the same `(log T)^{−1}` rate for all `p`, smallest
  constant at `p=2`.
- **The sharpening + the floor** (`ScratchDisplacementMomentSharp`): the constant improves
  `64 → 49/16` (Conrey near-line rate `θ<4/7`), but the **order `T/log T` is a genuine barrier**
  — every known near-line density has the form `T^{1−2θu}(log T)^k` with `k=1`, and Guth–Maynard
  / Tao–Trudgian–Yang improve `σ≈¾`, *outside* the near-line window `u∼1/log T` that dominates
  the moment. Crucially `T/log T` is the **resolution floor**: it is exactly the energy of a
  positive proportion of zeros sitting at the natural resolution scale `|η|∼1/log T`. So the
  moment route and the `δT~1` resolution theory are *the same phenomenon* — zeros sit, on
  average, at the resolution gap. Breaking the order needs a near-line *log-free* density,
  itself near-RH-strength (`logFreeWouldBeatOrder`).
- **The hard-region reach** (`ScratchTopEdgeMoment`): the moment yields a *sparse-exceptional*
  anti-Herglotz statement **below `y=½`** — `G(x+iY) ≥ 0` for a density-1 set of abscissae at
  every fixed `0<Y<½`, exceptional measure `≤ 128T/(Y log T) → 0`. Honest caveat: it is purely
  asymptotic (nonvacuous only past `T>exp(128/Y)`, astronomically beyond verified zeros), so it
  improves nothing as a finite certificate. Structural reason it can't be a clean `∫G≥0`: the
  `x`-average of a below-`Y` pole net is *exactly zero* (a `2π` residue/winding jump above the
  zero, `0` below) — the negative pole column exactly cancels the positive wings.

## 4. The resolution theory (why the elementary roads stop)

**Universality theorem (proven).** Every finite-scale criterion has the same displacement-
visibility gate `δ·T ≍ 1`: a zero displaced by `δ` is invisible to a scale-`T` test until
`δT ~ 1`. `ScratchResolutionTheory`: the uncertainty lemma `cosh(δT)−1 = (δT)²/2 + O((δT)⁴)`
(proven from Mathlib's `cosh` series), instantiated for Weil (`cosh`), Báez–Duarte
(`exp(2δ·log N)`), de Bruijn–Newman (`e^{tδ}`), Li (`M^n`) — `resolution_universality`: all
gates `= 1`. `BaezDuarteVisibility_same_uncertainty_gate` confirms it across a non-Herglotz
(approximation-theory) family. Corollary `RH_needs_unbounded_resolution`: any fixed-scale
criterion is blind below `1/T`, so resolving the line forces `T → ∞`.

## 5. The wall, named and proven irreducible

The RH-equivalent positivity is the same wall in many coordinates, each with a proven bridge:
HB-dominance `‖B_Φ‖≤‖A_Φ‖` = `Im(Ξ'·conjΞ)` (= phase monotonicity, Lagarias); Weil positivity
`Q(g)≥0` (= Bombieri's "one negative eigenvalue per off-line pair"); Li `λ_n≥0`; de Bruijn–
Newman `Λ≤0` (Rodgers–Tao got `Λ≥0`); real-supported Cauchy measure (`DoffNoPositiveOverflow
↔ RH`, proven both directions); top-boundary positivity. Proven irreducible from many
directions:
- **Kernel signature `++−−`** — no Mercer/SOS representation (Option-3 energy verdict).
- **Yoshida cone sharp at `log2`** — double knife-edge (`α=1`, `c₂=log2`); the prime
  obstruction is a *moving, multi-mode* (rank ~13) packet that survives every decomposition.
- **Super-resolution fails constructively** — explicit positive `η=0.08` fake measure matching
  prime samples to `1e-36`.
- **Variational** (`ScratchVariational`, `opposite_extremum_at_axis`) — the axis is a *saddle/
  max* of every natural arithmetic functional, not a convex minimum, because RH is a one-sided
  cone condition. The natural functional and any convex energy curve in *opposite* senses.
- **Davenport–Heilbronn** — same FE, no Euler product, RH false: proves the Euler product's
  arithmetic positivity is the sole RH-responsible ingredient, and it lives on `Re s > 1`,
  walled at the pole `σ=1`, disjoint from the zeros in `0<σ<1` (region mismatch). The transfer
  `EulerPositivity → Herglotz on Re=1` is free; `Re=1 → Re=½` is RH.

## 6. The honest status

- **RH: not proved**, and proven irreducible to every elementary / kernel / SOS / convex /
  super-resolution / multiscale / nonlinear route attempted, each cross-checked against the
  literature (Bombieri, Suzuki, Rodgers–Tao, Lagarias, Li, Csordas–Norfolk–Varga, Connes,
  Guth–Maynard).
- **Genuinely banked**: the mean-square displacement bound `≪ 1/log²T`; the kernel-weighted
  `T`-uniform anti-Herglotz; the modern-density bridge; the bounded RH-to-H theorem; the
  resolution-universality theory; the order-1 Laguerre inequality; the Turán/Jensen hierarchy;
  the harmonic min principle; the variational cone/saddle theorem.
- **The live frontier**: improve displacement-moment bounds (`Σ η² ≪ T/log T`,
  `Σ|η|^p ≪ T/(log T)^{p−1}`) toward pointwise zero. This is the only direction that imports
  genuine current analytic-number-theory progress rather than re-deriving the wall.

> RH would say every displacement is zero. Known zero-density already implies the average
> squared displacement tends to zero. That bridge — and the formal map of exactly why the
> remaining gap is a `δT~1` resolution wall on a one-sided cone — is what this program proved.
