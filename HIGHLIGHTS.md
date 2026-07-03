# Hey — here's what you'll find formalized in here

This repo is a large exploratory Lean 4 (Mathlib, toolchain v4.31.0-rc1) campaign around the
Riemann Hypothesis. **We did not prove RH and don't claim to** — every RH-strength statement
is an explicit named hypothesis, never a hidden axiom. But along the way a lot of classical
analytic number theory and complex analysis got formalized that (as far as we can tell) isn't
in Mathlib yet. If any of this is useful to you, pull it out — that's why we're posting it.

`lake build` compiles the main targets clean. Files carry `#print axioms` audits at the
bottom; the honest status ledgers are `GoldenAlgebra/STATUS.md`, `RH_THEOREM_PACKAGE.md`,
`RH_ATTACK_SUMMARY.md`, and a self-inflicted referee report in `NOVELTY_AUDIT.md`.

## 1. The Hadamard pipeline for the Riemann ξ — unconditional (`Scratch.lean`, `ScratchG3Close.lean`)

Built directly on Mathlib's `completedRiemannZeta₀`; every item below is a compiled theorem
with no hypotheses and no project axioms (`#print axioms` = the three standard ones):

- **An entire Riemann ξ**: `entireRiemannXi s = ½(s(s−1)Λ₀(s) + 1)` — entire, functional
  equation `ξ(1−s) = ξ(s)`, `ξ(0) = ½`, zero set = zeros of the completed zeta off `{0,1}`.
- **Global order-1 growth**: `‖ξ(z)‖ ≤ exp(A·‖z‖·log‖z‖)` for `‖z‖ ≥ 4`
  (`exists_norm_entireRiemannXi_le_exp_global`). The critical-strip piece is bounded via the
  Mellin/theta-kernel representation of `Λ₀` — no complex Stirling needed.
- **A Riemann–von Mangoldt-type zero count**: the ξ-zero divisor mass in a disk of radius r
  is `O(r log r)` (`xi_zero_count_bigO`), via Jensen (`AnalyticOnNhd.sum_divisor_le`).
- **`xi_zero_invSq_summable`**: `Σ_ρ 1/‖ρ‖² < ∞` over the ξ-zeros, by a reusable
  dyadic-shell engine (`summable_inv_sq_of_shellCard` / `_of_ballCount`).
- **`xi_genus1Product_LU`**: the genus-1 Hadamard product `∏_ρ (1−s/ρ)e^{s/ρ}` over ξ's
  zeros converges locally uniformly on ℂ.
- Hadamard structural steps, proven in general form: zero-free entire ⟹ `exp` of an entire
  function (via a primitive of `f'/f`); Borel–Carathéodory + generalized Liouville
  (entire + linear growth ⟹ affine); **two entire functions with matching zero orders have
  an entire zero-free quotient** (via Mathlib's meromorphic normal form); order of a finite
  product = sum of orders.
- The final assembly (`ScratchHadamardPackage.lean`): ξ = (genus-1 product)·C·e^{a+bz},
  with the three remaining inputs (multiplicity-index summability, order matching, and a
  genus-1 minimum-modulus estimate) isolated as named hypotheses. The minimum-modulus
  ingredient has its Cartan-lemma core proven (see §4).

## 2. Unconditional two-sided Stirling-type bounds for the complex Γ (three files)

Mathlib has no complex Stirling, no `arg Γ` asymptotics, no Riemann–Siegel theta. These
files build a big chunk of that from scratch:

- **`ScratchGammaDecay.lean`** — the exact identity `‖Γ(½+it)‖² = π/cosh(πt)` (from the
  reflection formula), sharp two-sided bounds
  `√π·e^{−π|t|/2} ≤ ‖Γ(½+it)‖ ≤ √(2π)·e^{−π|t|/2}`, and the two-sided
  `|sinh(πt)| ≤ ‖sin(π(σ+it))‖ ≤ cosh(πt)` machinery.
- **`ScratchBaseStrip.lean`** — **fully unconditional** Stirling-type upper bound on the
  strip: `‖Γ(w)‖ ≤ A₀·(Im w)^{Re w−½}·e^{−(π/2)Im w}` for `Re w ∈ [1,2]`, `Im w ≥ 1`, with
  an explicit constant. Method: bound the comparison function `Γ(s)·e^s·s^{½−s}` via
  Mathlib's `PhragmenLindelof.vertical_strip`, edge bounds from the exact critical-line
  identity + Γ-recurrence, plus a Jordan-inequality recovery-factor estimate.
- **`ScratchBandUpper.lean`** — Γ-recurrence + conjugation extend that to the full band
  `Re ∈ [−1,3]`, `|t| ≥ 1`. Combined with `ScratchGammaDecay`'s reflection argument this
  also gives the matching **lower** bound `c·|t|^{σ−1/2}e^{−π|t|/2} ≤ ‖Γ(σ+it)‖` on
  `σ ∈ [¼,2]` — i.e. genuine two-sided vertical-line Stirling, unconditionally.

Related Γ-phase work: the Riemann–Siegel theta asymptotic
`θ(T) = (T/2)log(T/2π) − T/2 − π/8 + O(1)` with the entire leading algebra proven
(`ScratchArgGammaStirling`), the Weierstrass arg-series `arg(1+z/k) = arctan((T/2)/(k+¼))`
with summable defect (`ScratchBinetSeries`), Binet kernel positivity
`1/(e^t−1) − 1/t + ½ ≥ 0` by a clean two-derivative argument (`ScratchBinet`), and a fully
proven uniform bound `|Lcollect T| ≤ π+1` for the collected Binet phase limit
(`ScratchCollectBound`). The only remaining axioms in this cluster are the Binet integral
identity itself and one branch-cut membership fact — both documented as genuine Mathlib gaps.

## 3. An argument principle for rectangles (`ScratchAP_*.lean`, `ScratchResidue`, `ScratchGoursat`)

Mathlib has Goursat on one rectangle and the circle Cauchy formula, but no rectangle
argument principle, no winding number, no "continuous argument along a path". These files
build the pieces:

- `ScratchAP_SingleZero`: **`∮_{∂R} f'/f = 2πi·m`** for an order-m interior zero — the
  residue computed edge-by-edge with the principal log, with explicit branch-cut handling
  (`log w − log(−w) = ±πi` on the left edge). No axioms.
- `ScratchAP_GlobalFactor`: from Mathlib's local factorization, the **global**
  `f = (z−a)^m·g` on a closed rectangle with `g` analytic and nonvanishing (removable
  singularity construction). No axioms.
- `ScratchAP_Deformation` / `ScratchAP_DeformN`: contour deformation — boundary integral
  over a rectangle with finitely many interior singularities = sum of small-square
  integrals (four-strip cancellation, horizontal-split additivity, then a clean induction
  over a `DeformChain`). No axioms.
- `ScratchAP_ArgVar`: `Δarg = Im ∮ f'/f` around a closed polygonal contour (FTC-2 with the
  principal log on slit-plane edges, telescoping; `Re ∮ = 0`).
- A fun proven *negative* result (`ScratchAP_SharpCount`): with only the exponent-1 strip
  bound on ζ, **no single Jensen disk spanning `[½,2]` can even have outer radius > inner
  radius** — the naive Backlund route provably yields nothing, pinning why convexity is
  needed.

## 4. Phragmén–Lindelöf, the ζ convexity bound, and Backlund counting (`RHConvexityTower` → `RHCountWiring`)

- **`halfStrip_PL`** — a half-strip Phragmén–Lindelöf maximum principle (constant bounds on
  three edges + double-exponential growth allowance `c < π/(u−l)`), proven from scratch with
  the classical ε-multiplier trick. Mathlib has full-strip PL; the half-strip three-edge
  version appears to be new.
- **`tWeightedPL_linear_sharp`** — sharp linear-interpolation PL on a vertical strip: edge
  bounds `|t|^α`, `|t|^β` interpolate to `|t|^{α(u−σ)/(u−l)+β(σ−l)/(u−l)}` inside, with the
  weight `exp(−p(s)·Log(−is+λ))` machinery fully proven.
- Chained to the classical **convexity bound `‖ζ(½+it)‖ ≤ C|t|^{1/4}`** and a
  Backlund–Jensen zero count with coefficient `(9/32)/log 16 ≈ 0.1014` — modulo a handful
  of named residuals (a lower-half reflection step, ζ edge data, and a good-height value
  bound), each listed at the file bottom via `#print axioms`.
- **`riemannZeta_conj`** (`ScratchLowerReflect.lean`) — `ζ(conj s) = conj(ζ s)` for **all**
  `s`, proven via the identity theorem on `{1}ᶜ` from the real-coefficient Dirichlet series
  (we couldn't find this in Mathlib). It then discharges the lower-half reflection residual
  above outright for the function the chain actually uses (`(s−1)ζ(s)` is
  conjugate-symmetric), via a small abstract lower-from-upper reflection lemma.
- **A harmonic minimum principle** (`ScratchMaxPrinciple.lean`) — Mathlib has max-modulus
  but no harmonic max/min principle; we derive one: if `h` is holomorphic on a bounded `U`
  (DiffContOnCl) and `−Im h ≥ C` on the frontier, then `−Im h ≥ C` on the closure — by
  applying max-modulus to the probe `exp(−i·h)`, whose modulus is `exp(Im h)`.
- **`ScratchCartan.lean`** — the elementary **Cartan lemma** radius-selection pigeonhole,
  fully proven with Lebesgue measure: bad radii have measure `≤ 2Σδᵢ`, so a good circle
  avoiding all exceptional disks exists; plus the per-factor lower bound
  `log|1−z/ρ| ≥ log δ − log|ρ|`. Cartan's lemma is absent from Mathlib.
- **`ScratchEulerMaclaurin.lean`** — Abel-summation Euler–Maclaurin machinery: the identity
  `Σ_{k∈(n,m]} g(k) = g(m)(m+1) − g(n)(n+1) − ∫ g'(t)(⌊t⌋+1)dt` for the arctan phase
  function, and the uniform remainder bound `|R| ≤ π/2` via a total-variation estimate —
  all proven, no axioms.
- **Quantitative far-tail decay** (`ScratchLogSumCore.lean`) — from a ball count
  `N(R) ≤ A·R·log R`, the tail `Σ_{‖ρ‖≥X} 1/‖ρ‖² ≤ 12A·(log X)/X` (dyadic shells with the
  dominating series summed in closed form), and hence the far-zeros genus-1 log-sum bound
  `Σ_far log|E₁(z/ρ)| ≥ −6A‖z‖log(2‖z‖)` — the order-1 far half of Hadamard's
  minimum-modulus argument, fully proven; the near-zeros half is exactly the Cartan
  circle-avoidance, whose measure-theoretic core is the `ScratchCartan` lemma above.
- **Multiplicity-aware Hadamard index** (`ScratchMultIndex`, `ScratchMultHadamard`) — the
  simplicity-of-zeros assumption is *eliminated* from the ξ factorization: index the
  product by `Σ ρ, Fin (analyticOrderNatAt ξ ρ)` and prove the hitting count of that index
  at every point equals `analyticOrderAt ξ` — so the quotient `ξ/∏` is entire with no
  simple-zeros hypothesis anywhere.

## 5. Honest RH-facing theorems (conditional, with the conditions in plain sight)

- **Bounded RH below H** (`ScratchBoundedRHtoH`, `ScratchBandFromVerified`,
  `ScratchDispAboveTail`): *verified zeros on the critical line up to height H ⟹ no
  off-line zeros below H*, with the zero-location input consumed at exactly one point, the
  per-zero displacement bounds and the Basel-tail convergence proven, and the remaining
  inputs (SOS/slab model margins, an RvM tail-spacing field) named RH-independent
  hypotheses.
- **The displacement obstruction** (`ScratchDisplacementObstruction`) — a fully proven
  honesty certificate: the displacement field of a functional-equation quadruple has a
  vanishing linear term at the critical line (it's a genuine critical point), a
  **sign-indefinite** quadratic coefficient with explicit witnesses, and `Im D → +∞`
  approaching an off-line pole — so the one-sided displacement gate is *provably false*
  given any off-line zero. The RH-strength hypothesis is not just unproven, it's shown to
  be exactly equivalent to what it claims to deliver.
- **de Branges / Hermite–Biehler route** (`ScratchDeBranges`, `ScratchHBDominance`): HB
  structure function machinery with the proven bridge *HB + Ξ = (E+E♯)/2 ⟹ all zeros
  real*, the integral identity that the one-sided Laplace transform is the A-partner of the
  cosine transform, and RH ⟺ Λ = 0 given Rodgers–Tao — with the single modulus inequality
  `‖B_Φ‖ ≤ ‖A_Φ‖` left as the honestly-named open Prop (it *is* RH).
- **Boundary/Laguerre tower** (`ScratchBoundaryDensity`): the Cauchy–Riemann boundary
  asymptotic `−Im(Ξ'/Ξ)(x+iy) = y·P₁(x) + O(y³)` with `P₁ = (Ξ'² − ΞΞ'')/Ξ²` proven
  end-to-end, plus a proven counterexample showing order-1 boundary positivity is
  necessary-but-not-sufficient for the global wall.
- **The capstone ledger** (`ScratchFinalCapstone`): the single theorem that assembles
  "RH in this formalization" from four typed hypothesis packages, with the complete honest
  residual list in the header. Nothing is hidden: `#print axioms` shows only the standard
  three.

## 6. Zero-density → displacement moments (`ScratchDisplacementMoment*`)

The layer-cake bridge `Σ_{γ≤T}(β−½)^p = p∫ u^{p−1}·N_off(u,T)du` wired against
Selberg/Jutila/Conrey near-line densities (carried as named, cited Props — they're not in
Mathlib), giving `Σ(β−½)² ≪ T/log T` and the general-p family, with proven envelope
comparisons (Conrey's 49/16 beats Selberg's 64; a log-free near-line density is exactly
what would break the `T/log T` order). Honesty note: our own `NOVELTY_AUDIT.md` classifies
the underlying bound as classical folklore (Selberg 1946 via Littlewood's lemma) — the
formalized layer-cake wiring is the contribution, not the theorem.

Two smaller items in the same cluster: the **modern zero-density exponent curve** is a Lean
function (`ScratchModernZeroDensity`: Ingham `3/(2−σ)` glued to Guth–Maynard `15/(3+5σ)`,
with continuity at `σ = 7/10` with value `30/13`, GM strictly below Ingham past the
breakpoint, and the budget comparison against `A = 3` — all *proven*; the density estimates
themselves stay named, cited Props). And a fully proven **termwise sign result**
(`ScratchKernelRegion`): at any probe `iy` (`y ≥ 1`), each zero's own on-line reference atom
`4y/(γ²+y²)` dominates its exact displacement-kernel penalty (`|K| ≤ 12yη²/(γ²+y²)²`,
`γ ≥ 14`, `|η| ≤ ½`) with ≥ 99.6% margin — per-zero, RH-free.

## 7. The honest big picture

`GoldenAlgebra/rh.lean` (~100k lines) plus the scratch stack reduce RH to single named
positivity statements in ~10 classical languages (Weil positivity, Li's criterion,
Hermite–Biehler, de Bruijn–Newman, boundary positivity of `−Im Ξ'/Ξ`, Báez-Duarte), with
proven Lean bridges between the faces — and every final positivity left as an explicit
unproven `Prop`, because each of them *is* RH. The repo's own status docs say this plainly:
"the file has correctly reduced RH to RH." What survives independently of that project goal
is the infrastructure above.

Caveats a careful reader should know: a few scratch files use `native_decide` for rational
table lookups (182 verified zero brackets); scratch files can't import each other, so some
results are transplanted between files as named `axiom`s with their provenance documented
(the consolidated `RH*` library targets in the lakefile remove these seams for the main
chain); and one superseded file (`ScratchBinetPhaseDischarge`) contains an axiom the project
itself later proved false and replaced with a sound limit-route proof
(`ScratchBinetPhaseFixed`, `ScratchCollectBound`) — kept as an honest record.

Start with `Scratch.lean` (the ξ/Hadamard pipeline), the `ScratchAP_*` files (rectangle
argument principle), and the Γ trio (`ScratchGammaDecay` / `ScratchBaseStrip` /
`ScratchBandUpper`); they're the most self-contained and the most upstreamable.
