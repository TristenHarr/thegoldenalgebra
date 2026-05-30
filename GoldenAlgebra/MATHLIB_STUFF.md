# MATHLIB_STUFF.md — what the v4.21→v4.31 upgrade buys us

> **Audience:** anyone driving `rh.lean` forward.
> **Companion to:** the architecture header inside `rh.lean` (§§1–17) and the Proof Map.
> **Pinned versions (verified):** Lean `v4.31.0-rc1`, Mathlib `2e770eae` (master, commit dated 2026-05-29 — bleeding edge).
> **Method:** every declaration below was located in the *pinned* checkout under
> `.lake/packages/mathlib/Mathlib/`. Signatures marked ⚠ are paraphrased from a survey pass and
> should be re-read at the source line before you lean on them; names + file paths are reliable.

---

## 0. TL;DR — the three landings that matter

The upgrade pulled in Mathlib master (commit dated 2026-05-29). Three brand-new files attack our
two hardest obligations directly:

1. **`Mathlib/Analysis/Complex/JensenFormula.lean`** ⭐NEW — Jensen's formula for meromorphic
   functions *plus* a packaged **zero-counting bound** `AnalyticOnNhd.sum_divisor_le`. This is the
   classical engine behind the Riemann–von Mangoldt `N(T)` estimate that
   `EntireXiLeftHalfLogDerivSignTarget` (our "analytic mountain", §17.A) reduces to.

2. **`Mathlib/NumberTheory/LSeries/ZetaZeros.lean`** ⭐NEW — `riemannZetaZeros` with
   `isDiscrete`, `isClosed`, and `IsCompact.inter_riemannZetaZeros_finite`. Makes the discrete zero
   measure `dN` in §16.1 (`FluctuationMeasureData`) *well-defined and locally finite for free*,
   instead of an assumed hypothesis.

3. **`Mathlib/Analysis/Complex/Poisson.lean`** ⭐NEW — a Herglotz–Riesz kernel
   (`herglotzRieszKernel`, `re_herglotzRieszKernel_le`). We hand-rolled the entire anti-Herglotz
   sign layer (§§1–6); we may now *ground* it in Mathlib's Poisson/Herglotz representation rather
   than carry it as bespoke machinery.

The rest of this doc is the inventory, organized by **which `rh.lean` obligation each asset attacks**.

---

## 2. The analytic mountain → **Jensen's formula + a ready-made zero-count bound** ⭐NEW

**File:** `Mathlib/Analysis/Complex/JensenFormula.lean` (did **not** exist in v4.21).

This is the highest-leverage landing for us. Our `EntireXiLeftHalfLogDerivSignTarget` (§17.A) — the
single genuine analytic input — reduces (per the recent shell-majorant commits and the project
memory note) to a **classical Riemann–von Mangoldt log zero-count**. Jensen's formula is *the*
classical tool for that, and Mathlib now ships it for meromorphic functions, with a zero-counting
corollary already packaged:

| name | line | what it gives us |
|---|---|---|
| `MeromorphicOn.circleAverage_log_norm` | 307 | Jensen: `circleAverage (log‖f‖) c R = log‖trailingCoeff‖ + Σ over divisor` |
| `AnalyticOnNhd.circleAverage_log_norm` | 375 | analytic case (no pole term) |
| **`AnalyticOnNhd.sum_divisor_le`** | 389 | ⭐ **bounds `Σ` over the divisor (the zero count) by a `log M` modulus term** — this *is* a Jensen-style `N(R) ≤ …` inequality, the RvM upper bound in disguise |
| `circleAverage_log_norm_factorizedRational` | 232 | Jensen for an explicit `∏ (·−ρ)^d` — directly matches our Hadamard genus‑1 product |
| `countingFunction_finsum_eq_finsum_add` | 275 | counting-function bookkeeping over a divisor `D : ℂ → ℤ` |
| `circleAverage_re_herglotzRieszKernel_mul_log` | 209 | Poisson–Jensen with the Herglotz kernel |

**Why this is the unlock:** instead of building `N(T) − N₀(T)` bounds from a contour integral we'd
have to assemble ourselves (there is still **no argument principle** in Mathlib, §8), we can feed our
explicit Hadamard genus‑1 product (§17 / the `rh.lean:74000+` block) into
`circleAverage_log_norm_factorizedRational` / `sum_divisor_le` and read off a zero-count inequality.
That is precisely the shape `ZeroCountingFluctuationBound` / `TuringStyleSBound` (§13, CXLIII/CXLIX-D)
want as input.

**Action:** wire `AnalyticOnNhd.sum_divisor_le` (applied to `entireRiemannXi`) into a constructor for
`TuringStyleSBound` / `HalfLogPlusHalfSBound`. The `(C, D)` closed form (§13, CL) already accepts a
crude `|S(u)| ≤ C·log u + D`; Jensen gives exactly that crude bound.

---

## 3. The discrete zero measure → **`ZetaZeros` is now a Mathlib citizen** ⭐NEW

**File:** `Mathlib/NumberTheory/LSeries/ZetaZeros.lean` (new).

| name | line | use |
|---|---|---|
| `riemannZetaZeros` | 33 | `def := riemannZeta ⁻¹' {0}` |
| `mem_riemannZetaZeros` | 35 | membership rewrite |
| `isClosed_riemannZetaZeros` | 57 | zero set is closed |
| `isDiscrete_riemannZetaZeros` | 60 | **zeros are discrete** |
| `IsCompact.inter_riemannZetaZeros_finite` | 64 | **finitely many zeros in any compact** |
| `tendsto_riemannZeta_cofinite_cocompact` | 70 | zeros escape to ∞ |

**Why it matters:** §16.1's `FluctuationMeasureData` / `discreteZeroCounting` currently *assume* the
zero ordinates form a locally-finite multiset. `IsCompact.inter_riemannZetaZeros_finite` discharges
that for real — `N(T)` is a genuine finite count on `[0,T]`, so `dN` is a legitimate locally-finite
measure and the Stieltjes/Abel route (§4) has a real integrand. It also lets
`firstTenRiemannZerosFluctuationData` (§16.1-A) be generalized from a hard-coded 10-zero list to "the
actual zero set up to height T".

---

## 4. The Stieltjes-IBP fluctuation route → **Abel summation is fully shipped**

**File:** `Mathlib/NumberTheory/AbelSummation.lean` — the best-supported path for §16's
`∫ K_z dS = boundary − ∫ S·K' du` reduction (CXLIV–CL).

| name | line | shape |
|---|---|---|
| `sum_mul_eq_sub_sub_integral_mul` | 129 | general Abel: `Σ f(k)c(k) = f(b)C(b) − f(a)C(a) − ∫ f'·C` |
| `sum_mul_eq_sub_integral_mul` | 189 | `a=0` case |
| `sum_mul_eq_sub_integral_mul₀` | 211 | `c 0 = 0` case (skips the singularity) |
| `tendsto_sum_mul_atTop_nhds_one_sub_integral` | 281 | **improper / `atTop` limit version** — matches our `ImproperStieltjesConverges` (§16.2) |
| `tendsto_sum_mul_atTop_nhds_one_sub_integral₀` | 300 | `c 0 = 0` improper version |

Supporting IBP (also present, used by our CXLIV layer):
- `intervalIntegral.integral_mul_deriv_eq_deriv_mul`, `integral_deriv_mul_eq_sub`
  (`…/IntervalIntegral/IntegrationByParts.lean`).
- **Improper IBP on `(a,∞)`:** `integral_Ioi_mul_deriv_eq_deriv_mul`,
  `integral_Ioi_deriv_mul_eq_sub` (`…/Integral/IntegralEqImproper.lean`) — these directly produce the
  boundary-term-at-∞ + tail-integral form our `ImaginaryStieltjesTailIBPBound` is built around.
- `StieltjesFunction` + `.measure` (`…/Measure/Stieltjes.lean`) with `measure_Ioc/Icc/Ioo/Ico` if we
  prefer the measure-theoretic encoding over the function-level split.

**Recommendation:** keep the **function-level split** (§16.2-A `StieltjesPartialSplit`) and discharge
it with `tendsto_sum_mul_atTop_nhds_one_sub_integral₀`. Mathlib has **no Stieltjes-specific IBP** and
**no Euler–Maclaurin**, so don't wait for those; Abel summation is the supported road and it lands
exactly on our `S(u)·K'(u)` integrand.

---

## 5. Schwarz symmetry (open obligation **i**) → still our job, but the route is intact

`rh.lean:245` notes "Mathlib v4.21 lacks the conjugation lemma on `completedRiemannZeta`." **That is
still true in v4.31** — there is **no** `completedRiemannZeta_conj` / `…_star`. So obligation (i),
`hurwitzEvenFEPair_zero_f_modif_ofReal_target`, remains ours. The good news: every ingredient our
§17.B–C reduction uses is present and unchanged:

- **Theta-level conjugation** (the root of our Schwarz chain):
  `jacobiTheta₂_conj`, `jacobiTheta₂'_conj` (`…/JacobiTheta/TwoVariable.lean`),
  and the kernel `re_eq_add_conj` identities for `evenKernel` / `cosKernel`
  (`HurwitzZetaEven.lean:79,94`).
- **Functional equation** (entire, pole-subtracted): `completedRiemannZeta₀_one_sub`,
  `completedRiemannZeta_one_sub`, `differentiable_completedZeta₀`
  (`…/LSeries/RiemannZeta.lean`).
- Our own §17.B `mellin_star_ofReal` keystone is built from `integral_conj`, `Complex.cpow_conj`,
  `Complex.conj_ofReal` — all still present.

**Bottom line:** no *direct* zeta-conjugation lemma landed — but the `f_modif` route is **not** the
cheapest way to discharge this. **➡ See Pass-2 #2 (bottom of this doc): the identity-theorem route
kills obligation §17.C outright in ~15–20 lines** using `DifferentiableAt.conj_conj` +
`AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq` (both verified present). Treat the `f_modif`
identity below as the *fallback*, not the plan.

> **The spike paid off.** `completedRiemannZeta₀` / `entireRiemannXi` is real on ℝ and entire; the
> identity theorem gives `conj`-symmetry directly. Mathlib even ships the Schwarz-reflection
> differentiability lemma (`Analysis/Calculus/Deriv/Star.lean`). Details in Pass-2 #2.

---

## 6. The log-derivative engine → Mathlib's `logDeriv` API (use it, don't hand-expand)

**File:** `Mathlib/Analysis/Calculus/LogDeriv.lean`.

| name | use |
|---|---|
| `logDeriv_mul`, `logDeriv_div` | `Λ[fg]=Λf+Λg`, `Λ[f/g]=Λf−Λg` |
| **`logDeriv_prod`** | finite-product rule — **the fix for the `rh.lean:74265` block** (don't `field_simp` by hand) |
| `logDeriv_fun_zpow` | `Λ[f^n]=n·Λf` |
| `logDeriv_comp` | chain rule (matches our `XiPullback_logDeriv_chain_rule`) |
| **`AnalyticAt.tendsto_mul_logDeriv_simple_zero`** | at a simple zero, `(w−x)·logDeriv f w → 1` — this is *exactly* our §3 pole-witness behaviour, now available as a Mathlib lemma |

`AnalyticAt.tendsto_mul_logDeriv_simple_zero` is a strong candidate to **replace part of our
hand-rolled `LogDerivPoleWitnessLaw` / local-pole-decomposition machinery** (§§3–5) for the
simple-zero case.

---

## 7. Factorization at a zero (obligation §16.4) → fully supported, already discharged

§16.4-A already turns "every analytic non-degenerate zero admits a factorization" into a *theorem*
via `AnalyticAt.exists_eventuallyEq_pow_smul_nonzero_iff`. The surrounding order/divisor API is rich
and stable:

- **`Mathlib/Analysis/Analytic/Order.lean`:** `analyticOrderAt` (`ℕ∞`), `analyticOrderNatAt`,
  `AnalyticAt.analyticOrderAt_eq_natCast` (the `f z = (z−z₀)ⁿ·g z`, `g z₀ ≠ 0` characterization).
- **`Mathlib/Analysis/Meromorphic/`:** `meromorphicOrderAt` (`WithTop ℤ`, allows poles),
  `meromorphicOrderAt_eq_int_iff`, `MeromorphicNFAt` (normal form),
  **`MeromorphicOn.divisor`** (`Function.locallyFinsuppWithin U ℤ` — a real *divisor* object),
  `meromorphicTrailingCoeffAt`.
- **`Mathlib/Analysis/Meromorphic/FactorizedRational.lean`:** functions `∏ᶠ u, (·−u)^(d u)` with
  `Function.FactorizedRational.analyticAt` — pairs perfectly with our genus‑1 Hadamard product
  *and* with `circleAverage_log_norm_factorizedRational` (§2).
- Support: `Mathlib/Analysis/Analytic/IsolatedZeros.lean`, `Analysis/Analytic/Uniqueness.lean`
  (identity theorem — see the §5 spike).

This whole layer is the connective tissue between "our explicit Hadamard product" and "Jensen's
zero-count bound." It is **the spine of the close-out**: divisor (Meromorphic) → factorized rational
→ Jensen (`circleAverage_log_norm_factorizedRational`) → `sum_divisor_le` → `TuringStyleSBound`.

---

## 8. Anti-Herglotz sign law → can now be *grounded*, not just asserted ⭐NEW kernel

**File:** `Mathlib/Analysis/Complex/Poisson.lean` (the Herglotz/Poisson kernel is new).

| name | use |
|---|---|
| `herglotzRieszKernel c w z` | `((z−c)+(w−c))/((z−c)−(w−c))` — the Herglotz–Riesz kernel |
| `re_herglotzRieszKernel_le`, `le_re_herglotzRieszKernel` | **sign/bounds on its real part** (interior vs boundary) |
| `poissonKernel`, `poissonKernel_eq_re_herglotzRieszKernel` | Poisson kernel ↔ Re of Herglotz |
| `DiffContOnCl.circleAverage_re_herglotzRieszKernel_smul` | Poisson representation of a holomorphic `f` from boundary data |

Plus the harmonic-function bridge (`Mathlib/Analysis/Complex/Harmonic/Analytic.lean`):
`HarmonicOnNhd.exists_analyticOnNhd_ball_re_eq` (recover holomorphic `F` with `Re F = ` given
harmonic), `HarmonicAt.analyticAt`.

And the atomic sign facts our §2 cloud needs are all present in `Mathlib/Data/Complex/Basic.lean`:
- **`Complex.inv_im : z⁻¹.im = -z.im / normSq z`** — literally our atom
  `complex_real_root_residue_imag_nonpos` (`Im 1/(z−r) = −Im z/|z−r|² ≤ 0`).
- `Complex.div_im`, `Complex.add_im`, `Complex.normSq` (+ `normSq_nonneg`).
- Open half-planes: `Analysis/Complex/HalfPlane.lean` `isOpen_im_gt_EReal` / `isOpen_im_lt_EReal`;
  full `UpperHalfPlane` (`ℍ`) infra in `Analysis/Complex/UpperHalfPlane/`.

**Opportunity:** our anti-Herglotz layer (§§1–6) is self-contained and *proven*, so this is not a
must-fix. But if a reviewer wants the sign law tied to standard theory, the Poisson/Herglotz
representation now exists to do it, and `re_herglotzRieszKernel_le` is the off-the-shelf sign bound.

Also handy and new-ish: **Borel–Carathéodory** (`Analysis/Complex/BorelCaratheodory.lean`:
`borelCaratheodory`, `borelCaratheodory_zero`) bounds `‖f‖` from a bound on `Re f` — useful if the
sign-target proof needs to convert a real-part bound into a modulus bound on `Λ[Ξ]`.

---

## 9. Supporting cast (present, stable, reach for as needed)

- **Cauchy integral formula / circle integrals** (`Analysis/Complex/CauchyIntegral.lean`,
  `MeasureTheory/Integral/CircleIntegral.lean`): `circleIntegral`,
  `two_pi_I_inv_smul_circleIntegral_sub_inv_smul_of_differentiable_on_off_countable`, the
  `nᵗʰ`-derivative formula. Building blocks if we ever need a bespoke argument principle.
- **Liouville** (`Analysis/Complex/Liouville.lean`), **maximum modulus**
  (`Analysis/Complex/AbsMax.lean`), **open mapping** (`Analysis/Complex/OpenMapping.lean`).
- **Hadamard three-lines** (`Analysis/Complex/Hadamard.lean`:
  `HadamardThreeLines.norm_le_interpStrip_…`) — *not* the Hadamard product; it's the convexity bound.
- **Euler sine product** (`Analysis/SpecialFunctions/Trigonometric/EulerSineProd.lean`):
  `∏(1−z²/n²)=sin(πz)/(πz)` — a worked infinite-product template to mirror for our genus‑1 product.
- **`RiemannHypothesis`** is a Mathlib `def` (`…/LSeries/RiemannZeta.lean`): the canonical target to
  ultimately connect our `entireRiemannXi`-based statement to.

---

## 10. What is STILL absent (don't wait for it — plan to hand-roll or route around)

| missing | impact on us | mitigation |
|---|---|---|
| **Argument principle** `(1/2πi)∮ f'/f = #zeros−#poles` | can't count zeros by contour directly | **use Jensen** (`sum_divisor_le`, §2) — equivalent for the upper bound we need |
| **Residue theorem / residue defn** | — | `meromorphicTrailingCoeffAt` covers the trailing coeff we actually use |
| **Hadamard product / order-of-entire-function theory** | our genus‑1 product is hand-built | keep building it; `FactorizedRational` + `EulerSineProd` are the templates; Jensen consumes it without needing a general product theorem |
| **Herglotz/Nevanlinna/Pick *function class*** | our anti-Herglotz layer stays hand-rolled | fine — it's proven; kernel (§8) only needed if grounding is wanted |
| **`completedRiemannZeta` conjugation/Schwarz** | obligation (i) stays ours | finish §17.C, or try the identity-theorem spike (§5) |
| **Phragmén–Lindelöf**, **zero-free regions**, **Euler product for ζ** | not on our critical path | n/a |

---

## 11. Close-out playbook (priority order — using the new assets)

1. **Land the zero-count bound** (§2 + §7): feed `entireRiemannXi`'s genus‑1 product through
   `circleAverage_log_norm_factorizedRational` → `AnalyticOnNhd.sum_divisor_le` to produce a
   `|S(u)| ≤ C·log u + D` bound; package it as `TuringStyleSBound` / `HalfLogPlusHalfSBound`
   (constructors already exist, §13 CL). This is the core of the analytic mountain.
2. **Make the zero measure real** (§3): replace the assumed local-finiteness in
   `FluctuationMeasureData` with `IsCompact.inter_riemannZetaZeros_finite`.
3. **Run the Abel-summation IBP** (§4): discharge `StieltjesIBPDataFor.hmargin` via
   `tendsto_sum_mul_atTop_nhds_one_sub_integral₀`, closing `ZeroCountingFluctuationBound`.
4. **Finish Schwarz** (§5): the §17.C `f_modif` identity (or the identity-theorem spike).
5. (Optional) **Ground the sign law** (§8) in `herglotzRieszKernel` for reviewer-facing rigor.

Steps 1+2+3 together discharge `XiZeroCountingErrorMarginPackage` ⇒ `XiPullbackAntiHerglotzTarget`
(§13 CXXXVI), which is the last RH-strength input. Step 5 closes the last identity-only input. After
that the §17 Mathlib-grounded chain is end-to-end.

---

### Quick file map (pinned checkout)

```
Analysis/Complex/JensenFormula.lean        ⭐ zero counting (NEW)
Analysis/Complex/Poisson.lean              ⭐ Herglotz/Poisson kernel (NEW)
Analysis/Complex/BorelCaratheodory.lean    Re-bound → modulus-bound
NumberTheory/LSeries/ZetaZeros.lean        ⭐ riemannZetaZeros discreteness (NEW)
NumberTheory/LSeries/RiemannZeta.lean      completedRiemannZeta₀, FE, RiemannHypothesis
NumberTheory/LSeries/HurwitzZetaEven.lean  evenKernel/cosKernel conj, FEPair
NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean  jacobiTheta₂_conj
NumberTheory/AbelSummation.lean            Abel/partial summation (Stieltjes-IBP route)
Analysis/Calculus/LogDeriv.lean            logDeriv_prod, tendsto_mul_logDeriv_simple_zero
Analysis/Analytic/Order.lean               analyticOrderAt
Analysis/Meromorphic/{Order,Divisor,NormalForm,FactorizedRational}.lean  divisor & factorization
MeasureTheory/Integral/IntegralEqImproper.lean   improper IBP on (a,∞)
MeasureTheory/Measure/Stieltjes.lean       StieltjesFunction.measure
```

---
---

# Pass 2 — reuse & simplification audit: what existing Mathlib lets us *delete*

> Second sweep (5 parallel agents over both `rh.lean` and the pinned Mathlib). Question this time:
> **where does `rh.lean` hand-roll something Mathlib already ships?** Every lemma name + signature
> below was re-verified directly in the pinned source. Ranked by burden reduction. **Two of these
> are on the open-frontier critical path** (#1, #2) — they don't just shrink the file, they retire
> obligations.

## Scoreboard

| # | Win | rh.lean target | Mathlib asset | Est. lines | Effort |
|---|---|---|---|---|---|
| **1** ⭐⭐⭐ | Collapse the finite→infinite log-deriv Hadamard bridge | `~74240–74475` | `logDeriv_tprod_eq_tsum` | **~200–300** | Med |
| **2** ⭐⭐⭐ | **Kill the Schwarz obligation §17.C outright** | `~49979–50088` chain | `DifferentiableAt.conj_conj` + identity theorem | retires obligation; **~15–20 to add** | Low |
| **3** ⭐⭐ | Unify 4 multiplicity-specific pole decompositions into 1 | `594–637` | `AnalyticAt.analyticOrderAt_eq_natCast` | **~45→~5** | Med |
| **4** ⭐⭐ | Bulk `fun_prop`/`continuity` for manual deriv/cont proofs | `2960`, `3847`, `13339+`, … | `fun_prop`, `@[continuity]` polynomial lemmas | **~60–100** | Low |
| **5** ⭐⭐ | Collapse CXXXII-D root factorization | `900–933` | `Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd` | **~15** | Low |
| **6** ⭐ | Shrink the residue imaginary-sign atom | `348–360` | `Complex.div_im` / `Complex.inv_im` | **~11** | Low |
| **7** (defer) | Replace hard-coded 10-zero list with real zero set | `~49464–49504` | `ZetaZeros` (`IsCompact.inter_riemannZetaZeros_finite`) | **~50** | Med (Phase 3) |

Net: **~400–550 deletable lines**, plus two retired obligations. Do **#1 and #2 first** — highest
value and they touch the frontier.

---

## #1 ⭐⭐⭐ — `logDeriv_tprod_eq_tsum` collapses the Hadamard log-derivative bridge

**File (NEW):** `Mathlib/Analysis/Calculus/LogDerivUniformlyOn.lean:24`. Verified signature:
```lean
theorem logDeriv_tprod_eq_tsum {ι : Type*} {s : Set ℂ} (hs : IsOpen s) {x : ℂ} (hx : x ∈ s)
    {f : ι → ℂ → ℂ} (hf : ∀ i, f i x ≠ 0) (hd : ∀ i, DifferentiableOn ℂ (f i) s)
    (hm : Summable fun i ↦ logDeriv (f i) x) (htend : MultipliableLocallyUniformlyOn f s)
    (hnez : ∏' i, f i x ≠ 0) :
    logDeriv (∏' i, f i ·) x = ∑' i, logDeriv (f i) x
```
This is *exactly* the identity our genus‑1 Hadamard machinery hand-builds: `logDeriv (∏' factor) =
∑' (1/(s−ρ) + 1/ρ)`. Today rh.lean routes around it with a finite-product log-deriv formula plus a
hand-rolled limit-passing layer — `logDeriv_indexedFiniteHadamardProduct`,
`HadamardLogDerivLimitData`, `HadamardLocallyUniformProductData.of_logDerivLimitData`
(`~rh.lean:74240–74475`). **All of that scaffolding is what `logDeriv_tprod_eq_tsum` does in one
call.**

The hypotheses are precisely the things rh.lean *already proves* elsewhere:
- `∀ i, f i x ≠ 0` — `hadamardGenus1Factor … ≠ 0` (the nonvanishing lemmas around `75100`),
- `DifferentiableOn` — `hadamardGenus1Factor_differentiableAt` (`74559`),
- `Summable (logDeriv (f i) x)` — our regularized series summability (`HadamardZeroInvSqSummability`),
- `MultipliableLocallyUniformlyOn f s` — `tendstoLocallyUniformlyOn_indexedFiniteHadamardProduct_*`
  (`75349`, `75431`) already establish this,
- `∏' f i x ≠ 0` — product nonvanishing (`75106`+).

> **Why it's frontier-critical:** the direct-canonical AFZ route currently discharges
> `canonicalXiPullbackHadamardLogDerivativeSource` *definitionally* (`logDeriv_eq_zeroContribution :=
> rfl`) — i.e. it renames the obligation rather than proving the analytic identity. Wiring
> `logDeriv_tprod_eq_tsum` in makes that source a **theorem**, closing the honest-Hadamard route's
> central identity with Mathlib instead of a `rfl` placeholder.

> Bonus: the Mathlib proof itself calls `logDeriv_tendsto` and `logDeriv_prod` — if we ever need the
> finite-stage facts, take them from there rather than re-deriving.

---

## #2 ⭐⭐⭐ — kill the Schwarz obligation §17.C with the identity theorem

The open obligation `hurwitzEvenFEPair_zero_f_modif_ofReal_target` (the `f_modif`
`Set.indicator`/`ofReal` identity) and its whole FE-pair lift (`~rh.lean:49979–50088`) can be
**bypassed entirely**. `entireRiemannXi` is entire and **real on ℝ**; Schwarz symmetry then follows
from the identity theorem. Both required Mathlib pieces exist and are verified:

- **`conj∘f∘conj` is holomorphic** — `Mathlib/Analysis/Calculus/Deriv/Star.lean:28`:
  ```lean
  lemma DifferentiableAt.conj_conj {f : 𝕜 → 𝕜} (hf : DifferentiableAt 𝕜 f x) :
      DifferentiableAt 𝕜 (conj ∘ f ∘ conj) (conj x)
  ```
  (plus `HasDerivAt.conj_conj`, `DifferentiableAt.star_conj` — this file exists *for* Schwarz
  reflection). This removes the only subtlety (conjugation is anti-holomorphic, but the *double*
  conjugate is holomorphic).
- **Identity theorem on ℂ** — `Mathlib/Analysis/Analytic/Uniqueness.lean:223` (and the `univ`
  specialization at `:237`):
  ```lean
  theorem AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq {f g : E → F} {U}
      (hf : AnalyticOnNhd 𝕜 f U) (hg : AnalyticOnNhd 𝕜 g U) … : EqOn f g U
  ```
  rh.lean **already uses this exact lemma** for the ξ-nontriviality argument (`49376–49394`,
  `49740–49747`), so the pattern is proven to work here.

**The kill (≈15–20 lines), reusable & domain-agnostic:**
```lean
theorem entire_conj_symm_of_real_on_real {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hreal : ∀ x : ℝ, f x = conj (f x)) :
    ∀ s, f (conj s) = conj (f s) := by
  -- g := conj ∘ f ∘ conj is entire (DifferentiableAt.conj_conj); g and f agree on ℝ (hreal);
  -- ℂ is preconnected ⇒ eqOn_of_preconnected_of_eventuallyEq ⇒ g = f everywhere.
```
Apply to `entireRiemannXi` (entire via `entireRiemannXi_differentiable`; real-on-ℝ via kernel
reality, which our `mellin_star_ofReal` already underwrites). Then `entireRiemannXi_schwarz_target`
falls out and the FE-pair `f_modif` obligation is **never needed**. Keep `mellin_star_ofReal` as a
library lemma, but it stops gating RH.

---

## #3 ⭐⭐ — one analytic-order lemma replaces the multiplicity case-split

`rh.lean:594–637` proves `complex_local_pole_decomposition_{simple,double,triple,general}` — four
parallel ~10-line algebraic identities, one per multiplicity. Mathlib's
**`AnalyticAt.analyticOrderAt_eq_natCast`** (`Mathlib/Analysis/Analytic/Order.lean:86`) characterizes
*all* multiplicities uniformly via `f z = (z−z₀)^n • g z`, `g z₀ ≠ 0`:
```lean
lemma AnalyticAt.analyticOrderAt_eq_natCast (hf : AnalyticAt 𝕜 f z₀) :
    analyticOrderAt f z₀ = n ↔
      ∃ g, AnalyticAt 𝕜 g z₀ ∧ g z₀ ≠ 0 ∧ ∀ᶠ z in 𝓝 z₀, f z = (z - z₀) ^ n • g z
```
(built on `AnalyticAt.exists_eventuallyEq_pow_smul_nonzero_iff`,
`Mathlib/Analysis/Analytic/IsolatedZeros.lean:185` — which §16.4-A *already* uses). Collapse the four
into one wrapper; the per-`m` algebra (`m`, `m−1`, `k+1`) is uniform and `field_simp; ring` closes it
in one shot. ~45 lines → ~5.

> Note: the higher-multiplicity *pole-witness limit* `(w−x)^m·logDeriv f w → m` is genuinely NOT in
> Mathlib (only the simple case, `AnalyticAt.tendsto_mul_logDeriv_simple_zero`,
> `LogDeriv.lean`). So the abstract pole-witness engine (§§3–5) stays ours — but the *factorization*
> input to it can be Mathlib's.

---

## #4 ⭐⭐ — `fun_prop` / `continuity` for the manual calculus proofs

rh.lean has **~343 `Continuous`/`Differentiable` mentions but only ~6 `fun_prop` calls.** The biggest
manual proofs that automation one-lines:
- **`deriv_smoothZeroCountingN0`** (`~2960`, ~48 lines) and **`deriv_pairedCauchyImKernel`**
  (`~3847`, ~45 lines): chains of explicit `HasDerivAt.{mul,div,const_mul,sub}` + `Real.deriv_log`.
  `fun_prop` (for differentiability) then `simp [...]`/`field_simp; ring` for the value collapses the
  derivative-existence half.
- **`polynomial_logDeriv_background_continuousAt`** (CXXXII-B, `~878–884`): `ContinuousAt.div` chain →
  `fun_prop`. `Polynomial.continuous`/`continuousAt` are tagged `@[continuity, fun_prop]`
  (`Mathlib/Topology/Algebra/Polynomial.lean:57,61`).
- **~12 `Continuous.div` chains** at `13339, 13364, 13701, 13743, 13803, 13810, 13855, 13862, 13921,
  13928, 13984, 13991` → `continuity` / `fun_prop` (pass the nonzero-denominator hyp).

Est. ~60–100 lines, low risk. (Algebraic tactics `ring`/`field_simp`/`positivity` are already used
well — no gain there.)

---

## #5 ⭐⭐ — `exists_eq_pow_rootMultiplicity_mul_and_not_dvd` collapses CXXXII-D

`rh.lean:900–933` hand-assembles `p = (X−ρ)^m·q` with `q(ρ)≠0` via a 5-step dance
(`rootMultiplicity_pos` → `pow_rootMultiplicity_dvd` → `dvd_iff_isRoot` → `le_rootMultiplicity_iff`).
Mathlib hands it over directly (`Mathlib/Algebra/Polynomial/Div.lean:560`):
```lean
theorem Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd (p : R[X]) (hp : p ≠ 0) (a : R) :
    ∃ q, p = (X - C a) ^ p.rootMultiplicity a * q ∧ ¬ (X - C a) ∣ q
```
~15 lines → ~3.

---

## #6 ⭐ — `Complex.div_im` for the residue sign atom

`complex_real_root_residue_imag_nonpos` (`rh.lean:348–360`, ~13 lines) proves
`Im(1/(z−r)) ≤ 0`. `Complex.inv_im : z⁻¹.im = -z.im / normSq z` (`Mathlib/Data/Complex/Basic.lean`)
+ `Complex.normSq_nonneg`/`normSq_pos` gives it in 2–3 lines. The weighted-cloud list induction
(`391–417`) similarly tidies via `Finset.sum_nonpos`, but that's minor.

---

## #7 (defer to Phase 3) — real zero set instead of the hard-coded 10 ordinates

`firstTenRiemannZeroOrdinates` / `riemannZeroOrdinatesExt` (`~49464–49504`) hard-code 10 zero
ordinates with `unitMultiplicity := 1`. The new `ZetaZeros` (`isDiscrete_riemannZetaZeros`,
`IsCompact.inter_riemannZetaZeros_finite`, §3 above) supplies the *general* locally-finite zero set,
letting `FluctuationMeasureData` quantify over the true `N(T)`. **Blocker:** Mathlib does **not** yet
prove simplicity (multiplicity 1) of zeta zeros, and the *numerical* ordinates still need an oracle —
so this stays a Phase-3 upgrade, not an immediate swap.

---

## Already optimal — leave alone

- **Summability** of the A1 shell mass (`summable_log_natCast_mul_pred_sq_inv`, `~79278`) already
  chains `isLittleO_log_rpow_atTop` + `Real.summable_one_div_nat_rpow` + `summable_of_isBigO_nat` —
  textbook-Mathlib, nothing to cut.
- **`Multipliable` from inv-square summability** (`75046`) already uses
  `Complex.multipliable_one_add_of_summable` (`SpecialFunctions/Log/Summable.lean`) — optimal.
- **`logDeriv_mul` / `logDeriv_prod`** are already taken from Mathlib, not re-derived.
- The **abstract anti-Herglotz / pole-witness engine** (§§1–6) is genuinely original (no Mathlib
  Herglotz *function class*); keep it.

## Suggested order of attack

1. **#2 Schwarz kill** — smallest, retires an obligation, low risk, proven pattern. Do it first.
2. **#1 `logDeriv_tprod_eq_tsum`** — biggest deletion *and* upgrades the Hadamard log-deriv source
   from `rfl`-placeholder to a real theorem. Highest overall value.
3. **#5, #6, #3** — mechanical, safe, ~70 lines, good warmups / can be batched.
4. **#4 `fun_prop` sweep** — do as a single dedicated pass (easy to verify by re-elaboration).
5. **#7** — park until zeta-zero simplicity lands upstream.

---
---

# Pass 3 — the BIG theorems: whole subsystems Mathlib can absorb

> Third sweep (5 agents), hunting **load-bearing theorems that retire entire hand-built
> subsystems**, not line-level collapses. Every name/path verified in the pinned source. Each item
> gets a blunt verdict: *what it takes off the plate* vs *the gap that keeps it from being a free
> lunch.* The honest headline: Mathlib's **classical complex-analysis + Nevanlinna + FE-pair**
> coverage is now deep; the **RH-strength pieces (sharp zero-free region, explicit formula,
> Hadamard order theory, Second Main Theorem) remain genuinely absent** — which is exactly where our
> bespoke content lives.

## Big-ticket scoreboard

| | Subsystem | Mathlib asset | Verdict |
|---|---|---|---|
| **A** ⭐⭐⭐ | Zero counting `N(r,f)` | `ValueDistribution.*` (logCounting / characteristic / FMT / Cartan) | real framework; gap = no Second Main Thm |
| **B** ⭐⭐⭐ | Critical-strip growth control | `Complex.PhragmenLindelof.*` (+ Hadamard 3-lines, Borel–Carathéodory, max-mod, Liouville) | **fully usable**, retires hand-rolled strip bounds |
| **C** ⭐⭐⭐ | ξ entire + functional eq + residues | `LSeries.AbstractFuncEq` (`WeakFEPair`/`StrongFEPair`) | hands ~80% of ξ scaffolding free; gap = no order/growth |
| **D** ⭐⭐ | Finite Weierstrass extraction | `Complex.CanonicalDecomposition` (`extract_zeros_poles`, `canonicalFactor`) | retires the finite "low-zero split"; gap = disk-local only |
| **E** ⭐⭐ | von Mangoldt ↔ ζ′/ζ, Chebyshev, zero-free Re≥1 | `LSeries.Dirichlet`, `Chebyshev`, `Nonvanishing` | ready bridge if we touch ζ′/ζ; gap = no explicit formula / sharp ZFR |
| **F** ⭐⭐ | Ground the anti-Herglotz sign law | `Complex.Harmonic.*` + `Poisson` (herglotzRieszKernel) | can ground §§1–6; gap = no Herglotz *representation* thm |

---

## A ⭐⭐⭐ — Nevanlinna value distribution: a genuine `N(r,f)` zero-counting framework

**Dir (verified):** `Mathlib/Analysis/Complex/ValueDistribution/` —
`CharacteristicFunction.lean`, `Proximity/`, `LogCounting/`, `FirstMainTheorem.lean`, `Cartan.lean`.

| decl | file | meaning |
|---|---|---|
| `ValueDistribution.logCounting` | `LogCounting/Basic.lean:96` | **the Nevanlinna counting function** `N(r,f) = Σ_z D(z)·log(r/‖z‖) + D(0)·log r`, built as an `AddMonoidHom` on the **divisor** `locallyFinsupp … ℤ` |
| `ValueDistribution.proximity` | `Proximity/Basic.lean:50` | `m(r,f) = circleAverage (log⁺‖f‖) 0 r` |
| `ValueDistribution.characteristic` | `CharacteristicFunction.lean:53` | `T(r,f) := proximity + logCounting` (Nevanlinna height) |
| `isBigO_characteristic_sub_characteristic_inv` | `FirstMainTheorem.lean:109` | **First Main Theorem**: `T(r,f) − T(r,f⁻¹) = O(1)` |
| `isBigO_characteristic_sub_characteristic_shift` | `FirstMainTheorem.lean:160` | FMT shift-invariance |
| (Cartan's formula) | `Cartan.lean` | `T(r,f)` as an integrated counting over the circle |

**Takes off the plate:** ξ is entire ⇒ trivially `MeromorphicOn univ` ⇒ it has a Mathlib **`divisor`**
(`MeromorphicOn.divisor`, Pass-1 §7), and `logCounting (divisor ξ) 0` *is* the weighted zero count
`N(r,ξ)`. Our bespoke shell-count / zero-count bookkeeping (`canonicalShellCard`, the
`ZeroCountingFluctuationBound` inputs) can be **re-expressed in Mathlib's counting function** rather
than carried as private definitions — and the FMT + Cartan give the standard manipulations for free.

**The gap (be honest):** **no Second Main Theorem** (`N(r) ≤ T(r) + S(r)` with the ramification term).
So Nevanlinna alone won't upper-bound the zero count — you still bound `T(r,ξ)` from above via
**Jensen** (Pass-1 §2) or Phragmén–Lindelöf growth (B). But *that* combination — `logCounting` for the
count, Jensen/PL for the majorant — is exactly the RvM-style `canonicalShellCard ≤ C·log n + C₀`
inequality (memory hole #1). **This is the framework to express hole #1 in.**

---

## B ⭐⭐⭐ — Phragmén–Lindelöf (+ the full growth toolkit): critical-strip control for free

**File (verified):** `Mathlib/Analysis/Complex/PhragmenLindelof.lean`.

| decl | line | what |
|---|---|---|
| `PhragmenLindelof.horizontal_strip` | 113 | bound `‖f‖` on a closed horizontal strip from boundary values + a sub-double-exponential interior bound |
| `PhragmenLindelof.vertical_strip` | 275 | same for `re ⁻¹' Ioo a b` — **directly the critical strip `0 ≤ Re ≤ 1`** |
| `eq_zero_on_vertical_strip` / `eqOn_vertical_strip` | 303 / 321 | **uniqueness on a strip** — a second identity-theorem-style tool |
| `quadrant_I…IV`, `right_half_plane_of_tendsto_zero_on_real` | 409+ | sector / half-plane versions |

Plus the rest of the classical kit, all present and usable (Pass-1 §8/§9 noted some):
- **Hadamard three-lines** `Complex.Hadamard.norm_le_interpStrip_…` (log-convex interpolation between
  two vertical lines) — pairs with PL: PL/3-lines bound the edges, interpolate the interior.
- **Borel–Carathéodory** `Complex.borelCaratheodory` — bound `‖f‖` (and `‖f′‖`) from a bound on
  `Re f` only. The standard tool for passing from `Re Λ[ξ]` control to modulus control.
- **Maximum modulus** `Complex.norm_le_of_forall_mem_frontier_norm_le` (frontier→interior, no
  connectedness needed); **Liouville/Cauchy estimates** `norm_iteratedDeriv_le_of_forall_mem_sphere…`
  (derivative bounds, i.e. control of `ξ′`).

**Takes off the plate:** any hand-rolled growth/max-modulus argument bounding ξ or `Λ[ξ]` across the
critical strip — feed it straight into the Turing/envelope inputs. **No hand-rolling needed.**

**The gap:** PL needs the *interior* sub-double-exponential bound as a hypothesis; for ξ that comes
from the Γ-factor + Dirichlet-series bound, which we supply (Mathlib has no order-1 statement, see C).

---

## C ⭐⭐⭐ — `WeakFEPair`/`StrongFEPair`: ~80% of the ξ analytic scaffolding, free

**File (verified):** `Mathlib/NumberTheory/LSeries/AbstractFuncEq.lean` — the abstraction *behind*
`completedRiemannZeta`. We already touch it via `hurwitzEvenFEPair` in §17.C.

| decl | line | hands us |
|---|---|---|
| `WeakFEPair` / `StrongFEPair` | 81 / 100 | the `(f,g,ε,k,f₀,g₀)` data; `Λ := mellin f`, `Λ₀ := mellin f_modif` |
| `StrongFEPair.differentiable_Λ` | 213 | **Λ entire** |
| `WeakFEPair.differentiable_Λ₀` | 399 | **Λ₀ entire** (the pole-subtracted version — our `entireRiemannXi` base) |
| `functional_equation` / `functional_equation₀` | 222 / 429 | **`Λ(k−s) = ε·symm.Λ s`** — proven automatically from the data |
| `Λ_residue_zero` / `Λ_residue_k` | (same file) | exact pole **residues** at `0`, `k` |

**Takes off the plate:** stop re-deriving "ξ is entire / satisfies the functional equation / has these
residues" — they are *theorems of the FE-pair*. The §17 `entireRiemannXi*` layer should consume these
maximally. Combined with **Pass-2 #2** (identity-theorem Schwarz), the FE-pair + one 20-line lemma
gives the entire "ξ entire, order-aside, FE, Schwarz, residues" package.

**The gap:** the FE-pair proves **no growth/order bound** — there is no "Λ is order 1" anywhere in
Mathlib (confirmed: only *local* `analyticOrderAt`/`meromorphicOrderAt`, never global growth order,
no genus, no canonical-product theorem). This — plus the absent Hadamard factorization theorem (D) —
is precisely *why* our genus-1 product is hand-built and must stay so.

---

## D ⭐⭐ — `extract_zeros_poles`: finite Weierstrass extraction, free

**File (verified):** `Mathlib/Analysis/Complex/CanonicalDecomposition.lean`.
- `MeromorphicOn.extract_zeros_poles` — rewrites `f` on a disk as `(∏ (·−u)^(divisor f u)) • g` with
  `g` analytic and **non-vanishing**.
- `Complex.canonicalFactor R w` (Blaschke factor) with `meromorphicOrderAt_canonicalFactor`,
  `canonicalFactor_ne_zero` (norm-1 on the sphere, single pole at `w`, no zeros in the ball).

**Takes off the plate:** the **finite-product extraction** half of the Hadamard machinery — i.e. the
"low-zero split" (pull the finitely-many low zeros out as explicit linear factors, leave an analytic
non-vanishing remainder). That non-vanishing-cofactor bookkeeping is currently hand-done.

**The gap:** it's **disk-local with a finite divisor**. The *infinite-product convergence* over all ξ
zeros is still ours — via `logDeriv_tprod_eq_tsum` (Pass-2 #1). So D + Pass-2 #1 together cover the
low-split and the tail; the *order-1 product theorem* tying them to growth is still absent (C).

---

## E ⭐⭐ — analytic NT bridge: von Mangoldt ↔ ζ′/ζ, Chebyshev, zero-free `Re ≥ 1`

| decl | file | gives |
|---|---|---|
| `LSeries_vonMangoldt_eq_deriv_riemannZeta_div` | `LSeries/Dirichlet.lean:434` | **`L(Λ,s) = −ζ′(s)/ζ(s)`** on `Re s > 1` |
| `MeromorphicOn.logDeriv` | `SpecialFunctions/Complex/LogDeriv.lean:130` | **`ζ′/ζ` is meromorphic** (logDeriv of meromorphic) |
| `Chebyshev.psi` / `theta` / `abs_psi_sub_theta_le_sqrt_mul_log` / `primeCounting_eq_theta_div_log_add_integral` | `NumberTheory/Chebyshev.lean` | ψ, θ with explicit bounds; a **Perron-like** π↔θ integral (via Abel summation) |
| `riemannZeta_ne_zero_of_one_le_re` | `LSeries/Nonvanishing.lean` | **ζ ≠ 0 on the closed half-plane `Re ≥ 1`** |

**Takes off the plate:** *if* our zero-count route ever connects to the von Mangoldt side / the
log-derivative of ζ (it plausibly does, via the explicit-formula intuition), the `−ζ′/ζ` identity +
`MeromorphicOn.logDeriv` + Chebyshev bounds are a ready-made bridge — no re-derivation.

**The gap (the RH-strength wall):** **no explicit formula** `ψ(x)=x−Σ_ρ x^ρ/ρ+…`, **no sharp
zero-free region** `σ>1−c/log t` (only the boundary line `Re ≥ 1`), **no `ζ′/ζ` growth bounds**.
These are the genuinely-hard inputs; Mathlib does not shortcut them, and neither can we.

---

## F ⭐⭐ — ground the anti-Herglotz sign law in harmonic/Poisson theory

**Files (verified):** `Mathlib/Analysis/Complex/Harmonic/*` + `Poisson.lean` (Pass-1 §8).
- `HarmonicOnNhd.exists_analyticOnNhd_ball_re_eq` — harmonic `u` ⇒ ∃ holomorphic `F`, `Re F = u`.
- mean-value / Poisson reconstruction (`HarmonicContOnCl.circleAverage_poissonKernel_smul`),
  `herglotzRieszKernel` with `re_herglotzRieszKernel_le`.

**Takes off the plate:** our hand-rolled anti-Herglotz layer (§§1–6) could be **grounded** in the
standard Poisson/Herglotz representation (reviewer-facing rigor; possible partial replacement).

**The gap:** **no Herglotz *representation theorem*** (positive-`Im` analytic on the UHP ↔ Poisson
integral of a measure), and **no Pick/Nevanlinna function class**. So this is grounding/optional, not
a wholesale replacement — keep the proven §§1–6 engine.

---

## What NO big theorem covers — stays hand-built or genuinely open

| missing | status | note |
|---|---|---|
| **Hadamard factorization theorem** (order-1 entire = product × exp(poly)) | absent — no global order/genus theory | keep the hand-built genus-1 product; Pass-2 #1 + D are the supports |
| **Second Main Theorem** (Nevanlinna) | absent | only FMT (A); bound `T(r)` via Jensen/PL instead |
| **Argument principle / residue theorem** | absent, but **assemblable** | ingredients all present: `circleIntegral` + `MeromorphicOn.divisor` + Cauchy formula + `MeromorphicOn.logDeriv` — a worthwhile one-time lemma |
| **Explicit formula / sharp ZFR / `ζ′/ζ` bounds / RH** | absent | the true RH-strength inputs — our bespoke certificates live here |
| **Riemann mapping / UHP↔disk Cayley** | incomplete in Mathlib | hand-roll `z ↦ (z−i)/(z+i)` if needed |

---

## Re-prioritized close-out (folding in the big theorems)

1. **Express hole #1 in Nevanlinna + Jensen** (A + Pass-1 §2): cast `canonicalShellCard ≤ C·log n+C₀`
   as `logCounting (divisor ξ)` bounded by `T(r,ξ)`, majorized via `AnalyticOnNhd.sum_divisor_le`.
   This replaces the "build our own contour zero-count" plan with assembled Mathlib pieces.
2. **Phragmén–Lindelöf for every strip growth bound** (B) feeding the Turing/envelope inputs — delete
   hand-rolled max-modulus arguments.
3. **Re-base §17 ξ facts on `WeakFEPair`** (C) + Pass-2 #2 Schwarz: entire, FE, residues all free.
4. **`extract_zeros_poles` for the low-zero split** (D); `logDeriv_tprod_eq_tsum` for the tail
   (Pass-2 #1).
5. **Keep** the genus-1 order argument, the anti-Herglotz engine, and the RH-strength certificates —
   no big theorem retires these, and that's where the real proof content is.

---
---

# Pass 4 — the certificate machinery: SOS / SDP / Backlund-Turing numerics

> Fourth sweep, scoped to the **certificate subsystem** — the externally-computed proofs the project
> imports: SOS/Schmüdgen polynomial inequalities (`golden_sos_certificate.*`), per-slab SDP margin
> certs (`slab_certificates.*`, `NineSlabCertInputs` §CLX), and the Backlund/Turing certified-numerics
> + zero-bracket tables (`BacklundTuring` §CXLIX-E ~L4294, the 182-zero table ~L35480). All
> names/paths verified in the pinned source. Verdict pattern: *supported / partial / hand-build.*

## Scoreboard

| flavor | Mathlib support | verdict |
|---|---|---|
| **SOS / Schmüdgen polynomial inequalities** | `nlinarith` (no Positivstellensatz lib; `polyrith` is **dead**) | **partial** — nlinarith is the discharge engine; feed it the multipliers |
| **SDP / PSD Gram-matrix → `p = vᵀQv ≥ 0`** | `Matrix.PosSemidef`, `posSemidef_gram`, `M = BᴴB`, eigenvalue criterion | **supported** via Cholesky-factor check; gap = no `decide`/Sylvester |
| **Backlund/Turing certified numerics** (π, exp/log, ratios) | `pi_gt_d6`, `sum_le_exp_of_nonneg`, `exp_bound'`, `log_le_log`, IVT, `bound` | **supported & already wired** |
| **Zero isolation / root counting** (the bracket tables) | — (no Sturm, no certified interval arith, no argument principle) | **hand-build / external oracle** (unchanged wall) |

---

## 4.1 SOS / Schmüdgen polynomial inequalities → `nlinarith` is the engine

**There is no Positivstellensatz / Schmüdgen / sum-of-squares *library* in Mathlib** (no `IsSumSq`
cone theory, no Artin, no certificate-checker). And **`polyrith` is dead** — `Mathlib/Tactic/
Polyrith.lean:57` literally throws `"polyrith is no longer available"` (the SageMath backend is gone).
So the discharge path is the tactic that *is* a Positivstellensatz search:

- **`nlinarith`** (`Mathlib/Tactic/Linarith/Frontend.lean`) — proves nonlinear arithmetic goals by
  forming pairwise products of hypotheses and running `linarith` over them. This is exactly the
  `Σ σ_S·∏ g_i` Schmüdgen shape. **rh.lean already uses `nlinarith`/`linarith` heavily (172 hits).**
  - **The win:** our SDP/Schmüdgen output gives the *multipliers explicitly*. Hand them to
    `nlinarith` as hints — `nlinarith [sq_nonneg (a*x+b*y), mul_nonneg hg_T hg_x, …]` — so it doesn't
    have to *search* for the certificate, only verify the linear combination. This is the cheapest
    reliable route and needs no new infrastructure.
  - **Caveat:** there is **no "check this SOS witness" data interface** — you can't pass a Gram
    matrix or a `σ_S` list as data and have Mathlib certify it. You either route through `nlinarith`
    hints or write the SOS identity explicitly (`have : target = a^2 + b^2 + … := by ring`) and close
    with `positivity` / `sq_nonneg`.
- **`positivity`** (`Mathlib/Tactic/Positivity/`) — closes pure `0 ≤ e` / `0 < e` goals (knows
  `sq_nonneg`, `mul_nonneg`, `div_nonneg`, sums). Good for the `σ_S` (sum-of-squares) sub-pieces,
  not for constrained slab goals.
- **`bound` / `gcongr`** (`Mathlib/Tactic/Bound.lean`, `gcongr`) — chain monotone inequalities
  (clear-denominator scalings like `K/T² ≤ K/T₀²`), which is how rh.lean's slab proofs already
  assemble (decompose → `norm_num` the scalar → `linarith`/`gcongr` the monotonicity).

**Verdict:** keep the decompose-then-`nlinarith`/`norm_num`/`gcongr` pattern (already proven on the
landed slabs). If you want SDP→Lean directly, emit the Schmüdgen multipliers and inject them as
`nlinarith` hints. Don't wait for a Positivstellensatz library — none is coming soon.

---

## 4.2 SDP / PSD Gram matrices → Mathlib *can* certify `p(x) = vᵀ Q v ≥ 0`

If a cert is an SDP Gram matrix `Q` with `p(x) = v(x)ᵀ Q v(x)`, Mathlib has the linear algebra:

| decl | file | role |
|---|---|---|
| `Matrix.PosSemidef` | `LinearAlgebra/Matrix/PosDef.lean:58` | `IsHermitian ∧ 0 ≤ xᴴMx` |
| **`posSemidef_conjTranspose_mul_self`** | `…/PosDef.lean:355` | **`Aᴴ*A` is always PSD** — the `M = BᴴB ⇒ vᵀMv = ‖Bv‖² ≥ 0` link |
| `Matrix.posSemidef_gram` | `Analysis/InnerProductSpace/GramMatrix.lean:83` | every Gram matrix is PSD |
| `gram_eq_conjTranspose_mul` | `GramMatrix.lean:131` | Gram `= mᴴ*m` (the factorization) |
| `IsHermitian.posSemidef_iff_eigenvalues_nonneg` | `Analysis/Matrix/PosDef.lean:34` | eigenvalue criterion |
| `PosSemidef.fromBlocks₁₁` / `₂₂` | `…/PosDef.lean:542` | Schur-complement reduction |

**Best path:** have the SDP solver emit the **Cholesky/LDL factor `L`** (not just `Q`); then prove
`Q = Lᴴ L` by **`norm_num`/`ring` on the concrete rational matrix entries** (decidable equality), and
`posSemidef_conjTranspose_mul_self` makes `Q` PSD with `vᵀQv = ‖Lv‖² ≥ 0` for free. This sidesteps the
gaps below.

**Gaps:** no **Sylvester's-criterion / `decide` / `norm_num` extension** for "this concrete rational
matrix is PSD" (so don't try to `decide` PSD directly — check the factor instead); the matrix square
root exists only via **noncomputable CFC** (`Analysis/Matrix/Order.lean`), not a computable Cholesky.

---

## 4.3 Backlund/Turing certified numerics → well-supported and already wired

The `BacklundTuring` layer (§CXLIX-E, ~L4294–4760) leans on Mathlib that is present and tight:

| need | Mathlib | rh.lean already uses |
|---|---|---|
| rational π bounds | `Real.pi_gt_d6 : 3.141592 < π`, `pi_lt_d6` (+ `pi_gt_d20`/`pi_lt_d20`) — `Analysis/Real/Pi/Bounds.lean:182` | `backlund_pi_lower_…` ~L4636 |
| exp Taylor certs | `Real.sum_le_exp_of_nonneg` (`Complex/Exponential.lean:244`), `Real.exp_bound'` (`:534`) | exp lower/upper certs ~L4558 |
| log ratio bounds | `Real.log_le_log` + `Real.log_exp`/`exp_log` (exp-inversion trick avoids needing a log-Taylor lemma, which Mathlib **lacks**) | `log_lower_of_exp_le` ~L4541 |
| monotone `x log x` main term | `Real.log_le_log`, `monotoneOn_of_deriv_nonneg` | `smoothMainTerm_*_of_log_ratio` ~L4432 |
| existence-of-value | IVT: `intermediate_value_Icc` (`Topology/Order/IntermediateValue.lean`) | — |
| inequality chaining | `bound` (`Mathlib/Tactic/Bound.lean`), `gcongr`, `norm_num` | pervasive |

**Verdict:** the π / exp / log / monotonicity certificate scaffolding is fully Mathlib-backed and
mostly wired already — no new infrastructure needed there.

---

## 4.4 The one real wall: zero isolation / root counting

The **zero-bracket tables** (`ZeroSetUpToHeight`, `WeightedZeroSetUpToHeight`, the 182-zero
`BacklundGrid2First182ZeroBracketTableCertificate…` ~L35480) cannot be *derived* inside Mathlib:

- **No Sturm's theorem** (the only `Sturm` hit is in a modular-forms dimension formula, unrelated).
- **No certified interval arithmetic** for transcendental functions (no certified box propagation).
- **No root-isolation / "exactly N zeros in [a,b]"** primitive; IVT gives *existence* only.
- **No argument principle** (the Pass-3 wall) to count complex ζ zeros in a box.

So the architecture is sound and unavoidable: an **external numerical oracle generates the brackets**,
and **Lean verifies the certificate post-hoc** (pairwise-disjoint rational brackets ⇒ distinctness;
the `complete_to_cutoff` field ⇒ completeness). That verification *is* well-supported (rational
interval comparisons via `norm_num`, `Finset` reasoning). The missing piece is purely the
*generation*-side automation, which is out of scope for Mathlib and correctly handled by the Python
Turing/Backlund tooling.

**Net for the certificate layer:** SOS → `nlinarith`-with-hints; SDP → check the Cholesky factor via
`posSemidef_conjTranspose_mul_self`; numerics → Mathlib's π/exp/log bounds (already wired); zero
brackets → keep the external-oracle + Lean-verifier split. No Positivstellensatz, PSD-`decide`,
Sturm, or interval-arithmetic library exists to change this.

---
---

# Pass 5 — mapping landed Mathlib onto the three live obligations (P1/P2/P3)

> The reduction is now down to a clean two-bundle capstone
> `XiPullbackAntiHerglotzTarget_of_directNonTuringInputsAFZ_turingBundle`, with exactly three
> analytic obligation classes left to *inhabit* (not prove from scratch):
> **P1** Backlund/Turing envelopes (`PathBTuringEnvelopeInputs`), **P2** entire-ξ Hadamard
> (`EntireXiClassicalHadamardTheorem`), **P3** the AFZ Stieltjes equalities
> (`CanonicalXiPullbackStieltjesSourceAFZ` & friends). This pass answers: *which landed Mathlib
> directly helps each, and where's the residual gap?* All cited lemmas were verified in earlier
> passes. **Mathlib support is highest for P3, partial for P2, lowest for P1 — which is exactly the
> recommended P3 → P2 → P1 order.**

## The single highest-leverage lemma cuts across P2 **and** P3

**`logDeriv_tprod_eq_tsum`** (`Mathlib/Analysis/Calculus/LogDerivUniformlyOn.lean:24`) proves
`logDeriv (∏' fᵢ) = ∑' logDeriv fᵢ` under `MultipliableLocallyUniformlyOn` + `Summable (logDeriv fᵢ x)`
+ nonvanishing. This is the identity currently discharged by the `rfl` placeholder
`canonicalXiPullbackHadamardLogDerivativeSource` (L90614). Proving it for real **simultaneously**:
- gives P2 its "locally-uniform log-derivative interchange" field, and
- gives P3 its mid/high cloud identity `Λ[Ξ] = Σ (residue terms)`.
Do this one lemma first — it de-`rfl`s the shared spine both bundles sit on.

---

## P3 — AFZ Stieltjes equalities → **strongly supported, do first**

`Hmid`/`Hhigh` express the zero contribution as cloud + smooth tail + true-kernel residual *limit*;
`Hlow` is the zero-index split `ZC(z) = P(z) + tailZC(z)` away from zeros. Landed Mathlib:

| sub-obligation | Mathlib asset | role |
|---|---|---|
| mid/high cloud identity | **`logDeriv_tprod_eq_tsum`** (LogDerivUniformlyOn.lean:24) | `Λ[Ξ] = Σ residues` — retires the `rfl` placeholder |
| mid/high tail-limit (IBP) | **Abel summation** `sum_mul_eq_sub_integral_mul₀`, `tendsto_sum_mul_atTop_nhds_one_sub_integral₀` (AbelSummation.lean) + improper IBP `integral_Ioi_mul_deriv_eq_deriv_mul` (IntegralEqImproper.lean) | `∫ K dS = boundary − ∫ S·K′` |
| **`Hlow` zero-split** | **`MeromorphicOn.extract_zeros_poles`** (CanonicalDecomposition.lean) | factor `f = (∏(·−u)^div)·g`, `g` analytic non-vanishing — *is* the low split |
| AFZ guard / factor-at-nonzero | `analyticOrderAt`, `exists_eventuallyEq_pow_smul_nonzero_iff` (Order.lean, IsolatedZeros.lean) | the `XiPullback z ≠ 0 →` localization |
| log-deriv plumbing | `MeromorphicOn.logDeriv` (Complex/LogDeriv.lean:130), `deriv_log_comp_eq_logDeriv` | ζ′/ζ-style manipulations are meromorphic-safe |

**Verdict:** every piece of P3 has a matching landed lemma; it's identity-only and tied to the
decomposition we already built. Highest expected yield per unit effort. **Start here.**

---

## P2 — entire-ξ Hadamard theorem → **convergence supported, order/growth is ours**

`EntireXiClassicalHadamardTheorem` bundles `zeroSystem / prefactor / zeroDistribution / luc / region /
factorization / prefactorData`. What Mathlib gives vs. what stays hand-built:

| field | Mathlib asset | status |
|---|---|---|
| `luc` (log-deriv interchange) | **`logDeriv_tprod_eq_tsum`** | ✅ supported (shared with P3) |
| `factorization` / product convergence | `Complex.multipliable_one_add_of_summable` (Log/Summable.lean), `multipliableLocallyUniformlyOn_one_add` (MultipliableUniformlyOn.lean) | ✅ already used (L75046+) |
| `zeroDistribution` (inverse-square) ← A1 | **Jensen `AnalyticOnNhd.sum_divisor_le`** (JensenFormula.lean) + **Nevanlinna `logCounting`** (ValueDistribution/) → the `canonicalShellCard ≤ C·log n+C₀` RvM bound | ✅ now sourceable from Mathlib (was the A1 hole) |
| `zeroSystem` | `MeromorphicOn.divisor`, `FactorizedRational` | ✅ supported |
| `prefactor`/`prefactorData` | **`WeakFEPair`/`StrongFEPair`** (AbstractFuncEq.lean): ξ entire + functional equation + residues free; + identity-theorem Schwarz (Pass-2 #2) | ✅ ~80% free |
| **order-1 / genus / growth** | — *no entire-function order theory, no Hadamard factorization theorem in Mathlib* | ❌ **hand-built (stays ours)** |

**Verdict:** Mathlib retires the *convergence*, *zero-distribution*, and *prefactor* sub-content; the
**genus-1 order/growth argument is the irreducible hand-built core** (confirmed absent in Pass 3).
Target the canonical-zero exp-affine constructors and let Mathlib carry everything but the order bound.

---

## P1 — Backlund/Turing envelopes → **least shortcut; the genuine residue**

`PathBTuringEnvelopeInputs` wants `|S(u)| ≤ C·log u + D` (slab-localized + high-log). Landed Mathlib:

| need | Mathlib asset | role |
|---|---|---|
| global RvM zero-count envelope | **Jensen `sum_divisor_le`** + **Nevanlinna `logCounting`/`characteristic`/FMT/Cartan** (JensenFormula.lean, ValueDistribution/) | `N(T) ≤ growth` — the main-term side of `S = N − N₀` |
| finite-band count well-defined on [140,370] | **`IsCompact.inter_riemannZetaZeros_finite`** (ZetaZeros.lean) | finitely many zeros in the band |
| strip growth hypothesis | **Phragmén–Lindelöf** (`Complex.PhragmenLindelof.*`) + Hadamard 3-lines, Borel–Carathéodory | bound ξ across the critical strip |
| finite-band numeric certificates | π `pi_gt_d6`/`pi_lt_d6`, exp `sum_le_exp_of_nonneg`/`exp_bound'`, log via exp-inversion, IVT, `bound`/`gcongr` | already wired (§4.3) |
| explicit-formula bridge (if used) | `LSeries_vonMangoldt_eq_deriv_riemannZeta_div` (`L(Λ,s)=−ζ′/ζ`), Chebyshev ψ/θ, zero-free `Re≥1` | optional route |
| **argument-principle zero count on [140,370]** | — *no argument principle, no Sturm, no certified interval root-counting* | ❌ **external oracle + Lean-verify (§4.4)** |

**Verdict:** Jensen+Nevanlinna give the *global* envelope's main-term majorant and PL controls growth,
but the **finite-band argument-principle / zero-bracketing count has no Mathlib shortcut** — it stays
external-oracle-generated + Lean-checked. The audit layer already flags P1 as the *only* place
RH-strength legitimately enters, and Mathlib confirms it: this is the irreducible estimate work.
**Do last.**

---

## One-line takeaways

- **Cross-cutting:** prove `logDeriv_tprod_eq_tsum` into the canonical log-deriv source first — it
  de-`rfl`s the spine under both P2 and P3.
- **P3:** fully matched by landed lemmas (Abel/IBP + `extract_zeros_poles` + tprod logDeriv) — start here.
- **P2:** convergence/zero-distribution/prefactor are Mathlib-carried; the genus-1 **order argument is
  the hand-built core** — no Mathlib order theory exists.
- **P1:** Jensen+Nevanlinna+PL help the global envelope; the **finite-band argument-principle count is
  the genuine remaining estimate** with no Mathlib shortcut — last.
- Mathlib support gradient (P3 ≫ P2 ≫ P1) **matches the recommended attack order**.

---
---

# Pass 6 — PROVEN bridges (compiled green, sorry-free) — `Scratch.lean`

> These are not survey notes — they are **actual theorems that compile** against the pinned Mathlib
> (`lake env lean Scratch.lean`, exit 0), each verified `#print axioms`-clean (only
> `propext`/`Classical.choice`/`Quot.sound`, **no `sorryAx`**). Committed on branch
> `push-p3-stieltjes`. Drop-in ready for `rh.lean` (adjust namespace/open as needed).

## Bridge 1 — `entire_conj_symm_of_real_on_real` (Schwarz, domain-agnostic)
```lean
theorem entire_conj_symm_of_real_on_real
    {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hreal : ∀ x : ℝ, f (x : ℂ) = conj (f (x : ℂ))) :
    ∀ z : ℂ, f (conj z) = conj (f z)
```
Entire + real-on-ℝ ⟹ Schwarz conjugation symmetry. Proof: `g := conj∘f∘conj` is entire via
`DifferentiableAt.conj_conj`; `f = g` by the identity theorem `AnalyticOnNhd.eq_of_frequently_eq`
on the sequence `1/(n+1) → 0` (reals accumulate at 0). **Use:** an alternative one-liner discharge
of `entireRiemannXi_schwarz_target` (apply with `hf := entireRiemannXi_differentiable` and the
real-axis reality of `completedRiemannZeta₀`). Generic — works for any real-on-ℝ entire function.

## Bridge 2 — `logDeriv_tprod_eq_tsum_wrapper` (the Hadamard `luc` field)
```lean
theorem logDeriv_tprod_eq_tsum_wrapper
    {ι : Type*} {f : ι → ℂ → ℂ} {x : ℂ}
    (hf : ∀ i, f i x ≠ 0) (hd : ∀ i, Differentiable ℂ (f i))
    (hm : Summable fun i ↦ logDeriv (f i) x)
    (htend : MultipliableLocallyUniformlyOn f Set.univ)
    (hnez : ∏' i, f i x ≠ 0) :
    logDeriv (fun y => ∏' i, f i y) x = ∑' i, logDeriv (f i) x
```
Univ-specialized wrapper over Mathlib's `logDeriv_tprod_eq_tsum`. **Use:** converts the
`canonicalXiPullbackHadamardLogDerivativeSource` `rfl`-placeholder (rh.lean L90584) into a real
theorem — supply the four hypotheses for ξ's genus-1 factors (`hf`/`hd`/`hnez` already exist near
L75100; `hm`/`htend` from `HadamardZeroInvSqSummability` + the `tendstoLocallyUniformlyOn_*` lemmas
at L75349/75431). Shared spine for P2 and P3's mid/high cloud identity.

## Bridge 3 — `jensen_zero_count_le` (RvM / A1 / P1 main-term engine)
```lean
open MeromorphicOn in
theorem jensen_zero_count_le
    {c : ℂ} {r R M : ℝ} {f : ℂ → ℂ}
    (r_pos : 0 < |r|) (r_lt_R : |r| < |R|) (hM : 1 ≤ M)
    (hf : Differentiable ℂ f) (h₂f : f c ≠ 0)
    (f_bound : ∀ z ∈ Metric.sphere c |R|, ‖f z‖ ≤ M) :
    ∑ᶠ u, divisor f (Metric.closedBall c |r|) u
      ≤ Real.log (M / ‖f c‖) / Real.log (R / r)
```
Thin wrapper over Jensen's `AnalyticOnNhd.sum_divisor_le`: for an entire `f`, the weighted zero
count in a disk is bounded by `log(M/‖f c‖)/log(R/r)`. **Use:** the Mathlib-grounded RvM upper
bound — majorizes `canonicalShellCard ≤ C·log n + C₀` (the A1 hole) and the `N(T)` main term feeding
the Turing envelope (P1). Last mile: instantiate `f := entireRiemannXi` (or `EntireXiPullback`),
choose `R/r` per shell, and supply the sphere bound from the Γ·ζ growth estimate.

## Honest status of the "last mile"
Each bridge is a *real, compiled* theorem, but landing it in `rh.lean` still needs project-specific
inputs that are themselves genuine math:
- **B1**: already discharged in rh.lean by another route (`entireRiemannXi_schwarz_target_holds`,
  L50084) — B1 is a cleaner reusable alternative, not a new fill.
- **B2**: needs ξ's `Multipliable`/summable-logDeriv hypotheses wired (P2 convergence content — exists
  in pieces near L75046–75431).
- **B3**: needs the per-shell sphere bound `‖ξ‖ ≤ M` from Γ·ζ growth (the genuinely missing
  order/growth estimate — no Mathlib shortcut, Pass 3).
The bridges retire the *Mathlib-facing* half of each obligation; the *analytic-content* half (growth
order, the envelope estimate) remains the irreducible work, exactly as the audits predicted.

---

## Pass 6 — CORRECTION (read the actual defs, earlier claim was wrong)

**Earlier claim (Pass 2 #1, Pass 5, and Bridge 2 above): "wiring `logDeriv_tprod_eq_tsum` turns
the `canonicalXiPullbackHadamardLogDerivativeSource` `rfl` placeholder into a real theorem and
deletes ~200–300 lines." THIS IS WRONG.** After reading the actual definitions:

- `canonicalXiPullbackZeroContribution := logDerivativeResponse XiPullback` (rh.lean L90208).
- So the struct field `logDeriv_eq_zeroContribution` is literally
  `logDerivativeResponse XiPullback z = logDerivativeResponse XiPullback z` — a **legitimate
  definitional tautology**, closed by `rfl`. It is **not** a placeholder hiding analytic work.
- The direct-canonical route *deliberately* sets the zero-contribution to the actual log-derivative,
  pushing all genuine content onto the **Stieltjes side** (`StieltjesMidHighTailEquality` etc., P3).
  Same pattern at L73441 (`if 0<z.im then logDerivativeResponse XiPullback z else 0`, closed by
  `simp`).

**Where Bridge 2 (`logDeriv_tprod_eq_tsum`) actually applies:** only on the *honest-Hadamard*
route, to prove `logDerivativeResponse XiPullback z = Σ' (1/(z−ρ) + …)` — and that step first needs
ξ written as a product over its zeros (the Hadamard **factorization**, P2), which requires
entire-function **order/growth theory that is NOT in Mathlib** (confirmed Pass 3). So Bridge 2 is
gated behind the genuinely-missing growth content; it is the *easy mile after the hard mile*, not a
standalone win. Bridge 2 remains a correct, compiled lemma — its applicability was overstated.

Net honest status of the three bridges: **all three compile and are axiom-clean, but each is gated
on project-specific analytic content that Mathlib does not provide** (B1 already done in-file
another way; B2 behind the Hadamard factorization/growth; B3 behind the per-shell Γ·ζ sphere
bound). They retire Mathlib-facing plumbing; they do not close P1/P2/P3.
