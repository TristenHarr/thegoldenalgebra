# Quantitative Uncertainty: Off-line Zero vs Bounded-Support Weil Positivity

Sharp version of Bombieri's "an off-line zero at displacement δ is invisible until support
T ≈ 1/δ". Scripts: `QUART_*.py` in this directory. All identities verified numerically.

## THE CENTRAL EXACT IDENTITY (the deliverable)

For `g` positive-type with `supp(g) ⊆ [−T,T]` (so `h = ĝ` is entire of exponential type `T`
and `h ≥ 0` on ℝ; `g = f⋆f̃`, `supp f ⊆ [−T/2,T/2]`), the contribution to the Weil sum
`Q(g) = Σ_ρ h(γ_ρ)` of one off-line zero quartet `{½ ± δ ± iγ₀}` is **exactly**

      N(δ, γ₀, T) = 4 ∫_{−T}^{T} g(u) cosh(δu) cos(γ₀u) du                          (★)

Derivation: `h(x+iy) = ∫_{−T}^{T} g(u) e^{uy} e^{−iux} du`; summing the four points
`±γ₀ ± iδ` produces `Σ e^{±uδ} · Σ e^{∓iuγ₀} = 2cosh(δu)·2cos(γ₀u)`.
**Verified to ~1e-26** against the literal 4-point evaluation of `h` (Gaussian),
`QUART_bernstein.py`.

Split:  `N = N0 + Δ`,  with
  - `N0 = 4 ĝ(γ₀) = 4 |f̂(γ₀)|² ≥ 0`  — this is the **on-line** value (δ=0), always ≥ 0.
  - `Δ = 4 ∫ g(u)(cosh(δu)−1)cos(γ₀u) du`  — the off-line correction. **`|Δ| ≤
    4(cosh(δT)−1) ∫|g|`.**

`cosh(δu) − 1 ≈ (δu)²/2` is `≈ 0` for `|u| ≪ 1/δ`. So on support `T ≪ 1/δ` the off-line
zero contributes the SAME (nonnegative) mass `N0` as an on-line zero, up to a **relative**
`O((δT)²)`. The negative mass can only appear by exploiting `cosh(δu)` at `|u| ~ 1/δ`,
i.e. **only once `T ≳ 1/δ`.** This is the sharp "invisible until 1/δ", and (★) makes the
constant explicit.

## TASK 1–2 — size of N, and the threshold; the constant is γ₀-INDEPENDENT

`QUART_magnitude.py`: minimizing `N` over positive-type `g` normalized by `g(0)=1` (this is
the min eigenvalue of the kernel `A_{xy} = cosh(δ(x−y))cos(γ₀(x−y))` on `[−T/2,T/2]`),

  - **γ₀-independence (key):** for fixed `(δ,T)` the most-negative `N_min/g(0)` is essentially
    identical across `γ₀ = 50, 200, 1000` (e.g. δ=0.1, T=10 → −1.789, −1.795, −1.801).
    The threshold is governed by **δT alone**, not γ₀.
  - **Scaling / the gate:** `|N_min|/g(0)` is governed by `x = δT`. Small `x`: `∝ x²`
    (quadratic, INVISIBLE — `≈0.21` at δT=0.5). Around `x ~ 1`: `O(1)` (`≈1.8` at δT=1).
    Large `x`: quasi-exponential, `ln|N_min| ~ 0.87·δT` on the test grid (the sharp
    Bernstein/Paley-Wiener rate is `e^{δT}`). The CROSSOVER (invisible → visible) is at
    `x = δT ~ 1`. Note `δT` is the *gate* but not a perfect invariant: at fixed `δT=2`,
    the split `(δ=0.2,T=10)` gives `−8.3` vs `(δ=0.4,T=5)` gives `−5.4` — larger `T`
    (smaller `δ`) yields MORE negative mass, consistent with `T` sitting in the exponent of
    the `cosh(δT)` edge growth. The threshold direction is unchanged: `δT ≳ c₀`.

  ⇒ **Optimal threshold `T*(δ) ≈ c₀/δ`, `c₀ = O(1)`, independent of γ₀.**

The earlier *Gaussian* model (`QUART_uncertainty.py`) gave a spurious `T ~ 1/√(γ₀δ)`: that is
an artifact of the Gaussian NOT being band-limited — its tail reaches up to height γ₀.
The band-limited (true support) law is **γ₀-free: `T ~ 1/δ`.**

A single matched *positive* bump `h = |sinc|²` is provably BLIND: its imaginary-shift
continuation `(sinh(aδ)/(aδ))² > 0` never goes negative (`QUART_bandlimited.py`). Negative
mass requires an OSCILLATING band-limited `h` with a double zero at γ₀ — resolvable only at
type `T ≳ 1/δ`.

## TASK 3 — the honest crux: why bounded positivity gives NO zero-free region

At `T ≤ log2 = 0.6931…` the prime sum is **empty** and `Q = ARCH + POLE ≥ 0` is a THEOREM
(Yoshida). **Honestly re-verified** with GENUINELY compactly-supported test functions (Hann
bumps, exact support, condition number 1–12) in `QUART_yoshida_honest.py`: min eigenvalue is
**strictly > 0** and decreases monotonically to ≈ 0 as `T → log2` (T=0.69 → +0.0041). The
prior Gaussian-basis scripts (`yoshida_clean.py`, etc.) reported NEGATIVE min eigenvalues
(−0.25 to −0.82) and wrongly excused them as "conditioning" — their Gaussian basis LEAKS
outside `[−T,T]`, so their "prime sum empty" premise was false. **This flaw is now corrected.**

Consequence: the quartet mass `N` is a **sub-part** of the provably-nonnegative form
`ARCH+POLE`. So for EVERY `(δ,γ₀)` the positive floor `≥ |N_neg|`. The maximal *detectable*
off-line displacement at `T = log2` is **NONE**: bounded short-support positivity carries
**zero** zero-location information. "Invisible until 1/δ" becomes, at `T=log2`, "invisible
for ALL δ". This is precisely WHY `Q_T ≥ 0` on the unconditional cone yields no zero-free
region — and why Yoshida's `T < log2` does not produce a fixed-width unconditional strip.

## TASK 4 — support cost of a width-w zero-free region

To certify "no zeros with displacement `δ ≥ w`", the form must be able to produce negative
mass for every such zero; by (★) that needs `δT ≳ c₀`, i.e.

      T_needed(w) ≳ c₀ / w,    c₀ = O(1).

As `w → 0` (a fixed strip arbitrarily close to Re=½, i.e. RH), `T_needed → ∞`: you need
**unbounded support = full-space Weil positivity = RH-strength.** No finite `T` gives a
fixed-width unconditional strip. The bounded cone `T=log2` corresponds to `w=∞` (no info),
fully consistent.

## TASK 5 — the SAME uncertainty constant in different clothes

| Framework | The cap | Off-line zero seen when |
|---|---|---|
| **Yoshida** `T<log2` | support cut at the FIRST PRIME; additive `(−log2,log2)` = multiplicative `(½,2)` | never (empty prime sum) |
| **Bombieri** | "truncation `t` big enough" | `δ·t ≳ c₀` (exactly our `T≳1/δ`) |
| **Sonin space** (Connes) | phase-space/prolate cutoff parameter = support cutoff; positivity on the COMPLEMENT of cutoff range | bounded support = inside cutoff = blind |
| **Li / Keiper–Li** | index `n` (resolution); `λ_n` for an off-line zero grows **exponentially in n** | `n` large = `T` large |
| **de Bruijn–Newman** | backward-heat gap | gap closes only as support → ∞ |

All are one Fourier uncertainty principle: a feature at displacement `δ` off the real axis is
resolved only with bandwidth/support `T ≳ 1/δ`. Confirmed against the literature: Bombieri's
theorem explicitly needs the truncation "big enough"; the Keiper–Li `λ_n` of an off-line zero
grows exponentially in `n` — the same `e^{δT}`-type growth we measured.

## VERDICT (honest)

- `WeilPositivityOnSupport(T) ⟹ zero-free β ≤ ½ + c/T` is **TRUE only with `c → ∞` as the
  strip narrows**: the honest implication is `T_needed(w) ≳ c₀/w`, so a FIXED-width strip
  needs `T = ∞`. On any BOUNDED support (in particular the only UNCONDITIONAL cone, `T<log2`)
  the implication is **VACUOUS**: positivity is forced there as a theorem (Yoshida) and the
  off-line quartet mass is a sub-part of that nonnegative form, hence undetectable for ALL δ.
- **No new unconditional zero-free strip.** Finite positivity gives finite resolution; a
  fixed strip is exactly RH-strength. The "1/δ" is not a loose heuristic — it is the exact
  gate `δT ~ 1` in identity (★), with a γ₀-independent O(1) constant.
- Best honest statement: **negativeWeilMass(δ,γ₀,T) is bounded by `4(cosh(δT)−1)∫|g|`, i.e.
  `O((δT)²)·(on-line mass)` for `δT ≲ 1` and `O(e^{δT})` beyond** — so bounded-support
  Weil positivity yields a zero-free region of width only `≳ c₀/T`, which `→ ½` (trivial) as
  `T` stays bounded, and recovers RH only as `T → ∞`.
