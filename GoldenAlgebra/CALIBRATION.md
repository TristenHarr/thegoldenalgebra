# CALIBRATION: What does `Σ_{0<γ≤T}(β−½)² ≪ T/log T` actually say?

**An honest, RH-agnostic audit of the displacement-energy bound.**

Date: 2026-05-31. This document does NOT assume RH. It is written to keep us
honest about what we would be *claiming*, as distinct from what is *measured*.

Notation: nontrivial zeros are `ρ = β + iγ`. Write the **displacement** `η = β − ½`.
By the functional equation, zeros are symmetric about the line: if `β+iγ` is a zero
so is `1−β+iγ`, hence `η` and `−η` both occur and `(β−½)² = η²` is symmetric.
Define the **displacement energy**
```
    S(T) := Σ_{0<γ≤T} (β − ½)².
```

---

## 0. The one-paragraph honest summary

`S(T) ≪ T/log T` is an **unconditional** theorem (true regardless of RH). But its
**content is entirely hypothetical**: it bounds the total squared displacement of
*off-line zeros that no one has ever observed*. On every range that has actually been
verified — up to height `T ≈ 3×10¹²`, all `≈1.236×10¹³` zeros — the measured value is
**`S(T) = 0` exactly**, because every known zero has `β = ½`. So on verified ranges the
theorem reads `0 ≤ 32·T/log T`, which is trivially true and conveys no measurement.
The bound is a **quantitative constraint on potential RH violations**, not a measurement
that "zeros lie close to the line." The correct framing is the former; the latter
oversells it.

---

## 1. What the theorem constrains (Task 1)

The statement `S(T) ≪ T/log T` is unconditional, but unpacking it:

- **If RH is true**, every `β = ½`, so `S(T) = 0` for all `T`, and the bound is the
  trivially-true `0 ≪ T/log T`.
- **If RH is false**, there exist off-line zeros with `η ≠ 0`. The theorem then says:
  *the sum of their squared displacements, up to height `T`, is at most a constant times
  `T/log T`.* This is the only regime in which the bound carries information.

Therefore the honest reading is:

> **`S(T) ≪ T/log T` bounds the displacement energy of any unverified, hypothetical
> off-line zeros. It says nothing about the actual (verified) zeros, for which the
> quantity is identically zero.**

It is a ceiling on a population whose existence is unknown, not a description of an
observed one.

### Numerical anchor (verified, this machine)

`mpmath` check of the first zeros — each sits on the line to `<10⁻²⁴`:

| zero n | γ (≈) | \|ζ(½+iγ)\| | (β−½)² |
|---|---|---|---|
| 1 | 14.134725 | 5.1e−26 | 0 |
| 2 | 21.022040 | 2.2e−25 | 0 |
| 3 | 25.010858 | 2.2e−25 | 0 |
| 4 | 30.424876 | 7.0e−26 | 0 |
| 5 | 32.935062 | 2.4e−25 | 0 |

Combined with Platt–Trudgian (RH verified to `T = 3·10¹²`, `12 363 153 437 138` zeros,
all on the line and simple), the **measured** partial sum is `S(T) = 0` for every
computable `T` to date.

At the verification frontier `T = 3×10¹²`, the theorem's ceiling is
`32·T/log T ≈ 3.3×10¹²` — i.e. even there the theorem only *certifies* that any
undetected off-line displacement energy is `≲ 3×10¹²`, while the **measured** value
is `0`. The entire content of the bound lives in the gap between "certified ceiling"
and "measured value," and that gap is populated only by hypotheticals.

---

## 2. Conjectured true order, and is there a lower bound? (Task 2)

- **Under RH:** `S(T) = 0` exactly. Trivially `o(T/log T)`, indeed identically zero.
- **Unconditionally, expected order:** there is no nonzero lower bound known, and none
  expected. The density of zeros off the line is conjecturally zero (RH), and even the
  best unconditional partial results point downward, not toward a positive floor:
  - Pratt–Robles–Zaharescu–Zeindler (2020): **≥ 41.7%** of zeros are *exactly* on the
    line (and ≥ 40.7% simple and on the line) — unconditionally. These contribute `0`
    to `S(T)`.
  - Zero-density theorems force the off-line population to be a vanishing proportion of
    all zeros (`N(σ,T)/N(T) → 0` for any fixed `σ > ½`).
- **Is `S(T) = o(T/log T)` expected?** Yes — overwhelmingly. Under RH it is `0`. Even
  without RH, no mechanism is known that would make `S(T)` as large as its proven
  ceiling; the `T/log T` rate is an *upper-bound artifact of the method* (see §3), not a
  predicted growth rate.
- **Is there any unconditional reason `S(T)` is bounded *below* by a positive function?**
  **No.** There is no known unconditional argument forcing `S(T) > 0`. It is entirely
  consistent with all current knowledge that `S(T) = 0` for all `T` (this is RH). So the
  honest statement is: `0 ≤ S(T) ≪ T/log T`, with the left endpoint achieved on every
  verified range and conjecturally everywhere.

**Conclusion:** the *conjectured true order is `0`*; the proven order `≪ T/log T` is a
ceiling, and the genuine gap between conjecture (`0`) and theorem (`T/log T`) is the
honest measure of our ignorance about off-line zeros.

---

## 3. Where `T/log T` comes from: ZFR × density together (Task 3)

The bound is **not** obtained by naively integrating a generic zero-density estimate —
doing that with an Ingham-type bound `N(σ,T) ≪ T^{3(1−σ)/(2−σ)}log⁵T` *diverges* at the
line (the near-line region `σ→½` degenerates to the full count `~T log T`, and the
`η²`-weight is too weak to tame it). The `T/log T` rate requires the **two inputs
combined**:

**(A) Zero-free region (how FAR off the line a zero can be).**
The classical de la Vallée Poussin region `β < 1 − c/log γ` gives a hard cap on
displacement:
```
    η = β − ½ < ½ − c/log γ        (maximum possible displacement at height γ)
```
(Vinogradov–Korobov sharpens the *far* region to `1−β ≪ ((log t)^{2/3}(loglog t)^{1/3})⁻¹`,
explicit constant `1/53.989` (Mossinghoff–Trudgian–type), but the *near-line* control
below is what governs the moment.)

**(B) Near-line zero-density (how MANY zeros at each displacement).**
Selberg's estimate is the right input because it **decays exponentially in `η`**:
```
    N(½+η, T) ≪ T^{1 − η/4} · log T = (T log T) · e^{−(η/4)·log T}.
```

**Combining via integration by parts** (with `S(T) = 2∫₀^{η_max} η·N(½+η,T) dη`):
```
    S(T) ≪ 2·(T log T) ∫₀^∞ η·e^{−(log T/4)·η} dη
          = 2·(T log T) · 16/(log T)²
          = 32 · T/log T.
```

**Verified numerically (this machine):** the ratio `S(T)/(T/log T)` converges to the
constant **32** as `T→∞`:

| T | S(T) majorant | T/log T | ratio |
|---|---|---|---|
| 10⁶ | 1.18e6 | 7.24e4 | 16.4 |
| 10⁹ | 1.12e9 | 4.83e7 | 23.3 |
| 10¹² | 9.93e11 | 3.62e10 | 27.4 |
| 10¹⁵ | 8.60e14 | 2.90e13 | 29.7 |

→ 32, confirming the rate is **exactly `T/log T`** for this method, not smaller.

**Does the moment capture both "not too far" AND "not too many"?** It captures both, but
**weighted toward the near-line regime.** The `η`-integral is dominated by `η ~ 1/log T`,
i.e. by hypothetical zeros within `O(1/log T)` of the line — precisely the zero-free-region
scale. Consequences:

- The **far** part of the ZFR (`η` close to `½−c/log γ`) contributes negligibly to the
  *moment*, because the Selberg density there is exponentially tiny. So `S(T)` is **not**
  a faithful witness to "a single deep off-line zero": one zero with large `η` contributes
  `η² ≤ ¼` — a bounded amount — which `T/log T` swamps trivially.
- The moment is mainly a statement about **the count of zeros very near the line**. It
  conflates "few far zeros" and "many near zeros" into one scalar and cannot, by itself,
  distinguish them. To separately certify "nothing far" you need the ZFR statement
  directly; to certify "nothing close" you need the density statement directly. The
  squared-displacement moment is a *coarsening* of both.

**Honest takeaway for §3:** `S(T) ≪ T/log T` is a genuine consequence of ZFR + near-line
density, but it is a *coarse, near-line-weighted* combination. It does **not** dominate
the information in either input; the raw ZFR and the raw density estimate each say strictly
more about their respective regimes than the moment does.

---

## 4. The correct honest framing (Task 4)

Two candidate phrasings:

- ❌ **"Zeta zeros are close to the critical line."** This is **wrong as stated** — it
  sounds like a measurement of actual zeros. All *measured* zeros are *on* the line
  (distance `0`), and the theorem says nothing additional about them. The phrasing
  smuggles in the suggestion that we have observed near-line (off-line) zeros and bounded
  their distance. We have not.

- ✅ **"A quantitative constraint on potential RH violations."** This is **correct**. The
  theorem says: *should off-line zeros exist, their aggregate squared displacement up to
  height `T` cannot exceed `≈ 32·T/log T`.* It is a conditional ceiling on a hypothetical
  population.

The honest framing must:
1. State the quantity is `0` on all verified ranges (vacuous there);
2. Present the bound as a constraint on *hypothetical* off-line zeros, conditional on
   their existence;
3. Never describe it as a measured property of known zeros;
4. Acknowledge the conjectured true value is `0` (RH), so the theorem's *informational
   content* is the size of the still-open gap `[0, 32·T/log T]`.

---

## 5. Does this strengthen or weaken publishability? (Task 5 — honest take)

**It strengthens the *legitimacy* and weakens the *hype* — and that is the correct trade.**

- **Legitimate strength.** Unconditional quantitative constraints on the off-line zero
  population are a respected, real category of analytic number theory (Selberg, Levinson,
  Conrey, density estimates, ZFRs). A clean displacement-energy bound `≪ T/log T`,
  *honestly framed as a constraint on violations*, sits squarely in that tradition. It is
  publishable **as what it is**.

- **What would sink it.** Framing it as "zeros are near the line" or implying it measures
  actual zeros, or implying it is *evidence for* RH beyond what the verified computations
  already give. It is not evidence for RH; it is a conditional ceiling that is *consistent
  with* RH and with `41.7%+` of zeros provably on the line.

- **Novelty caveat (be honest).** The ingredients (ZFR + Selberg density + integration by
  parts) are classical. Before claiming novelty, one must check whether `Σ(β−½)² ≪ T/log T`
  (or sharper, e.g. with the Vinogradov–Korobov region replacing `c/log T`, which would
  *improve* the rate) is already in the literature in this exact form. The mechanism here
  is standard enough that a near-equivalent likely exists; the contribution, if any, would
  be in an *explicit constant*, an *improved log-power via VK*, or a *clean self-contained
  formalization* — not in the qualitative `T/log T` rate.

**Net:** publishable as an honest, unconditional **constraint on hypothetical RH
violations**, with the displacement-energy framing and an explicit constant — provided it
is **not** sold as a measurement of zeros nor as progress toward proving RH.

---

## 6. Caveats and reproducibility

- All numerics above were computed with `mpmath` (dps 25–30). The `S(T)` figures are
  evaluations of the **Selberg-density majorant** `2∫η·N(½+η,T)dη`, i.e. an explicit
  upper-bound model, **not** a sum over actual zeros (the actual sum is `0` on all
  computable ranges). They confirm the *order* and *constant* of the majorant, nothing
  about real zeros.
- The constant `32` is method-dependent (de la Vallée Poussin `c/log T` cap + Selberg's
  `T^{1−η/4}`). A different (sharper) density exponent changes the constant and possibly
  the log-power; the `T/log T` rate is robust to the *qualitative* form of these inputs.
- This file assumes **nothing** about RH and makes **no** claim that the bound is evidence
  for it.

## Sources

- Platt & Trudgian, *The Riemann hypothesis is true up to 3·10¹²*, Bull. LMS (2021).
  https://londmathsoc.onlinelibrary.wiley.com/doi/abs/10.1112/blms.12460
- Selberg near-line density `N(σ,T) ≪ T^{1−¼(σ−½)}log T` (1946); see also Simonič,
  *Explicit zero density estimate near the critical line*, arXiv:1910.08274.
  https://arxiv.org/pdf/1910.08274
- Pratt, Robles, Zaharescu, Zeindler, *More than five-twelfths of the zeros... on the
  critical line* (≥41.7% unconditional). https://arxiv.org/pdf/1002.4127 (Bui–Conrey–Young
  41%) and the PRZZ refinement.
- Mossinghoff, Trudgian et al., *Zero-free regions for the Riemann zeta function*
  (Vinogradov–Korobov, explicit constants). https://arxiv.org/pdf/1910.08205
- Ingham/Carlson zero-density background; Goldston & Suriajaya, *Zeta zeros on the
  critical line* (2025), arXiv:2511.20059. https://arxiv.org/pdf/2511.20059
- von Mangoldt explicit formula / Littlewood `S(t)` background (context for sums over
  zeros). https://en.wikipedia.org/wiki/Riemann_hypothesis
