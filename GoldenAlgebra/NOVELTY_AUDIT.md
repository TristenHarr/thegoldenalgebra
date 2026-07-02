# Novelty Audit: the displacement-moment bound Σ_{0<γ≤T}(β−½)² ≪ T/log T

**Auditor stance:** ruthless referee. **Date:** 2026-05-31.
**Verdict in one line: FOLKLORE.** The bound is a two-line corollary of a classical
1946 theorem (Selberg's zero-density estimate), and the underlying object
`Σ(β−½)` is one of the oldest tools in the subject (Littlewood's lemma, 1924).
It is **not novel as a theorem.** The most that can be claimed is mild novelty of
*framing/packaging* — and even that is weak.

---

## 1. What the bound actually is, and is it correct?

Claim: `Σ_{0<γ≤T} (β−½)² ≪ T/log T`, equivalently the mean-square horizontal
displacement `(1/N(T)) Σ(β−½)² ≪ 1/log²T`.

**The math checks out** (verified symbolically, `/tmp/novelty_audit`):

- **Layer-cake identity (exact, elementary):**
  `Σ_{β>½} (β−½)² = 2 ∫₀^{1/2} u · N(½+u, T) du`, where `N(σ,T) = #{ρ : β>σ, 0<γ≤T}`.
  Per-zero: `2∫₀^d u du = d²`. Verified.
- **Selberg (1946):** `N(½+u, T) ≪ T^{1−¼u} log T` for `0 < u ≤ ½`. (Confirmed as
  classical, in Titchmarsh §9.) Substituting and integrating:
  `Σ(β−½)² ≪ T log T ∫₀^{1/2} u·T^{−u/4} du ≪ T log T · (1/(c² log²T)) = O(T/log T)`.
  The `∫₀^∞ u e^{−cuL} du = 1/(c²L²)` is what produces the `1/log²T` saving over the
  trivial `¼N(T) ≍ T log T`. Verified symbolically.

So: correct, and exactly a `(log T)²` improvement over the trivial bound. **But note
the logical posture:** under RH every `β=½`, so the LHS is *identically 0* and the
bound is vacuous. The statement only has content **unconditionally**, where it is
precisely a repackaging of Selberg's density theorem. There is no new input.

## 2. The object `Σ(β−½)` is ~100-year-old folklore (this is the decisive point)

The first-power sum is **not** an auxiliary — it is literally the left-hand side of
**Littlewood's lemma**, the workhorse behind every zero-density estimate:

> **Littlewood's lemma** (as stated verbatim in Simonič, arXiv:1910.08274, §4.2):
> for `f` holomorphic on the rectangle `σ ≤ Re s ≤ a`, `T ≤ Im s ≤ 2T`,
> `2π ∫_σ^a n_f(τ) dτ = ∫_T^{2T} (log|f(σ+it)| − log|f(a+it)|) dt + ∫_σ^a (arg f(τ+i2T) − arg f(τ+iT)) dτ`.

Taking `f=ζ`, `σ=½`, the LHS `∫_{1/2}^1 N(τ,T) dτ` **equals `Σ_{0<γ≤T,β>½}(β−½)`**
exactly (this is the same layer-cake at `p=1`). So the displacement sum *is* the
Littlewood-lemma integral of `log|ζ|` on the critical line. This identity is in:

- **J. E. Littlewood, "On the zeros of the Riemann zeta-function," Proc. Camb. Phil.
  Soc. 22 (1924), 295–318.** The original.
- **E. C. Titchmarsh, *The Theory of the Riemann Zeta-Function* (2nd ed., Heath-Brown),
  §9.9 and Ch. 9–11.** Standard textbook treatment of `∫N(σ,T)dσ` via Littlewood's lemma.
- **A. Selberg, "Contributions to the theory of the Riemann zeta-function," Arch.
  Math. Naturvid. 48 (1946), no. 5, 89–155.** Source of `N(σ,T) ≪ T^{1−¼(σ−½)}log T`.
- **Sekatskii et al., "On the use of the generalized Littlewood theorem…,"
  arXiv:2204.12925** — explicitly uses the contour-integral-of-log form to compute
  *sums of powers of (ρ − vertical line)* over zeros. This is exactly the `Σ(β−½)^p`
  machinery, treated as a known tool.

**Crucially, the second moment is already classical too, via S₁(t):**
Define `S(t) = (1/π) arg ζ(½+it)` and `S₁(t) = ∫₀^t S(u)du`. The Littlewood-lemma
integral of `log|ζ|` on the critical line is, up to explicit main terms, exactly
`−π S₁(T)` plus the `T log T` boundary terms. **Selberg (1946) proved
unconditionally** (confirmed in arXiv:2006.08503, arXiv:2407.14867):
`∫₀^T S₁(t)² dt = (C₁/2π²) T + O(T/log T)`. This second moment of `S₁` is the
*sharp form* of the same displacement information and the `O(T/log T)` error term is
literally the same order as the claimed bound. The displacement sum is wired directly
into Selberg's `S(t)`/`S₁(t)` theory, which is in every analytic-number-theory course.

## 3. Search for the exact statement Σ(β−½)² ≪ T/log T in the literature

Exhaustive searching (Titchmarsh, Ivić surveys, Selberg, Montgomery, Simonič 2019,
Tao–Trudgian–Yang 2025 / ANTEDB, S(t)/S₁(t) literature, "horizontal distribution,"
"moments of distance of zeros," "second moment displacement"):

- **No source states `Σ(β−½)² ≪ T/log T` as a named/numbered theorem.** It is not in
  Titchmarsh, not in Ivić's *The Riemann Zeta-Function* / his zero-distribution survey
  (empslocal.ex.ac.uk/.../Ivic-Sanutalk.pdf — explicitly checked, no displacement-moment
  sum, no `∫N(σ,T)dσ`), not in the ANTEDB zero-density chapter
  (teorth.github.io/expdb — confirmed: tracks `N(σ,T)`, `A(σ)`, large values, and "zero
  additive energy," but **no displacement moments**).
- This **absence is itself diagnostic**: it is absent not because it is unknown, but
  because it is a trivial corollary nobody bothers to state. The standard "sums over
  zeros" people *do* write down are `Σ 1/γ`, `Σ 1/ρ`, `Σ 1/|ρ|²` (e.g. arXiv:2009.05251,
  1307.5723) and ordinate sums — the *vertical* distribution. The *horizontal* sum
  `Σ(β−½)` is left implicit inside Littlewood's-lemma / `S₁` computations.

## 4. What is the SHARPEST known statement (the real state of the art)?

This is the part that actually matters, and it **kills any sharpness novelty**:

- The **first-power** sum has an essentially *exact* unconditional evaluation:
  `Σ_{0<γ≤T}(β−½) = (1/2π)∫₀^T log|ζ(½+it)| dt + (explicit main terms) + O(log T)`,
  via Littlewood's lemma applied to `ξ`/`ζ`. Combined with the
  Littlewood–Hardy `∫₀^T log|ζ(½+it)|dt = O(T)` this gives `Σ(β−½) = O(T)`
  unconditionally, with explicit constants.
- The **second-power** sharp form is **Selberg's** `∫₀^T S₁² = (C₁/2π²)T + O(T/log T)`
  (1946, unconditional), refined by **Fujii** and (under RH) by **Goldston** and
  others. This is *stronger and more precise* than `Σ(β−½)² ≪ T/log T`: it pins the
  asymptotic main term, not just an upper bound. Anyone wanting the second moment of
  horizontal displacement reaches for `S₁`, and gets an asymptotic, not an `≪`.
- Frontier zero-density work (**Tao–Trudgian–Yang, arXiv:2501.16779, 2025**; Simonič
  arXiv:1910.08274, 2019; Heath-Brown; Conrey; PRZZ) is about *sharpening
  `N(σ,T)` itself* — which would *automatically* sharpen the displacement-moment
  constant. The displacement moment is downstream of, and strictly weaker than, the
  density estimates that the whole field is actively pushing.

## 5. Referee verdict (brutally honest)

**(a) Is `≪ T/log T` already in the literature explicitly?**
Not verbatim as a stated theorem — but its sharp parent (`∫S₁² = cT + O(T/log T)`,
Selberg 1946) is, and the bound is an immediate weakening of it. So "explicitly stated"
= effectively yes (Selberg's `S₁` second moment); "stated in this exact `Σ(β−½)²`
notation" = no, because it's too trivial to bother.

**(b) Is it folklore?** **Yes, unambiguously.** Two lines for any analytic number
theorist: layer-cake + Selberg `N(σ,T)`. Both inputs are 80–100 years old and in the
standard textbook (Titchmarsh §9). An expert would not regard `Σ(β−½)² ≪ T/log T` as a
theorem; they would regard it as an exercise, and a *non-sharp* one at that (Selberg's
`S₁` asymptotic is strictly better).

**(c) Is the FRAMING (displacement moments / mean-square distance / "anti-Herglotz")
novel?** Marginally and weakly. "Mean-square horizontal displacement of zeros" is a
mild rebranding of Selberg's `S₁`-theory / the Littlewood-lemma integral. The phrase
isn't standard, but the *quantity* is. The "anti-Herglotz" packaging is non-standard
terminology but does not correspond to a new mathematical object — `Σ(β−½)` is the real
part of `Σ 1/(s−ρ)`-type sums whose sign/monotonicity (Herglotz/Pick) structure is
classical (Hadamard product, `Re ζ'/ζ`). **No defensible novelty claim survives here.**

**(d) Sharpest known statement about `Σ(β−½)^p` / horizontal distribution:**
- `p=1`: exact, `Σ(β−½) = (1/2π)∫₀^T log|ζ(½+it)| + main terms`, `= O(T)` uncond.
  (Littlewood 1924; Titchmarsh §9; Selberg `S₁`).
- `p=2`: **Selberg's asymptotic** `∫₀^T S₁(t)²dt = (C₁/2π²)T + O(T/log T)` (1946),
  which dominates `Σ(β−½)² ≪ T/log T`.
- General horizontal control flows from `N(σ,T)` estimates, currently being sharpened
  by Tao–Trudgian–Yang (2025) and the ANTEDB program.

### Bottom line for any publishability claim
Do **not** present `Σ(β−½)² ≪ T/log T` as a new result. It is folklore, it is vacuous
under RH, its sharp form (Selberg's `S₁` second moment) predates it by ~80 years, and
the field's active frontier (`N(σ,T)`) sits strictly upstream of it. The honest move is
to cite Selberg (1946), Littlewood (1924), and Titchmarsh §9, and treat the bound as a
known consequence — not a contribution.

---

## References (exact)
1. J. E. Littlewood, *On the zeros of the Riemann zeta-function*, Proc. Camb. Phil.
   Soc. **22** (1924), 295–318.
2. A. Selberg, *Contributions to the theory of the Riemann zeta-function*, Arch. Math.
   Naturvid. **48** (1946), no. 5, 89–155.
3. E. C. Titchmarsh (rev. D. R. Heath-Brown), *The Theory of the Riemann Zeta-Function*,
   2nd ed., Oxford, 1986 — §9 (esp. §9.9), Ch. 9–11 (zero density, Littlewood's lemma).
4. A. Ivić, *The Riemann Zeta-Function*, Dover, 2003 — zero-density chapter;
   survey "The distribution of zeros of the zeta-function"
   (empslocal.ex.ac.uk/people/staff/mrwatkin/zeta/Ivic-Sanutalk.pdf).
5. A. Simonič, *Explicit zero density estimate for the Riemann zeta-function near the
   critical line*, arXiv:1910.08274 (Littlewood's lemma stated verbatim, §4.2;
   explicit Selberg `N(σ,T)`).
6. T. Tao, T. Trudgian, A. Yang, *New exponent pairs, zero density estimates, and zero
   additive energy estimates: a systematic approach*, arXiv:2501.16779 (2025); ANTEDB,
   teorth.github.io/expdb (zero-density chapter — tracks `N(σ,T)`, no displacement moment).
7. Selberg `S₁` second-moment line: e.g. *The second moment of S_n(t) on RH*,
   arXiv:2006.08503; *On a level analog of Selberg's result on S(t)*, arXiv:2407.14867
   (both quote `∫₀^T S₁² = (C₁/2π²)T + O(T/log T)`).
8. S. Sekatskii et al., *On the use of the generalized Littlewood theorem…*,
   arXiv:2204.12925 (contour-integral-of-log evaluation of sums of powers of zeros).
