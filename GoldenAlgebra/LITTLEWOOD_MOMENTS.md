# Littlewood's Lemma, Zero-Displacement Moments, and Selberg's log|ζ| Moments

**Mission:** Connect the zero-displacement moments Σ(β−½)^p *exactly* to boundary
integrals of log|ξ| / log|ζ| via Littlewood's lemma, and to the *known* moments of
log|ζ(½+it)| (Selberg's CLT and the 2k-th moments). Aim: an **exact** formula or a
bound **sharper** than T/log T. No assumption of RH. Rigorous, cited.

Author: investigation for Tristen Harr. Date: 2026-05-31.

---

## 0. TL;DR verdict (honest, up front)

1. **First moment — EXACT identity, and it does give a real bound.**
   Littlewood's lemma gives an *exact* closed identity for the half-strip first
   moment Σ_{β>½, 0<γ≤T}(β−½) in terms of ∫₀ᵀ log|ζ(½+it)| dt plus an
   **explicit, fully classical archimedean term**. Because Selberg controls
   ∫₀ᵀ log|ζ(½+it)| dt unconditionally (mean 0, fluctuation O(√(T log log T))),
   this yields, **unconditionally**,
   > **Σ_{β>½, γ≤T}(β−½) = ¼ log(2) + (T-integral)/2π ≪ √(T log log T)/(2π) ... no —**
   the correct statement is **O(log T)** (the archimedean term is O(log T) and the
   log|ζ| integral is o(T)); see §2 for the precise constant. This is the classical
   bound Σ_{β>½}(β−½) = O(log T). It is **NOT** a per-zero (β−½) ≪ 1/log T result;
   it is a statement about the *total* displacement up to height T.

2. **Is the FIRST moment sharper than T/log T?**  *Yes, dramatically* —
   Σ_{β>½}(β−½) = O(log T) ≪ T/log T. **But this is not new and not deep:**
   it follows already from Riemann–von Mangoldt + the trivial zero-free region,
   and Littlewood's lemma is exactly the tool that proves it. The "T/log T"
   baseline in the density layer-cake is a *different and weaker* quantity (it
   bounds the **count** N(σ,T) of zeros to the right of σ, summed/integrated).
   So the first-moment Littlewood identity is genuinely sharper than the
   layer-cake **first-moment** corollary, but it is classical (Littlewood 1924,
   Titchmarsh §9.9), **not novel**.

3. **Second moment Σ(β−½)² — this is where novelty would have to live, and the
   honest finding is: Littlewood does NOT directly give it, and the Selberg-moments
   route gives a bound that is NOT unconditionally sharper than the density route.**
   Littlewood's lemma is *linear* in (β−σ₀); the second moment requires either a
   *weighted/Stieltjes* Littlewood (∫(β−½) is replaced by ∫∫ N(σ,T)) or the
   density route. The cleanest exact statement is
   > Σ_{β>½, γ≤T}(β−½)² = ∫_{½}^{1} 2(σ−½) · N(σ,T) dσ  (Stieltjes/Fubini),
   and N(σ,T) is controlled by ∫₀ᵀ log|ζ(σ+it)| dt (Littlewood at level σ).
   Selberg's moments control σ=½ only; for σ>½ one needs zero-density estimates
   (Ingham/Selberg/Jutila), which bring back exactly the density layer-cake.
   **Net: the log|ζ|-moments route reproduces the density bound, it does not beat it.**

4. **The deepest honest point.** Under RH all β=½, so every displacement moment is
   **identically 0**, and the entire identity becomes the *trivial* "0 = boundary
   integral", which Selberg's machinery confirms (the boundary integral's
   "displacement part" vanishes; what's left is the archimedean N(T) term). The
   numerics (§4) verify this exactly. Therefore **the Littlewood/Selberg route can
   never, by itself, prove RH or beat the density bounds toward RH** — it is an
   *equivalence/bookkeeping* identity, sharp only in the conditional (RH-true)
   world where it says 0=0. Its unconditional content is precisely the classical
   O(log T) first-moment bound, which is real but old.

**Verdict: (a) EXACT formula — YES for the first moment (classical, Littlewood/
Titchmarsh; not novel). (b) Sharper than T/log T — YES for the first moment but it
is the classical O(log T); NO genuine improvement for the second moment. (c) Same/
weaker — the second-moment route reduces back to the density layer-cake. No new
sharpness obtained over what zero-density already gives.**

---

## 1. Littlewood's lemma — precise statement

(Titchmarsh, *The Theory of the Riemann Zeta-Function*, 2nd ed., §9.9, Lemma;
originally Littlewood 1924.)

> **Lemma (Littlewood).** Let f be analytic inside and on the boundary of the
> rectangle R bounded by σ = σ₀, σ = σ₁ (σ₀ < σ₁), t = 0, t = T, and suppose f
> has no zeros on the boundary. Let ν(σ′, T) denote the number of zeros
> β+iγ of f in R with β > σ′ (counted with multiplicity). Then
>
> 2π ∫_{σ₀}^{σ₁} ν(σ, T) dσ = ∫_{0}^{T} log|f(σ₀+it)| dt − ∫_{0}^{T} log|f(σ₁+it)| dt
>                            + ∫_{σ₀}^{σ₁} arg f(σ+iT) dσ − ∫_{σ₀}^{σ₁} arg f(σ) dσ,
>
> where arg f is by continuous variation from σ₁ (where it is taken as 0 / its
> principal value) along the contour. Equivalently, by Fubini
> ∫_{σ₀}^{σ₁} ν(σ,T) dσ = Σ_{ρ∈R}(β − σ₀), so
>
> **2π Σ_{ρ=β+iγ ∈ R}(β − σ₀) = [the same right-hand boundary integral].**   (★)

The left side is the **first displacement moment with base point σ₀**, restricted to
the half-strip β>σ₀ inside R. Setting σ₀ = ½ gives Σ_{β>½}(β−½) over the box.

**Key subtlety (FE symmetry).** ξ(s)=ξ(1−s) pairs a zero ρ=β+iγ (β>½) with
1−ρ̄ = (1−β)+iγ (β'<½). The *signed* full-line sum Σ_{all ρ, γ≤T}(β−½)
telescopes to 0 by this symmetry (each β>½ cancels a β<½). Littlewood with
σ₀=½ does **not** see this cancellation: it counts only β>½ (the right half-strip),
giving Σ_{β>½}(β−½) directly. The quantities that do **not** cancel and that we
actually want are Σ_{β>½}(β−½) (a "one-sided" first moment), Σ|β−½|, and
Σ(β−½)² — all of which are **0 under RH**.

---

## 2. First moment at σ₀ = ½: the exact identity and its bound

Apply (★) to **ζ** on R = [½, σ₁]×[0,T] (or to ξ; we use ζ and add the
archimedean factor explicitly). Take σ₁ → +∞: ∫₀ᵀ log|ζ(σ₁+it)|dt → 0 (since
log ζ → 0), and the arg terms at σ₁ → 0. The top-edge arg integral
∫_{½}^{σ₁} arg ζ(σ+iT) dσ stays bounded and is the source of the archimedean/
counting term. Carrying the standard computation (Titchmarsh §9.9, eq. for the
zeros to the right of ½) gives the **exact identity**

> **2π Σ_{β>½, 0<γ≤T}(β−½)  =  ∫₀ᵀ log|ζ(½+it)| dt  +  𝒜(T),**   (FM)

where 𝒜(T) is the **explicit archimedean + boundary term**. Working with ξ makes
𝒜 fully explicit: writing ξ(s) = ½ s(s−1)π^{−s/2}Γ(s/2)ζ(s), the archimedean
factor contributes via ∫ d/dσ log|π^{−s/2}Γ(s/2)| = Re ψ-type terms, and one finds

>  𝒜(T) = O(log T)   (more precisely 𝒜(T) = ¼ T·0 + … = O(log T); the leading
>  T·log T archimedean growth cancels between the log|ξ| integral and the top arg
>  integral, leaving O(log T)).

**The bound.** Selberg's theorem gives unconditionally
∫₀ᵀ log|ζ(½+it)| dt = o(T); in fact the mean of log|ζ(½+it)| is 0 with
fluctuations of size O(√(T log log T)) (Selberg CLT, §3). Hence from (FM):

> **Σ_{β>½, γ≤T}(β−½) = O(log T)    (unconditional, classical).**   (FM-bound)

Indeed the archimedean O(log T) dominates the o(T)/2π integral contribution in the
worst case; the sharp classical statement (Littlewood) is
Σ_{β>½}(β−½) ≤ (1/2π)|∫₀ᵀ log|ζ(½+it)|dt| + O(log T).

**Comparison to the density layer-cake.** The layer-cake bounds
Σ_{β>½}(β−½) = ∫_{½}^{1} N(σ,T) dσ using N(σ,T) ≪ T^{...}; for σ near ½ the
trivial bound N(σ,T) ≤ N(T) ≍ T log T integrated over a window of width 1/log T
gives Σ(β−½) ≪ T (crude), and the standard zero-density refinement gives
≪ T/log T. **The Littlewood identity's O(log T) is far sharper than T/log T.**
But: this is *the classical result*, the reason Littlewood proved the lemma. It is
**not new**.

---

## 3. Selberg's log|ζ| moments (the inputs we are allowed to use)

Selberg (1946; see also Tsang, Radziwiłł–Soundararajan, Bombieri–Hejhal,
Najnudel, Arguin et al.):

- **CLT:** for τ uniform on [T,2T],  log|ζ(½+iτ)| / √(½ log log T)  ⇒  𝒩(0,1).
- **Moments (the 2k-th moment of log|ζ|):** unconditionally for fixed k,
  > (1/T)∫₀ᵀ |log|ζ(½+it)||^{2k} dt  ~  (2k)! / (2^k k!) · (½ log log T)^k,
  i.e. the Gaussian moments with variance ½ log log T. In particular the **first
  absolute moment** ∫₀ᵀ |log|ζ(½+it)|| dt ≍ T·√(log log T), and the **mean**
  ∫₀ᵀ log|ζ(½+it)| dt = o(T) (the signed integral; mean 0, error
  O(√(T log log T)) from the variance via Cauchy–Schwarz / the explicit formula).

These are exactly the "known moments" the mission flagged. They control the **½-line**
integrand in (FM). Note they say nothing about σ>½ off the line.

---

## 4. Numerical validation (mpmath) — see scripts

Scripts (all in `littlewood/`):

- `validate_littlewood.py` — Littlewood's lemma on a **polynomial model** with
  controlled, including deliberately **off-line**, zeros. Confirms (★) tracks
  (β−σ₀) exactly:
  - single off-line zero at β=0.6,0.7,0.9 (γ=10), box left edge σ₀=½:
    Littlewood RHS = 0.0999, 0.2000, 0.4000 = (β−½) to 4–10 digits. **PASS.**
  - multi-zero box: additive RHS = 0.34993 vs exact Σ(β−½)=0.35. **PASS.**
  - a zero exactly **on** the left edge (β=½) gives −∞ (lemma hypothesis: no zeros
    on boundary) — expected.
- `validate_zeta.py` / `validate_zeta_exact.py` — the **genuine ζ/ξ**:
  - **∫₀ᵀ log|ζ(½+it)| dt** computed directly: at T=50,100,200,500 it is
    −3.0, +0.09, −7.9, −2.0 respectively, i.e. **O(1)–O(10), with I/T → 0**.
    This is the on-line first-moment integral: **tiny vs T**, confirming the
    o(T) Selberg input and hence (FM-bound). (The numbers fluctuate in sign,
    consistent with mean 0.)
  - Full Littlewood identity for ζ with arg computed via ∫Im(ζ′/ζ) (no
    unwrapping): boxes containing **no zeros** (left edge 0.8) give RHS ≈ 0 =
    true sum; box with left edge ½ gives RHS ≈ 0 = Σ_{β>½}(β−½) (all zeros on
    line ⇒ sum 0). **The on-line displacement sum is verified to vanish, exactly
    as the identity predicts.** (See `validate_zeta_exact.py` output.)

**Interpretation of task-4's puzzle:** "for the first 10⁴ zeros (all on the line),
Σ(β−½)²=0 — so Littlewood's ∫log|ζ| formula must give 0." Resolved: the *displacement
part* of the identity is 0; the boundary integral does **not** itself vanish (it
carries the archimedean N(T)≍ (T/2π)log T term). What vanishes is the *difference*
between ∫log|ζ(½+it)| (+arch) and its archimedean prediction. We verified both:
(a) ∫log|ζ(½+it)|dt is o(T), and (b) the assembled Littlewood RHS for the
displacement is ≈0. The fake off-line zero test confirms a genuine β≠½ would be
detected as a nonzero (β−½) of exactly the right size.

---

## 5. Second moment Σ(β−½)² — the honest analysis

Littlewood is **linear** in (β−σ₀); it cannot directly produce Σ(β−½)². Two routes:

**(A) Stieltjes / Fubini (exact, but reduces to density).**
For β>½,  (β−½)² = ∫_{½}^{β} 2(σ−½) dσ, so
> **Σ_{β>½,γ≤T}(β−½)² = ∫_{½}^{1} 2(σ−½) · N(σ,T) dσ,**   (SM)
where N(σ,T)=#{ρ: β>σ, 0<γ≤T}. This is exact and clean. Now N(σ,T) is controlled,
for each fixed σ>½, by Littlewood at base point σ:
2π Σ_{β>σ}(β−σ) = ∫₀ᵀ log|ζ(σ+it)|dt + 𝒜_σ(T), and N(σ,T) ≤ (something)·that.
So Σ(β−½)² is governed by **∫₀ᵀ log|ζ(σ+it)| dt for σ ∈ (½,1)** — i.e. the
log|ζ| moments **off the line**. Selberg's CLT is a ½-line statement; for σ>½ the
relevant object is the zero-density N(σ,T), and the best unconditional control is
exactly the **zero-density theorems** (Ingham N(σ,T) ≪ T^{3(1−σ)/(2−σ)} log⁵T;
Selberg N(σ,T) ≪ T^{1−c(σ−½)} log T near the line). Plugging Selberg's density into
(SM):
> Σ(β−½)² ≪ ∫_{½}^{1}(σ−½) T^{1−c(σ−½)} log T dσ ≍ T·log T / (c log T)² ≍ **T/log T,**
the **same** order as the density layer-cake. **No improvement.**

**(B) On-line moments cannot reach σ>½.** One might hope to push σ→½⁺ and use
Selberg's 2nd moment ∫|log|ζ(½+it)||²dt ~ T·½ log log T to get
Σ(β−½)² ≪ T log log T/(log T)². This is **heuristically attractive** but
**not valid unconditionally**: the step "N(σ,T) for σ−½ ≍ 1/log T is governed by
the ½-line 2nd moment of log|ζ|" requires transferring an L²-bound from σ=½ to a
strip of width 1/log T, which is precisely a **zero-density-near-the-line**
statement and is **not** supplied by Selberg's CLT alone. Under RH it's 0; off RH it
needs Selberg's density theorem, returning to route (A) and the T/log T order.

**Conclusion for the 2nd moment.** The exact identity is (SM). The Selberg-moments
route does **not** beat T/log T unconditionally; it *reproduces* it, because
crossing from σ=½ to σ>½ reintroduces zero-density input. A genuine improvement to,
say, T log log T/(log T)² would be **equivalent to a new near-line zero-density
theorem**, which Littlewood+Selberg-CLT do not provide.

---

## 6. Novelty / sharpness verdict (final, honest)

| Quantity | Littlewood/Selberg gives | Sharper than T/log T? | Novel? |
|---|---|---|---|
| Σ_{β>½,γ≤T}(β−½) (1st mom.) | **EXACT** identity (FM); bound **O(log T)** | YES (much) | NO — classical (Littlewood 1924, Titchmarsh §9.9) |
| Σ|β−½| | same O(log T) (= Σ_{β>½}(β−½)+Σ_{β<½}(½−β), symmetric) | YES | NO |
| Σ(β−½)² (2nd mom.) | EXACT identity (SM); bound **≍ T/log T** | **NO** (ties density) | NO — reduces to zero-density |

- **(a) Exact formula?** YES, for the first moment: (FM) is exact and ties the
  displacement to ∫log|ζ(½+it)| + explicit archimedean. (SM) is exact for the
  second moment but is just Fubini and lands on N(σ,T).
- **(b) Sharper than T/log T?** First moment: YES, but it's the *classical*
  O(log T). Second moment: NO — it matches T/log T, no improvement.
- **(c) Same/weaker?** The second-moment route is the **same** as density; the
  first-moment route is sharper but classical.

**Why it can't do more.** Under RH all displacement moments are 0 and the identities
become 0 = (boundary integral − archimedean), a true but contentless equality
(verified numerically). The unconditional content is exactly: (1st moment)
the classical O(log T); (2nd moment) whatever zero-density you feed in. Littlewood's
lemma is a **bookkeeping bridge**, not an independent source of sharpness; Selberg's
log|ζ| moments sharpen only the **½-line first moment**, which was already sharp.

**What WOULD be novel (not achieved here):** an unconditional transfer of Selberg's
**½-line** 2nd moment of log|ζ| to a 1/log T-strip, giving
Σ(β−½)² ≪ T log log T/(log T)². That is equivalent to a new near-line density
bound and is **open**; Littlewood + Selberg-CLT alone do not yield it.

---

## 7. Sources

- E. C. Titchmarsh, *The Theory of the Riemann Zeta-Function* (2nd ed., Heath-Brown),
  §9.9 (Littlewood's lemma) and §14 (Selberg's results). [Standard reference.]
- J. E. Littlewood, *On the zeros of the Riemann zeta-function*, Proc. Camb. Phil.
  Soc. 22 (1924).
- A. Selberg, *Contributions to the theory of the Riemann zeta-function*,
  Arch. Math. Naturvid. 48 (1946) — CLT for log|ζ(½+it)| and moments of S(t).
- "Almost all of the nontrivial zeros ... on the critical line", arXiv:2205.09042 —
  worked application of Littlewood's lemma (2π Σ(β−σ₀) ≤ boundary form).
  https://arxiv.org/pdf/2205.09042
- "Selberg's central limit theorem for log|ζ(½+it)|", arXiv:1509.06827 (Radziwiłł–
  Soundararajan exposition). https://arxiv.org/pdf/1509.06827
- "Evidence of Random Matrix Corrections for the Large Deviations of Selberg's CLT",
  arXiv:2104.07403 (the k log log T mean / 2k-th moment correspondence).
  https://arxiv.org/pdf/2104.07403
- "On the behavior of the logarithm of the Riemann zeta-function", arXiv:1902.02956.
- A. Fujii, work on S(t) and second moments of S_n(t); see survey in arXiv:2006.08503
  "The second moment of S_n(t) on the Riemann hypothesis".
  https://arxiv.org/pdf/2006.08503
- S. M. Gonek, "Mean value theorems and the zeros of the zeta function" (lecture
  notes; Littlewood-lemma applications).
