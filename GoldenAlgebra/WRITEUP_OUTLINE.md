# Honest Writeup Outline — what is, and is not, a contribution

*Calibrated after a four-way skeptical audit (novelty, Littlewood/`S₁`, salvage, calibration).
The one-sentence honest summary: there is no new theorem; the defensible object is a **Lean 4
formalization of an anti-Herglotz framework for RH**, in which classical results are recast in a
displacement/sign-law language and machine-checked. Every mathematical claim below is tagged
**[classical — cite]** or **[formalization contribution]**. Nothing is claimed as a new theorem
of analytic number theory.*

---

## Proposed framing

**Title (honest):** *A Lean 4 formalization of an anti-Herglotz / displacement framework for the
Riemann zeta zeros.*

**Genre:** formalization paper (e.g. ITP/CPP/journal of formalized mathematics), **not** an
analytic-number-theory research paper. The value is the verified library and the unifying
language, not new mathematics.

**What it must NOT claim:** a proof of RH; novelty for the displacement-moment bound; that zeros
are "measured" close to the line (they are measured *on* it; the bounds constrain hypotheticals).

---

## §1. The anti-Herglotz reduction  **[classical equivalence — cite; formalized]**

`G(z) := −Im(Ξ'/Ξ)(z) ≥ 0` on the UHP `⟺` RH, with `Ξ(z)=ξ(½+iz)`. This is the Hermite–Biehler /
Lagarias sign-law equivalence (cite Lagarias; de Branges). **Formalization contribution:** the
pole-probe engine (`antiHerglotz_plus_symmetry_forces_real_zeros_complex`) and the bridge to RH
are machine-checked in Lean, axiom-clean.

## §2. Height vs displacement decomposition  **[exposition; formalized kernels]**

`ρ = ½ + η + iγ`, `η = β−½`. Real-supported paired-Cauchy kernels are anti-Herglotz by
construction (`finitePositivePairedTail_antiHerglotz` — formalized). The exact displacement
kernel `K_z(η,γ) = −Im D_quad` is given in closed form. **Honest note:** the model side is
elementary; the content is entirely in the displacement.

## §3. Displacement moments  **[CLASSICAL — Littlewood 1924, Selberg 1946; cite, do not claim]**

`Σ_{0<γ≤T}|β−½|^p ≪_p T/(log T)^{p−1}`; mean `(1/N(T))Σ(β−½)² ≪ 1/log²T`.
- **Provenance, stated openly:** `Σ(β−½)` is the LHS of **Littlewood's lemma (1924)**
  (Titchmarsh §9.9). In fact the **first moment has an exact identity and is far sharper:**
  `2π·Σ_{β>½,0<γ≤T}(β−½) = ∫₀^T log|ζ(½+it)|dt + 𝒜(T)`, and since the signed mean of `log|ζ|`
  is `0` (Selberg), this gives `Σ_{β>½,γ≤T}(β−½) = O(log T)` — vastly smaller than `T/log T`.
  This is pure Littlewood/Selberg, **classical, not ours**. The *second* moment is **not** given
  by Littlewood (linear in `β−½`); via Fubini `Σ(β−½)² = ∫_½^1 2(σ−½)N(σ,T)dσ` it depends on
  `N(σ,T)`, governed by **Selberg's `S₁`-theory (1946)** (sharper asymptotic
  `∫₀^T S₁² = (C₁/2π²)T + O(T/log T)`). Our `≪ T/log T` is a two-line corollary of Selberg
  density via the layer-cake — and the agent confirmed the `log|ζ|`-moments route does **not**
  beat it (crossing `σ=½ → σ>½` reintroduces the same near-line density input).
- **Presented as:** a *formalized, explicit-constant* corollary (Lean files
  `ScratchDisplacementMoment{,Family,Sharp}`), constant `64 → 49/16` via Conrey. **Not** as new.
- **Calibration (must appear):** every verified zero is *on* the line, so the actual sum is `0`;
  the bound constrains hypothetical off-line zeros, and is in fact a *coarsening weaker than its
  inputs* (ZFR + density each say more). Frame as "quantitative constraint on potential
  violations."

## §4. The resolution principle  **[synthesis / observation; formalized]**

Every finite-scale criterion detects displacement only at `δ·T ≍ 1`. Formalized uncertainty
lemma `cosh(δT)−1 = (δT)²/2 + O((δT)⁴)`, instantiated for Weil / Báez–Duarte / de Bruijn–Newman /
Li, with `resolution_universality` (all gates `=1`). **This is the most original *observation*** —
the typical displacement `1/log T` *is* the resolution scale (`T_eff ∼ log T`), tying §3 to the
gate. Present as a structural synthesis, honestly noting the pieces (Bombieri uncertainty, Selberg
`S₁`, Connes/Sonin) are individually known; the unified `δT~1` statement-and-formalization is the
new packaging.

## §5. The averaged sign-law illustration  **[formalization contribution; nonvacuous]**

`(1/T)∫₀^T (G(x+iY))₋ dx ≤ 2π·T^{−8Y/7}·log T → 0` — the negative part of `G` on the line at
height `0<Y<½` has density-zero average. **Nonvacuous at human heights** (`Y≥0.29` at `T=10⁶`,
detects an inserted fake off-line zero at `T≈40`), `ScratchAveragedSignLaw` (axiom-clean). Honest
caveats: still a zero-density corollary in anti-Herglotz language; the small-`Y` crossover
`exp(O(1)/Y)` is intrinsic. This is the one place the *framework* produces a clean, nonvacuous,
machine-checked statement that isn't a bare rephrasing — present it as such, modestly.

## §6. Bounded RH-to-H  **[reconstruction; formalized]**

`RH_below_H_of_verifiedZeros_fullyDerived`: verified-on-line-to-`H` ⟹ no off-line zeros below `H`,
through the anti-Herglotz machine (formalized, axiom-clean). A formal reconstruction of
finite-height RH verification in the sign-law language; the input (verified zeros) is external.

## §7. Honest limitations / the wall  **[essential section]**

Why the framework does *not* prove RH, stated as proven facts (cite our Lean obstruction files):
kernel signature `++−−`; Yoshida cone sharp at `log2`; the prime obstruction is a moving
multi-mode packet; the axis is a *saddle/max* of every natural arithmetic functional (RH is a
one-sided cone); super-resolution fails (explicit fake measure); the Euler→Herglotz transfer is
free only to `Re s=1` and `Re=1→½` is RH (Davenport–Heilbronn witness). These belong in the paper
as the honest boundary of the method.

---

## What goes where (referee-proofing)

| Claim | Status in paper |
|---|---|
| RH proved | **never** |
| `Σ(β−½)^p ≪ T/(log T)^{p−1}` | corollary of Littlewood/Selberg — **cited, formalized, not claimed** |
| anti-Herglotz `⟺` RH | classical (Lagarias/de Branges) — cited, formalized |
| `δT~1` universality | synthesis/observation + formalization — modest contribution |
| averaged sign-defect (nonvacuous) | formalization contribution — the one clean framework result |
| bounded RH-to-H | formal reconstruction |
| Lean library (no sorry, no axioms) | **the actual contribution** |

## Verdict

A defensible paper exists **only** as a formalization-and-framework contribution with the
mathematics openly attributed to Littlewood, Selberg, Conrey, de la Vallée Poussin, Lagarias,
Bombieri, Connes. The displacement-moment bound is folklore and must be cited, not claimed. The
genuine, referee-proof contributions are: (i) the machine-checked anti-Herglotz library; (ii) the
formalized `δT~1` resolution theory; (iii) the one nonvacuous averaged sign-law. That is honest,
modest, and real.
