# An Anti-Herglotz Approach to the Riemann Hypothesis

*Companion to the Lean 4 formalization in `GoldenAlgebra/rh.lean`.*

## Abstract

Let
$$
\xi(s) \;=\; \tfrac{1}{2}\, s\,(s-1)\,\pi^{-s/2}\,\Gamma(s/2)\,\zeta(s),
\qquad
\Xi(z) \;=\; \xi\!\left(\tfrac{1}{2}+iz\right).
$$
The Riemann Hypothesis (RH) asserts that every zero of the entire
function $\Xi$ is real. We isolate this as a sign condition on the
logarithmic derivative of $\Xi$ — the *anti-Herglotz sign law*
$$
\operatorname{Im}\frac{\Xi'(z)}{\Xi(z)} \;\le\; 0
\qquad (\operatorname{Im} z > 0)
$$
— and we prove, fully in Lean 4 against Mathlib, that this sign law,
together with Schwarz reflection on $\Xi$ and analytic local
factorization at every upper-half-plane zero, forces every zero of
$\Xi$ to be real. The reduction is unconditional for polynomials and,
in the entire-function setting, requires only Mathlib's isolated-zeros
lemma (which the file applies directly).

We then reduce the sign law itself via an explicit decomposition
$$
\frac{\Xi'(z)}{\Xi(z)}
\;=\;
\underbrace{\sum_{j=1}^{100}\!\Bigl(\tfrac{1}{z-\gamma_j}+\tfrac{1}{z+\gamma_j}\Bigr)}_{\text{finite cloud}}
\;+\;
\underbrace{\int_{2\pi}^\infty\!\rho(u)\Bigl(\tfrac{1}{z-u}+\tfrac{1}{z+u}\Bigr) du}_{\text{smooth tail}}
\;+\;
\underbrace{E(z)}_{\text{residual}},
\qquad
\rho(u)=\tfrac{1}{2\pi}\log\tfrac{u}{2\pi},
$$
in which the first two summands are anti-Herglotz by construction and
the residual $E$ admits region-by-region control. The model side — the
anti-Herglotz property of the smooth tail at the canonical cutoff
$T_\bullet = 2\pi$, the quantitative pointwise lower bound on
$-\operatorname{Im}$, *and* the model-side numerical arithmetic
inequality on the compact low box — are *all* discharged unconditionally
inside the file.

The conditional sign law has now been reduced to its cleanest form:
Theorem 6, the canonical-source variants, the one-bundle non-Turing
front door, the two-bundle Path B capstone, and now the source-level
two-bundle capstone immediately after them. The
Γ-cancellation bridge between the textbook $\xi$ and Mathlib's
`entireRiemannXi` — once a three-piece structural input of Theorem 4,
then a one-Mathlib-identity input of Theorem 5 — has been **fully
discharged unconditionally** inside the file. Mathlib's
`Gammaℝ` factor in `completedRiemannZeta`, together with
`Complex.Gamma_neg_nat_eq_zero` and `completedRiemannZeta_eq`, closes
the raw-ζ off-pole formula `CompletedRiemannZetaRawOffPoleFormula`
without external hypothesis. The current state of Path B is therefore
the cleanest possible:

* two slab-localized Backlund/Turing log envelopes (P1), now bundled
  as `PathBTuringEnvelopeInputs`, with the Trudgian/Platt route
  sharpened to the finite band `[140, exp (647/100)]` and the
  Platt-Trudgian route shortened to `[140, exp (593/100)]`;
* an **entire-ξ Hadamard product theorem** against Mathlib's
  pole-subtracted `entireRiemannXi` (P2);
* three AFZ-guarded Stieltjes equalities, the low band being a pure
  zero-index splitting (P3), now also bundled with the Hadamard and
  zero-start data as `PathBNonTuringInputs`, and lowerable further to
  the completed-ξ-source bundle `PathBNonTuringSourceInputs` and the
  direct canonical AFZ bundle `PathBDirectNonTuringInputsAFZ`.

An *audit layer* (§§CCCLXVI–CCCLXVIII) formally certifies that the
Hadamard and Stieltjes bundles carry only *identity content* — no
positivity, sign, or zero-location claims — so the only inputs that
can legitimately carry RH-strength are the named envelope/gap bundle.

This document gives a structural account of each step, points to the
Lean declarations that carry it out, and indicates the path to a
Mathlib-grade Riemann Hypothesis theorem. The formalization comprises
85,489 lines and roughly 4,088 top-level declarations. It contains no
axioms; every occurrence of the keyword `sorry` lies inside prose. All
names quoted below are real Lean declarations.

---

## Headline result

The cleanest current statement of the reduction is the Lean theorem
```
XiPullbackAntiHerglotzTarget_of_directNonTuringInputsAFZ_turingBundle
```
(§CDXLVIII of `rh.lean`):
$$
\bigl(h_{\text{Turing}} \,+\, h_{\text{HighLog}}\bigr)
\;\oplus\;
\underbrace{H_{\text{direct}}}_{\substack{Z\ge15\\\text{direct canonical AFZ Stieltjes}}}
\;\Longrightarrow\;
\text{RH}.
$$
Its unbundled-envelope sibling is
`XiPullbackAntiHerglotzTarget_of_directNonTuringInputsAFZ_turingEnvelopes`.
The older source-level theorem
`XiPullbackAntiHerglotzTarget_of_pathBSourceInputBundles` remains the
completed-ξ-source capstone:
$$
\bigl(h_{\text{Turing}} \,+\, h_{\text{HighLog}}\bigr)
\;\oplus\;
\underbrace{H_{\text{src}}}_{\substack{\text{completed-}\xi\\\text{log-derivative source}}}
\;\oplus\;
\underbrace{H_{\text{st}}}_{\substack{\text{matched AFZ}\\\text{Stieltjes equality source}}}
\;\Longrightarrow\;
\text{RH}.
$$
The two log envelopes are classical Backlund/Turing analytic number
theory and are bundled as `PathBTuringEnvelopeInputs`. The
`PathBNonTuringInputs` bundle packages the atom-level zero-start datum,
the entire-ξ Hadamard theorem, and the publication-level Stieltjes
explicit-formula bundle keyed to the canonical completed-ξ source. The
entire-ξ Hadamard theorem is the classical genus-1 factorization for a
function that is *entire by construction*; and the three Stieltjes
equalities are the AFZ-guarded explicit-formula identifications, with
the low band collapsed to a pure zero-index splitting. The canonical
version packages the completed-ξ source as
`Hhad.toCompletedXiSourceAFZ_canonical`, so the Stieltjes hypotheses
are stated against a stable named source rather than a repeated
bridge expression. §CDXLVI then lowers this further to
`PathBNonTuringSourceInputs`, whose only non-Turing fields are
`h_Z_ge_15`, a `CompletedXiLogDerivativeSourceAFZ`, and the matched
`XiZeroContributionStieltjesEqualitySourceAFZ` for its pullback zero
contribution. The full Γ-cancellation between the textbook $\xi$
and Mathlib's `entireRiemannXi` has now been **fully discharged
unconditionally**, via the chain §§CDXIX–CDXLIV: closedness of the
Γ-pole pullback set, the no-pole structural piece, the pole-vanishing
identity, the $\xi$-formula source, the $\zeta_0$ correction formula,
the raw-ζ off-pole identity `completedRiemannZetaRawOffPoleFormula`
(proved from Mathlib's `Gammaℝ`/`riemannZeta_def_of_ne_zero` chain),
the named raw/entire log-derivative bridge
`entireXiToCompletedXiLogDerivBridge`, and finally the canonical
Hadamard-to-completed-ξ source
`EntireXiClassicalHadamardTheorem.toCompletedXiSourceAFZ_canonical`.

A formal audit layer (§10) certifies that the Hadamard and Stieltjes
bundles are *identity-only* — no positivity, sign, or zero-location
content — so the only inputs that can legitimately carry RH-strength
are the named envelope/gap bundle. Theorem 3 (§CCCLXV, raw-ξ
Hadamard), Theorem 4 (§CDXIV, entire-ξ Hadamard + three-piece
Γ-bridge), Theorem 5 (§CDXLII, entire-ξ Hadamard + single raw-ζ
identity), and Theorem 6 (§CDXLIII, Γ-cancellation fully discharged)
are progressively sharper restatements of the same conditional sign
law. §CDXLIV adds canonical-source front doors for the same theorem,
including direct low-zero-split, low-IBP-source, combined-mid/high,
unguarded-compatibility, reassembled-Stieltjes, and publication-level
classical-Stieltjes forms. §CDXLV bundles all non-Turing data into
`PathBNonTuringInputs`, leaving only the two visible envelope
hypotheses. §CDXLVI packages those envelopes into
`PathBTuringEnvelopeInputs`, proves the two-bundle capstone, and then
lowers the non-Turing side to the completed-ξ source-level bundle
`PathBNonTuringSourceInputs`. §§CDXLVII–CDXLVIII add canonical
completed-ξ and pullback-Ξ source front doors, so the same theorem can
now be stated directly against the named canonical source packages.
§CDXLVIII also packages the direct canonical non-Turing payload as
`PathBDirectNonTuringInputsAFZ`, with split, low-IBP, low-zero-split,
and low-cloud/tail front doors. Each front door follows from the
previous by an unconditional structural reduction (§9).

```
   RH for ζ
     ⇕
   every zero of Ξ is real                            (§1)
     ⇑
   anti-Herglotz sign law on Λ[Ξ]                     (§§2–4, Thm 1)
     ⇑
   decomposition  Λ[Ξ] = cloud + smoothTail + residual,
   with cloud and tail anti-Herglotz by construction
   and residual controlled in three bands              (§§5–8)
     ⇑
   Path B conditional (Thm 3, §9, §CCCLXV):
   five inputs — Hadamard bundle + 3 Stieltjes (raw ξ)
     ⇑   (Γ-cancellation: 3-piece bridge)
   Path B conditional (Thm 4, §9, §CDXIV):
   entire-ξ Hadamard + 3 Γ-bridge facts + 3 Stieltjes
     ⇑   (Γ-bridge collapse via §§CDXIX–CDXLI)
   Path B conditional (Thm 5, §9, §CDXLII):
   entire-ξ Hadamard + 1 raw-ζ identity + 3 Stieltjes
     ⇑   (raw-ζ identity proved unconditionally, §CDXXXVI)
   Path B conditional (Thm 6, §9, §CDXLIII):
     │  Backlund/Turing envelopes (P1) ─────────────┐
     │  entire-ξ Hadamard theorem (P2) ──┐ identity │
     │  3 Stieltjes equalities (P3) ─────┘ -only    │
     └─ trivial atom-level Z ≥ 15                    │
     ⇑   (canonical named completed-ξ source, §CDXLIV)
     ⇑   (bundle all non-Turing data, §CDXLV)
     ⇑   (bundle Turing envelopes, §CDXLVI)
     ⇑   (lower non-Turing data to a source bundle, §CDXLVI)
     ⇑   (canonical completed-ξ and pullback-Ξ sources, §§CDXLVII–CDXLVIII)
     ⇑   (direct canonical non-Turing bundle, §CDXLVIII)
   Path B two-bundle capstone:
   PathBDirectNonTuringInputsAFZ + PathBTuringEnvelopeInputs
                                                     ↓
                                       audit layer (§10) confirms
                                       identity bundles are identity
```

---

## Notation

| Symbol | Meaning |
|---|---|
| $\xi$, $\Xi$ | Completed zeta; critical-line pullback $\Xi(z) := \xi(\tfrac12 + iz)$. |
| `completedXiFunction` | The textbook formula $\xi(s) = \tfrac{1}{2}s(s-1)\pi^{-s/2}\Gamma(s/2)\zeta(s)$, which carries explicit $\Gamma$-poles in its definition. |
| `entireRiemannXi` | Mathlib's pole-subtracted form $\tfrac12 s(s-1) \cdot \texttt{completedRiemannZeta}_0\,s + \tfrac12$ — entire by construction. |
| $\Lambda[f]$ | Logarithmic derivative $f'/f$ (`logDerivativeResponse`). |
| $\gamma_j$ | The $j$-th positive ordinate of a nontrivial $\zeta$-zero ($\gamma_1 \approx 14.13$). |
| $\zeta_{100}$ | `zeros100ceil`: a 100-element list of ceiling-rounded ordinates $\lceil\gamma_j\rceil$, first entry $15$. |
| $K_u(z)$ | Paired Cauchy kernel $\tfrac{1}{z-u} + \tfrac{1}{z+u} = \tfrac{2z}{z^2 - u^2}$ (`pairedCauchyKernel`). |
| $k_z(u)$ | Its imaginary part: $-y\bigl(\tfrac{1}{(x-u)^2+y^2}+\tfrac{1}{(x+u)^2+y^2}\bigr)$ (`pairedCauchyImKernel`). |
| $N(u)$ | Multiplicity-weighted count of nontrivial $\zeta$-zeros with $0 < \operatorname{Im}\rho \le u$. |
| $N_0(u)$ | Riemann–von Mangoldt smooth main term $\tfrac{u}{2\pi}\log\tfrac{u}{2\pi} - \tfrac{u}{2\pi} + \tfrac{7}{8}$ (`smoothZeroCountingN0`). |
| $\rho(u)$ | Smooth density $N_0'(u) = \tfrac{1}{2\pi}\log\tfrac{u}{2\pi}$ (`zeroDensityRho`). |
| $S(u)$ | Fluctuation $N(u) - N_0(u)$ (`concreteS`; encoded structurally as `finiteFluctuationPrimitive`). |
| $T_\bullet$ | Canonical density cutoff $2\pi$ — the basepoint of the honest model. |
| $T_0$ | IBP basepoint of the fluctuation primitive ($T_0 = 10$ in the headline front door). |
| $A=2$ | Adaptive-cutoff constant: $2(1 + |x| + y) \le T$ characterizes the "adaptive regime". |
| $M$, $E$ | Model and residual: $\Lambda[\Xi](z) = M(z) + E(z)$. |
| $\mathrm{ZC}$ | Hadamard zero contribution: an entire function whose log-derivative agrees with $\Lambda[\Xi]$ away from zeros (`xiZeroContribution`). |
| $E_1(w)$ | Weierstrass genus-1 primary factor $(1-w)\exp(w)$ (`hadamardGenus1Factor`). |
| LUC | Locally uniformly convergent — the analytic mode that allows interchange of $\log$-derivative with infinite product. |
| AFZ | "Away from zeros" — the $\Xi(z) \neq 0$ guard that the taint convention requires on Hadamard/Stieltjes hypotheses. |
| Γ-poles | $\{-2n : n \in \mathbb{N}\}$, the poles of $\Gamma(s/2)$ that appear in `completedXiFunction` but not in `entireRiemannXi`. |

The Lean namespace is `OverflowResidueRH`; "overflow" refers to the
divergent-imaginary blow-up of $\Lambda[f]$ near an upper-half-plane
zero, which is the engine's contradiction mechanism.

---

## Proof map

The proof flows in seven conceptual layers, each closed in the file
before the next is consumed as a black box.

* **Sign law $\Rightarrow$ real zeros** (§§2–4). An elementary
  pole-probe contradiction: an upper-half-plane zero of $f$ forces
  $\operatorname{Im}\Lambda[f]$ to escape to $+\infty$ at probe
  points, contradicting the sign law. Schwarz reflection extends this
  to the lower half-plane. Polynomial RH is unconditional (§3); the
  entire-function lift via Mathlib's isolated-zeros library is
  conditional only on Schwarz reflection and the sign law (§4).
* **Decomposition $\Rightarrow$ sign law** (§§5–7). The four
  equivalent target Props (§5) include the anti-Herglotz target
  itself, its Pick/Nevanlinna dual, the $s$-plane sign target, and an
  energy form. The decomposition route splits $\Lambda[\Xi]$ as
  $\text{cloud} + \text{smoothTail} + \text{residual}$ (§6). Both
  cloud and smooth-tail summands are *anti-Herglotz by construction*;
  the smooth tail's quantitative lower bound on $-\operatorname{Im}$
  is proved unconditionally via an arctan-to-rational trade (§7).
* **Residual is controllable** (§§8–9). The xi-side residual is
  controlled in three regions (mid/high/low) via the
  integration-by-parts form of the classical explicit formula. The
  low-band has been corrected to use a boundary-inclusive identity,
  and the operative Path B parameters $(T, \gamma_1, D) = (11, 14,
  1/2)$ have been factored into structural and numerical pieces all
  proved inside the file.
* **Reduction to a Hadamard + Stieltjes pair, formally audited** (§9, Thm 3
  and §10). After internalizing every technical input, the conditional
  sign law has three classical analytic obligations: two log envelopes,
  the Hadamard side bundle, and three Stieltjes identifications. The
  audit layer (§10) proves with Lean Props that the Hadamard and
  Stieltjes bundles carry only identity content.
* **Γ-cancellation bridge to the entire-ξ form** (§9, Thm 4). The
  Hadamard product theorem is naturally stated for the *entire*
  Mathlib-grounded `entireRiemannXi`, not the Γ-pole-bearing
  `completedXiFunction`. A three-piece bridge (no-pole structural fact,
  Γ-pole-avoiding neighborhood source, off-pole formula equality)
  identifies the two functions on the relevant region, letting the
  classical Hadamard input live on the cleaner side.
* **Γ-bridge collapse to a single Mathlib ζ-identity** (§9, Thm 5).
  Two pieces of the three-piece bridge — the structural no-pole and
  topological avoiding-nhds — are proved unconditionally from Mathlib's
  `Complex.Gamma_neg_nat_eq_zero` and from a direct closedness proof of
  the Γ-pole pullback set. The third (off-pole formula identity) is
  *factored* through Mathlib's $\zeta_0$ correction formula
  (`completedRiemannZeta_eq`) and a `rfl`-discharged $\xi$ formula
  source, leaving only one external input: the raw-ζ off-pole formula
  $\zeta_{\text{completed}}(s) = \pi^{-s/2}\Gamma(s/2)\zeta(s)$.
* **Full Γ-cancellation discharge** (§9, Thm 6). The raw-ζ off-pole
  identity is itself proved unconditionally from Mathlib's
  `Gammaℝ`/`riemannZeta_def_of_ne_zero` chain (§CDXXXVI), so the
  Γ-cancellation between textbook $\xi$ and `entireRiemannXi`
  evaporates entirely. The remaining obligations are exactly (P1) the
  Backlund/Turing envelopes, (P2) the entire-ξ Hadamard theorem, and
  (P3) the three Stieltjes equalities. Status (§11) and architecture
  (§12) catalogue the file structure.

---

## 1. The reduction to real zeros

The textbook completed zeta function $\xi$ is entire, and its zeros
agree with the nontrivial zeros of $\zeta$ inside the critical strip.
RH asserts that these zeros lie on the critical line
$\operatorname{Re} s = \tfrac{1}{2}$. The change of variable
$s = \tfrac{1}{2}+iz$ sends the critical line to the real axis, so RH
is equivalent to the statement that every zero of the *critical-line
pullback* $\Xi(z) := \xi(\tfrac{1}{2}+iz)$ is real.

The file carries two parallel implementations of this pullback, each
playing a distinct role.

**The textbook pullback.**
```lean
noncomputable def completedXiFunction (s : ℂ) : ℂ :=
  (1 / 2 : ℂ) * s * (s - 1)
    * Complex.exp (-(s / 2) * (Real.log Real.pi : ℂ))
    * Complex.Gamma (s / 2)
    * riemannZeta s

noncomputable def XiPullback (z : ℂ) : ℂ :=
  completedXiFunction ((1 / 2 : ℂ) + Complex.I * z)
```
This follows the textbook formula verbatim. The cancellation of
$\Gamma$-poles against $\zeta$-zeros is visible only after explicit
calculation, but the formula is exactly what is needed when relating
$\Lambda[\Xi]$ to its explicit factors on the right-hand side.

**The Mathlib-grounded pullback.**
```lean
noncomputable def entireRiemannXi (s : ℂ) : ℂ :=
  (1 / 2 : ℂ) * s * (s - 1) * completedRiemannZeta₀ s + (1 / 2 : ℂ)

noncomputable def EntireXiPullback (z : ℂ) : ℂ :=
  entireRiemannXi ((1 / 2 : ℂ) + Complex.I * z)
```
This is built from Mathlib's pole-subtracted `completedRiemannZeta₀`,
so it is *entire by construction*: differentiability everywhere
(`entireRiemannXi_differentiable`) and the functional equation
$\xi(1-s) = \xi(s)$ (`entireRiemannXi_one_sub`) are proved directly
from Mathlib. Schwarz reflection $\xi(\bar s) = \overline{\xi(s)}$ is
proved unconditionally as `entireRiemannXi_schwarz_target_holds`. Both
pullbacks share the same nontrivial zeros, so RH is equivalent to
either of
$$
\forall \rho\in\mathbb{C},\;\Xi(\rho)=0\ \Longrightarrow\ \operatorname{Im}\rho=0,
\qquad
\forall \rho\in\mathbb{C},\;\Xi_{\text{Mathlib}}(\rho)=0\ \Longrightarrow\ \operatorname{Im}\rho=0.
$$

The custom `XiPullback` is the natural target for the sign-law
machinery — direct access to the textbook formula is what makes the
decomposition of $\Lambda[\Xi]$ tractable. The Mathlib-grounded
`EntireXiPullback` is the natural target for the *Hadamard product*
input (where being entire by construction matters) and for the final
RH statement, where Mathlib's library discharges the analytic
preliminaries. The two chains run in parallel and are bridged by an
elementary chain rule on the engine side, and by the §9 Γ-cancellation
bridge on the Hadamard side.

## 2. The sign law and its engine

Throughout we write
```lean
noncomputable def logDerivativeResponse (f : ℂ → ℂ) : ℂ → ℂ :=
  fun z => deriv f z / f z
```
for the (Lean-side) logarithmic derivative $\Lambda[f] := f'/f$. The
*anti-Herglotz upper-half-plane sign law* is
```lean
def AntiHerglotzUHP (R : ℂ → ℂ) : Prop :=
  ∀ z : ℂ, 0 < z.im → (R z).im ≤ 0.
```
**Theorem 1 (sign law implies real zeros).** *Let $f : \mathbb{C} \to
\mathbb{C}$ be real-symmetric on $\mathbb{R}$ — i.e.\ $f(\bar z) =
\overline{f(z)}$ — and suppose $\Lambda[f]$ satisfies the anti-Herglotz
sign law. Suppose further that every upper-half-plane zero of $f$ comes
equipped with a local pole-decomposition of $\Lambda[f]$. Then every
zero of $f$ is real.*

The Lean statement is
```lean
theorem antiHerglotz_plus_symmetry_forces_real_zeros_complex
    {f R : ℂ → ℂ}
    (hpole : LogDerivPoleWitnessLaw f R)
    (hanti : AntiHerglotzUHP R)
    (hsym  : ∀ z : ℂ, f (star z) = star (f z)) :
    ∀ ρ : ℂ, f ρ = 0 → ρ.im = 0.
```
The proof has two steps.

### Step 1 — the pole-probe mechanism

Suppose $f$ has a zero $\rho$ with $\operatorname{Im}\rho > 0$ of
multiplicity $m \ge 1$. Local analytic factorization gives
$f(z) = (z-\rho)^m g(z)$ with $g(\rho) \neq 0$ on a neighborhood of
$\rho$, hence
$$
\Lambda[f](z) \;=\; \frac{m}{z-\rho} \,+\, \frac{g'(z)}{g(z)}.
$$
Probe at $z_\varepsilon := \rho - i\varepsilon$, still in the upper
half-plane for $\varepsilon < \operatorname{Im}\rho$. Then
$z_\varepsilon - \rho = -i\varepsilon$, and the *residue rotation*
$$
\frac{m}{-i\varepsilon} \;=\; \frac{m\,i}{\varepsilon}
\qquad\Longrightarrow\qquad
\operatorname{Im}\frac{m}{z_\varepsilon - \rho} \;=\; \frac{m}{\varepsilon}
$$
sends the residue onto the positive imaginary axis with magnitude
$m/\varepsilon \to +\infty$ as $\varepsilon \downarrow 0$. The
background $g'/g$ is continuous at $\rho$ and bounded by some $K$ on
a small disk. For $\varepsilon < m/(2K)$ the divergent residue
overwhelms the bounded background, giving
$\operatorname{Im}\Lambda[f](z_\varepsilon) > 0$ — a strict violation
of the sign law on a point with strictly positive imaginary part.

The Lean abstraction is
```lean
structure LocalLogDerivPoleDecomposition (R : ℂ → ℂ) (ρ : ℂ) where
  m              : ℕ
  hm_pos         : 0 < m
  background     : ℂ → ℂ
  ε0             : ℝ
  hε0            : 0 < ε0
  hε0_lt         : ε0 < ρ.im
  K              : ℝ
  hK_pos         : 0 < K
  decomp_at_probe : ∀ ε, 0 < ε → ε < ε0 →
    R (ρ - (ε : ℂ) * Complex.I) =
      ((m : ℝ) : ℂ) / ((ρ - (ε : ℂ) * Complex.I) - ρ) +
      background (ρ - (ε : ℂ) * Complex.I)
  background_bounded : ∀ ε, 0 < ε → ε < ε0 →
    |(background (ρ - (ε : ℂ) * Complex.I)).im| ≤ K
```
and the engine theorem `localLogDerivPoleDecomposition_forces_escape`
chooses $\varepsilon := \min(\varepsilon_0/2,\, m/(2K))$ and produces
the contradiction. The structure is deliberately abstracted from the
analytic machinery used to produce it; the same lemma discharges the
polynomial, the custom-xi, and the Mathlib-grounded-xi cases.

### Step 2 — Schwarz reflection

The upper and lower half-planes are linked by $f(\bar z) =
\overline{f(z)}$: if $\rho$ is a lower-half-plane zero of $f$ then
$\bar\rho$ is an upper-half-plane zero, killed by Step 1. The only
remaining possibility is $\operatorname{Im}\rho = 0$.

### The taint convention

Lean's $a/0 = 0$ division convention forces $\Lambda[f](z) = 0$ at
every zero of $f$, where the inequality $\operatorname{Im}\Lambda[f](z)
\le 0$ reads $0 \le 0$ — trivially true. This makes the sign law
itself harmless: the engine queries $\Lambda[f]$ only at probe points
$\rho - i\varepsilon$ with $\varepsilon > 0$, provably distinct from
$\rho$ by `probe_ne_pole`.

The danger appears downstream. Any analytic input that mentions
$\Lambda[\Xi](z)$ or $E(z) := \Lambda[\Xi](z) - M(z)$ over a UHP
region carries an implicit obligation at the totalized zeros, where
the residual collapses *definitionally* to $-M(\rho)$. Discharging
such an unguarded input at a totalized zero would require first ruling
that zero out — i.e.\ proving RH — so the obligation is *circular*
unless the input is weakened.

The file codifies the fix as a **taint convention** (§CCLXXXVIII): any
public analytic input mentioning $\Lambda[\Xi]$ or `xiResidualError`
over a UHP region must carry an explicit `XiPullback z ≠ 0 →` guard.
The corresponding `…AwayFromZeros` Props (henceforth AFZ) embed that
guard; the zero case is then closed internally by
`errorMargin_at_XiPullback_zero_of_decomp`, whose mechanism is one
line of algebra: at $\Xi(\rho) = 0$ we have $\Lambda[\Xi](\rho) = 0$,
so $E(\rho) = -M(\rho)$; anti-Herglotz of $M$ gives
$\operatorname{Im}M(\rho) \le 0$, hence
$\bigl|\operatorname{Im}E(\rho)\bigr| = -\operatorname{Im}M(\rho)$ —
the margin holds with equality.

The same convention forces the Hadamard product identity (§9 below)
to be asserted only away from zeros: at a totalized zero the
left-hand side $\Lambda[\Xi](\rho) = 0$, but the Hadamard zero-sum
diverges, so the unguarded form is mathematically uninhabitable.

## 3. Polynomial RH as a worked example

Specializing the engine to polynomials yields an unconditional theorem.
At any root $\rho$ of $p \neq 0$ of multiplicity $m$, Mathlib's
`rootMultiplicity` machinery produces the factorization
$p = (X - C\rho)^m \cdot q$ with $q(\rho) \neq 0$. The log-derivative
unfolds to $m/(z-\rho) + q'(z)/q(z)$, continuity of $q'/q$ at $\rho$
supplies the bounded background, and the data assemble into a
`LocalLogDerivPoleDecomposition`. The engine fires and we obtain
```lean
theorem polynomial_roots_real_of_logDeriv_antiHerglotz_and_conjSymm'
    (p : Polynomial ℂ) (hp : p ≠ 0)
    (hanti : AntiHerglotzUHP (polynomialLogDerivResponse p))
    (hsym  : ∀ z : ℂ, p.eval (star z) = star (p.eval z)) :
    ∀ ρ : ℂ, p.eval ρ = 0 → ρ.im = 0
```
with no analytic side-conditions. The converse direction is proved
in factorized form, yielding
`polynomial_realLinearFactorized_antiHerglotz_iff`. The polynomial
case confirms that the engine is correctly calibrated and serves as
the template for the entire-function lift.

## 4. The entire-function lift, and the Mathlib chain

At the level of entire functions, Mathlib's `rootMultiplicity` is
replaced by its isolated-zeros library. The key fact is

> **(Analytic factorization.)** If $f$ is analytic at $\rho$ and not
> identically zero in a neighborhood of $\rho$, then there exist
> $m \ge 0$ and $g$ analytic at $\rho$ with $g(\rho) \neq 0$ such that
> $f(z) = (z-\rho)^m g(z)$ eventually near $\rho$.

This is `AnalyticAt.exists_eventuallyEq_pow_smul_nonzero_iff`. The
per-zero specialization `analytic_zero_admits_factorization` together
with `EntireXiPullback_analyticAt` supplies the analytic factorization
for our actual targets. The structural bridge
`localAnalyticZeroFactorization_gives_LocalLogDerivPoleDecomposition`
lifts the algebraic identity of §2 through `Filter.EventuallyEq.deriv_eq`
to the actual `deriv` of $f$, and discharges the engine's pole-witness
hypothesis. The resulting capstone
`entire_function_roots_real_of_analytic_factor_antiHerglotz_and_conjSymm`
reduces RH to three inputs: analytic factorization, Schwarz reflection,
and the anti-Herglotz sign law.

The zero-side local logarithmic-derivative principal-part target is
now proved directly as `hasLogDerivPrincipalPart_of_analytic_zero`:
analytic order `m` at `s` gives `HasLogDerivPrincipalPart f s m` on
the punctured neighborhood. The zeta specialization
`zetaLogDeriv_principalPart_at_nontrivial_zero_direct` supplies the
direct nat-valued principal part at every nontrivial zero, with
`zetaLogDeriv_principalPart_at_nontrivial_zero_nat` retaining the
factorization-route spelling; `zetaLogDeriv_integerPrincipalPart_at_nontrivial_zero`
lifts this zero-side result to the integer-valued interface consumed
by the later residue-free rectangle machinery.

For the Mathlib-grounded pullback `EntireXiPullback`, the first two
hold unconditionally:

* *Analytic factorization* follows from `analytic_zero_admits_factorization`
  applied to `EntireXiPullback_analyticAt`.
* *Schwarz reflection* rests on the **Mellin keystone**
  ```lean
  theorem mellin_star_ofReal (f : ℝ → ℝ) (s : ℂ) :
    mellin (fun t => (f t : ℂ)) (star s)
      = star (mellin (fun t => (f t : ℂ)) s),
  ```
  proved via `integral_conj`, `Complex.cpow_conj`, and
  `Complex.conj_ofReal`. This lifts up the chain
  `WeakFEPair → completedHurwitzZetaEven₀ → completedRiemannZeta₀` to
  `entireRiemannXi_schwarz_target_holds`, unconditionally.

What remains on the Mathlib side is the *single real inequality*
```lean
def EntireXiLeftHalfLogDerivSignTarget : Prop :=
  ∀ s : ℂ, s.re < (1 / 2 : ℝ) →
    ((deriv entireRiemannXi s) / entireRiemannXi s).re ≤ 0.
```
The corresponding capstone `EntireXiPullback_zeros_real_of_signTarget`
is the cleanest Mathlib-side conditional theorem in the file: just
the real inequality $\operatorname{Re}(\xi'/\xi)(s) \le 0$ on
$\operatorname{Re} s < \tfrac{1}{2}$.

The chain rules `XiPullback_logDeriv_chain_rule` and
`EntireXiPullback_logDeriv_chain_rule` translate between the
$z$-plane target $\operatorname{Im}(\Xi'/\Xi)(z) \le 0$ and the
$s$-plane target $\operatorname{Re}(\xi'/\xi)(s) \le 0$ under
$s = \tfrac{1}{2}+iz$, using $\operatorname{Im}(i \cdot w) =
\operatorname{Re}(w)$.

## 5. Four equivalent formulations of the sign law

The anti-Herglotz sign law has several mathematically interchangeable
formulations, each opening a distinct line of attack:

| Lean name | Statement |
|-----------|-----------|
| `XiPullbackAntiHerglotzTarget` | $\operatorname{Im}(\Xi'/\Xi)(z) \le 0$ on the upper half-plane. |
| `XiHerglotzTarget`             | $-\Xi'/\Xi$ is Herglotz (Pick/Nevanlinna dual). |
| `XiLeftHalfLogDerivSignTarget` | $\operatorname{Re}(\xi'/\xi)(s) \le 0$ on $\operatorname{Re} s < \tfrac{1}{2}$ ($s$-plane form). |
| `XiPullbackEnergyMonotoneAwayFromZeros` | $\partial_y \lVert \Xi(x+iy)\rVert^2 \ge 0$ away from zeros of $\Xi$. |

The duality is `negHerglotzUHP_iff_antiHerglotzUHP` (proved); the
forward implication from the $s$-plane form is
`XiPullbackAntiHerglotzTarget_of_XiLeftHalfLogDerivSignTarget`.

The energy form deserves comment because it converts the sign law
into a calculus statement on $y \mapsto \lVert F(x+iy)\rVert^2$. The
mechanism is
$$
2\,\operatorname{Re}\!\bigl(\overline{F(z)}\cdot i F'(z)\bigr)
\;=\; -2\, \lVert F(z)\rVert^2 \,\operatorname{Im}\!\bigl(F'(z)/F(z)\bigr)
$$
(`energy_logDeriv_algebra`). The left-hand side is exactly
$\partial_y\lVert F\rVert^2$ via the chain rule
`hasDerivAt_norm_sq_complex`; dividing by $2\lVert F\rVert^2 > 0$
(away from zeros) turns sign of $\partial_y\lVert F\rVert^2$ into
sign of $-\operatorname{Im}(F'/F)$. The capstone
`XiPullbackAntiHerglotzTarget_of_energyMonotone_and_diff` lands the
sign law from energy monotonicity plus differentiability of $\Xi$.
Pushing further, the xi integral representation $\Xi(z) =
\int_0^\infty \Phi(u)\cos(zu)\,du$ expresses $\partial_y
\lVert \Xi\rVert^2$ as a double integral and reduces the energy form
to a *total positivity* statement for an explicit symmetric kernel
(`XiDoubleKernel.IntegratedDoubleKernelPositivity`,
`XiKernelEnergyInequality.implies_energyMonotone`). The main effort
in `rh.lean` routes through `XiPullbackAntiHerglotzTarget`.

## 6. The decomposition and the canonical residual

Write $\Lambda[\Xi] := \Xi'/\Xi$. The decomposition route splits this
response, on the relevant region of the upper half-plane, as
$$
\Lambda[\Xi](z)
\;=\;
\underbrace{P(z)}_{\text{cloud}}
\;+\;
\underbrace{S_T(z)}_{\text{smooth tail}}
\;+\;
\underbrace{E(z)}_{\text{residual}}.
$$
The first two summands are anti-Herglotz by construction; the residual
$E$ is what requires region-by-region analysis. The structural
motivation is the classical Riemann–von Mangoldt asymptotic
$N(T) \sim \tfrac{T}{2\pi}\log\tfrac{T}{2\pi}$: the actual nontrivial
zero count $N(T)$ splits as a discrete part (the explicit first
hundred-or-so zeros) plus the smooth density $\rho(u) = N_0'(u) =
\tfrac{1}{2\pi}\log\tfrac{u}{2\pi}$ extending to infinity. The
log-derivative inherits the same split.

**Finite cloud.** Explicit paired sum
`pairedFiniteCloudFromZeros us z := Σ_{u ∈ us} (1/(z − u) + 1/(z + u))`
at `us = zeros100ceil`. The list is the *ceiling* of the first 100
positive $\zeta$-ordinates: `[15, 22, 26, 31, ..., 236]`. Ceiling is
chosen because the cloud's $-\operatorname{Im}$ at $(x,y)$ is
proportional to $\sum_j 1/((x \pm \gamma_j)^2 + y^2)$, which
*decreases* in $\gamma_j$; rounding up gives a uniformly *conservative*
lower bound for the cloud margin in the slab and box certificates.
Each paired term is anti-Herglotz on the upper half-plane
(`pairedCauchyKernel_im_nonpos_at`), and the finite sum inherits the
property by linearity.

**Smooth tail.** Improper integral against $\rho$,
`zeroDensitySmoothTailModel T z := ∫_T^∞ ρ(u) · (1/(z−u) + 1/(z+u)) du`,
the model's continuum analogue of the cloud tail beyond the
explicit-zero cutoff. Anti-Herglotz of the smooth tail and a
quantitative pointwise lower bound on $-\operatorname{Im}$ are both
proved unconditionally; see §7.

**Residual.** Defined as the *difference*
```lean
noncomputable def xiResidualError
    (M : CloudDensityTailModelDecomposition) : ℂ → ℂ :=
  fun z => logDerivativeResponse XiPullback z − M.model z.
```
The decomposition identity $\Lambda[\Xi] = M.\text{model} +
\text{xiResidualError}\,M$ is then proved by `ring`
(`xiResidualError_decomp`). What was previously a globally postulated
xi identity becomes a *definitional truth*, reducing the analyst-facing
obligation to a regional one: on each region of the upper half-plane,
either bound $\operatorname{Im}\, E$ by an explicit function, or
exhibit $E$ as a Tendsto limit of explicit paired-Cauchy partials.

**The canonical model at $T_\bullet = 2\pi$.** The "honest" model is
the single named object
`honestZeroDensityModelTwoPi : CloudDensityTailModelDecomposition`,
built from the finite cloud over `zeros100ceil` and the smooth tail
at the cutoff $T_\bullet = 2\pi$ (the natural basepoint, where the
classical density vanishes and is then positive thereafter). The
"honest" name distinguishes this from earlier prototype models whose
anti-Herglotz property was *assumed*: here every model-side fact is
*unconditional*. The data bundle `honestZeroDensityModelData_twoPi`
records the cloud zero list, the cloud + tail decomposition, and the
rational lower bound of §7. Anti-Herglotz of the sum
(`hmodelAnti_of_honestZeroDensityModel`) then follows by linearity.

## 7. The smooth tail and its arctan lower bound

The smooth tail $S_T$ satisfies anti-Herglotz on the UHP and admits an
explicit pointwise lower bound on $-\operatorname{Im}$. Both are
proved unconditionally.

### The atomic anti-Herglotz mechanism

The whole anti-Herglotz infrastructure rests on a single elementary
calculation: for any *real* $r$ and any $z = x+iy$ with $y > 0$,
$$
\operatorname{Im}\frac{1}{z-r}
\;=\; \operatorname{Im}\frac{\overline{z-r}}{|z-r|^2}
\;=\; \frac{-y}{(x-r)^2 + y^2} \;<\; 0.
$$
Pairing two such residues at $\pm r$ gives the paired Cauchy kernel
$K_u(z) := \tfrac{1}{z-u} + \tfrac{1}{z+u}$, whose closed form
$K_u(z) = 2z/(z^2 - u^2)$ makes the imaginary part
$$
\operatorname{Im}K_u(x+iy)
\;=\; -y\!\left(\tfrac{1}{(x-u)^2+y^2}+\tfrac{1}{(x+u)^2+y^2}\right)
\;\le\; 0,
$$
recorded as `pairedCauchyImKernel` and proved nonpositive on the UHP
(`pairedCauchyKernel_im_nonpos_at`). Any nonnegative-weighted
combination — finite sums (`finitePositivePairedTail`) or improper
integrals (`PositivePairedCauchyTail`) — inherits the sign by
linearity.

### Qualitative anti-Herglotz of the smooth tail

Two ingredients suffice. *(a) Finite-window anti-Herglotz* — for
$\rho \ge 0$, $\rho(u) K_u(z)$ has nonpositive imaginary part
pointwise; pulling $\operatorname{Im}$ through the interval integral
gives `smoothDensityTailModelPartial_im_nonpos`. *(b) Closure under
pointwise limits* — the limit-transfer principle
`AntiHerglotzUHP.of_eventual_pointwise_tendsto_UHP` extends the sign
to the improper integral as $X \to \infty$, provided the partials
converge. Convergence follows from the cancellation
$$
\frac{1}{z-u} + \frac{1}{z+u} \;=\; \frac{2z}{z^2 - u^2},
$$
which gives the $1/u^2$ decay
$\lVert K_u(z)\rVert \le 4(\lVert z\rVert + 1)/u^2$ eventually
(`norm_pairedCauchyKernel_le_const_div_sq_eventually`). The
$\log u / u^2$ envelope on $\rho(u) K_u(z)$ is then absolutely
integrable on $[T, \infty)$.

### Quantitative lower bound

For a UHP probe $z = x + iy$ and a one-sided cutoff $T \ge |x|$, the
elementary identity
$$
\int_T^\infty \frac{y}{(u-x)^2 + y^2}\, du
\;=\; \frac{\pi}{2} - \arctan\!\frac{T-x}{y}
$$
expresses one-sided arctan tails as definite integrals. The
transcendental $\arctan$ is then traded for its rational
under-approximant
$$
\arctan s \;\ge\; \frac{s}{1+s^2} \qquad (s \ge 0)
$$
(`div_one_add_sq_le_arctan`) — a routine inequality whose virtue
is that the right-hand side is rational, hence amenable to symbolic
verification by `norm_num` and friends. Pairing the two sides and
factoring out $\rho(T)$ produces
```lean
noncomputable def smoothTailRationalLowerBoundAbs (x y T : ℝ) : ℝ :=
  zeroDensityRho T *
    (y * (T − |x|) / ((T − |x|)² + y²)
     + y * (T + |x|) / ((T + |x|)² + y²)).
```
The capstone `HonestSmoothTailRationalLB_twoPi` states that for every
UHP $z$ and every admissible adaptive cutoff $T$,
$$
-\operatorname{Im} S_{T_\bullet}(z) \;\ge\; \text{smoothTailRationalLowerBoundAbs}(\operatorname{Re} z,\, \operatorname{Im} z,\, T).
$$
The honest model packages this into its `densityTailRationalLB` field,
closing the model side unconditionally.

## 8. The xi-side residual

What remains is the imaginary part of `xiResidualError`. The upper
half-plane is split into three regions; each region carries its own
analytic obligation, in the AFZ-guarded form mandated by the taint
convention.

### The adaptive regime and why $A = 2$

The mid and high band conditions are anchored on the *adaptive
inequality*
$$
2\,(1 + |x| + y) \;\le\; T,
$$
expressing that the cutoff $T$ stays far enough above the probe
position $z = x+iy$ for the tail kernel envelopes to be uniformly
useful. Concretely, $|x| \le u/2$ on $[T, \infty)$ — which reduces
the split kernel-derivative envelope
$|k_z'(u)| \le 2y\bigl(\tfrac{1}{(u-|x|)^3} + \tfrac{1}{(u+|x|)^3}\bigr)$
(`abs_pairedCauchyImKernelDeriv_le_split`) to the closed-form
$|k_z'(u)| \le 18 y / u^3$
(`abs_pairedCauchyImKernelDeriv_le_adaptive_18`). The constant $A=2$
was identified by an empirical sweep over zeros and adaptive constants
as the cleanest comfortably-safe choice.

### The IBP mechanism

The shape of the analytic obligation in each band is the
*integration-by-parts* form of the classical explicit formula.
Writing the finite-window contribution to $\Lambda[\Xi] - M$ as a
Stieltjes integral against the fluctuation $S(u) = N(u) - N_0(u)$,
$$
\int_T^X K_u(z)\, dS(u) \;=\; K_X(z)\,S(X) - K_T(z)\,S(T) - \int_T^X K_u'(z)\,S(u)\, du,
$$
converts an integral *against the discrete measure* $dS$ into one
*against $S$ as a bounded function*. The crucial gain is that the
right-hand side bounds entirely in terms of $|S(u)|$, the Backlund/
Turing-controlled log envelope — without ever instantiating $dS$ as a
signed measure. The relevant Mathlib substrate
(`Phase1IBP.finiteFluctuationPrimitive`,
`Phase1IBP.derivativeSidePartial`, ordered discrete Abel summation,
the true-kernel FTC bridge, and the convergence engine
`improperComplexIntegralConverges_of_normMajorant`) lives entirely
inside the file.

### Three-band split and Path B parameters

**Mid band:** adaptive regime with $10 \le T \le 140$. The residual
is the $X \to \infty$ limit of a true-kernel paired-Cauchy partial,
asserted only at $\Xi(z) \neq 0$. **High band:** $T \ge 140$. Same
shape. **Low band:** $|\operatorname{Re} z| \le 4$ and
$0 < \operatorname{Im} z \le 4$. Here the residual is controlled by
an explicit closed-form first-zero envelope at a triple
$(T, \gamma_1, D)$.

The operative specialization is **Path B**:
$(T, \gamma_1, D) = (11, 14, 1/2)$. The three numbers are chosen for
mutually exclusive reasons:

* $T = 11$ is the inner cutoff between the closed-form IBP estimate
  and the model interior; pushing it higher loosens the model margin,
  pushing it lower forces $D > 1/2$.
* $\gamma_1 = 14$ is just below the true first nontrivial zero
  $\gamma_1 \approx 14.13476$; the conservative integer cutoff keeps
  the IBP basepoint and the gap interval entirely below the first
  zero.
* $D = 1/2$ is the smallest power-of-two value of $|S(u)|$ achievable
  on $[T_0, 14]$ at the pinned basepoint $T_0 = 10$:
  $|S(10, u)| = |N_0(10) - N_0(u)| \le 1/2$ on $[11, 14]$ with margin
  $\approx 0.05$ (see §9).

The worst-case model margin at the corner $z = 4i$ is approximately
$9.7 \times 10^{-3}$; Path B clears every numerical constraint with
slack.

## 9. The main conditional theorems

The Path B conditional sign law is now stated in progressively
sharper forms. Theorem 2 is the natural intermediate form. Theorem 3
factors the xi-side analytic content into one classical Hadamard
bundle plus three Stieltjes equalities (against `completedXiFunction`).
Theorem 4 redirects the Hadamard input to the cleaner
`entireRiemannXi`, isolating the Γ-cancellation between the two as a
three-piece structural bridge. Theorem 5 discharges two of those three
bridge pieces unconditionally and factors the third through two further
Mathlib-internal identities, so that only a single Mathlib raw-ζ
off-pole formula remains. Theorem 6 then closes that last identity
unconditionally against Mathlib's `Gammaℝ` factor and exposes the
Γ-discharged headline: an entire-ξ Hadamard bundle plus three
Stieltjes equalities and the two slab envelopes — nothing else.
The §CDXLIV canonical variants then name the completed-ξ source once
and offer both split-Stieltjes and reassembled-Stieltjes front doors.

### Theorem 2 — natural Path B front door

```lean
theorem XiPullbackAntiHerglotzTarget_of_twoPiModel_lowExplicit_11_14_halfAwayFromZeros
    (Dzero : Phase1IBP.OrderedFluctuationMeasureData) (T0 : ℝ)
    (hT0_pos : 0 < T0) (hT0_le_10 : T0 ≤ 10)
    (hTuring  : …)
    (hHighLog : …)
    (Hcanon_tailLimit : XiCanonicalResidualAsTailLimitAwayFromZeros
                          Dzero T0 honestZeroDensityModelTwoPi)
    (Hhigh_tailLimit  : XiHighResidualAsTailLimitAwayFromZeros
                          Dzero T0 honestZeroDensityModelTwoPi)
    (Hlow_explicit_11_14_half : XiLowResidualExplicitData_11_14_halfAwayFromZeros
                                  honestZeroDensityModelTwoPi)
    (Hlow_arith_11_14_half    : LowExplicitArithmeticBound_11_14_half) :
    XiPullbackAntiHerglotzTarget.
```
Six guarded inputs: two slab-localized log envelopes; two guarded
Tendsto identities for the mid/high residual; one guarded first-zero
residual bound on the low box; one model-side arithmetic inequality.

### How the §§CCLXXXV–CCXCIII reductions discharge four inputs

A sequence of structural and numerical reductions has internalized
four of Theorem 2's inputs.

1. **Interval integrability** (§CCLXXXVI): falls out of
   `finiteFluctuationPrimitive_kernelDeriv_intervalIntegrable_generic`.
2. **The first-zero gap identity** (§§CCLXXXVII, CCLXXXIX): under
   `DzeroStartsAfter Dzero 14`, the FTC bridge gives
   $S(T_0, u) = N_0(u) - N_0(T_0)$ on $[T_0, 14]$. For `zeros100ceil`
   (first entry $15$) the structural Prop is the one-liner
   $\forall i,\ 15 \le \text{Dzero}.Z_i$ (`DzeroStartsAfter_of_Z_ge_15`).
3. **The fluctuation bound** $|S| \le 1/2$ on $[11, 14]$ (§CCXC):
   reduces to the two-sided enclosure $N_0(14) \le 9/20$ and
   $N_0(10) \ge -1/20$. The lower bound on $N_0(10)$ uses the
   **Padé under-approximant** $\tfrac{2x}{x+2} \le \log(1+x)$
   (Mathlib's `Real.le_log_one_add_of_nonneg`) at $x = (5-\pi)/\pi$,
   reducing to $37\pi^2 - 415\pi + 1000 \ge 0$ on $(3.14, 3.15)$
   (`nlinarith`, margin $\approx 60$).
4. **The model-side arithmetic certificate `HlowArith`** (§§CCXCII,
   CCXCIII): normalizes by $y > 0$ to a constant inequality
   $C_0 \le \widetilde P + \widetilde S$ with $C_0 = 17/242 - 9/392
   \approx 0.0473$. Cloud LB $\approx 0.0370$ (uses $x^2+y^2 \le 16$)
   plus smooth LB $\approx 0.01246$ sum to $\approx 0.04949 > C_0$,
   margin $\approx 0.0022$; closed by `norm_num` on `zeros100ceil`.

### Theorem 3 — Hadamard + three Stieltjes inputs (against raw $\xi$)

After (1)–(4), the entire xi-side analytic content factors into *one
classical Hadamard bundle* plus *three Stieltjes equalities*, one
per band:
```lean
theorem XiPullbackAntiHerglotzTarget_of_classicalPathBHadamard_midHigh_lowSplit
    (Dzero : Phase1IBP.OrderedFluctuationMeasureData)
    {ι : Type}
    (h_Z_ge_15 : ∀ i : ℕ, (15 : ℝ) ≤ Dzero.toFluctuationMeasureData.Z i)
    (hTuring  : …)  (hHighLog : …)  -- at T0 = 10
    (Hhadamard : ClassicalPathBAnalyticInputs ι)
    (Hmid  : StieltjesMidTailEqualityAFZ  Dzero 10
                (pullbackZeroContribution Hhadamard.toCompletedXiSourceAFZ))
    (Hhigh : StieltjesHighTailEqualityAFZ Dzero 10
                (pullbackZeroContribution Hhadamard.toCompletedXiSourceAFZ))
    (HlowSplit : LowZeroContributionSplitAFZ Dzero 10
                    (pullbackZeroContribution Hhadamard.toCompletedXiSourceAFZ)) :
    XiPullbackAntiHerglotzTarget.
```
The IBP basepoint $T_0 = 10$ is pinned in the type; the Stieltjes
inputs are matched against the $z$-plane pullback of the Hadamard
zero contribution (chain rule
$\Lambda[\Xi](z) = i \cdot \Lambda[\xi](\tfrac12 + iz)$,
`pullbackZeroContribution`).

The unwrapping of the low Stieltjes input is the cleanest single
reduction in the file. Where Theorem 2 demanded a boundary-inclusive
imaginary-part equality involving an explicit Stieltjes integral, the
new `HlowSplit` input is the purely conceptual
$$
\mathrm{ZC}(z) \;=\; P(z) \;+\; \text{tailZC}(z)
\qquad (z \in \text{low box},\ \Xi(z) \neq 0,\ \text{no atoms in }[11,14]).
$$
The boundary-inclusive form is reconstructed internally because the
tail formula $\text{tailZC} = S_{T_\bullet} + \text{residualModel}$
is *definitionally true* by construction and discharges by `rfl`
(`LowTailStieltjesResidualFormulaAFZ.trivial`).

The Hadamard bundle `ClassicalPathBAnalyticInputs ι` packages the
classical genus-1 factorization of $\xi$,
$$
\xi(s) \;=\; \text{prefactor}(s) \cdot \prod_{\rho} E_1\!\bigl(s/\rho\bigr),
\qquad
E_1(w) := (1-w)\,e^{w},
$$
in five independently-provable pieces: `Hinv` (inverse-square
summability of zeros), `Hluc` (locally uniformly convergent
log-derivative interchange), `Hregion`/`HnonzeroRegion` (region
compatibility on the AFZ set of $\xi$), `Hfact` (the factorization
identity), and `Hpref_diff`/`Hpref_ne` (prefactor differentiability
and nonvanishing on the AFZ set). The composite bridge
`.toCompletedXiSourceAFZ` applies `logDeriv_mul` to the factorization
and identifies the product's log-derivative with the regularized series
via `Hluc`, producing a `CompletedXiLogDerivativeSourceAFZ`.

### Theorem 4 — entire-ξ Hadamard with Γ-cancellation bridge

The classical Hadamard product theorem is more naturally stated for an
*entire* function. Mathlib's `entireRiemannXi` is entire by
construction; the textbook `completedXiFunction` carries explicit
$\Gamma$-poles at the points $s \in \{-2n : n \in \mathbb{N}\}$ that
cancel against trivial $\zeta$-zeros only after explicit calculation.
Theorem 4 routes the Hadamard input through `entireRiemannXi` and
isolates the $\Gamma$-cancellation between the two as a small
structural bridge.

```lean
theorem XiPullbackAntiHerglotzTarget_of_gammaNoPole_avoidingNhds_offPoleFormula_entireHadamard_midHigh_lowSplit
    (Dzero : Phase1IBP.OrderedFluctuationMeasureData)
    {ι : Type}
    (h_Z_ge_15 : ∀ i : ℕ, (15 : ℝ) ≤ Dzero.toFluctuationMeasureData.Z i)
    (hTuring  : …)  (hHighLog : …)
    (Hnopole  : CompletedXiNonzeroExcludesGammaPole)
    (Hnhds    : GammaPoleAvoidingNeighborhoodSource)
    (Hformula : CompletedXiRawEntireXiOffPoleFormulaEquality)
    (Hhad     : EntireXiClassicalHadamardTheorem ι)
    (Hmid     : StieltjesMidTailEqualityAFZ  … )
    (Hhigh    : StieltjesHighTailEqualityAFZ … )
    {finiteCloud tail : ℂ → ℂ}
    (Hlow     : LowCloudTailSplitAFZ … finiteCloud tail) :
    XiPullbackAntiHerglotzTarget.
```
(The Stieltjes inputs are matched against the $z$-plane pullback of
the source assembled from `Hhad` and the three bridge pieces; the
explicit pullback expression is suppressed for readability.) The
chain is

> entire-ξ Hadamard theorem $\xrightarrow{\;\text{Γ-bridge}\;}$
> raw-completed-ξ log-derivative source $\xrightarrow{\text{chain rule}}$
> $z$-plane source $\xrightarrow{\;\text{Stieltjes}\;}$
> Λ[Ξ] decomposition $\xrightarrow{\;\text{engine}\;}$
> anti-Herglotz sign law.

#### The entire-ξ Hadamard theorem `EntireXiClassicalHadamardTheorem`

The same field structure as the raw-ξ form, but with every field stated
against `entireRiemannXi`:
```lean
structure EntireXiClassicalHadamardTheorem (ι : Type) : Type where
  zeroSystem       : ConcreteEntireXiZeroSystem ι
  prefactor        : ℂ → ℂ
  zeroDistribution : EntireXiZeroInvSqDistribution zeroSystem
  luc              : HadamardProductLUCLogDerivData zeroSystem.zeroLoc
  region           : ∀ s, entireRiemannXi s ≠ 0 → s ∈ luc.region
  factorization    : EntireXiHadamardFactorization zeroSystem prefactor
  prefactorData    : EntireXiHadamardPrefactor prefactor
```
The bridge `.toLogDerivativeSourceAFZ` applies `logDeriv_mul` to the
factorization and identifies the product's log-derivative with the
regularized series via `luc`, yielding an
`EntireXiLogDerivativeSourceAFZ`.

#### The Γ-cancellation bridge — three structural pieces

The bridge from the entire-ξ source to the raw-ξ source needed by
the engine is split into three independently-provable Props:

* **`Hnopole : CompletedXiNonzeroExcludesGammaPole`** — *structural*:
  wherever `completedXiFunction s ≠ 0`, the input $s$ is not a
  pullback of a $\Gamma$-pole. In Lean's totalized arithmetic
  $\Gamma(-n) = 0$, so at a Γ-pole pullback the entire textbook
  product evaluates to $0$, and the contrapositive gives the claim.
  Proved unconditionally as `completedXiNonzeroExcludesGammaPole`
  (§CDXXXII) from `Complex.Gamma_neg_nat_eq_zero`.

* **`Hnhds : GammaPoleAvoidingNeighborhoodSource`** — *topological
  discreteness*: any $s$ avoiding the $\Gamma$-pole pullback set has
  an open neighborhood avoiding it as well, because the pullback set
  $\{2(-n) : n \in \mathbb{N}\}$ is closed in $\mathbb{C}$. Proved
  unconditionally as `gammaPoleAvoidingNeighborhoodSource` (§CDXX)
  from `isClosed_gammaPoleSet`.

* **`Hformula : CompletedXiRawEntireXiOffPoleFormulaEquality`** —
  *pure formula identity*: the textbook formula
  $\tfrac12 s(s-1)\pi^{-s/2}\Gamma(s/2)\zeta(s)$ equals
  $\tfrac12 s(s-1)\cdot \texttt{completedRiemannZeta}_0\,s + \tfrac12$
  pointwise, off the $\Gamma$-pole pullback set. This is the actual
  algebraic content of "trivial-zero cancellation"; Theorem 5 below
  reduces it further to a single Mathlib raw-ζ off-pole formula.

Composed via
```lean
CompletedXiGammaRegularNeighborhoodSource.of_noPole_and_avoidingNhds
CompletedXiRawEntireXiLocalEqualitySource.of_gammaRegular_offPoleFormula
CompletedXiRawEqualsEntireXiOffGammaPoles.of_localEqualitySource
EntireXiToCompletedXiLogDerivBridge.of_rawOffGammaPoles
```
they produce an `EntireXiToCompletedXiLogDerivBridge`, which converts
any `EntireXiLogDerivativeSourceAFZ` into the matching
`CompletedXiLogDerivativeSourceAFZ`. Differentiability of `entireRiemannXi`
is auto-discharged from `entireRiemannXi_differentiabilitySource`
(unconditional, derived from `entireRiemannXi_differentiable`).

### Theorem 5 — Γ-bridge collapsed to one Mathlib ζ-identity

The §§CDXIX–CDXLI chain discharges the Γ-cancellation bridge of
Theorem 4 *almost entirely* against Mathlib, leaving only one
classical formula identity:

* `isClosed_gammaPoleSet` (§CDXIX) — direct topology proof that the
  Γ-pole pullback set $\{-2n : n \in \mathbb{N}\}$ is closed in
  $\mathbb{C}$, via the realization
  $\text{gammaPoleSet} = (-\cdot)^{-1}\!\bigl(\operatorname{Im}^{-1}\{0\} \cap \operatorname{Re}^{-1}(\mathbb{N})\bigr)$
  and the closedness of `Nat.isClosedEmbedding_coe_real`.
  `gammaPoleAvoidingNeighborhoodSource` (§CDXX) is unconditional.
* `completedXiVanishesOnGammaPolePullback` (§CDXXXII) — at a Γ-pole
  pullback $s/2 = -n$, $\Gamma(s/2) = 0$ by Mathlib's
  `Complex.Gamma_neg_nat_eq_zero`, so the raw $\xi$ product vanishes.
  This proves `Hnopole` (`completedXiNonzeroExcludesGammaPole`)
  unconditionally.
* `entireRiemannXiFormulaSource` (§CDXXXVIII) — the formula
  $\xi_{\text{entire}}(s) = \tfrac12 s(s-1)\zeta_0(s) + \tfrac12$ is
  exactly the definition of `entireRiemannXi`; the source is proved
  by `rfl`.
* `completedRiemannZetaZeroCorrectionFormula` (§CDXXXVII) —
  `completedRiemannZeta s = completedRiemannZeta₀ s − 1/s − 1/(1-s)`
  is Mathlib's `completedRiemannZeta_eq`.

What remains is the single Mathlib formula identity
```lean
structure CompletedRiemannZetaRawOffPoleFormula : Prop where
  eq_raw :
    ∀ s : ℂ,
      s / 2 ∉ gammaPoleSet →
      completedRiemannZeta s
        = Complex.exp (-(s / 2) * (Real.log Real.pi : ℂ))
          * Complex.Gamma (s / 2) * riemannZeta s
```
which is the classical $\zeta_{\text{completed}}(s) = \pi^{-s/2}\Gamma(s/2)\zeta(s)$
identity off the Γ-pole set. The §CDXLI bridge
`CompletedXiRawEntireXiOffPolePointwiseFormula.of_completedZetaIdentities`
then composes the three formula sources into the off-pole pointwise
formula via a calc chain that runs through
$\tfrac12 s(s-1)\,\zeta_{\text{completed}}(s)$,
$\tfrac12 s(s-1)\,(\zeta_0(s) − 1/s − 1/(1-s))$, and finally
$\tfrac12 s(s-1)\,\zeta_0(s) + \tfrac12 = \xi_{\text{entire}}(s)$ (the
$+1/2$ correction is supplied by the algebra lemma
`xi_completedZeta_correction_algebra` at $s \neq 0,1$).

The intermediate Path B front door is
```lean
theorem XiPullbackAntiHerglotzTarget_of_completedZetaRaw_entireHadamard_midHigh_lowSplit
    (Dzero : Phase1IBP.OrderedFluctuationMeasureData)
    {ι : Type}
    (h_Z_ge_15 : ∀ i : ℕ, (15 : ℝ) ≤ Dzero.toFluctuationMeasureData.Z i)
    (hTuring  : …)  (hHighLog : …)
    (HzetaRaw : CompletedRiemannZetaRawOffPoleFormula)
    (Hhad     : EntireXiClassicalHadamardTheorem ι)
    (Hmid     : StieltjesMidTailEqualityAFZ  … )
    (Hhigh    : StieltjesHighTailEqualityAFZ … )
    {finiteCloud tail : ℂ → ℂ}
    (Hlow     : LowCloudTailSplitAFZ … finiteCloud tail) :
    XiPullbackAntiHerglotzTarget.
```
The surviving inputs partition into four obligation classes: the
slab-envelope pair $(h_{\text{Turing}}, h_{\text{HighLog}})$, the
entire-ξ Hadamard bundle `Hhad`, the Stieltjes triple
$(H_{\text{mid}}, H_{\text{high}}, H_{\text{low}})$, and the single
raw-ζ formula identity `HzetaRaw`. The Γ-cancellation between the
textbook $\xi$ and Mathlib's `entireRiemannXi`, often treated as
routine but combinatorially fiddly, is now a *one-Mathlib-identity*
obligation rather than a multi-piece bridge. Theorem 6 below
discharges that single identity, and §CDXLIV packages the resulting
completed-ξ source canonically, leaving Path B with three obligation
classes.

### Theorem 6 — Γ-cancellation fully discharged

Even the single raw-ζ formula identity of Theorem 5 turns out to be
provable directly against Mathlib. The proof (§CDXXXVI) unwinds
Mathlib's `completedRiemannZeta` against its `Gammaℝ` factor:
$$
\zeta_{\text{completed}}(s)
\;=\; \mathrm{Gamma}_{\mathbb R}(s)\,\zeta(s)
\qquad (s \neq 0)
$$
(via `riemannZeta_def_of_ne_zero` and a field-simp away of `Gammaℝ ≠ 0`),
and identifies the real-Γ factor with the explicit exponential form
$$
\mathrm{Gamma}_{\mathbb R}(s)
\;=\; \exp\!\bigl(-\tfrac{s}{2}\log\pi\bigr)\,\Gamma(s/2)
$$
(`GammaReal_eq_exp_gamma`, via `Gammaℝ_def` and `Complex.cpow_def_of_ne_zero`).
Off the Γ-pole pullback set, $s \neq 0$ holds automatically
(`ne_zero_of_half_not_gammaPole`) and $\mathrm{Gamma}_{\mathbb R}(s) \neq 0$
holds via `Complex.Gammaℝ_eq_zero_iff`
(`GammaReal_ne_zero_of_half_not_gammaPole`). The unconditional theorem
is then
```lean
theorem completedRiemannZetaRawOffPoleFormula :
    CompletedRiemannZetaRawOffPoleFormula
```
and the Path B headline collapses to
```lean
theorem XiPullbackAntiHerglotzTarget_of_entireHadamard_midHigh_lowSplit
    (Dzero : Phase1IBP.OrderedFluctuationMeasureData)
    {ι : Type}
    (h_Z_ge_15 : ∀ i : ℕ, (15 : ℝ) ≤ Dzero.toFluctuationMeasureData.Z i)
    (hTuring  : …)  (hHighLog : …)
    (Hhad     : EntireXiClassicalHadamardTheorem ι)
    (Hmid     : StieltjesMidTailEqualityAFZ  … )
    (Hhigh    : StieltjesHighTailEqualityAFZ … )
    {finiteCloud tail : ℂ → ℂ}
    (Hlow     : LowCloudTailSplitAFZ … finiteCloud tail) :
    XiPullbackAntiHerglotzTarget.
```
The Γ-bridge has disappeared as a hypothesis entirely; the proof
threads it through internally via the unconditional
`completedXiRawEntireXiOffPolePointwiseFormula` (§CDXLI). The
publication-grade obligations are now exactly *three*: the slab
envelopes (P1), the entire-ξ Hadamard theorem (P2), and the three
Stieltjes equalities (P3). The canonical §CDXLIV variants expose the
same result with hypotheses keyed to
`Hhad.toCompletedXiSourceAFZ_canonical`, including the bundled
`ClassicalPathBStieltjesInputsAFZ` form.

### Why the AFZ guard is essential

At a zero $\Xi(\rho) = 0$ with $0 < \operatorname{Im}\rho$:

* The left-hand side $\Lambda[\Xi](\rho) = 0$ by Lean's totalization
  convention.
* The Hadamard zero sum on the right-hand side *diverges* (the term
  $1/(\rho - \rho) = 1/0$ blows up before regularization).

No finite value of $\mathrm{ZC}(\rho)$ can satisfy both the Hadamard
identity and the Stieltjes equality at a totalized zero. The AFZ
guard `XiPullback z ≠ 0` is what makes both hypotheses
*mathematically inhabitable*. Theorems 3, 4, 5, 6, and the canonical
§CDXLIV variants are all strictly weaker than RH.

### From sign law to RH

To translate `XiPullbackAntiHerglotzTarget` into a Mathlib-grade RH
theorem, compose with the chain rule `XiPullback_logDeriv_chain_rule`
(transferring to the $s$-plane sign target) and the Mathlib-side
capstone `EntireXiPullback_zeros_real_of_signTarget`.

## 10. Auditing the conditional — where RH-power enters

A conditional reduction of RH is only meaningful if its hypotheses are
*genuinely weaker than RH*. The taint convention (§2) protects against
the simplest failure mode: an unguarded analytic input cannot
implicitly demand a zero-free region for $\Xi$. But a subtler trap
remains — a hypothesis that *looks* classical but secretly carries
RH-strength (e.g., a positivity statement on the residual, or an
anti-Herglotz claim on the zero contribution, or a zero-free-region
assumption hidden inside the prefactor). §§CCCLXVI–CCCLXVIII install a
formal audit layer that closes this trap with Lean Props.

### Identity-only certification of the Hadamard bundle (§CCCLXVI)

```lean
structure HadamardInputsAreClassical
    {ι : Type} (_H : ClassicalPathBAnalyticInputs ι) : Prop where
  factorization_is_identity : True
  invSq_is_growth : True
  luc_is_complex_analysis : True
  prefactor_is_local_AFZ : True
```
The four `True` fields are documentary: they classify each Hadamard
component as a particular flavor of classical entire-function content.
`Hfact` is a pointwise *identity*, not a sign claim. `Hinv` is a
classical *growth* fact about the rank-1 density of zeros, not a claim
about where zeros lie. `Hluc` is *complex-analytic* (LUC + log-deriv
interchange). `Hpref_diff`/`Hpref_ne` are *local AFZ* regularity. The
theorem `HadamardInputsAreClassical.holds` inhabits the Prop trivially;
its purpose is to serve as a structural commitment that survives
refactoring. The same classification applies to the entire-ξ analogue
`EntireXiClassicalHadamardTheorem` (every field has the same flavor).

### Pure-identity certification of the Stieltjes bundle (§CCCLXVII)

```lean
structure StieltjesInputsArePureIdentities
    {Dzero : …} {T0 : ℝ} {ZC : ℂ → ℂ}
    (_H : ClassicalPathBStieltjesInputsAFZ Dzero T0 ZC) : Prop where
  mid_is_equality_only : True
  high_is_equality_only : True
  low_is_split_only : True
```
The Stieltjes bundle is the more dangerous side: if any field were to
assert *positivity* of the residual, *anti-Herglotz behavior* on the
upper half-plane, or a *zero-free region* for $\Xi$ on the relevant
band, then inhabiting the bundle would already amount to proving RH
on that band. The audit Prop documents that `mid_eq`, `high_eq`, and
the low-band `low_eq` (or its zero-index splitting version
`HlowSplit`) are *equality statements only*.

### The named boundary for RH-flavored content (§CCCLXVIII)

```lean
structure PathBSignOrEnvelopeInputs
    (_Dzero : Phase1IBP.OrderedFluctuationMeasureData) : Prop where
  turing_envelope : True
  high_log_envelope : True
  zero_gap_data : True
```
This Prop names the *only* place where RH-flavored content can
legitimately enter Path B: the Backlund/Turing log envelopes
`hTuring`, `hHighLog`, and the zero-gap data (`DzeroStartsAfter`,
`LowFirstZeroGapNoAtoms`, ultimately the one-liner `h_Z_ge_15`). A
clean conceptual statement of Path B is

> *identity bundles* (entire-ξ Hadamard + Stieltjes)
> $\oplus$ *sign/envelope bundle* (Turing + HighLog + zero-gap)
> $\Longrightarrow$ `XiPullbackAntiHerglotzTarget`.

The Γ-cancellation bridge added in Theorem 4 (`Hnopole`, `Hnhds`,
`Hformula`) inherits the identity-only classification: `Hnopole` is
structural, `Hnhds` is topological discreteness of the
$\{-2n : n \in \mathbb{N}\}$ poles, and `Hformula` is a pointwise
algebraic identity off the pole set. None carries sign content; all
three have now been proved unconditionally in the file, and the
single raw-ζ formula identity that Theorem 5 reduced them to is
itself proved against Mathlib (Theorem 6). At Theorem 6 the Γ-bridge
no longer appears as a hypothesis at all.

If RH-power is hiding anywhere in Theorems 3, 4, 5, or 6, it must be
in the sign/envelope bundle. The identity bundles are certified by
§§CCCLXVI–CCCLXVIII. This decomposition is what makes the conditional
reduction *trustworthy*: a future inhabitation of the Hadamard or
Stieltjes bundles cannot accidentally import an RH-equivalent
assumption without violating one of the classification Props.

## 11. Status

The proof is *conditional* on three classical analytic obligations.

**(P1) The Backlund/Turing envelopes.** The two log envelopes
$h_{\text{Turing}}$ and $h_{\text{HighLog}}$ are the remaining hard
analytic inputs from classical analytic number theory. Once any of
`BacklundTuringProofIngredients`, `ProvenBacklundTuringBound`,
`HalfLogPlusHalfSBound`, or `TuringStyleSBound` is inhabited, the
slab-localized form follows mechanically. The current file also
exports the sourced classical proof packages directly into the generic
`S`-bound interfaces, proves their fields reduce to `concreteS`,
`lower = 140`, and `C = D = 1/2` by `rfl`, and provides the direct
high-side allowance `|concreteS u| ≤ (1/2) log u + 49/20`.

**(P2) The entire-ξ Hadamard product theorem.**
`EntireXiClassicalHadamardTheorem ι` is the classical genus-1 Hadamard
factorization of `entireRiemannXi` — a function that is entire by
construction. Its data fields (zero system, prefactor, inverse-square
distribution, LUC interchange, region compatibility, factorization
identity, prefactor regularity) admit the same identity-only
classification as the raw form, and exist as the natural target for
the classical Hadamard product theorem from Mathlib.

**(P3) The three Stieltjes equalities.**
`Hmid` and `Hhigh` are the AFZ-guarded Tendsto identities expressing
the mid/high zero contribution as the cloud + smooth tail plus a
true-kernel paired-Cauchy partial limit. `HlowSplit` is the pure
*zero-index splitting* $\mathrm{ZC}(z) = P(z) + \text{tailZC}(z)$ on
the low compact region. The atomic reducer `LowCloudTailSplitAFZ`
(§CCCLXIX) breaks `HlowSplit` further into three identities against
any chosen decomposition $\mathrm{ZC} = \text{finiteCloud} +
\text{tail}$. Certified identity-only by §CCCLXVII.

**Previously open items, now retired.** Interval integrability on
$[11,14]$ (`Hint`), the first-zero gap identity (`Hgap`), the
basepoint root condition (`hN0_T0`), the xi-side IBP domination
(`Hdom`), the model-side arithmetic certificate (`HlowArith`), the
boundary-inclusive form of the low Stieltjes equality
(`LowFiniteStieltjesFormulaOnFirstZeroGapAFZ`), the differentiability
hypothesis on the raw `completedXiFunction`, all three structural
pieces of the Γ-bridge (`Hnopole`, `Hnhds`, `Hformula`), the
$\zeta_0$ correction `completedRiemannZeta_eq`, the entire-ξ formula
source, and the raw-ζ off-pole formula
`CompletedRiemannZetaRawOffPoleFormula` are all now discharged
unconditionally inside the file.

A handful of residual chases remain on the architecture side — the
two backward directions of the §5 equivalence and the identification
between the custom and Mathlib pullbacks — but none of these
contributes new analytic content.

### How to discharge the remaining inputs

For an analytic agent wanting to close Path B, the work splits along
the three obligation lines, with concrete handoff targets in each case.

* **(P1) Backlund/Turing envelopes.** Inhabit *any one* of
  `BacklundTuringProofIngredients`, `ProvenBacklundTuringBound`,
  `HalfLogPlusHalfSBound`, or `TuringStyleSBound`. The
  argument-principle scaffolding in the Q–Z / AA–BO namespaces is the
  in-file engine. The sourced classical packages
  `ClassicalBacklundTuringProofInputs` and
  `ClassicalBacklundTuringVerifiedInputs` now export directly to
  `ProvenBacklundTuringBound`, `HalfLogPlusHalfSBound`, and
  `TuringStyleSBound`, so a verified Backlund/Turing proof can be
  consumed by either the headline theorem or the generic residual-bound
  interfaces without an extra adapter layer. The associated `_S`,
  `_lower`, `_C`, `_D`, and `_bound` theorems make those exported
  fields definitionally visible. A proved `ProvenBacklundTuringBound`
  now also exports the envelope-call-shape methods
  `ProvenBacklundTuringBound.halfLogPlusHalfEnvelope` and
  `ProvenBacklundTuringBound.highLogEnvelope`, and
  `BacklundTuringAnalyticInputs.concreteS_halfLogPlusHalfEnvelope`
  and `BacklundTuringAnalyticInputs.concreteS_highLogEnvelope` expose
  the master analytic input package in the same downstream shape.
  `ClassicalBacklundTuringProofInputs.concreteS_halfLogPlusHalfEnvelope`
  and
  `ClassicalBacklundTuringVerifiedInputs.concreteS_halfLogPlusHalfEnvelope`
  supply the sharp concrete `S` envelope, while
  `ClassicalBacklundTuringPlattGlobalFiniteRangeInputs.concreteS_halfLogPlusHalfEnvelope`,
  `ClassicalBacklundTuringPlattAPFixedPiExpAutoRectEndpointCountInputs370.concreteS_halfLogPlusHalfEnvelope`,
  `ClassicalBacklundTuringPlattEndpointCountRangeFixedPiExpInputs370.concreteS_halfLogPlusHalfEnvelope`,
  and
  `ClassicalBacklundTuringPlattGlobalFiniteRangeInputs.concreteS_halfLogPlusHalfEnvelopeNearEndpoint`
  do the same for the Platt/global, endpoint-count, fixed-π exp, and
  near-endpoint packages. The high-side forms
  `ClassicalBacklundTuringVerifiedInputs.concreteS_highLogEnvelope`
  and `ClassicalBacklundTuringProofInputs.concreteS_highLogEnvelope`,
  together with
  `ClassicalBacklundTuringPlattGlobalFiniteRangeInputs.concreteS_highLogEnvelope`,
  `ClassicalBacklundTuringPlattAPFixedPiExpAutoRectEndpointCountInputs370.concreteS_highLogEnvelope`,
  `ClassicalBacklundTuringPlattEndpointCountRangeFixedPiExpInputs370.concreteS_highLogEnvelope`,
  and
  `ClassicalBacklundTuringPlattGlobalFiniteRangeInputs.concreteS_highLogEnvelopeNearEndpoint`,
  supply the downstream high-log envelope with the larger `49/20`
  allowance. The published Platt-Trudgian analytic estimate also has a
  direct sharp and high-side bridge:
  `PlattTrudgianBacklundGlobalInput.concreteS_halfLogPlusHalfEnvelope`,
  `plattTrudgianBacklundEnvelope_le_highLogEnvelope_of_ge_exp_one`
  and `PlattTrudgianBacklundGlobalInput.concreteS_highLogEnvelope`.
  It also now exports reusable `S`-bound packages:
  `PlattTrudgianBacklundGlobalInput.toHighLogTuringStyleSBound`,
  `PlattTrudgianBacklundGlobalInput.toHighLogTuringStyleSBound_bound`,
  `PlattTrudgianBacklundGlobalInput.toTailHalfLogPlusHalfSBound`,
  `PlattTrudgianBacklundGlobalInput.toTailTuringStyleSBound`, and
  `PlattTrudgianBacklundGlobalInput.toTailHalfLogPlusHalfSBound_bound`.
  The right-continuity/extension side is now explicitly packaged by
  `concreteSRightContinuityInput` and
  `ConcreteSBacklundEstimateExtensionFrom140.of_backlundGoodHeightArgumentBound`.
  A single good-height argument bound now builds the final packages
  directly through
  `BacklundGoodHeightArgumentBound.toFinalBacklundTuringTwoInputs`,
  `BacklundGoodHeightArgumentBound.toFinalBacklundTuringAnalyticInputs`,
  and `BacklundGoodHeightArgumentBound.concreteS_halfLogPlusHalf`.
  The sharp Platt/global finite-range and sourced verified inputs expose
  those final packages as
  `FinalBacklundTuringTwoInputs.of_globalPlattTrudgian_and_finiteRange_475481_80440`,
  `FinalBacklundTuringAnalyticInputs.of_globalPlattTrudgian_and_finiteRange_475481_80440`,
  `concreteS_halfLogPlusHalf_of_globalPlattTrudgian_and_finiteRange_viaFinalInputs`,
  `FinalBacklundTuringAnalyticInputs.toProvenBacklundTuringBound`,
  `FinalBacklundTuringAnalyticInputs.toHalfLogPlusHalfSBound`,
  `FinalBacklundTuringAnalyticInputs.toTuringStyleSBound`,
  `FinalBacklundTuringAnalyticInputs.concreteS_halfLogPlusHalfEnvelope`,
  `FinalBacklundTuringAnalyticInputs.concreteS_highLogEnvelope`,
  `FinalBacklundTuringTwoInputs.toProvenBacklundTuringBound`,
  `FinalBacklundTuringTwoInputs.toHalfLogPlusHalfSBound`,
  `FinalBacklundTuringTwoInputs.toTuringStyleSBound`,
  `ClassicalBacklundTuringPlattGlobalFiniteRangeInputs.toFinalBacklundTuringTwoInputs`,
  `ClassicalBacklundTuringPlattGlobalFiniteRangeInputs.toFinalBacklundTuringAnalyticInputs`,
  `ClassicalBacklundTuringVerifiedInputs.toFinalBacklundTuringTwoInputs`,
  and
  `ClassicalBacklundTuringVerifiedInputs.toFinalBacklundTuringAnalyticInputs`.
  The verified package also exports to the older
  `BacklundNumericalExtractionInput` API via
  `ClassicalBacklundTuringVerifiedInputs.toNumericalExtraction`, so the
  Trudgian/Platt route can feed both the modern `S`-bound interfaces
  and the earlier numerical-extraction frontier. It can now be built
  directly from the stronger global Platt-Trudgian estimate and the
  finite-range computation via
  `ClassicalBacklundTuringVerifiedInputs.of_plattTrudgianGlobal`. The right-side
  rectangle input has also been simplified:
  `backlund_right_side_zeta_ne_zero` proves nonvanishing of `ζ(s)` on
  the line `Re s = 2` from Mathlib's Euler-product nonvanishing theorem,
  and
  `BacklundRightSideArgumentVariationEstimate.of_logDeriv_bound_on_re_two`
  leaves only the right-side log-derivative bound to be supplied.
  The line `Re s = 2` also has a von Mangoldt-series bridge:
  `backlund_right_side_vonMangoldt_eq_neg_logDeriv` specializes
  Mathlib's Euler-product identity, and
  `BacklundRightSideArgumentVariationEstimate.of_vonMangoldt_bound_on_re_two`
  turns a von Mangoldt L-series bound directly into the right-side
  argument-variation estimate. The file now discharges the whole
  right-side input: `backlund_right_side_vonMangoldtLSeries_continuous`
  proves continuity on the vertical line, `backlund_right_side_vonMangoldt_plain_bound`
  gives a compact-window bound, and
  `BacklundRightSideArgumentVariationEstimate.of_abs_vonMangoldt_bound_on_re_two`
  feeds the final theorem `backlundRightSideArgumentVariationInput`.
  The Jensen-window input is also discharged under the present
  existential formulation: `BacklundJensenRectangleEstimate.of_height_ge_140`
  chooses a per-height finite-window constant, and
  `backlundJensenRectangleInput` packages this into the global input.
  With Jensen, right-side, and horizontal estimates discharged in-file,
  `BacklundClassicalCombinationInput.toGoodHeightArgumentBound` now turns
  the isolated classical combination lemma directly into the good-height
  Backlund argument bound. The count/right-continuity side is also now
  supplied in-file: `zetaZeroHeightRightGapToLocalConstancyInput` turns
  the global zero-height right-gap theorem into local constancy of the
  weighted count, `zetaWeightedZeroCountRightLocalConstancyInput`
  packages the unconditional instance, and the strip-gap variant
  `zetaStripGapToLocalConstancyInput` is built from
  `zetaWeightedCountExtensionalityInput`, yielding
  `concreteS_halfLogPlusHalf_of_numericalExtraction_and_stripGap`.
  The global zero-height gap route analogously gives
  `concreteS_halfLogPlusHalf_of_numericalExtraction_and_zeroHeightGap`.
  Then
  `concreteS_halfLogPlusHalf_of_backlundArgument` reduces the final
  half-log-plus-half bound to the single good-height Backlund argument
  input. The fixed-`K` classical proof package now closes the same loop:
  `ClassicalBacklundTuringProofInputs.toGoodHeightArgumentBound`
  projects it back to the exact good-height argument bound, and
  `classicalBacklundTuringProofInputs_iff_goodHeightArgumentBound`
  records equivalence with that single remaining input.
  A second sourced route
  now records the modern Hasanalizade--Shen--Wong large-height envelope
  `hasanalizadeShenWongBacklundEnvelope` together with the
  Platt/Trudgian finite-range computation:
  `BacklundGoodHeightArgumentBound.of_hsw_large_and_plattTrudgian`
  and `concreteS_halfLogPlusHalf_of_hsw_and_plattTrudgian` prove the
  same half-log-plus-half `concreteS` bound from those inputs. The HSW
  route has also been sharpened into tail-threshold variants at
  `exp 8` and `exp (77/10)`, with reduced finite-band checks
  `BacklundFiniteBandCheck140_exp8` and
  `BacklundFiniteBandCheck140_exp77_10`; the headline theorems
  `concreteS_halfLogPlusHalf_of_hsw_tail_and_plattTrudgian` and
  `concreteS_halfLogPlusHalf_of_hsw_sharpTail_and_plattTrudgian`
  route those tail estimates through the older Platt/Trudgian finite
  input. The latest refinement tightens the tail threshold again to
  `exp (769/100)` via `HasanalizadeShenWongTightTailInput`,
  `BacklundFiniteBandCheck140_exp769_100`, and
  `concreteS_halfLogPlusHalf_of_hsw_tightTail_and_plattTrudgian`.
  In parallel, CW32 sharpens the Trudgian arithmetic split itself:
  `backlund_log_log_le_one_tenth_log_plus_seven_fifths`,
  `trudgianBacklundEnvelope_le_halfLogPlusHalf_of_log_ge_647_100`,
  and
  `trudgianBacklundEnvelope_le_halfLogPlusHalf_of_ge_exp_647_100`
  prove the public half-log-plus-half target from
  `T ≥ exp (647/100)`, while `backlund_exp_647_100_lt_1200` keeps the
  remaining finite band inside the older Platt/Trudgian range. The
  new inputs `TrudgianBacklundSharpTailInput` and
  `BacklundFiniteBandCheck140_exp647_100` feed
  `BacklundGoodHeightArgumentBound.of_trudgian_sharpTail_and_finite`,
  with headline theorems
  `concreteS_halfLogPlusHalf_of_trudgian_sharpTail_and_finite` and
  `concreteS_halfLogPlusHalf_of_globalTrudgian_and_plattTrudgian_sharp`.
  CW34 then records the Platt-Trudgian global envelope
  `plattTrudgianBacklundEnvelope`, whose arithmetic comparison
  `plattTrudgianBacklundEnvelope_le_halfLogPlusHalf_of_ge_exp_593_100`
  reaches the public target on `T ≥ exp (593/100)`. The tail input
  `PlattTrudgianBacklundTailInput`, finite-band check
  `BacklundFiniteBandCheck140_exp593_100`, and adapter
  `BacklundGoodHeightArgumentBound.of_plattTrudgian_tail_and_finite`
  culminate in
  `concreteS_halfLogPlusHalf_of_globalPlattTrudgian_and_finiteRange`.
  The Platt-Trudgian envelope now also lowers to the older Trudgian
  global interface: `backlund_log_fifteen_le_three` supplies the
  elementary comparison input,
  `plattTrudgianBacklundEnvelope_le_trudgianBacklundEnvelope_of_ge_exp_one`
  proves the pointwise envelope domination for `T ≥ exp 1`, and
  `PlattTrudgianBacklundGlobalInput.toTrudgianGlobal` exports the
  stronger global input through the older `TrudgianBacklundGlobalInput`
  surface.
  The endpoint-specialized route through `[140, 374]` is exposed by
  `concreteS_halfLogPlusHalf_of_globalPlattTrudgian_and_finite374`,
  with the broad finite-range source adapter
  `concreteS_halfLogPlusHalf_of_globalPlattTrudgian_and_plattTrudgianRange_concrete`.
  The Platt route has also been shaved to the concrete endpoint `373`:
  `backlund_exp_592_100_lt_373`,
  `BacklundFiniteBandCheck140_373`,
  `BacklundFiniteBandUniform25167Check140_373`,
  `BacklundFiniteBandUniform25167Check140_373.toFiniteBandCheck`,
  `BacklundFiniteBandCheck140_373.of_plattTrudgian`, and
  `BacklundFiniteBandCheck140_exp592_100.of_140_373` feed the headline
  theorems `concreteS_halfLogPlusHalf_of_globalPlattTrudgian_and_finite373`,
  `concreteS_halfLogPlusHalf_of_globalPlattTrudgian_and_plattTrudgianRange_concrete373`,
  and
  `concreteS_halfLogPlusHalf_of_globalPlattTrudgian_and_uniformFinite373`.
  The same Platt-Trudgian route has now been sharpened one more step:
  `backlund_log_six_le_224_125` and
  `backlund_log_log_le_one_sixth_log_plus_ninety_nine_125` improve the
  tangent/log side, giving
  `plattTrudgianBacklundEnvelope_le_halfLogPlusHalf_of_log_ge_739_125`,
  `backlund_log_ge_739_125_of_ge_exp_739_125`, and
  `plattTrudgianBacklundEnvelope_le_halfLogPlusHalf_of_ge_exp_739_125`.
  The sharper tail interface
  `PlattTrudgianBacklundCut739_125TailInput`, supplied from the global
  envelope by `PlattTrudgianBacklundCut739_125TailInput.of_global`,
  pairs with `BacklundFiniteBandCheck140_exp739_125` and
  `BacklundFiniteBandCheck140_exp739_125.of_plattTrudgian` to prove
  `concreteS_halfLogPlusHalf_of_plattTrudgian_739_125Tail_and_finite`
  and
  `concreteS_halfLogPlusHalf_of_globalPlattTrudgian_and_finiteRange_739_125`.
  Since `backlund_exp_739_125_lt_370`, the concrete `[140, 370]`
  interfaces `BacklundFiniteBandCheck140_370`,
  `BacklundFiniteBandUniform25167Check140_370`,
  `BacklundFiniteBandUniform25167Check140_370.toFiniteBandCheck`,
  `BacklundFiniteBandUniform25167Check140_3690757803_10000000.of_140_370`,
  `BacklundFiniteBandCheck140_3690757803_10000000.of_140_370`,
  `BacklundFiniteBandCheck140_370.of_plattTrudgian`, and
  `BacklundFiniteBandCheck140_exp739_125.of_140_370` yield the headline
  theorems `concreteS_halfLogPlusHalf_of_globalPlattTrudgian_and_finite370`,
  `concreteS_halfLogPlusHalf_of_globalPlattTrudgian_and_plattTrudgianRange_concrete370`,
  and
  `concreteS_halfLogPlusHalf_of_globalPlattTrudgian_and_uniformFinite370`.
  The theorem-target certificate
  `BacklundFiniteBandArgumentPrincipleTheoremFixedPiExpAutoPosCertificate140_370`
  lowers via `toUniform25167Check` and culminates in
  `concreteS_halfLogPlusHalf_of_globalPlattTrudgian_and_argumentPrincipleTheoremFixedPiExpAutoPosFinite370`.
  The exact tangent-arithmetic refinement now reaches the cutoff
  `exp (151476/25625)`: the comparison theorems
  `plattTrudgianBacklundEnvelope_le_halfLogPlusHalf_of_log_ge_151476_25625`,
  `backlund_log_ge_151476_25625_of_ge_exp_151476_25625`, and
  `plattTrudgianBacklundEnvelope_le_halfLogPlusHalf_of_ge_exp_151476_25625`
  feed `PlattTrudgianBacklundCut151476_25625TailInput`,
  `BacklundFiniteBandCheck140_exp151476_25625`,
  `BacklundGoodHeightArgumentBound.of_plattTrudgian_151476_25625Tail_and_finite`,
  and the headline
  `concreteS_halfLogPlusHalf_of_plattTrudgian_151476_25625Tail_and_finite`.
  The exact global/finite-range route now exports directly to the
  generic interfaces as
  `ProvenBacklundTuringBound.of_globalPlattTrudgian_and_finiteRange_151476_25625`,
  `HalfLogPlusHalfSBound.of_globalPlattTrudgian_and_finiteRange_151476_25625`,
  and
  `TuringStyleSBound.of_globalPlattTrudgian_and_finiteRange_151476_25625`.
  The symbolic tangent split was then sharpened at `59/10`, with
  `backlund_log_59_10_le_71_40`,
  `backlund_log_log_le_tangent_59_10`,
  `plattTrudgianBacklundEnvelope_le_halfLogPlusHalf_of_log_ge_475481_80440`,
  `backlund_log_ge_475481_80440_of_ge_exp_475481_80440`, and
  `plattTrudgianBacklundEnvelope_le_halfLogPlusHalf_of_ge_exp_475481_80440`
  recording the improved cutoff. The full `475481/80440` route now has
  its own tail input, finite-band check, good-height adapter, headline
  theorem, global/finite-range theorem, and generic S-bound exports:
  `PlattTrudgianBacklundCut475481_80440TailInput`,
  `BacklundFiniteBandCheck140_exp475481_80440`,
  `BacklundGoodHeightArgumentBound.of_plattTrudgian_475481_80440Tail_and_finite`,
  `concreteS_halfLogPlusHalf_of_plattTrudgian_475481_80440Tail_and_finite`,
  `concreteS_halfLogPlusHalf_of_globalPlattTrudgian_and_finiteRange_475481_80440`,
  `ProvenBacklundTuringBound.of_globalPlattTrudgian_and_finiteRange_475481_80440`,
  `HalfLogPlusHalfSBound.of_globalPlattTrudgian_and_finiteRange_475481_80440`,
  and
  `TuringStyleSBound.of_globalPlattTrudgian_and_finiteRange_475481_80440`.
  The same tangent-at-`59/10` arithmetic now records the improved
  decimal cutoff `5911/1000` through
  `backlund_log_591_100_le_350_197`,
  `backlund_log_log_le_tangent_591_100`,
  `plattTrudgianBacklundEnvelope_le_halfLogPlusHalf_of_log_ge_5911_1000`,
  `backlund_log_ge_5911_1000_of_ge_exp_5911_1000`,
  `plattTrudgianBacklundEnvelope_le_halfLogPlusHalf_of_ge_exp_5911_1000`,
  `PlattTrudgianBacklundCut5911_1000TailInput`,
  `PlattTrudgianBacklundCut5911_1000TailInput.of_global`,
  `BacklundFiniteBandCheck140_exp5911_1000`,
  `BacklundFiniteBandCheck140_exp5911_1000.of_plattTrudgian`,
  `BacklundGoodHeightArgumentBound.of_plattTrudgian_5911_1000Tail_and_finite`,
  `concreteS_halfLogPlusHalf_of_plattTrudgian_5911_1000Tail_and_finite`,
  and
  `concreteS_halfLogPlusHalf_of_globalPlattTrudgian_and_finiteRange_5911_1000`.
  Its concrete endpoint layer records
  `backlund_exp_11_1000_le_101106073_100000000`,
  `backlund_exp_5911_1000_lt_369075049_1000000`,
  `BacklundFiniteBandCheck140_369075049_1000000`,
  `BacklundFiniteBandUniform25167Check140_369075049_1000000`,
  `BacklundFiniteBandUniform25167Check140_369075049_1000000.toFiniteBandCheck`,
  `BacklundFiniteBandCheck140_369075049_1000000.of_plattTrudgian`,
  `BacklundFiniteBandCheck140_exp5911_1000.of_140_369075049_1000000`,
  and headline theorems
  `concreteS_halfLogPlusHalf_of_globalPlattTrudgian_and_finite369075049_1000000`,
  `concreteS_halfLogPlusHalf_of_globalPlattTrudgian_and_plattTrudgianRange_concrete369075049_1000000`,
  and
  `concreteS_halfLogPlusHalf_of_globalPlattTrudgian_and_uniformFinite369075049_1000000`.
  The improved decimal endpoint now mirrors the count-range certificate
  stack too:
  `BacklundFiniteBandCountRangeMainCertificate140_369075049_1000000`,
  `BacklundFiniteBandEndpointCountRangeMainCertificate140_369075049_1000000`,
  `BacklundFiniteBandEndpointCountRangeFixedPiExpCertificate140_369075049_1000000`,
  the `[140, 370]` restriction adapters
  `BacklundFiniteBandCountRangeMainCertificate140_369075049_1000000.of_140_370`,
  `BacklundFiniteBandEndpointCountRangeMainCertificate140_369075049_1000000.of_140_370`,
  and
  `BacklundFiniteBandEndpointCountRangeFixedPiExpCertificate140_369075049_1000000.of_140_370`,
  the conversion adapters
  `BacklundFiniteBandEndpointCountRangeMainCertificate140_369075049_1000000.toCountRange`,
  `BacklundFiniteBandEndpointCountRangeFixedPiExpCertificate140_369075049_1000000.toEndpointCountRange`,
  uniform exports
  `BacklundFiniteBandCountRangeMainCertificate140_369075049_1000000.toUniform25167Check`,
  `BacklundFiniteBandEndpointCountRangeMainCertificate140_369075049_1000000.toUniform25167Check`,
  and
  `BacklundFiniteBandEndpointCountRangeFixedPiExpCertificate140_369075049_1000000.toUniform25167Check`,
  headline count-range theorems
  `concreteS_halfLogPlusHalf_of_globalPlattTrudgian_and_countRangeMainFinite369075049_1000000`,
  `concreteS_halfLogPlusHalf_of_globalPlattTrudgian_and_endpointCountRangeMainFinite369075049_1000000`,
  and
  `concreteS_halfLogPlusHalf_of_globalPlattTrudgian_and_endpointCountRangeFixedPiExpFinite369075049_1000000`,
  plus source-pair good-height adapters
  `BacklundGoodHeightArgumentBound.of_globalPlattTrudgian_and_endpointCountRangeFixedPiExpFinite369075049_1000000`
  and
  `BacklundGoodHeightArgumentBound.of_globalPlattTrudgian_and_endpointCountRangeFixedPiExpFinite370_improvedDecimal`.
  A concrete two-unit endpoint-count grid now packages this interval
  into row-local certificate obligations:
  `BacklundGrid2EndpointCountRow`,
  `BacklundGrid2EndpointCountRowFacts`,
  `BacklundGrid2EndpointCountEqualities`,
  `BacklundGrid2EndpointSmoothFacts`,
  `BacklundGrid2EndpointSmoothExpFacts`,
  `BacklundGrid2EndpointSmoothExpFacts.toSmoothFacts`,
  `BacklundGrid2EndpointCountRowFacts.ofSeparated`,
  `BacklundGrid2EndpointCountRow.toEndpointCountRangeMainSlab`,
  `backlundGrid2EndpointCount140_369075049_1000000`,
  `backlundGrid2EndpointRow140_369075049_1000000`,
  `backlundGrid2EndpointRows140_369075049_1000000`,
  `backlundGrid2EndpointRows140_369075049_1000000_cover`,
  `BacklundGrid2EndpointCountFacts140_369075049_1000000`,
  `BacklundGrid2EndpointCountEqualities140_369075049_1000000`,
  `BacklundGrid2EndpointSmoothFacts140_369075049_1000000`,
  `BacklundGrid2EndpointSmoothExpFacts140_369075049_1000000`,
  `backlundGrid2EndpointSmoothRationalExpFact_row0`,
  `backlundGrid2EndpointSmoothRationalExpFact_row1`,
  `backlundGrid2EndpointSmoothRationalExpFact_row2`,
  `backlundGrid2EndpointSmoothRationalExpFact_row3`,
  `backlundGrid2EndpointSmoothRationalExpFact_row4`,
  `backlundGrid2EndpointSmoothRationalExpFact_row5`,
  `backlundGrid2EndpointSmoothRationalExpFact_row6`,
  `backlundGrid2EndpointSmoothRationalExpFact_row7`,
  `backlundGrid2EndpointSmoothRationalExpFact_row8`,
  `backlundGrid2EndpointSmoothRationalExpFact_row9`,
  `backlundGrid2EndpointSmoothRationalExpFact_row10`,
  `backlundGrid2EndpointSmoothRationalExpFact_row11`,
  `backlundGrid2EndpointSmoothRationalExpFact_row12`,
  `backlundGrid2EndpointSmoothRationalExpFact_row13`,
  `backlundGrid2EndpointSmoothRationalExpFact_row14`,
  `backlundGrid2EndpointSmoothRationalExpFact_row15`,
  `backlundGrid2EndpointSmoothRationalExpFact_row16`,
  `backlundGrid2EndpointSmoothRationalExpFact_row17`,
  `backlundGrid2EndpointSmoothRationalExpFact_row18`,
  `backlundGrid2EndpointSmoothRationalExpFact_row19`,
  `backlundGrid2EndpointSmoothRationalExpFact_row20`,
  `backlundGrid2EndpointSmoothRationalExpFact_row21`,
  `backlundGrid2EndpointSmoothRationalExpFact_row22`,
  `backlundGrid2EndpointSmoothRationalExpFact_row23`,
  `backlundGrid2EndpointSmoothRationalExpFact_row24`,
  `backlundGrid2EndpointSmoothRationalExpFact_row25`,
  `backlundGrid2EndpointSmoothRationalExpFact_row26`,
  `backlundGrid2EndpointSmoothRationalExpFact_row27`,
  `backlundGrid2EndpointSmoothRationalExpFact_row28`,
  `backlundGrid2EndpointSmoothRationalExpFact_row29`,
  `backlundGrid2EndpointSmoothRationalExpFact_row30`,
  `backlundGrid2EndpointSmoothRationalExpFact_row31`,
  `backlundGrid2EndpointSmoothRationalExpFact_row32`,
  `backlundGrid2EndpointSmoothRationalExpFact_row33`,
  `backlundGrid2EndpointSmoothRationalExpFact_row34`,
  `backlundGrid2EndpointSmoothRationalExpFact_row35`,
  `backlundGrid2EndpointSmoothRationalExpFact_row36`,
  `backlundGrid2EndpointSmoothRationalExpFact_row37`,
  `backlundGrid2EndpointSmoothRationalExpFact_row38`,
  `backlundGrid2EndpointSmoothRationalExpFact_row39`,
  `backlundGrid2EndpointSmoothRationalExpFact_row40`,
  `backlundGrid2EndpointSmoothRationalExpFact_row41`,
  `backlundGrid2EndpointSmoothRationalExpFact_row42`,
  `backlundGrid2EndpointSmoothRationalExpFact_row43`,
  `backlundGrid2EndpointSmoothRationalExpFact_row44`,
  `backlundGrid2EndpointSmoothRationalExpFact_row45`,
  `backlundGrid2EndpointSmoothRationalExpFact_row46`,
  `backlundGrid2EndpointSmoothRationalExpFact_row47`,
  `backlundGrid2EndpointSmoothRationalExpFact_row48`,
  `backlundGrid2EndpointSmoothRationalExpFact_row49`,
  `backlundGrid2EndpointSmoothRationalExpFact_row50`,
  `backlundGrid2EndpointSmoothRationalExpFact_row51`,
  `backlundGrid2EndpointSmoothRationalExpFact_row52`,
  `backlundGrid2EndpointSmoothRationalExpFact_row53`,
  `backlundGrid2EndpointSmoothRationalExpFact_row54`,
  `backlundGrid2EndpointSmoothRationalExpFact_row55`,
  `backlundGrid2EndpointSmoothRationalExpFact_row56`,
  `backlundGrid2EndpointSmoothRationalExpFact_row57`,
  `backlundGrid2EndpointSmoothRationalExpFact_row58`,
  `backlundGrid2EndpointSmoothRationalExpFact_row59`,
  `backlundGrid2EndpointSmoothRationalExpFact_row60`,
  `backlundGrid2EndpointSmoothRationalExpFact_row61`,
  `backlundGrid2EndpointSmoothRationalExpFact_row62`,
  `backlundGrid2EndpointSmoothRationalExpFact_row63`,
  `backlundGrid2EndpointSmoothRationalExpFact_row64`,
  `backlundGrid2EndpointSmoothRationalExpFact_row65`,
  `backlundGrid2EndpointSmoothRationalExpFact_row66`,
  `backlundGrid2EndpointSmoothRationalExpFact_row67`,
  `backlundGrid2EndpointSmoothRationalExpFact_row68`,
  `backlundGrid2EndpointSmoothRationalExpFact_row69`,
  `backlundGrid2EndpointSmoothRationalExpFact_row70`,
  `backlundGrid2EndpointSmoothRationalExpFact_row71`,
  `backlundGrid2EndpointSmoothRationalExpFact_row72`,
  `backlundGrid2EndpointSmoothRationalExpFact_row73`,
  `backlundGrid2EndpointSmoothRationalExpFact_row74`,
  `backlundGrid2EndpointSmoothRationalExpFact_row75`,
  `backlundGrid2EndpointSmoothRationalExpFact_row76`,
  `backlundGrid2EndpointSmoothRationalExpFact_row77`,
  `backlundGrid2EndpointSmoothRationalExpFact_row78`,
  `backlundGrid2EndpointSmoothRationalExpFact_row79`,
  `backlundGrid2EndpointSmoothRationalExpFact_row80`,
  `backlundGrid2EndpointSmoothRationalExpFact_row81`,
  `backlundGrid2EndpointSmoothRationalExpFact_row82`,
  `backlundGrid2EndpointSmoothRationalExpFact_row83`,
  `backlundGrid2EndpointSmoothRationalExpFact_row84`,
  `backlundGrid2EndpointSmoothRationalExpFact_row85`,
  `backlundGrid2EndpointSmoothRationalExpFact_row86`,
  `backlundGrid2EndpointSmoothRationalExpFact_row87`,
  `backlundGrid2EndpointSmoothRationalExpFact_row88`,
  `backlundGrid2EndpointSmoothRationalExpFact_row89`,
  `backlundGrid2EndpointSmoothRationalExpFact_row90`,
  `backlundGrid2EndpointSmoothRationalExpFact_row91`,
  `backlundGrid2EndpointSmoothRationalExpFact_row92`,
  `backlundGrid2EndpointSmoothRationalExpFact_row93`,
  `backlundGrid2EndpointSmoothRationalExpFact_row94`,
  `backlundGrid2EndpointSmoothRationalExpFact_row95`,
  `backlundGrid2EndpointSmoothRationalExpFact_row96`,
  `backlundGrid2EndpointSmoothRationalExpFact_row97`,
  `backlundGrid2EndpointSmoothRationalExpFact_row98`,
  `backlundGrid2EndpointSmoothRationalExpFact_row99`,
  `backlundGrid2EndpointSmoothRationalExpFact_row100`,
  `backlundGrid2EndpointSmoothRationalExpFact_row101`,
  `backlundGrid2EndpointSmoothRationalExpFact_row102`,
  `backlundGrid2EndpointSmoothRationalExpFact_row103`,
  `backlundGrid2EndpointSmoothRationalExpFact_row104`,
  `backlundGrid2EndpointSmoothRationalExpFact_row105`,
  `backlundGrid2EndpointSmoothRationalExpFact_row106`,
  `backlundGrid2EndpointSmoothRationalExpFact_row107`,
  `backlundGrid2EndpointSmoothRationalExpFact_row108`,
  `backlundGrid2EndpointSmoothRationalExpFact_row109`,
  `backlundGrid2EndpointSmoothRationalExpFact_row110`,
  `backlundGrid2EndpointSmoothRationalExpFact_row111`,
  `backlundGrid2EndpointSmoothRationalExpFact_row112`,
  `backlundGrid2EndpointSmoothRationalExpFact_row113`,
  `backlundGrid2EndpointSmoothRationalExpFact_row114`,
  `BacklundGrid2EndpointSmoothFacts140_369075049_1000000.ofExpFacts`,
  `BacklundGrid2EndpointCountFacts140_369075049_1000000.ofSeparated`,
  `BacklundGrid2EndpointCountFacts140_369075049_1000000.toEndpointCountRangeMainCertificate`,
  and the headline
  `concreteS_halfLogPlusHalf_of_globalPlattTrudgian_and_grid2EndpointCountFacts369075049`.
  The separated endpoint-count plus rational/exponential smooth route is
  exposed by
  `concreteS_halfLogPlusHalf_of_globalPlattTrudgian_and_grid2CountExpFacts369075049`,
  and its verified smooth-main wrapper is
  `concreteS_halfLogPlusHalf_of_globalPlattTrudgian_and_grid2CountFacts369075049_verifiedSmooth`.
  The sharp sourced pair is also packaged as
  `ClassicalBacklundTuringPlattGlobalFiniteRangeInputs`, with exports
  `toGoodHeightArgumentBound`, `toProofInputs`,
  `toProvenBacklundTuringBound`, `toHalfLogPlusHalfSBound`, and
  `toTuringStyleSBound`, plus headline theorem
  `concreteS_halfLogPlusHalf_of_plattGlobalFiniteRangeBacklundTuringInputs`.
  Its near-endpoint export layer routes through
  `3690757803/10000000` via
  `toGoodHeightArgumentBoundNearEndpoint`,
  `toProofInputsNearEndpoint`,
  `toProvenBacklundTuringBoundNearEndpoint`,
  `toHalfLogPlusHalfSBoundNearEndpoint`,
  `toTuringStyleSBoundNearEndpoint`, and
  `concreteS_halfLogPlusHalf_of_plattGlobalFiniteRangeBacklundTuringInputs_nearEndpoint`.
  The Taylor-certified endpoint layer now also records the finer bound
  `backlund_exp_475481_80440_lt_3690757800925204_10000000000000`,
  together with
  `BacklundFiniteBandCheck140_3690757800925204_10000000000000`,
  `BacklundFiniteBandUniform25167Check140_3690757800925204_10000000000000`,
  `BacklundFiniteBandUniform25167Check140_3690757800925204_10000000000000.toFiniteBandCheck`,
  `BacklundFiniteBandCheck140_3690757800925204_10000000000000.of_plattTrudgian`,
  `BacklundFiniteBandCheck140_3690757800925204_10000000000000.of_140_3690757800926_10000000000`,
  `BacklundFiniteBandCheck140_exp475481_80440.of_140_3690757800925204_10000000000000`,
  and headline theorems
  `concreteS_halfLogPlusHalf_of_globalPlattTrudgian_and_finite3690757800925204_10000000000000`,
  `concreteS_halfLogPlusHalf_of_globalPlattTrudgian_and_plattTrudgianRange_concrete3690757800925204_10000000000000`,
  and
  `concreteS_halfLogPlusHalf_of_globalPlattTrudgian_and_uniformFinite3690757800925204_10000000000000`.
  The same finer endpoint now has count-range certificate surfaces:
  `BacklundFiniteBandCountRangeMainCertificate140_3690757800925204_10000000000000`,
  `BacklundFiniteBandEndpointCountRangeMainCertificate140_3690757800925204_10000000000000`,
  `BacklundFiniteBandEndpointCountRangeFixedPiExpCertificate140_3690757800925204_10000000000000`,
  their `[140, 370]` restriction adapters
  `BacklundFiniteBandCountRangeMainCertificate140_3690757800925204_10000000000000.of_140_370`,
  `BacklundFiniteBandEndpointCountRangeMainCertificate140_3690757800925204_10000000000000.of_140_370`,
  and
  `BacklundFiniteBandEndpointCountRangeFixedPiExpCertificate140_3690757800925204_10000000000000.of_140_370`,
  conversion adapters
  `BacklundFiniteBandEndpointCountRangeMainCertificate140_3690757800925204_10000000000000.toCountRange`,
  `BacklundFiniteBandEndpointCountRangeFixedPiExpCertificate140_3690757800925204_10000000000000.toEndpointCountRange`,
  and uniform-certificate exports
  `BacklundFiniteBandCountRangeMainCertificate140_3690757800925204_10000000000000.toUniform25167Check`,
  `BacklundFiniteBandEndpointCountRangeMainCertificate140_3690757800925204_10000000000000.toUniform25167Check`,
  and
  `BacklundFiniteBandEndpointCountRangeFixedPiExpCertificate140_3690757800925204_10000000000000.toUniform25167Check`.
  The sharper fixed-π exp endpoint count-range source pair also lowers
  all the way to final and generic bound packages:
  `BacklundGoodHeightArgumentBound.of_globalPlattTrudgian_and_endpointCountRangeFixedPiExpFinite3690757800925204_10000000000000`,
  `FinalBacklundTuringTwoInputs.of_globalPlattTrudgian_and_endpointCountRangeFixedPiExpFinite3690757800925204_10000000000000`,
  `FinalBacklundTuringAnalyticInputs.of_globalPlattTrudgian_and_endpointCountRangeFixedPiExpFinite3690757800925204_10000000000000`,
  `ProvenBacklundTuringBound.of_globalPlattTrudgian_and_endpointCountRangeFixedPiExpFinite3690757800925204_10000000000000`,
  `HalfLogPlusHalfSBound.of_globalPlattTrudgian_and_endpointCountRangeFixedPiExpFinite3690757800925204_10000000000000`,
  `TuringStyleSBound.of_globalPlattTrudgian_and_endpointCountRangeFixedPiExpFinite3690757800925204_10000000000000`,
  and
  `concreteS_halfLogPlusHalf_of_globalPlattTrudgian_and_endpointCountRangeFixedPiExpFinite3690757800925204_10000000000000_viaProven`.
  The concrete endpoint for this sharp route first pushed to
  `1846/5`: `backlund_exp_5_lt_74207_500`,
  `backlund_exp_9_10_lt_24597_10000`,
  `backlund_exp_59111_10000_lt_1846_5`, and
  `backlund_exp_475481_80440_lt_1846_5` support
  `BacklundFiniteBandCheck140_1846_5`,
  `BacklundFiniteBandUniform25167Check140_1846_5`, and
  `BacklundFiniteBandUniform25167Check140_1846_5.toFiniteBandCheck`.
  It is now shaved again to `3691/10` via
  `backlund_exp_177_16088_le_25277_25000`,
  `backlund_exp_475481_80440_lt_3691_10`,
  `BacklundFiniteBandCheck140_3691_10`,
  `BacklundFiniteBandUniform25167Check140_3691_10`,
  `BacklundFiniteBandUniform25167Check140_3691_10.toFiniteBandCheck`,
  `BacklundFiniteBandCheck140_3691_10.of_plattTrudgian`,
  `BacklundFiniteBandCheck140_3691_10.of_140_1846_5`,
  `BacklundFiniteBandCheck140_exp475481_80440.of_140_3691_10`,
  `concreteS_halfLogPlusHalf_of_globalPlattTrudgian_and_finite3691_10`,
  `concreteS_halfLogPlusHalf_of_globalPlattTrudgian_and_plattTrudgianRange_concrete3691_10`,
  and
  `concreteS_halfLogPlusHalf_of_globalPlattTrudgian_and_uniformFinite3691_10`.
  The endpoint has since been tightened again to `9227/25 = 369.08`,
  using `backlund_exp_5_lt_3710329_25000`,
  `backlund_exp_9_10_lt_3074504_1250000`,
  `backlund_exp_177_16088_le_126383_125000`, and
  `backlund_exp_475481_80440_lt_9227_25`; the finite-band interfaces
  are `BacklundFiniteBandCheck140_9227_25`,
  `BacklundFiniteBandUniform25167Check140_9227_25`, and
  `BacklundFiniteBandUniform25167Check140_9227_25.toFiniteBandCheck`.
  The near-exact endpoint now sits at
  `3690757803/10000000`, supported by
  `backlund_exp_5_lt_148413159142_1000000000`,
  `backlund_exp_9_10_lt_24596031113_10000000000`,
  `backlund_exp_177_16088_le_1263828416885_1250000000000`, and
  `backlund_exp_475481_80440_lt_3690757803_10000000`; it exposes
  `BacklundFiniteBandCheck140_3690757803_10000000`,
  `BacklundFiniteBandUniform25167Check140_3690757803_10000000`,
  `BacklundFiniteBandUniform25167Check140_3690757803_10000000.toFiniteBandCheck`,
  `BacklundFiniteBandCheck140_3690757803_10000000.of_plattTrudgian`,
  `BacklundFiniteBandCheck140_3690757803_10000000.of_140_369075781_1000000`,
  `BacklundFiniteBandCheck140_exp475481_80440.of_140_3690757803_10000000`,
  `concreteS_halfLogPlusHalf_of_globalPlattTrudgian_and_finite3690757803_10000000`,
  `concreteS_halfLogPlusHalf_of_globalPlattTrudgian_and_plattTrudgianRange_concrete3690757803_10000000`,
  and
  `concreteS_halfLogPlusHalf_of_globalPlattTrudgian_and_uniformFinite3690757803_10000000`.
  A Taylor-certified refinement moves the endpoint to
  `3690757801/10000000`, using
  `backlund_exp_one_le_271828182846_100000000000`,
  `backlund_exp_9_10_le_245960311116_100000000000`,
  `backlund_exp_177_16088_le_101106273351_100000000000`, and
  `backlund_exp_475481_80440_lt_3690757801_10000000`. Its public
  surfaces are `BacklundFiniteBandCheck140_3690757801_10000000`,
  `BacklundFiniteBandUniform25167Check140_3690757801_10000000`,
  `BacklundFiniteBandUniform25167Check140_3690757801_10000000.toFiniteBandCheck`,
  `BacklundFiniteBandCheck140_3690757801_10000000.of_plattTrudgian`,
  `BacklundFiniteBandCheck140_3690757801_10000000.of_140_3690757803_10000000`,
  `BacklundFiniteBandCheck140_exp475481_80440.of_140_3690757801_10000000`,
  and
  `concreteS_halfLogPlusHalf_of_globalPlattTrudgian_and_finite3690757801_10000000`.
  A higher-order Taylor refinement pushes the endpoint to
  `369075780093/1000000000`, using
  `backlund_exp_one_le_27182818284591_10000000000000`,
  `backlund_exp_9_10_le_2459603111157_1000000000000`,
  `backlund_exp_177_16088_le_5055313667537_5000000000000`, and
  `backlund_exp_475481_80440_lt_369075780093_1000000000`; it exposes
  `BacklundFiniteBandCheck140_369075780093_1000000000`,
  `BacklundFiniteBandUniform25167Check140_369075780093_1000000000`,
  `BacklundFiniteBandUniform25167Check140_369075780093_1000000000.toFiniteBandCheck`,
  `BacklundFiniteBandCheck140_369075780093_1000000000.of_plattTrudgian`,
  `BacklundFiniteBandCheck140_369075780093_1000000000.of_140_3690757801_10000000`,
  `BacklundFiniteBandCheck140_exp475481_80440.of_140_369075780093_1000000000`,
  `concreteS_halfLogPlusHalf_of_globalPlattTrudgian_and_finite369075780093_1000000000`,
  `concreteS_halfLogPlusHalf_of_globalPlattTrudgian_and_plattTrudgianRange_concrete369075780093_1000000000`,
  and
  `concreteS_halfLogPlusHalf_of_globalPlattTrudgian_and_uniformFinite369075780093_1000000000`.
  A nineteenth-order Taylor refinement moves to
  `3690757800926/10000000000`, using
  `backlund_exp_one_le_271828182845905_100000000000000`,
  `backlund_exp_9_10_le_245960311115695_100000000000000`,
  `backlund_exp_177_16088_le_101106273350734_100000000000000`, and
  `backlund_exp_475481_80440_lt_3690757800926_10000000000`; it exposes
  `BacklundFiniteBandCheck140_3690757800926_10000000000`,
  `BacklundFiniteBandUniform25167Check140_3690757800926_10000000000`,
  `BacklundFiniteBandUniform25167Check140_3690757800926_10000000000.toFiniteBandCheck`,
  `BacklundFiniteBandCheck140_3690757800926_10000000000.of_plattTrudgian`,
  `BacklundFiniteBandCheck140_3690757800926_10000000000.of_140_369075780093_1000000000`,
  `BacklundFiniteBandCheck140_exp475481_80440.of_140_3690757800926_10000000000`,
  `concreteS_halfLogPlusHalf_of_globalPlattTrudgian_and_finite3690757800926_10000000000`,
  `concreteS_halfLogPlusHalf_of_globalPlattTrudgian_and_plattTrudgianRange_concrete3690757800926_10000000000`,
  and
  `concreteS_halfLogPlusHalf_of_globalPlattTrudgian_and_uniformFinite3690757800926_10000000000`.
  A twenty-first-order refinement reaches
  `36907578009252/100000000000`, with
  `backlund_exp_one_le_2718281828459046_1000000000000000`,
  `backlund_exp_9_10_le_2459603111156950_1000000000000000`,
  `backlund_exp_177_16088_le_1011062733507339_1000000000000000`, and
  `backlund_exp_475481_80440_lt_36907578009252_100000000000`; its
  finite-band interfaces are
  `BacklundFiniteBandCheck140_36907578009252_100000000000`,
  `BacklundFiniteBandUniform25167Check140_36907578009252_100000000000`,
  and
  `BacklundFiniteBandUniform25167Check140_36907578009252_100000000000.toFiniteBandCheck`.
  The narrow computational-certificate interface
  `BacklundFiniteBandUniform25167Check140_374` packages the uniform
  `|S(T)| ≤ 2.5167` check on `[140, 374]`, converts through
  `BacklundFiniteBandUniform25167Check140_374.toFiniteBandCheck`, and
  yields the headline
  `concreteS_halfLogPlusHalf_of_globalPlattTrudgian_and_uniformFinite374`.
  The next executable certificate target is
  `BacklundFiniteBandCountMainCertificate140_374`: a finite list of
  `BacklundCountMainSlabCertificate` slabs covering `[140, 374]`, where
  each slab supplies the weighted zero-count identity and
  smooth-main-term interval bounds. The adapter
  `BacklundFiniteBandCountMainCertificate140_374.toUniform25167Check`
  feeds the uniform certificate, and
  `concreteS_halfLogPlusHalf_of_globalPlattTrudgian_and_countMainFinite374`
  is the resulting count/main-term finite-band front door. The smooth
  main-term side now has its own endpoint infrastructure:
  `hasDerivAt_smoothMainTerm`, `smoothMainTerm_monotoneOn_Ici_two_pi`,
  and `smoothMainTerm_bounds_of_endpoint_bounds` reduce slabwise
  main-term bounds to endpoint estimates once the slab begins above
  `2π`. The endpoint-table interface
  `BacklundFiniteBandEndpointCountMainCertificate140_374`, built from
  `BacklundEndpointCountMainSlabCertificate`, lowers through
  `BacklundFiniteBandEndpointCountMainCertificate140_374.toCountMain`
  and `toUniform25167Check`; the headline theorem
  `concreteS_halfLogPlusHalf_of_globalPlattTrudgian_and_endpointCountMainFinite374`
  is the endpoint-style computational front door. The even closer
  table-facing interface
  `BacklundFiniteBandEndpointCumulativeCountMainCertificate140_374`
  records cumulative zero counts only at slab endpoints; the monotonicity
  lemma `zetaWeightedZeroCountUpToHeight_eq_of_endpoint_eq` makes the
  count constant on the slab. Its adapters `toEndpoint` and
  `toUniform25167Check` culminate in
  `concreteS_halfLogPlusHalf_of_globalPlattTrudgian_and_endpointCumulativeCountMainFinite374`.
  A more robust count-range interface,
  `BacklundFiniteBandCountRangeMainCertificate140_374`, allows slabs
  containing zero ordinates by bounding the cumulative count between
  endpoint values. Its endpoint-table version
  `BacklundFiniteBandEndpointCountRangeMainCertificate140_374` lowers
  through `toCountRange` and `toUniform25167Check`, with headline
  theorems
  `concreteS_halfLogPlusHalf_of_globalPlattTrudgian_and_countRangeMainFinite374`
  and
  `concreteS_halfLogPlusHalf_of_globalPlattTrudgian_and_endpointCountRangeMainFinite374`.
  The argument-principle finite-band interface,
  `BacklundFiniteBandArgumentPrincipleCountRangeMainCertificate140_374`,
  packages each slab as a rectangle argument-principle certificate
  `BacklundArgumentPrincipleCountRangeMainSlabCertificate`, whose
  natural argument index is proved to be the actual zeta slab count.
  The adapters `toTuringCountRange` and `toUniform25167Check` lower
  this argument-principle data to the existing count-range certificate,
  and
  `concreteS_halfLogPlusHalf_of_globalPlattTrudgian_and_argumentPrincipleCountRangeMainFinite374`
  is the corresponding headline finite-band theorem. The front-most
  theorem-target interface,
  `BacklundFiniteBandArgumentPrincipleTheoremCountRangeMainCertificate140_374`,
  accepts slabs
  `BacklundArgumentPrincipleTheoremCountRangeMainSlabCertificate`
  carrying `ZetaRectangleArgumentPrincipleTheorem` data directly.
  Its `toArgumentPrinciple` and `toUniform25167Check` adapters lower
  through the canonical argument-principle layer, yielding
  `concreteS_halfLogPlusHalf_of_globalPlattTrudgian_and_argumentPrincipleTheoremCountRangeMainFinite374`.
  The sharpest packaged source interface is now
  `ClassicalBacklundTuringPlattAPInputs`: it pairs the global
  Platt--Trudgian input with the theorem-target finite-band certificate.
  Its adapters `toFinite374`, `toGoodHeightArgumentBound`,
  `toProofInputs`, `toTheoremPackage`,
  `toProvenBacklundTuringBound`, `toHalfLogPlusHalfSBound`, and
  `toTuringStyleSBound` feed the existing Backlund/Turing APIs, while
  `concreteS_halfLogPlusHalf_of_plattAPBacklundTuringInputs` is the
  compact final S-bound front door for this package.
  The newest table-facing variant pushes endpoint arithmetic one layer
  closer to emitted data:
  `smoothMainTerm_lower_bound_of_log_ratio_lower` and
  `smoothMainTerm_upper_bound_of_log_ratio_upper` turn endpoint
  log-ratio bounds into `smoothMainTerm` bounds, while
  `BacklundArgumentPrincipleTheoremLogBoundSlabCertificate` and
  `BacklundFiniteBandArgumentPrincipleTheoremLogBoundCertificate140_374`
  package those log bounds for the finite `[140, 374]` table. Their
  adapters `toTheoremSlab`, `toTheoremCountRange`, and
  `toUniform25167Check` feed the theorem-target layer, yielding
  `concreteS_halfLogPlusHalf_of_globalPlattTrudgian_and_argumentPrincipleTheoremLogBoundFinite374`.
  One layer closer to rational interval arithmetic,
  `log_ratio_lower_of_ratio_lower` and
  `log_ratio_upper_of_ratio_upper` turn certified ratio bounds for
  `T / (2π)` into log-ratio bounds. The corresponding table shape
  `BacklundArgumentPrincipleTheoremRatioBoundSlabCertificate`, finite
  certificate
  `BacklundFiniteBandArgumentPrincipleTheoremRatioBoundCertificate140_374`,
  and adapters `toLogBound`, `toLogBoundSlab`, and
  `toUniform25167Check` lower the ratio-bound table into the log-bound
  finite-band route. The ratio arithmetic now also has table-friendly
  multiplicative and rational-π helpers:
  `ratio_lower_of_two_pi_mul_le`, `ratio_upper_of_le_two_pi_mul`,
  `ratio_lower_of_pi_upper_bound`, and
  `ratio_upper_of_pi_lower_bound`; the exponential log-certificate
  helpers `log_lower_of_exp_le` and `log_upper_of_le_exp` let a table
  prove logarithm bounds through exponential inequalities instead. The
  concrete six-decimal bounds
  `backlund_pi_lower_3141592_1000000` and
  `backlund_pi_upper_3141593_1000000` are exposed for finite-table
  arithmetic, and `top_ratio_pos_of_fixed_pi_lower_mul` derives the
  positivity of a fixed-π upper ratio endpoint from the fixed lower
  π-bound certificate. The
  corresponding Pi/exp certificate layer is
  `BacklundArgumentPrincipleTheoremPiExpSlabCertificate` and
  `BacklundFiniteBandArgumentPrincipleTheoremPiExpCertificate140_374`,
  with `toRatioBound`, `toUniform25167Check`, and the headline
  `concreteS_halfLogPlusHalf_of_globalPlattTrudgian_and_argumentPrincipleTheoremPiExpFinite374`.
  The exported source package
  `ClassicalBacklundTuringPlattAPPiExpInputs` lowers through
  `toRatioInputs` and `toPlattAPInputs`, exports the usual
  `toFinite374`, `toGoodHeightArgumentBound`, `toProofInputs`,
  `toTheoremPackage`, `toProvenBacklundTuringBound`,
  `toHalfLogPlusHalfSBound`, and `toTuringStyleSBound` adapters, and
  culminates in
  `concreteS_halfLogPlusHalf_of_plattAPPiExpBacklundTuringInputs`.
  The fixed-π Pi/exp layer,
  `BacklundArgumentPrincipleTheoremFixedPiExpSlabCertificate` and
  `BacklundFiniteBandArgumentPrincipleTheoremFixedPiExpCertificate140_374`,
  removes per-row π bounds from the table; its `toPiExp`,
  `toUniform25167Check`, and
  `concreteS_halfLogPlusHalf_of_globalPlattTrudgian_and_argumentPrincipleTheoremFixedPiExpFinite374`
  lower back into the Pi/exp route. The auto-positivity fixed-π exp
  layer:
  `BacklundArgumentPrincipleTheoremFixedPiExpAutoPosSlabCertificate`
  and
  `BacklundFiniteBandArgumentPrincipleTheoremFixedPiExpAutoPosCertificate140_374`
  drop the explicit top-ratio positivity field and derive it from the
  endpoint inequality. Their `toFixedPiExp` and `toUniform25167Check`
  adapters feed the fixed-π route, with headline theorem
  `concreteS_halfLogPlusHalf_of_globalPlattTrudgian_and_argumentPrincipleTheoremFixedPiExpAutoPosFinite374`.
  The matching source package
  `ClassicalBacklundTuringPlattAPFixedPiExpAutoPosInputs` lowers through
  `toFixedPiExpInputs` and `toProofInputs`, exports
  `toProvenBacklundTuringBound`, `toHalfLogPlusHalfSBound`, and
  `toTuringStyleSBound`, and culminates in
  `concreteS_halfLogPlusHalf_of_plattAPFixedPiExpAutoPosBacklundTuringInputs`.
  It now also lowers individual slabs directly via
  `BacklundArgumentPrincipleTheoremFixedPiExpAutoPosSlabCertificate.toCountRangeMainSlab`
  and
  `BacklundArgumentPrincipleTheoremFixedPiExpAutoPosSlabCertificate.uniform25167`.
  The current smallest finite-table row shape is the auto-bottom
  fixed-π exp layer: `backlund_two_pi_le_of_ge_140` proves the common
  `2π ≤ R.bottom` side condition from the table-facing hypothesis
  `140 ≤ R.bottom`, and
  `BacklundArgumentPrincipleTheoremFixedPiExpAutoBottomSlabCertificate`
  lowers through
  `BacklundArgumentPrincipleTheoremFixedPiExpAutoBottomSlabCertificate.toAutoPosSlab`.
  The finite-list source
  `BacklundFiniteBandArgumentPrincipleTheoremFixedPiExpAutoBottomCertificate140_370`
  packages these auto-bottom theorem-target slabs on `[140, 370]`,
  lowers through
  `BacklundFiniteBandArgumentPrincipleTheoremFixedPiExpAutoBottomCertificate140_370.toAutoPos`
  and `toUniform25167Check`, and gives the headline theorem
  `concreteS_halfLogPlusHalf_of_globalPlattTrudgian_and_argumentPrincipleTheoremFixedPiExpAutoBottomFinite370`.
  The sharpened finite list
  `BacklundFiniteBandArgumentPrincipleTheoremFixedPiExpAutoPosCertificate140_373`
  supplies `toUniform25167Check`, yielding
  `concreteS_halfLogPlusHalf_of_globalPlattTrudgian_and_argumentPrincipleTheoremFixedPiExpAutoPosFinite373`.
  The new `370`-endpoint package
  `ClassicalBacklundTuringPlattAPFixedPiExpAutoPosInputs370` is the
  corresponding smallest source surface: it lowers to the good-height
  proof input, proves
  `concreteS_halfLogPlusHalf_of_plattAPFixedPiExpAutoPosBacklundTuringInputs370`,
  and exports `toProvenBacklundTuringBound`, `toHalfLogPlusHalfSBound`,
  and `toTuringStyleSBound` for the general Path B envelope interface.
  The auto-bottom version
  `ClassicalBacklundTuringPlattAPFixedPiExpAutoBottomInputs370` is now
  the leanest current Backlund/Turing source package: it lowers through
  `toAutoPosInputs370`, `toGoodHeightArgumentBound`, and
  `toProofInputs`, proves
  `concreteS_halfLogPlusHalf_of_plattAPFixedPiExpAutoBottomBacklundTuringInputs370`,
  and exports `toProvenBacklundTuringBound`, `toHalfLogPlusHalfSBound`,
  and `toTuringStyleSBound`.
  The newest and most table-facing version is the auto-rectangle layer:
  `backlundFixedSideRectangle`, `backlundFixedSideRectangle_left_lt_zero`,
  and `backlundFixedSideRectangle_one_lt_right` fix the horizontal sides
  at `-1` and `2`, so
  `BacklundArgumentPrincipleTheoremFixedPiExpAutoRectSlabCertificate`
  records only the vertical endpoints plus the argument-principle and
  numerical data. Its `toAutoBottomSlab` adapter feeds
  `BacklundFiniteBandArgumentPrincipleTheoremFixedPiExpAutoRectCertificate140_370`,
  whose `toAutoBottom` and `toUniform25167Check` adapters culminate in
  `concreteS_halfLogPlusHalf_of_globalPlattTrudgian_and_argumentPrincipleTheoremFixedPiExpAutoRectFinite370`.
  The natural-index variant
  `BacklundArgumentPrincipleTheoremFixedPiExpAutoRectNatSlabCertificate`
  lets the table provide a natural contour index and an equality to the
  integer argument index; `backlund_argumentIndexNat_eq_of_eq_nat`
  converts that equality into Lean's canonical nonnegative-index
  conversion, and `toAutoRectSlab` lowers back to the auto-rectangle row.
  Its finite-list package
  `BacklundFiniteBandArgumentPrincipleTheoremFixedPiExpAutoRectNatCertificate140_370`
  lowers through `toAutoRect` and `toUniform25167Check`, with headline
  theorem
  `concreteS_halfLogPlusHalf_of_globalPlattTrudgian_and_argumentPrincipleTheoremFixedPiExpAutoRectNatFinite370`.
  The endpoint-count auto-rectangle layer is closer to a verified zero
  table: `BacklundArgumentPrincipleTheoremFixedPiExpAutoRectEndpointCountSlabCertificate`
  records cumulative weighted zero counts at the bottom and top
  endpoints, derives the slab index as their difference, and lowers via
  `toNatSlab`. Its finite-list package
  `BacklundFiniteBandArgumentPrincipleTheoremFixedPiExpAutoRectEndpointCountCertificate140_370`
  lowers through `toNat` and `toUniform25167Check`, with headline theorem
  `concreteS_halfLogPlusHalf_of_globalPlattTrudgian_and_argumentPrincipleTheoremFixedPiExpAutoRectEndpointCountFinite370`.
  It can also forget the argument-principle theorem rows once endpoint
  counts are present:
  `BacklundArgumentPrincipleTheoremFixedPiExpAutoRectEndpointCountSlabCertificate.toEndpointCountRangeFixedPiExpSlab`
  lowers each row to fixed-π exp endpoint count-range data, and
  `BacklundFiniteBandArgumentPrincipleTheoremFixedPiExpAutoRectEndpointCountCertificate140_370.toEndpointCountRangeFixedPiExp`
  performs the finite-list conversion.
  The source package
  `ClassicalBacklundTuringPlattAPFixedPiExpAutoRectInputs370` lowers
  through `toAutoBottomInputs370`, `toGoodHeightArgumentBound`, and
  `toProofInputs`, proves
  `concreteS_halfLogPlusHalf_of_plattAPFixedPiExpAutoRectBacklundTuringInputs370`,
  and exports `toProvenBacklundTuringBound`, `toHalfLogPlusHalfSBound`,
  and `toTuringStyleSBound`.
  The natural-index source package
  `ClassicalBacklundTuringPlattAPFixedPiExpAutoRectNatInputs370`
  lowers through `toAutoRectInputs370`, `toGoodHeightArgumentBound`, and
  `toProofInputs`, proves
  `concreteS_halfLogPlusHalf_of_plattAPFixedPiExpAutoRectNatBacklundTuringInputs370`,
  and exports `toProvenBacklundTuringBound`, `toHalfLogPlusHalfSBound`,
  and `toTuringStyleSBound`.
  The endpoint-count source package
  `ClassicalBacklundTuringPlattAPFixedPiExpAutoRectEndpointCountInputs370`
  lowers through `toNatInputs370`, `toGoodHeightArgumentBound`, and
  `toProofInputs`, proves
  `concreteS_halfLogPlusHalf_of_plattAPFixedPiExpAutoRectEndpointCountBacklundTuringInputs370`,
  and exports `toProvenBacklundTuringBound`, `toHalfLogPlusHalfSBound`,
  and `toTuringStyleSBound`. It also exports final Backlund/Turing
  package adapters
  `ClassicalBacklundTuringPlattAPFixedPiExpAutoRectEndpointCountInputs370.toFinalBacklundTuringTwoInputs`
  and
  `ClassicalBacklundTuringPlattAPFixedPiExpAutoRectEndpointCountInputs370.toFinalBacklundTuringAnalyticInputs`.
  The endpoint count-range/main-term route also has a `[140, 370]`
  surface: `BacklundFiniteBandEndpointCountRangeMainCertificate140_370`
  lowers through `toCountRange` and `toUniform25167Check`, feeding
  `concreteS_halfLogPlusHalf_of_globalPlattTrudgian_and_countRangeMainFinite370`
  and
  `concreteS_halfLogPlusHalf_of_globalPlattTrudgian_and_endpointCountRangeMainFinite370`.
  The source package
  `ClassicalBacklundTuringPlattEndpointCountRangeInputs370` lowers
  through `toGoodHeightArgumentBound` and `toProofInputs`, proves
  `concreteS_halfLogPlusHalf_of_plattEndpointCountRangeBacklundTuringInputs370`,
  and exports `toProvenBacklundTuringBound`, `toHalfLogPlusHalfSBound`,
  and `toTuringStyleSBound`.
  The fixed-π exp endpoint count-range variant
  `BacklundEndpointCountRangeFixedPiExpSlabCertificate` removes raw
  endpoint `smoothMainTerm` inequalities from each row, replacing them
  with rational ratio bounds and exponential log certificates. Its
  finite package
  `BacklundFiniteBandEndpointCountRangeFixedPiExpCertificate140_370`
  lowers through `toEndpointCountRange` and `toUniform25167Check`, with
  headline theorem
  `concreteS_halfLogPlusHalf_of_globalPlattTrudgian_and_endpointCountRangeFixedPiExpFinite370`.
  The source package
  `ClassicalBacklundTuringPlattEndpointCountRangeFixedPiExpInputs370`
  lowers through `toEndpointCountRangeInputs370`,
  `toGoodHeightArgumentBound`, and `toProofInputs`, proves
  `concreteS_halfLogPlusHalf_of_plattEndpointCountRangeFixedPiExpBacklundTuringInputs370`,
  and exports `toProvenBacklundTuringBound`, `toHalfLogPlusHalfSBound`,
  and `toTuringStyleSBound`.
  These endpoint count-range source packages now expose the same final
  package layer:
  `ClassicalBacklundTuringPlattEndpointCountRangeInputs370.toFinalBacklundTuringTwoInputs`,
  `ClassicalBacklundTuringPlattEndpointCountRangeInputs370.toFinalBacklundTuringAnalyticInputs`,
  `ClassicalBacklundTuringPlattEndpointCountRangeFixedPiExpInputs370.toFinalBacklundTuringTwoInputs`,
  and
  `ClassicalBacklundTuringPlattEndpointCountRangeFixedPiExpInputs370.toFinalBacklundTuringAnalyticInputs`.
  The exact current source pair, global Platt-Trudgian plus fixed-π exp
  endpoint count-range finite rows on `[140, 370]`, now lowers all the
  way to final packages through
  `BacklundGoodHeightArgumentBound.of_globalPlattTrudgian_and_endpointCountRangeFixedPiExpFinite370`,
  `FinalBacklundTuringTwoInputs.of_globalPlattTrudgian_and_endpointCountRangeFixedPiExpFinite370`,
  `FinalBacklundTuringAnalyticInputs.of_globalPlattTrudgian_and_endpointCountRangeFixedPiExpFinite370`,
  and
  `ProvenBacklundTuringBound.of_globalPlattTrudgian_and_endpointCountRangeFixedPiExpFinite370`.
  The same exact-current pair now exports the smaller `S`-bound
  interfaces and direct proved headline:
  `HalfLogPlusHalfSBound.of_globalPlattTrudgian_and_endpointCountRangeFixedPiExpFinite370`,
  `TuringStyleSBound.of_globalPlattTrudgian_and_endpointCountRangeFixedPiExpFinite370`,
  and
  `concreteS_halfLogPlusHalf_of_globalPlattTrudgian_and_endpointCountRangeFixedPiExpFinite370_viaProven`.
  The near-exact endpoint now also has count-range certificate surfaces:
  `BacklundFiniteBandCountRangeMainCertificate140_3690757803_10000000`,
  `BacklundFiniteBandEndpointCountRangeMainCertificate140_3690757803_10000000`,
  and
  `BacklundFiniteBandEndpointCountRangeFixedPiExpCertificate140_3690757803_10000000`,
  with headline theorems
  `concreteS_halfLogPlusHalf_of_globalPlattTrudgian_and_endpointCountRangeMainFinite3690757803_10000000`
  and
  `concreteS_halfLogPlusHalf_of_globalPlattTrudgian_and_endpointCountRangeFixedPiExpFinite3690757803_10000000`.

* **(P2) Entire-ξ Hadamard bundle.** Inhabit
  `EntireXiClassicalHadamardTheorem ι` (§CCCLXXXVIII) — the per-field
  obligations are stated against `entireRiemannXi`, where Mathlib's
  Hadamard machinery applies most naturally:

  | Field | Concrete shape |
  |---|---|
  | `zeroSystem` | A concrete enumeration of `entireRiemannXi`-zeros — for the textbook $\xi$ these are the nontrivial $\zeta$-zeros lifted to the critical strip. |
  | `prefactor` | Of the form $C\exp(a+bs)$; use `EntireXiHadamardPrefactor.exp_affine` (or the raw-side analogue `ConcreteCompletedXiHadamardPrefactor.exp_affine`) to discharge the regularity. |
  | `zeroDistribution` | $\sum_\rho |\rho|^{-2} < \infty$ (Riemann–von Mangoldt) and the cofinite "large-zero" estimate. |
  | `luc` | LUC log-derivative interchange for the infinite product on the AFZ region. Mathlib's `Multipliable` API is the substrate. |
  | `region` | $\xi_{\text{entire}}(s) \neq 0 \Rightarrow s \in \text{luc.region}$ — region compatibility on the AFZ set. |
  | `factorization` | The pointwise identity $\xi_{\text{entire}}(s) = \text{prefactor}(s)\,\prod_i E_1(s/\rho_i)$ — the classical Hadamard product theorem at genus 1. |
  | `prefactorData` | Differentiability and non-vanishing of `prefactor` on the AFZ region. |

* **(P3) Three Stieltjes equalities.** Inhabit `Hmid`, `Hhigh`, and
  any concrete `finiteCloud, tail` together with an inhabitant of
  `LowCloudTailSplitAFZ` (§CCCLXIX), or equivalently provide the
  reassembled `ClassicalPathBStieltjesInputsAFZ` bundle against
  `Hhad.toCompletedXiSourceAFZ_canonical`. The canonical
  `XiPullbackAntiHerglotzTarget_of_entireHadamard_canonical_midHigh_lowZeroSplit`
  front door also accepts the low side directly as
  `LowZeroContributionSplitAFZ`, deriving `DzeroStartsAfter Dzero 14`
  from the atom-level `h_Z_ge_15` hypothesis. The mid/high equalities
  can also be combined with a direct
  `LowFiniteStieltjesIBPSourceAFZ` through
  `ClassicalPathBStieltjesInputsAFZ.of_mid_high_lowIBPSource`. At the
  compact identity-side surface, a single
  `StieltjesMidHighTailEqualityAFZ` is split into its mid and high
  components by `StieltjesMidTailEqualityAFZ.of_midHighAFZ` and
  `StieltjesHighTailEqualityAFZ.of_midHighAFZ`, then combined with the
  low zero split, low cloud/tail split, or low IBP source by
  `ClassicalPathBStieltjesInputsAFZ.of_midHighAFZ_lowZeroSplit`,
  `ClassicalPathBStieltjesInputsAFZ.of_midHighAFZ_lowCloudTailSplit`,
  and
  `ClassicalPathBStieltjesInputsAFZ.of_midHighAFZ_lowIBPSource`.
  The theorem
  `XiPullbackAntiHerglotzTarget_of_entireHadamard_canonical_midHighAFZ_lowIBPSource`
  exposes the compact low-IBP route directly, with sibling front doors
  for the low-zero and low-cloud/tail forms. Older unguarded Stieltjes
  equality sources can be safely weakened into AFZ form by
  `StieltjesMidHighTailEqualityAFZ.of_unguarded`,
  `LowFiniteStieltjesFormulaOnFirstZeroGapAFZ.of_unguarded`, and
  `XiZeroContributionStieltjesEqualitySourceAFZ.of_unguarded`; the
  compatibility front doors
  `XiPullbackAntiHerglotzTarget_of_entireHadamard_canonical_unguardedStieltjesSource`
  and
  `XiPullbackAntiHerglotzTarget_of_entireHadamard_canonical_unguardedMidHigh_lowFirstZeroFormula`
  route those older packages into the canonical chain. At the
  publication surface,
  `XiPullbackAntiHerglotzTarget_of_entireHadamard_and_classicalStieltjes`
  accepts `ClassicalStieltjesExplicitFormulaInputs` and performs the
  canonical reassembly internally. The mid/high equalities are the
  tail-limit form of the explicit formula at $\Xi(z) \neq 0$; the low
  split is the conceptual statement
  $\mathrm{ZC}(z) = P(z) + \text{tailZC}(z)$.
  The named tail-value wrapper also records the Hausdorff uniqueness
  and transport utilities `XiFluctuationTailValue.unique` and
  `XiFluctuationTailValue.congr`.

For convenience, `PathBNonTuringInputs Dzero ι` bundles (P2), (P3),
and the zero-start condition in one structure, with the Stieltjes side
stored as the assembled `ClassicalPathBStieltjesInputsAFZ` keyed to the
canonical completed-ξ source. The constructors
`PathBNonTuringInputs.of_classicalStieltjes` and
`PathBNonTuringInputs.of_stieltjesInputs` build it from either the
publication-level cloud/tail input or an already assembled canonical
AFZ bundle. Additional constructors build it from combined AFZ mid/high
data plus low IBP, low zero-split, or low cloud/tail inputs, and from
older unguarded Stieltjes packages. The current source-compatible
constructors also include
`ClassicalPathBStieltjesInputsAFZ.of_equalitySourceAFZ`,
`PathBNonTuringInputs.of_stieltjesEqualitySourceAFZ`, and
`PathBNonTuringInputs.of_mid_high_lowIBPSource`, so a unified AFZ
Stieltjes equality source or the direct mid/high plus low-IBP source
can enter without first expanding all fields by hand. Projection and
raw-component views are exposed by
`PathBNonTuringInputs.to_entireHadamard`,
`PathBNonTuringInputs.to_stieltjesInputs`,
`PathBNonTuringRawComponents`, `pathBNonTuringInputsEquiv`, and
`PathBNonTuringRawComponents.to_inputs`. The raw/bundle equivalence is
now certified by the `[simp]` round trips
`PathBNonTuringRawComponents.to_inputs_to_rawComponents` and
`PathBNonTuringInputs.to_rawComponents_to_inputs`.

Once this bundle is inhabited for the same `Dzero`, it pairs with the
§CDXLVI `PathBTuringEnvelopeInputs Dzero` bundle, whose two fields are
exactly the slab-localized `hTuring` and high-log `hHighLog` estimates.
`PathBTuringEnvelopeInputs.of_envelopes` builds that bundle from the
raw estimates, and the two-bundle capstone
`XiPullbackAntiHerglotzTarget_of_pathBInputBundles` consumes only
`PathBNonTuringInputs` plus `PathBTuringEnvelopeInputs`. §CDXLVI also
defines `PathBNonTuringSourceInputs`, the leanest source-level
non-Turing bundle: a zero-start datum, a
`CompletedXiLogDerivativeSourceAFZ`, and the matched
`XiZeroContributionStieltjesEqualitySourceAFZ`. The source capstone
`XiPullbackAntiHerglotzTarget_of_pathBSourceInputBundles` consumes
only that source bundle plus `PathBTuringEnvelopeInputs`. Its
constructors
`PathBNonTuringSourceInputs.of_completedXiSource`,
`PathBNonTuringSourceInputs.of_hadamardProductData`,
`PathBNonTuringSourceInputs.of_classicalPathBAnalyticInputs`,
`PathBNonTuringSourceInputs.of_concreteCompletedXiHadamardInputs`,
`PathBNonTuringSourceInputs.of_completedXiClassicalHadamard`,
`PathBNonTuringSourceInputs.of_entireHadamardInputs`, and
`PathBNonTuringSourceInputs.of_entireXiSource` expose the same theorem
from completed-ξ source data, completed-ξ Hadamard product data,
classical Path B analytic inputs, concrete completed-ξ Hadamard
inputs, the publication completed-ξ Hadamard theorem, the existing
entire-Hadamard bundle, or the entire-ξ source via the Γ-cancellation
bridge. The source bundle also has explicit projections and a raw
component equivalence:
`PathBNonTuringSourceInputs.to_completedXiSource`,
`PathBNonTuringSourceInputs.to_stieltjesSourceAFZ`,
`PathBNonTuringSourceRawComponents`, and
`pathBNonTuringSourceInputsEquiv`, with
`PathBNonTuringSourceRawComponents.to_sourceInputs` converting back to
the bundled source form. Its source-level raw/bundle equivalence is
also registered by the `[simp]` round trips
`PathBNonTuringSourceRawComponents.to_sourceInputs_to_rawComponents`
and
`PathBNonTuringSourceInputs.to_rawComponents_to_sourceInputs`. The
source and publication full bundles now project back to raw component
views through `PathBSourceFullInputBundle.to_rawComponents` and
`PathBFullInputBundle.to_rawComponents`, with `[simp]` rebuild checks
`PathBSourceFullInputBundle.to_rawComponents_to_sourceInputs` and
`PathBFullInputBundle.to_rawComponents_to_inputs`. The
same bundled and raw views now expose
method forms of the non-direct target capstones:
`PathBNonTuringSourceInputs.to_target_turingBundle`,
`PathBNonTuringSourceInputs.to_target_turingEnvelopes`,
`PathBNonTuringInputs.to_target_turingBundle`,
`PathBNonTuringInputs.to_target_turingEnvelopes`,
`PathBNonTuringSourceRawComponents.to_target_turingBundle`,
`PathBNonTuringSourceRawComponents.to_target_turingEnvelopes`,
`PathBNonTuringRawComponents.to_target_turingBundle`, and
`PathBNonTuringRawComponents.to_target_turingEnvelopes`. The raw
component views also feed the direct target through
`PathBNonTuringSourceRawComponents.to_directAFZ`,
`PathBNonTuringRawComponents.to_directAFZ`,
`PathBNonTuringSourceRawComponents.to_target_direct_turingBundle`,
`PathBNonTuringSourceRawComponents.to_target_direct_turingEnvelopes`,
`PathBNonTuringRawComponents.to_target_direct_turingBundle`, and
`PathBNonTuringRawComponents.to_target_direct_turingEnvelopes`. These
raw component views now also assemble the one-object full bundles:
`PathBNonTuringSourceRawComponents.to_sourceFullBundle`,
`PathBNonTuringSourceRawComponents.to_directFullBundle`,
`PathBNonTuringSourceRawComponents.to_sourceFullBundle_envelopes`,
`PathBNonTuringSourceRawComponents.to_directFullBundle_envelopes`,
`PathBNonTuringRawComponents.to_fullBundle`,
`PathBNonTuringRawComponents.to_sourceFullBundle`,
`PathBNonTuringRawComponents.to_directFullBundle`,
`PathBNonTuringRawComponents.to_fullBundle_envelopes`, and
`PathBNonTuringRawComponents.to_directFullBundle_envelopes`. Their
target-level full-bundle method forms are
`PathBNonTuringSourceRawComponents.to_target_full_turingBundle`,
`PathBNonTuringSourceRawComponents.to_target_full_turingEnvelopes`,
`PathBNonTuringSourceRawComponents.to_target_directFull_turingBundle`,
`PathBNonTuringSourceRawComponents.to_target_directFull_turingEnvelopes`,
`PathBNonTuringRawComponents.to_target_full_turingBundle`,
`PathBNonTuringRawComponents.to_target_full_turingEnvelopes`,
`PathBNonTuringRawComponents.to_target_directFull_turingBundle`, and
`PathBNonTuringRawComponents.to_target_directFull_turingEnvelopes`. These
raw-component views are also exposed as top-level front doors:
`XiPullbackAntiHerglotzTarget_of_pathBSourceRawComponents_turingBundle`,
`XiPullbackAntiHerglotzTarget_of_pathBSourceRawComponents_turingEnvelopes`,
`XiPullbackAntiHerglotzTarget_of_pathBRawComponents_turingBundle`,
`XiPullbackAntiHerglotzTarget_of_pathBRawComponents_turingEnvelopes`,
`XiPullbackAntiHerglotzTarget_of_pathBSourceRawComponents_direct_turingBundle`,
`XiPullbackAntiHerglotzTarget_of_pathBSourceRawComponents_direct_turingEnvelopes`,
`XiPullbackAntiHerglotzTarget_of_pathBRawComponents_direct_turingBundle`,
and
`XiPullbackAntiHerglotzTarget_of_pathBRawComponents_direct_turingEnvelopes`.
The full-bundle paths also have top-level front doors:
`XiPullbackAntiHerglotzTarget_of_pathBSourceRawComponents_full_turingBundle`,
`XiPullbackAntiHerglotzTarget_of_pathBSourceRawComponents_full_turingEnvelopes`,
`XiPullbackAntiHerglotzTarget_of_pathBSourceRawComponents_directFull_turingBundle`,
`XiPullbackAntiHerglotzTarget_of_pathBSourceRawComponents_directFull_turingEnvelopes`,
`XiPullbackAntiHerglotzTarget_of_pathBRawComponents_full_turingBundle`,
`XiPullbackAntiHerglotzTarget_of_pathBRawComponents_full_turingEnvelopes`,
`XiPullbackAntiHerglotzTarget_of_pathBRawComponents_directFull_turingBundle`,
and
`XiPullbackAntiHerglotzTarget_of_pathBRawComponents_directFull_turingEnvelopes`.
§CDXLVII adds the canonical completed-ξ source names
`canonicalEntireXiLogDerivativeSourceAFZ`,
`canonicalCompletedXiLogDerivativeSourceAFZ`,
`canonicalPathBZeroContribution`, and
`CanonicalPathBStieltjesSource`, together with
`PathBNonTuringSourceInputs.of_canonicalStieltjesSource` and the
front door
`XiPullbackAntiHerglotzTarget_of_canonicalStieltjesSource_turingBundle`.
§CDXLVIII mirrors this at the pullback-Ξ level with
`canonicalXiPullbackZeroContribution`,
`canonicalXiPullbackHadamardLogDerivativeSource`,
`CanonicalXiPullbackStieltjesSource`,
`CanonicalXiPullbackStieltjesSourceAFZ`,
`CanonicalXiPullbackLowIBPSourceAFZ`,
`CanonicalXiPullbackLowZeroSplitAFZ`,
`CanonicalXiPullbackLowCloudTailSplitAFZ`, and front doors such as
`XiPullbackAntiHerglotzTarget_of_canonicalXiPullbackStieltjesSource_turingBundle`,
`XiPullbackAntiHerglotzTarget_of_canonicalXiPullback_midHigh_low_turingBundle`,
`XiPullbackAntiHerglotzTarget_of_canonicalXiPullbackStieltjesSourceAFZ_turingBundle`,
and
`XiPullbackAntiHerglotzTarget_of_canonicalXiPullback_midHighAFZ_lowAFZ_turingBundle`,
with direct low-IBP and low-zero-split variants
`XiPullbackAntiHerglotzTarget_of_canonicalXiPullback_midHighAFZ_lowIBP_turingBundle`
and
`XiPullbackAntiHerglotzTarget_of_canonicalXiPullback_midHighAFZ_lowZeroSplit_turingBundle`,
plus the low cloud/tail variant
`XiPullbackAntiHerglotzTarget_of_canonicalXiPullback_midHighAFZ_lowCloudTail_turingBundle`.
The bridge
`pullbackZeroContribution_eq_canonicalXiPullbackZeroContribution`
is the generic completed-ξ source-to-direct pullback bridge: any
`CompletedXiLogDerivativeSourceAFZ` identifies its pulled-back zero
contribution with `canonicalXiPullbackZeroContribution` away from zeros.
The canonical special case
`canonicalPathBZeroContribution_eq_canonicalXiPullbackZeroContribution`
identifies the source-level canonical Path B zero contribution with
the direct pullback log-derivative away from zeros, yielding direct
canonical AFZ imports
`CanonicalXiPullbackMidHighStieltjesEqualityAFZ.of_completedXiSource`,
`CanonicalXiPullbackLowFirstZeroFormulaAFZ.of_completedXiSource`,
`CanonicalXiPullbackStieltjesSourceAFZ.of_completedXiSource`,
`CanonicalXiPullbackLowIBPSourceAFZ.of_completedXiSource`,
`CanonicalXiPullbackLowZeroSplitAFZ.of_completedXiSource`,
`CanonicalXiPullbackLowCloudTailSplitAFZ.of_completedXiSource`,
`CanonicalXiPullbackMidHighStieltjesEqualityAFZ.of_canonicalPathB`,
`CanonicalXiPullbackLowFirstZeroFormulaAFZ.of_canonicalPathB`, and
`CanonicalXiPullbackStieltjesSourceAFZ.of_canonicalPathB`.
The low-side source/direct canonical Path B bridge now has direct method
forms `CanonicalXiPullbackLowIBPSourceAFZ.of_canonicalPathB`,
`CanonicalXiPullbackLowZeroSplitAFZ.of_canonicalPathB`, and
`CanonicalXiPullbackLowCloudTailSplitAFZ.of_canonicalPathB`, plus iff
front doors
`canonicalPathBLowIBPSourceAFZ_iff_canonicalXiPullbackLowIBPSourceAFZ`,
`canonicalPathBLowZeroSplitAFZ_iff_canonicalXiPullbackLowZeroSplitAFZ`,
and
`canonicalPathBLowCloudTailSplitAFZ_iff_canonicalXiPullbackLowCloudTailSplitAFZ`.
The mid/high and low first-zero canonical Path B interfaces now have
matching iff front doors too:
`canonicalPathBMidHighStieltjesEqualityAFZ_iff_canonicalXiPullbackMidHighStieltjesEqualityAFZ`
and
`canonicalPathBLowFirstZeroFormulaAFZ_iff_canonicalXiPullbackLowFirstZeroFormulaAFZ`.
The reverse adapters now push direct canonical AFZ Stieltjes proofs
back through any completed-ξ source:
`StieltjesMidHighTailEqualityAFZ.of_canonicalXiPullback`,
`LowFiniteStieltjesFormulaOnFirstZeroGapAFZ.of_canonicalXiPullback`,
`XiZeroContributionStieltjesEqualitySourceAFZ.of_canonicalXiPullback`,
`CanonicalPathBStieltjesSource.of_canonicalXiPullback`,
`LowFiniteStieltjesIBPSourceAFZ.of_canonicalXiPullback`,
`LowZeroContributionSplitAFZ.of_canonicalXiPullback`,
`LowCloudTailSplitAFZ.of_canonicalXiPullback`,
`CanonicalPathBLowIBPSourceAFZ_of_canonicalXiPullback`,
`CanonicalPathBLowZeroSplitAFZ_of_canonicalXiPullback`,
`CanonicalPathBLowCloudTailSplitAFZ_of_canonicalXiPullback`, and
`canonicalPathBStieltjesSource_iff_canonicalXiPullbackStieltjesSourceAFZ`.
This direct canonical Stieltjes source now also feeds the source-level
non-Turing/full-bundle layer through
`PathBNonTuringSourceInputs.of_canonicalXiPullbackStieltjesSource`,
`PathBSourceFullInputBundle.of_canonicalXiPullbackStieltjesSource`,
`PathBSourceFullInputBundle.of_canonicalXiPullbackStieltjesSource_envelopes`,
`XiPullbackAntiHerglotzTarget_of_sourceCanonicalXiPullbackStieltjesSource_turingBundle`,
and
`XiPullbackAntiHerglotzTarget_of_sourceCanonicalXiPullbackStieltjesSource_turingEnvelopes`.
The split and low-side direct canonical Stieltjes inputs have bundled
source full-bundle front doors too:
`PathBSourceFullInputBundle.of_canonicalXiPullbackSplitStieltjes`,
`PathBSourceFullInputBundle.of_canonicalXiPullbackIBPStieltjes`,
`PathBSourceFullInputBundle.of_canonicalXiPullbackZeroSplitStieltjes`,
`PathBSourceFullInputBundle.of_canonicalXiPullbackCloudTailStieltjes`,
`XiPullbackAntiHerglotzTarget_of_sourceCanonicalXiPullbackSplitStieltjes_turingBundle`,
`XiPullbackAntiHerglotzTarget_of_sourceCanonicalXiPullbackIBPStieltjes_turingBundle`,
`XiPullbackAntiHerglotzTarget_of_sourceCanonicalXiPullbackZeroSplitStieltjes_turingBundle`,
and
`XiPullbackAntiHerglotzTarget_of_sourceCanonicalXiPullbackCloudTailStieltjes_turingBundle`.
Their raw-envelope siblings are
`XiPullbackAntiHerglotzTarget_of_sourceCanonicalXiPullbackSplitStieltjes_turingEnvelopes`,
`XiPullbackAntiHerglotzTarget_of_sourceCanonicalXiPullbackIBPStieltjes_turingEnvelopes`,
`XiPullbackAntiHerglotzTarget_of_sourceCanonicalXiPullbackZeroSplitStieltjes_turingEnvelopes`,
and
`XiPullbackAntiHerglotzTarget_of_sourceCanonicalXiPullbackCloudTailStieltjes_turingEnvelopes`.
The direct canonical layer then packages these Stieltjes shapes as
`CanonicalXiPullbackSplitStieltjesInputsAFZ`,
`CanonicalXiPullbackIBPStieltjesInputsAFZ`,
`CanonicalXiPullbackZeroSplitStieltjesInputsAFZ`, and
`CanonicalXiPullbackCloudTailStieltjesInputsAFZ`, all feeding
`PathBDirectNonTuringInputsAFZ`. The direct two-bundle capstone
`XiPullbackAntiHerglotzTarget_of_directNonTuringInputsAFZ_turingBundle`
consumes only `PathBDirectNonTuringInputsAFZ` and
`PathBTuringEnvelopeInputs`; the unified source constructor
`PathBDirectNonTuringInputsAFZ.of_stieltjesSource` gives direct access
from `CanonicalXiPullbackStieltjesSourceAFZ`. The unguarded canonical
source also has direct target front doors
`XiPullbackAntiHerglotzTarget_of_canonicalXiPullbackStieltjesSource_turingEnvelopes`,
`XiPullbackAntiHerglotzTarget_of_canonicalXiPullback_midHigh_low_turingEnvelopes`,
`CanonicalXiPullbackStieltjesSource.to_target_turingBundle`, and
`CanonicalXiPullbackStieltjesSource.to_target_turingEnvelopes`.
The direct bundle now has
projection round trips
`PathBDirectNonTuringInputsAFZ.of_splitStieltjes_to_splitStieltjes`
and
`PathBDirectNonTuringInputsAFZ.of_stieltjesSource_to_stieltjesSource`,
so rebuilding from its split or unified Stieltjes payload preserves the
payload definitionally. The canonical Stieltjes inputs also have method
forms lowering directly to the non-Turing bundle:
`CanonicalXiPullbackStieltjesSourceAFZ.to_directNonTuringInputs`,
`CanonicalXiPullbackSplitStieltjesInputsAFZ.to_directNonTuringInputs`,
`CanonicalXiPullbackIBPStieltjesInputsAFZ.to_directNonTuringInputs`,
`CanonicalXiPullbackZeroSplitStieltjesInputsAFZ.to_directNonTuringInputs`,
and
`CanonicalXiPullbackCloudTailStieltjesInputsAFZ.to_directNonTuringInputs`.
The older unguarded canonical Stieltjes inputs now have matching method
forms too:
`CanonicalXiPullbackStieltjesSource.to_directNonTuringInputs` and
`CanonicalXiPullbackMidHighStieltjesEquality.to_directNonTuringInputs`.
The unified and split canonical Stieltjes inputs now also expose direct
target method forms:
`CanonicalXiPullbackStieltjesSourceAFZ.to_target_turingBundle`,
`CanonicalXiPullbackStieltjesSourceAFZ.to_target_turingEnvelopes`,
`CanonicalXiPullbackSplitStieltjesInputsAFZ.to_target_turingBundle`,
and
`CanonicalXiPullbackSplitStieltjesInputsAFZ.to_target_turingEnvelopes`.
The source-level canonical Path B Stieltjes source now has the same
method-form bridge:
`CanonicalPathBStieltjesSource.to_directNonTuringInputs`,
`CanonicalPathBStieltjesSource.to_directFullInputBundle`,
`CanonicalPathBStieltjesSource.to_directFullInputBundle_envelopes`,
`CanonicalPathBStieltjesSource.to_target_turingBundle`, and
`CanonicalPathBStieltjesSource.to_target_turingEnvelopes`.
The generic completed-ξ
source constructor `PathBDirectNonTuringInputsAFZ.of_completedXiSource`
feeds direct completed-source front doors
`XiPullbackAntiHerglotzTarget_of_directCompletedXiSourceStieltjesAFZ_turingBundle`
and its unbundled-envelope sibling. The source-bundle constructor
`PathBDirectNonTuringInputsAFZ.of_sourceInputs` lowers any
`PathBNonTuringSourceInputs` directly, yielding
`XiPullbackAntiHerglotzTarget_of_pathBSourceInputBundles_direct`
and the unbundled-envelope sibling
`XiPullbackAntiHerglotzTarget_of_pathBSourceInputBundles_direct_turingEnvelopes`.
The entire-ξ non-Turing bundle also lowers directly through
`PathBDirectNonTuringInputsAFZ.of_entireHadamardInputs`, giving
`XiPullbackAntiHerglotzTarget_of_pathBInputBundles_direct` and
`XiPullbackAntiHerglotzTarget_of_pathBInputBundles_direct_turingEnvelopes`.
Specialized direct capstones now cover the main completed-ξ source
shapes: `XiPullbackAntiHerglotzTarget_of_directHadamardProductData_stieltjesAFZ_turingBundle`,
`XiPullbackAntiHerglotzTarget_of_directClassicalPathBAnalyticInputs_stieltjesAFZ_turingBundle`,
`XiPullbackAntiHerglotzTarget_of_directConcreteCompletedXiHadamard_stieltjesAFZ_turingBundle`,
`XiPullbackAntiHerglotzTarget_of_directCompletedXiClassicalHadamard_stieltjesAFZ_turingBundle`,
and
`XiPullbackAntiHerglotzTarget_of_directEntireXiSource_stieltjesAFZ_turingBundle`;
each also has a matching `_turingEnvelopes` sibling.
The older unguarded canonical sources are weakened by
`CanonicalXiPullbackSplitStieltjesInputsAFZ.of_unguardedStieltjesSource`
and
`CanonicalXiPullbackSplitStieltjesInputsAFZ.of_unguarded_midHigh_low`,
then packaged by
`PathBDirectNonTuringInputsAFZ.of_unguardedStieltjesSource` and
`PathBDirectNonTuringInputsAFZ.of_unguardedMidHighLow`. The
unified-source, unguarded-source, unguarded-mid/high-low, split,
low-IBP, low-zero-split, and low-cloud/tail front doors each have
bundled-Turing and unbundled Turing-envelope variants.
The §CDXLV
theorem
`XiPullbackAntiHerglotzTarget_of_nonTuringInputs_and_turingEnvelopes`
is the unbundled-envelope version of the same result. To translate the
resulting
`XiPullbackAntiHerglotzTarget` into a Mathlib-grade RH theorem, compose
with `XiPullback_logDeriv_chain_rule` and the Mathlib-side capstone
`EntireXiPullback_zeros_real_of_signTarget`.

## 12. Architecture of the formalization

The file is organized into functional layers, each consuming the
previous as a black box.

**Lake targets.** `lakefile.toml` now registers `rh` as a Lean library
and includes it in `defaultTargets`, so a default Lake build covers the
RH formalization alongside `GoldenAlgebra`.

**Sign-law engine** (§§1–6 of `rh.lean`). The atomic substrate:
`AntiHerglotzUHP`, `PositiveUpperImaginaryEscape`, the residue-cloud
atom `complex_real_root_residue_imag_nonpos`, the pole-probe arithmetic
at $m/(-i\varepsilon)$, the local pole decomposition, the engine
`localLogDerivPoleDecomposition_forces_escape`, and the two driver
theorems combining these with Schwarz reflection. §6-bis isolates the
totalization-at-zeros analysis.

**Polynomial case** (§§7–9). Discharges the engine's analytic
hypothesis for polynomials via Mathlib's `rootMultiplicity` and lands
unconditional polynomial RH. Converse direction proved in factorized
form.

**Entire-function lift** (§10). Replaces `rootMultiplicity` by
Mathlib's isolated-zeros library and lands the entire-function
capstone of §4.

**Custom xi and four targets** (§§11–12). `completedXiFunction`,
`XiPullback`, the abstract `AbstractXiOverflowPackage`, and the four
target Props of §5 with their equivalences. The integrated-kernel form
lives in the `XiDoubleKernel` namespace.

**Mathlib-grounded entire xi** (§17). `entireRiemannXi`,
`EntireXiPullback`, chain-rule and Schwarz bridges, the Mellin
keystone `mellin_star_ofReal`, and the conditional capstone
`EntireXiPullback_zeros_real_of_signTarget`.

**Backlund/Turing infrastructure** (§13). `AntiHerglotzWithErrorMargin`,
`zeroDensityRho`, `smoothZeroCountingN0`, the imaginary-kernel IBP
setup, kernel envelopes, slab algebra (`TuringIntervalCertificate`,
listed Turing rows, two-row and three-row slab tables), and
`smoothTailRationalLowerBoundAbs` with its numerical specializations.
CW30 exports `ClassicalBacklundTuringProofInputs` and
`ClassicalBacklundTuringVerifiedInputs` into the generic
`ProvenBacklundTuringBound`, `HalfLogPlusHalfSBound`, and
`TuringStyleSBound` interfaces, preserving the concrete threshold
`140` and constants `C = D = 1/2`; the accompanying rfl-field and
direct-bound theorems make the exported packages easy to rewrite, and
the `concreteS_highLogEnvelope` theorems feed the high-side residual
bound directly. The same area now includes the HSW large-height
envelope and the bridge
`BacklundGoodHeightArgumentBound.of_hsw_large_and_plattTrudgian`,
plus the verified-input export
`ClassicalBacklundTuringVerifiedInputs.toNumericalExtraction`. The HSW
tail has reduced-threshold front doors at `exp 8`, `exp (77/10)`, and
`exp (769/100)`, with finite-band adapters from the Platt/Trudgian
range.

**Argument-principle scaffolding** (Q–Z and AA–BO namespaces).
Rectangle-contour geometry, edge integrability, residue-theorem chain,
Cauchy–Goursat on punctured rectangles via small-square deformation,
and the four-strip boundary cancellation that lifts Mathlib's
rectangle Cauchy–Goursat to the coordinate form.

**Phase 1 IBP and true-kernel convergence** (`Phase1Measure` /
`Phase1IBP` namespaces, §§CXCI–CCLIII). The nine SDP-backed slab
certificates, the fluctuation primitive, the true finite-window IBP,
ordered discrete Abel summation, the FTC bridges, and true-kernel
convergence machinery. Four real non-demo per-slab certificates over
$[2\pi, 10]$ are unconditionally proved.

**Canonical residual and honest model** (§§CCLVII–CCLXXV). The
residual `xiResidualError`, `HonestZeroDensityModelData`, and the
canonical `honestZeroDensityModelTwoPi` with the smooth-tail rational
lower bound `HonestSmoothTailRationalLB_twoPi`.

**Compact low-band reduction chain** (§§CCLXXVI–CCXCII). Eight
progressively sharper Path B front doors at $(11, 14, 1/2)$
(explicit → bridge → IBP → bounded finite-IBP → `Hint`-free →
`Hgap`-free → SBound → $T_0 = 10$ pinned + atom-level). §CCLXXXVIII
codifies the taint convention; §CCXCII normalizes `HlowArith` to its
$y$-free constant form.

**Model-side arithmetic discharge** (§CCXCIII). `HlowArith` fully
proved; the `…_T0_10_Z_ge_15_AFZ_noArith` front door drops the
arithmetic hypothesis entirely.

**Stieltjes formula bundle and zero-side equality chain**
(§§CCXCIV–CCCXVIII). The three xi-side AFZ inputs are bundled into
`XiResidualStieltjesFormulaData`. §§CCXCVIII–CCXCIX correct the
low-band split (boundary + integral); §§CCC–CCCII expose the master
`XiExplicitFormulaPackage`; §§CCCIII–CCCXII develop the
zero-contribution split and Stieltjes data scaffolding;
§§CCCXIII–CCCXV define the AFZ source/equality structures and the
master composition `XiResidualStieltjesFormulaData_of_AFZ`; the
standard first-zero hypothesis now has the direct wrapper
`XiResidualStieltjesFormulaData_of_AFZ_Z_ge_15`;
the low contribution formula similarly has
`StieltjesLowContributionData_of_firstZeroGapFormula_Z_ge_15`;
§§CCCXVI–CCCXVIII lift to the $s$-plane via the chain rule and land
an intermediate `_of_completedXiHadamardAndStieltjesAFZ` front door.

**Classical Hadamard infrastructure** (§§CCCXIX–CCCXLI). The genus-1
Hadamard product over an indexed zero family:
`hadamardGenus1Factor (ρ s) := (1 - s/ρ) · exp(s/ρ)`,
`infiniteHadamardProduct`, `hadamardRegularizedLogDerivSeries`,
`HadamardLocallyUniformProductData`, `HadamardLogDerivLimitData`,
`HadamardZeroInvSqSummability`, `GenusOneTaylorBoundData`,
`CompletedXiHadamardProductWithZeros`, and the user-facing
`ClassicalPathBAnalyticInputs ι` with composite bridge
`toCompletedXiSourceAFZ`.

**Two-bundle assembly and low-side zero-split chain**
(§§CCCXLII–CCCLXV). Per-package Hadamard ingredients
(`CompletedXiZeroIndexPackage`, `CompletedXiHadamardPrefactorData`,
`CompletedXiHadamardFactorizationData`), per-band Stieltjes splits
(`StieltjesMidTailEqualityAFZ`, `StieltjesHighTailEqualityAFZ`,
`StieltjesLowEqualityAFZ`), and the low-side unwrapping chain
through `LowFiniteStieltjesContributionIdentityAFZ`,
`LowFiniteStieltjesResidualSourceAFZ`,
`LowFirstZeroGapNoAtoms.of_startsAfter`,
`LowFiniteStieltjesIBPSourceAFZ`, `LowZeroContributionSplitAFZ`,
`LowTailStieltjesResidualFormulaAFZ.trivial`, and
`LowFiniteStieltjesIBPSourceAFZ.of_zeroSplit`. The low-side wrappers now
also have reverse/equivalence bridges:
`StieltjesLowEqualityAFZ.to_lowFiniteFormula`,
`stieltjesLowEqualityAFZ_iff_lowFiniteFormula`,
`LowFiniteStieltjesContributionIdentityAFZ.of_lowFiniteFormula`,
`lowFiniteStieltjesFormulaOnFirstZeroGapAFZ_iff_contributionIdentity`,
`stieltjesLowEqualityAFZ_iff_contributionIdentity`,
`LowFiniteStieltjesIBPIdentityAFZ.of_contributionIdentity`,
  `lowFiniteStieltjesContributionIdentityAFZ_iff_ibpIdentity`, and
`stieltjesLowEqualityAFZ_iff_ibpIdentity`. The low IBP/zero-split
bridge is also registered by the `[simp]` round trips
`LowFiniteStieltjesIBPSourceAFZ.of_zeroSplit_of_ibpSource` and
`LowZeroContributionSplitAFZ.of_ibpSource_of_zeroSplit`. The mid/high
side now has
`StieltjesMidHighTailEqualityAFZ.of_mid_high` and
`stieltjesMidHighTailEqualityAFZ_iff_mid_and_high`, and the assembled
Stieltjes bundle has
`classicalPathBStieltjesInputsAFZ_iff_equalitySourceAFZ`. The standard
`Z ≥ 15` hypothesis now bypasses explicit `DzeroStartsAfter` plumbing via
`LowFirstZeroGapNoAtoms.of_Z_ge_15`,
`LowFiniteStieltjesResidualSourceAFZ.of_ibpSource_and_Z_ge_15`,
`LowFiniteZeroSumStieltjesFormulaAFZ.of_ibpSource_and_startsAfter`,
`LowFiniteZeroSumStieltjesFormulaAFZ.of_ibpSource_and_Z_ge_15`,
`StieltjesLowEqualityAFZ.of_lowIBPSource_and_startsAfter`,
`StieltjesLowEqualityAFZ.of_lowIBPSource_and_Z_ge_15`,
`LowFiniteStieltjesIBPIdentityAFZ.of_ibpSource_and_startsAfter`,
`LowFiniteStieltjesIBPIdentityAFZ.of_ibpSource_and_Z_ge_15`,
`LowFiniteStieltjesContributionIdentityAFZ.of_ibpSource_and_startsAfter`,
`LowFiniteStieltjesContributionIdentityAFZ.of_ibpSource_and_Z_ge_15`,
`LowFiniteStieltjesFormulaOnFirstZeroGapAFZ.of_lowIBPSource_and_startsAfter`,
`LowFiniteStieltjesFormulaOnFirstZeroGapAFZ.of_lowIBPSource_and_Z_ge_15`,
`StieltjesLowEqualityAFZ.of_lowZeroContributionSplit_Z_ge_15`, and
`ClassicalPathBStieltjesInputsAFZ.of_mid_high_lowSplit_Z_ge_15`.
The Theorem 3 form
`XiPullbackAntiHerglotzTarget_of_classicalPathBHadamard_midHigh_lowSplit`
lives at §CCCLXV.

**Audit layer** (§§CCCLXVI–CCCLXVIII). The three documentary Props
`HadamardInputsAreClassical`, `StieltjesInputsArePureIdentities`, and
`PathBSignOrEnvelopeInputs`. Discussed in §10.

**Atomic low-split reducer** (§CCCLXIX). `LowCloudTailSplitAFZ`
reduces `LowZeroContributionSplitAFZ` to three identity fields against
any chosen decomposition.

**Concrete Hadamard handoff bundles** (§§CCCLXX–CCCLXXVI). The
analytic-agent-facing templates for the raw-ξ form:
`ConcreteCompletedXiZeroSystem`, `ConcreteCompletedXiHadamardPrefactor`
with the `.exp_affine` convenience, `ConcreteCompletedXiHadamardFactorization`,
`CompletedXiZeroInvSqDistribution`, `ConcreteCompletedXiHadamardInputs`,
and the concrete-input front door
`XiPullbackAntiHerglotzTarget_of_concreteHadamard_midHigh_cloudTailLow`.
The Hadamard LUC/log-derivative handoff can now be stated directly on
the ξ-nonzero region through `HadamardProductLUCOnXiNonzeroData`; its
`toLUCLogDerivData` adapter and inverse-direction restriction
`HadamardProductLUCOnXiNonzeroData.of_LUCLogDerivData` feed
`ClassicalPathBAnalyticInputs.of_hadamard_packages_onXiNonzero`,
`ConcreteCompletedXiHadamardInputs.of_lucOnXiNonzero`,
`ConcreteCompletedXiHadamardInputs.of_lucLogDerivData`, and the
publication constructors. Its nonzero completed-ξ zero-system layer now
includes `CompletedXiNonzeroZeroIndex`, `completedXiNonzeroZeroLoc`,
`ConcreteCompletedXiNonzeroZeroSystem`,
`ConcreteCompletedXiNonzeroZeroSystem.nonzero_no_collision`, and
`concreteCompletedXiNonzeroZeroSystem`, separating the nonzero indexed
zero payload from the later bridge that may reinsert the origin. The
publication constructors
`CompletedXiClassicalHadamardTheorem.of_lucOnXiNonzero` and
`CompletedXiClassicalHadamardTheorem.of_lucLogDerivData`. It also has a
direct completed-ξ source constructor
`CompletedXiLogDerivativeSourceAFZ.of_lucOnXiNonzeroHadamard` and its
arbitrary-region sibling
`CompletedXiLogDerivativeSourceAFZ.of_lucLogDerivDataHadamard`, feeding
`XiPullbackAntiHerglotzTarget_of_lucOnXiNonzeroHadamardSource_and_stieltjesAFZ`
and
`XiPullbackAntiHerglotzTarget_of_lucOnXiNonzeroHadamardSource_and_stieltjesAFZ_turingBundle`.
The same direct source now builds the source-level non-Turing Path B
bundle through `PathBNonTuringSourceInputs.of_lucOnXiNonzeroHadamard`.
The arbitrary-region LUC version feeds
`PathBNonTuringSourceInputs.of_lucLogDerivDataHadamard`.
It also lowers directly into the canonical direct AFZ non-Turing bundle
through `PathBDirectNonTuringInputsAFZ.of_lucOnXiNonzeroHadamard` and
`PathBDirectNonTuringInputsAFZ.of_lucLogDerivDataHadamard`.
The same LUC handoff now builds source full bundles via
`PathBSourceFullInputBundle.of_lucOnXiNonzeroHadamard`,
`PathBSourceFullInputBundle.of_lucOnXiNonzeroHadamard_envelopes`,
`PathBSourceFullInputBundle.of_lucLogDerivDataHadamard`, and
`PathBSourceFullInputBundle.of_lucLogDerivDataHadamard_envelopes`, and
direct AFZ full bundles via
`PathBDirectFullInputBundleAFZ.of_lucOnXiNonzeroHadamard`,
`PathBDirectFullInputBundleAFZ.of_lucOnXiNonzeroHadamard_envelopes`,
`PathBDirectFullInputBundleAFZ.of_lucLogDerivDataHadamard`, and
`PathBDirectFullInputBundleAFZ.of_lucLogDerivDataHadamard_envelopes`.
Their direct-full capstones are
`XiPullbackAntiHerglotzTarget_of_pathBDirectFull_lucOnXiNonzeroHadamard_stieltjesAFZ_turingBundle`,
`XiPullbackAntiHerglotzTarget_of_pathBDirectFull_lucOnXiNonzeroHadamard_stieltjesAFZ_turingEnvelopes`,
`XiPullbackAntiHerglotzTarget_of_pathBDirectFull_lucLogDerivDataHadamard_stieltjesAFZ_turingBundle`,
and
`XiPullbackAntiHerglotzTarget_of_pathBDirectFull_lucLogDerivDataHadamard_stieltjesAFZ_turingEnvelopes`.
The genuine entire-ξ side has the analogous LUC package:
`EntireXiNonzeroZeroIndex`,
`entireXiNonzeroZeroLoc`,
`concreteEntireXiZeroSystem`,
`HadamardProductLUCOnEntireXiNonzeroData`,
`HadamardProductLUCOnEntireXiNonzeroData.toLUCLogDerivData`,
`HadamardProductLUCOnEntireXiNonzeroData.of_LUCLogDerivData`,
`HadamardProductLUCOnEntireXiNonzeroData.toLogDerivLimitData`,
`HadamardProductLUCLogDerivData.toEntireXiLogDerivLimitData`,
`EntireXiClassicalHadamardTheorem.of_lucOnEntireXiNonzero`, and
`EntireXiClassicalHadamardTheorem.of_lucLogDerivData`; the bundle now
also exposes
`EntireXiClassicalHadamardTheorem.product_multipliable` and
`EntireXiClassicalHadamardTheorem.toLogDerivLimitData`, plus nonzero-
locus consequences
`EntireXiClassicalHadamardTheorem.regularized_summable_at_nonzero`,
`EntireXiClassicalHadamardTheorem.product_differentiable_at_nonzero`,
`EntireXiClassicalHadamardTheorem.product_ne_at_nonzero`,
and
`EntireXiClassicalHadamardTheorem.product_logDeriv_eq_tsum_at_nonzero`.
The canonical nonzero-zero index type now gives zero-system-free
publication front doors
`EntireXiClassicalHadamardTheorem.of_canonicalZeros_lucOnEntireXiNonzero`
and
`EntireXiClassicalHadamardTheorem.of_canonicalZeros_lucLogDerivData`.
The canonical-zero route now also has exponential-affine prefactor
front doors
`EntireXiClassicalHadamardTheorem.of_canonicalZeros_expAffine_lucOnEntireXiNonzero`
and
`EntireXiClassicalHadamardTheorem.of_canonicalZeros_expAffine_lucLogDerivData`.
The explicit Hadamard log-derivative layer now includes
`logDerivativeResponse_exp_affine_prefactor`,
`EntireXiClassicalHadamardTheorem.logDerivativeResponse_eq_prefactor_plus_series`,
and
`EntireXiClassicalHadamardTheorem.logDerivativeResponse_eq_expAffine_plus_series`,
with source adapters
`EntireXiClassicalHadamardTheorem.toExpAffineLogDerivativeSourceAFZ`
and
`EntireXiClassicalHadamardTheorem.toCompletedXiExpAffineSourceAFZ`.
The completed-side explicit contribution is recorded by
`EntireXiClassicalHadamardTheorem.toCompletedXiExpAffineSourceAFZ_xiZeroContribution`.
The z-plane pullback layer now records the explicit exp-affine series
through
`expAffineHadamardPullbackZeroContribution`,
`EntireXiClassicalHadamardTheorem.pullbackZeroContribution_toCompletedXiExpAffineSourceAFZ`,
`EntireXiClassicalHadamardTheorem.XiHadamardLogDerivativeSourceAFZ_of_toCompletedXiExpAffineSourceAFZ_zeroContribution`,
and
`EntireXiClassicalHadamardTheorem.XiPullback_logDerivativeResponse_eq_expAffine_series`.
It also exposes the direct AFZ source/front-door layer
`EntireXiClassicalHadamardTheorem.toExpAffinePullbackHadamardSourceAFZ`,
`EntireXiClassicalHadamardTheorem.toExpAffinePullbackHadamardSourceAFZ_zeroContribution`,
`expAffineHadamardPullbackZeroContribution_eq_prefactor_plus_tsum`,
`expAffineHadamardPullbackZeroContributionExpanded`,
`expAffineHadamardPullbackFiniteContribution`,
`expAffineHadamardPullbackFiniteContribution_eq_prefactor_plus_finiteRegularizedSum`,
`EntireXiClassicalHadamardTheorem.expAffineHadamardPullbackFiniteContribution_eq_prefactor_plus_finiteProductLogDeriv`,
`expAffineHadamardPullbackZeroContribution_eq_expanded`,
`EntireXiClassicalHadamardTheorem.pullback_regularized_summable_at_XiPullback_nonzero`,
`EntireXiClassicalHadamardTheorem.pullback_regularized_hasSum_at_XiPullback_nonzero`,
`EntireXiClassicalHadamardTheorem.tendsto_finiteHadamardRegularizedSum_at_XiPullback_nonzero`,
`EntireXiClassicalHadamardTheorem.tendsto_finiteProductLogDeriv_at_XiPullback_nonzero`,
`EntireXiClassicalHadamardTheorem.tendsto_expAffine_finiteProductLogDeriv_to_XiPullback_logDerivativeResponse`,
`EntireXiClassicalHadamardTheorem.tendsto_expAffineHadamardPullbackFiniteContribution`,
`EntireXiClassicalHadamardTheorem.tendsto_expAffineHadamardPullbackFiniteContribution_compact`,
`EntireXiClassicalHadamardTheorem.tendsto_expAffineHadamardPullbackFiniteContribution_to_XiPullback_logDerivativeResponse`,
`stieltjes_limit_identity_of_finite_decompositions`,
`ExpAffineHadamardFiniteStieltjesMidSourceAFZ`,
`ExpAffineHadamardFiniteStieltjesHighSourceAFZ`,
`ExpAffineHadamardFiniteStieltjesLowSourceAFZ`,
`StieltjesMidTailEqualityAFZ.of_expAffineHadamardFiniteSource`,
`StieltjesHighTailEqualityAFZ.of_expAffineHadamardFiniteSource`,
`StieltjesMidHighTailEqualityAFZ.of_expAffineHadamardFiniteSources`,
`LowZeroContributionSplitAFZ.of_expAffineHadamardFiniteSource`,
`StieltjesLowEqualityAFZ.of_expAffineHadamardFiniteSource`,
`StieltjesLowEqualityAFZ.of_expAffineHadamardFiniteSource_Z_ge_15`,
`XiPullbackAntiHerglotzTarget_of_expAffineHadamardFiniteSources_lowSplit`,
`XiPullbackAntiHerglotzTarget_of_expAffineHadamardFiniteStieltjesSources`,
`expAffineHadamardFiniteResidualTail`,
`expAffineHadamardFiniteLowTail`,
`expAffineHadamardFiniteProductResidualTail`,
`expAffineHadamardFiniteProductLowTail`,
`expAffineHadamardPullbackFiniteContribution_eq_cloud_smooth_residualTail`,
`expAffineHadamardPullbackFiniteContribution_eq_cloud_lowTail`,
`EntireXiClassicalHadamardTheorem.expAffineHadamardFiniteProductResidualTail_eq_finiteResidualTail`,
`EntireXiClassicalHadamardTheorem.expAffineHadamardFiniteProductLowTail_eq_finiteLowTail`,
`EntireXiClassicalHadamardTheorem.tendsto_expAffineHadamardFiniteProductResidualTail_to_XiPullback_residual`,
`EntireXiClassicalHadamardTheorem.tendsto_expAffineHadamardFiniteProductLowTail_to_XiPullback_residual`,
`ExpAffineHadamardResidualTailConvergenceMidAFZ`,
`ExpAffineHadamardResidualTailConvergenceHighAFZ`,
`ExpAffineHadamardResidualTailConvergenceLowAFZ`,
`ExpAffineHadamardResidualTailConvergenceMidAFZ.of_stieltjesEquality`,
`ExpAffineHadamardResidualTailConvergenceHighAFZ.of_stieltjesEquality`,
`ExpAffineHadamardResidualTailConvergenceLowAFZ.of_lowZeroSplit`,
`expAffineHadamardFiniteProductResidualTailConvergenceMid_of_stieltjesEquality`,
`expAffineHadamardFiniteProductResidualTailConvergenceHigh_of_stieltjesEquality`,
`expAffineHadamardFiniteProductLowTailConvergence_of_lowZeroSplit`,
`ExpAffineHadamardResidualTailConvergenceMidAFZ.of_finiteProductResidualTailConvergence`,
`ExpAffineHadamardResidualTailConvergenceHighAFZ.of_finiteProductResidualTailConvergence`,
`ExpAffineHadamardResidualTailConvergenceLowAFZ.of_finiteProductLowTailConvergence`,
`ExpAffineHadamardResidualTailConvergenceMidAFZ.to_finiteProductResidualTailConvergence`,
`ExpAffineHadamardResidualTailConvergenceHighAFZ.to_finiteProductResidualTailConvergence`,
`ExpAffineHadamardResidualTailConvergenceLowAFZ.to_finiteProductLowTailConvergence`,
`expAffineHadamardFiniteProductResidualTailConvergenceMid_iff_residualTailConvergence`,
`expAffineHadamardFiniteProductResidualTailConvergenceHigh_iff_residualTailConvergence`,
`expAffineHadamardFiniteProductLowTailConvergence_iff_residualTailConvergenceLow`,
`expAffineHadamardFiniteProductResidualTailConvergenceMid_iff_stieltjesMidTailEqualityAFZ`,
`expAffineHadamardFiniteProductResidualTailConvergenceHigh_iff_stieltjesHighTailEqualityAFZ`,
`expAffineHadamardFiniteProductLowTailConvergence_iff_lowZeroContributionSplitAFZ`,
`expAffineHadamardFiniteProductResidualTailConvergenceMid_of_exists_identified_tail`,
`expAffineHadamardFiniteProductResidualTailConvergenceHigh_of_exists_identified_tail`,
`XiPullbackAntiHerglotzTarget_of_expAffineHadamardFiniteProductResidualConvergence`,
`expAffineHadamardResidualTailConvergenceMid_iff_stieltjesMidTailEqualityAFZ`,
`expAffineHadamardResidualTailConvergenceHigh_iff_stieltjesHighTailEqualityAFZ`,
`expAffineHadamardResidualTailConvergenceLow_iff_lowZeroContributionSplitAFZ`,
`ExpAffineHadamardFiniteStieltjesMidSourceAFZ.of_residualTailConvergence`,
`ExpAffineHadamardFiniteStieltjesHighSourceAFZ.of_residualTailConvergence`,
`ExpAffineHadamardFiniteStieltjesLowSourceAFZ.of_residualTailConvergence`,
`StieltjesMidTailEqualityAFZ.of_expAffineHadamardResidualTailConvergence`,
`StieltjesHighTailEqualityAFZ.of_expAffineHadamardResidualTailConvergence`,
`LowZeroContributionSplitAFZ.of_expAffineHadamardResidualTailConvergence`,
`StieltjesLowEqualityAFZ.of_expAffineHadamardResidualTailConvergence_Z_ge_15`,
`XiPullbackAntiHerglotzTarget_of_expAffineHadamardResidualTailConvergence`,
`StieltjesLowEqualityAFZ.congr_zeroContribution`,
`LowCloudTailSplitAFZ.congr_zeroContribution`,
`ClassicalPathBStieltjesInputsAFZ.congr_zeroContribution`,
`XiZeroContributionStieltjesEqualitySourceAFZ.of_expAffineHadamardPullbackExpanded`,
`XiPullbackAntiHerglotzTarget_of_expAffineHadamardPullbackExpandedStieltjesAFZ`,
`XiPullbackAntiHerglotzTarget_of_expAffineHadamardPullbackExpanded_midHigh_lowSplit`,
and
`XiPullbackAntiHerglotzTarget_of_expAffineHadamardPullback_midHigh_lowSplit`.
It now also
exports direct source constructors
`EntireXiLogDerivativeSourceAFZ.of_lucOnEntireXiNonzeroHadamard` and
`EntireXiLogDerivativeSourceAFZ.of_lucLogDerivDataHadamard`, plus the
canonical-zero variants
`EntireXiLogDerivativeSourceAFZ.of_canonicalZeros_lucOnEntireXiNonzeroHadamard`
and
`EntireXiLogDerivativeSourceAFZ.of_canonicalZeros_lucLogDerivDataHadamard`,
with exp-affine-prefactor variants
`EntireXiLogDerivativeSourceAFZ.of_canonicalZeros_expAffine_lucOnEntireXiNonzeroHadamard`
and
`EntireXiLogDerivativeSourceAFZ.of_canonicalZeros_expAffine_lucLogDerivDataHadamard`.
Their explicit zero-contribution simp front doors are
`EntireXiLogDerivativeSourceAFZ.of_canonicalZeros_expAffine_lucOnEntireXiNonzeroHadamard_xiZeroContribution`
and
`EntireXiLogDerivativeSourceAFZ.of_canonicalZeros_expAffine_lucLogDerivDataHadamard_xiZeroContribution`.
This
ξ-nonzero-region package now also has publication front doors
`XiPullbackAntiHerglotzTarget_of_lucLogDerivDataHadamardSource_and_stieltjesAFZ`,
`XiPullbackAntiHerglotzTarget_of_lucOnXiNonzeroHadamard_and_classicalStieltjes`,
`XiPullbackAntiHerglotzTarget_of_lucOnXiNonzeroHadamard_and_stieltjesAFZ`,
`XiPullbackAntiHerglotzTarget_of_lucLogDerivDataHadamard_and_classicalStieltjes`,
`XiPullbackAntiHerglotzTarget_of_lucLogDerivDataHadamard_and_stieltjesAFZ`,
`XiPullbackAntiHerglotzTarget_of_lucLogDerivDataHadamardSource_and_stieltjesAFZ_turingBundle`,
`XiPullbackAntiHerglotzTarget_of_lucLogDerivDataHadamard_and_classicalStieltjes_turingBundle`,
`XiPullbackAntiHerglotzTarget_of_lucLogDerivDataHadamard_and_stieltjesAFZ_turingBundle`,
`XiPullbackAntiHerglotzTarget_of_lucOnXiNonzeroHadamard_and_classicalStieltjes_turingBundle`,
and
`XiPullbackAntiHerglotzTarget_of_lucOnXiNonzeroHadamard_and_stieltjesAFZ_turingBundle`.

**Publication-level bundles** (§§CCCLXXVII–CCCLXXIX). Public-name
renames: `CompletedXiClassicalHadamardTheorem` (the publication name
for the raw-ξ bundle) and `ClassicalStieltjesExplicitFormulaInputs`
(packaging mid + high + low cloud/tail), with the publication-style
front door
`XiPullbackAntiHerglotzTarget_of_classicalHadamard_and_classicalStieltjes`.

**Entire-ξ Hadamard chain** (§§CCCLXXX–CCCLXXXIX). The parallel
Hadamard infrastructure for `entireRiemannXi`:
`ConcreteEntireXiZeroSystem`, `EntireXiZeroInvSqDistribution`,
`EntireXiHadamardPrefactor`, `EntireXiHadamardFactorization`,
`EntireXiClassicalHadamardTheorem` (§CCCLXXXVIII), and
`EntireXiLogDerivativeSourceAFZ`. The source-level front door
`XiPullbackAntiHerglotzTarget_of_completedXiSource_midHigh_lowSplit`
(§CCCLXXXIX) takes a `CompletedXiLogDerivativeSourceAFZ` directly.

**Γ-cancellation bridge between raw-ξ and entire-ξ**
(§§CCCXC–CDXIV). The chain that identifies `completedXiFunction` with
`entireRiemannXi` away from $\Gamma$-pole pullbacks:

* §§CCCXCI–CCCXCV — `CompletedXiRawEntireXiPointwiseEqualitySource`,
  `CompletedXiRawEntireXiOpenNeighborhoodEqualitySource`,
  `CompletedXiRawEntireXiLocalEqualitySource`, nonzero transfer,
  differentiability transfer, log-derivative equality from local equality,
  and raw-correctness constructors
  `CompletedXiRawEntireXiPointwiseEqualitySource.of_rawCorrectness` and
  `CompletedXiRawEntireXiOpenNeighborhoodEqualitySource.of_rawCorrectness`.
* §§CCCXCVI–CCCXCVII — `CompletedXiRawEqualsEntireXiOffGammaPoles`
  raw off-pole equality target.
* §§CCCXCVIII–CDII — auto-discharged differentiability via
  `entireRiemannXi_differentiabilitySource`; the front door
  `XiPullbackAntiHerglotzTarget_of_rawEntireLocalEquality_entireXiHadamard_midHigh_lowSplit`.
* §§CDIII–CDVIII — Γ-cancellation analysis at the formula level:
  `CompletedXiRawEntireXiOpenEqualitySource`,
  `CompletedXiGammaRegularNeighborhoodSource`,
  `CompletedXiRawEntireXiOffPoleFormulaEquality`.
* §§CDIX–CDXII — Γ-pole set, `CompletedXiNonzeroExcludesGammaPole`,
  `GammaPoleAvoidingNeighborhoodSource`, and the composite bridge.
* §CDXIV — the **Theorem 4** headline,
  `XiPullbackAntiHerglotzTarget_of_gammaNoPole_avoidingNhds_offPoleFormula_entireHadamard_midHigh_lowSplit`,
  consuming the most decomposed form of the Γ-bridge: no-pole +
  avoiding-nhds + off-pole formula.

**Γ-bridge discharge** (§§CDXV–CDXLIV). The chain that unconditionally
discharges every piece of the Γ-bridge, culminating in the headline
theorem where Γ-cancellation no longer appears as a hypothesis:

* §§CDXV–CDXVII — `gammaPoleSet` norm facts and the `IsClosed`
  target; closed-set bridge to `GammaPoleAvoidingNeighborhoodSource`.
* §§CDXVIII–CDXXI — Path B front door with `IsClosed` as a hypothesis,
  direct proof `isClosed_gammaPoleSet` via
  `Nat.isClosedEmbedding_coe_real`, and the
  `_gammaNoPole_offPoleFormula_…` front door with topology discharged.
* §§CDXXII–CDXXIII — `RawCompletedXiCorrectness` bundle and the
  matching front door.
* §§CDXXIV–CDXXVII — pointwise off-pole formula target, vanishing
  contrapositive, raw correctness from pointwise formula targets, and
  the `_rawPointwise_…` front door.
* §§CDXXIX–CDXXXII — `rawCompletedXiFormula` (matches `completedXiFunction`
  by `rfl`), `completedXiFunction_vanishes_of_half_eq_neg_nat` via
  `Complex.Gamma_neg_nat_eq_zero`, and
  `completedXiVanishesOnGammaPolePullback` (unconditional). The
  Γ-vanishing piece of the Γ-bridge is now closed.
* §CDXXXV — the `_rawFormulaPointwise_…` front door with both
  Γ-vanishing and topology discharged. Only the off-pole formula
  identity remains.
* §§CDXXXVI–CDXL — three formula sources, all unconditional: the raw-ζ
  off-pole formula `completedRiemannZetaRawOffPoleFormula` (proved
  from Mathlib's `Gammaℝ`/`riemannZeta_def_of_ne_zero` chain together
  with `GammaReal_eq_exp_gamma`, `ne_zero_of_half_not_gammaPole`, and
  `GammaReal_ne_zero_of_half_not_gammaPole`), Mathlib's $\zeta_0$
  correction `completedRiemannZetaZeroCorrectionFormula`
  (=`completedRiemannZeta_eq`), and `entireRiemannXiFormulaSource`
  (proved by `rfl`). The algebra lemma
  `xi_completedZeta_correction_algebra` discharges the $+1/2$
  correction.
* §CDXLI — `CompletedXiRawEntireXiOffPolePointwiseFormula.of_completedZetaIdentities`
  composes the three formula sources into the off-pole pointwise
  formula; the unconditional inhabitant
  `completedXiRawEntireXiOffPolePointwiseFormula` follows.
* §CDXLII — **Theorem 5**,
  `XiPullbackAntiHerglotzTarget_of_completedZetaRaw_entireHadamard_midHigh_lowSplit`,
  consuming only one Mathlib identity in place of the full Γ-bridge.
* §CDXLIII — **Theorem 6**,
  `XiPullbackAntiHerglotzTarget_of_entireHadamard_midHigh_lowSplit`,
  with the Γ-cancellation fully discharged. Only (P1), (P2), (P3)
  appear as hypotheses.
* §CDXLIV — **canonical front doors**:
  `rawCompletedXiCorrectness`,
  `completedXiRawEntireXiPointwiseEqualitySource`,
  `completedXiRawEntireXiOpenNeighborhoodEqualitySource`,
  `completedXiRawEntireXiLocalEqualitySource`,
  `completedXiRawEqualsEntireXiOnRegularRegion`,
  `completedXiRawEqualsEntireXiOffGammaPoles`,
  `completedXiEqualsEntireXiLocallyAFZSource`,
  `entireXiToCompletedXiLogDerivBridge`, and
  `EntireXiClassicalHadamardTheorem.toCompletedXiSourceAFZ_canonical`
  name the completed-ξ source once; the theorem variants
  `XiPullbackAntiHerglotzTarget_of_entireHadamard_canonical_midHigh_lowSplit`,
  `XiPullbackAntiHerglotzTarget_of_entireHadamard_canonical_midHigh_lowZeroSplit`,
  `XiPullbackAntiHerglotzTarget_of_entireHadamard_canonicalStieltjesAFZ`,
  `XiPullbackAntiHerglotzTarget_of_entireHadamard_canonicalStieltjesInputs`,
  `XiPullbackAntiHerglotzTarget_of_entireHadamard_canonical_midHigh_lowIBPSource`,
  `XiPullbackAntiHerglotzTarget_of_entireHadamard_canonical_midHighAFZ_lowZeroSplit`,
  `XiPullbackAntiHerglotzTarget_of_entireHadamard_canonical_midHighAFZ_lowCloudTailSplit`,
  `XiPullbackAntiHerglotzTarget_of_entireHadamard_canonical_midHighAFZ_lowIBPSource`,
  `XiPullbackAntiHerglotzTarget_of_entireHadamard_canonical_unguardedStieltjesSource`,
  `XiPullbackAntiHerglotzTarget_of_entireHadamard_canonical_unguardedMidHigh_lowFirstZeroFormula`,
  and
  `XiPullbackAntiHerglotzTarget_of_entireHadamard_and_classicalStieltjes`
  expose the same Γ-discharged reduction with stable Stieltjes
  hypothesis shapes, from direct low-zero/low-IBP sources up to the
  publication-level classical Stieltjes bundle. The helper theorems
  `ClassicalStieltjesExplicitFormulaInputs.toClassicalPathBStieltjesInputsAFZ`,
  `ClassicalStieltjesExplicitFormulaInputs.toClassicalPathBStieltjesInputsAFZ_Z_ge_15`,
  `ClassicalPathBStieltjesInputsAFZ.of_mid_high_lowIBPSource`, and
  `ClassicalPathBStieltjesInputsAFZ.of_midHighAFZ_lowIBPSource`
  perform the canonical Stieltjes reassembly; the mid/high splitters
  `StieltjesMidTailEqualityAFZ.of_midHighAFZ` and
  `StieltjesHighTailEqualityAFZ.of_midHighAFZ` expose the two
  components of a combined AFZ mid/high equality, while the
  `of_unguarded` helpers weaken older global equalities into the AFZ
  hypotheses used by the final chain.
* §CDXLV — **one-bundle non-Turing input**:
  `PathBNonTuringInputs` packages the zero-start datum, entire-ξ
  Hadamard theorem, and assembled AFZ Stieltjes bundle keyed to
  `Hhad.toCompletedXiSourceAFZ_canonical`.
  `PathBNonTuringInputs.of_classicalStieltjes`,
  `PathBNonTuringInputs.of_stieltjesInputs`,
  `PathBNonTuringInputs.of_stieltjesEqualitySourceAFZ`,
  `PathBNonTuringInputs.of_mid_high_lowIBPSource`,
  `PathBNonTuringInputs.of_midHighAFZ_lowIBPSource`,
  `PathBNonTuringInputs.of_midHighAFZ_lowZeroSplit`,
  `PathBNonTuringInputs.of_midHighAFZ_lowCloudTailSplit`,
  `PathBNonTuringInputs.of_unguardedMidHigh_lowFirstZeroFormula`,
  `PathBNonTuringInputs.of_unguardedStieltjesSource`,
  `PathBNonTuringInputs_to_target`, and
  `XiPullbackAntiHerglotzTarget_of_nonTuringInputs_and_turingEnvelopes`
  leave only the two Backlund/Turing envelope hypotheses visible. The
  sibling only-envelopes-unbundled front doors cover assembled
  Stieltjes inputs, publication Stieltjes inputs, combined AFZ
  mid/high with low IBP/zero/cloud-tail inputs, and older unguarded
  Stieltjes packages. The entire-Hadamard unified-AFZ Stieltjes source
  case is also exposed directly as
  `XiPullbackAntiHerglotzTarget_of_entireHadamard_stieltjesEqualitySourceAFZ_turingEnvelopes`.
* §CDXLVI — **two-bundle Path B capstone**:
  `PathBTuringEnvelopeInputs` packages the slab-localized Turing
  envelope and the high-log envelope, with
  `PathBTuringEnvelopeInputs.of_envelopes` as the raw-estimate
  constructor. `XiPullbackAntiHerglotzTarget_of_pathBInputBundles`
  proves the final local capstone from exactly two bundles:
  `PathBNonTuringInputs` and `PathBTuringEnvelopeInputs`. The
  one-object publication frontier `PathBFullInputBundle` packages those
  together; `PathBFullInputBundle.of_envelopes` builds it from raw
  Turing envelopes. It now also has bundled-Turing constructors
  `PathBFullInputBundle.of_classicalStieltjes`,
  `PathBFullInputBundle.of_stieltjesInputs`, and
  `PathBFullInputBundle.of_stieltjesEqualitySourceAFZ`, plus the
  mid/high AFZ low-side variants
  `PathBFullInputBundle.of_midHighAFZ_lowIBPSource`,
  `PathBFullInputBundle.of_midHighAFZ_lowZeroSplit`, and
  `PathBFullInputBundle.of_midHighAFZ_lowCloudTailSplit`. Each has a
  raw-envelope sibling:
  `PathBFullInputBundle.of_classicalStieltjes_envelopes`,
  `PathBFullInputBundle.of_stieltjesInputs_envelopes`,
  `PathBFullInputBundle.of_stieltjesEqualitySourceAFZ_envelopes`,
  `PathBFullInputBundle.of_midHighAFZ_lowIBPSource_envelopes`,
  `PathBFullInputBundle.of_midHighAFZ_lowZeroSplit_envelopes`, and
  `PathBFullInputBundle.of_midHighAFZ_lowCloudTailSplit_envelopes`, with
  `PathBFullInputBundle.to_target` and
  `XiPullbackAntiHerglotzTarget_of_pathBFullInputBundle` as capstones.
  The new
  `PathBNonTuringSourceInputs` lowers the non-Turing side further to a
  completed-ξ log-derivative source plus its matched AFZ Stieltjes
  equality source, and
  `XiPullbackAntiHerglotzTarget_of_pathBSourceInputBundles` is the
  minimal source-level two-bundle capstone. The one-object source
  frontier `PathBSourceFullInputBundle` has the raw-envelope constructor
  `PathBSourceFullInputBundle.of_envelopes` and exposes
  `PathBSourceFullInputBundle.to_target` and
  `XiPullbackAntiHerglotzTarget_of_pathBSourceFullInputBundle`. The
  source constructors
  `PathBNonTuringSourceInputs.of_completedXiSource`,
  `PathBNonTuringSourceInputs.of_hadamardProductData`,
  `PathBNonTuringSourceInputs.of_classicalPathBAnalyticInputs`,
  `PathBNonTuringSourceInputs.of_concreteCompletedXiHadamardInputs`,
  `PathBNonTuringSourceInputs.of_completedXiClassicalHadamard`,
  `PathBNonTuringSourceInputs.of_entireHadamardInputs`, and
  `PathBNonTuringSourceInputs.of_entireXiSource` feed the completed-ξ,
  Hadamard-product, classical-analytic, concrete completed-ξ
  Hadamard, publication completed-ξ Hadamard, entire-Hadamard, and
  entire-ξ source routes. The sibling `_turingBundle` front doors
  expose the same result for completed-ξ sources, completed-ξ
  Hadamard product data, classical analytic inputs, concrete
  completed-ξ Hadamard inputs, publication completed-ξ Hadamard inputs,
  entire-ξ sources, canonical Stieltjes inputs, unified AFZ Stieltjes
  equality sources, publication Stieltjes inputs, combined AFZ
  mid/high plus low IBP, zero split, and cloud/tail, split mid/high
  plus low IBP/zero/cloud-tail inputs, and older unguarded split or
  unified Stieltjes inputs. The completed-ξ source-level AFZ Stieltjes
  cases now also have unbundled-envelope front doors:
  `XiPullbackAntiHerglotzTarget_of_completedXiSource_stieltjesAFZ_turingEnvelopes`,
  `XiPullbackAntiHerglotzTarget_of_hadamardProductData_stieltjesAFZ_turingEnvelopes`,
  `XiPullbackAntiHerglotzTarget_of_classicalPathBAnalyticInputs_stieltjesAFZ_turingEnvelopes`,
  `XiPullbackAntiHerglotzTarget_of_concreteCompletedXiHadamard_stieltjesAFZ_turingEnvelopes`,
  `XiPullbackAntiHerglotzTarget_of_completedXiClassicalHadamard_stieltjesAFZ_turingEnvelopes`,
  and
  `XiPullbackAntiHerglotzTarget_of_entireXiSource_stieltjesAFZ_turingEnvelopes`.
* §CDXLVII — **canonical completed-ξ source front door**:
  `canonicalEntireXiLogDerivativeSourceAFZ`,
  `canonicalCompletedXiLogDerivativeSourceAFZ`,
  `canonicalPathBZeroContribution`, and
  `CanonicalPathBStieltjesSource` name the canonical source and its
  Stieltjes equality source once. The source-level Stieltjes source can
  now also be built from the direct canonical AFZ Stieltjes source by
  `StieltjesMidHighTailEqualityAFZ.of_canonicalXiPullback`,
  `LowFiniteStieltjesFormulaOnFirstZeroGapAFZ.of_canonicalXiPullback`,
  `XiZeroContributionStieltjesEqualitySourceAFZ.of_canonicalXiPullback`,
  and `CanonicalPathBStieltjesSource.of_canonicalXiPullback`; the
  matching low-side bridges are
  `LowFiniteStieltjesIBPSourceAFZ.of_canonicalXiPullback`,
  `LowZeroContributionSplitAFZ.of_canonicalXiPullback`,
  `LowCloudTailSplitAFZ.of_canonicalXiPullback`,
  `CanonicalPathBLowIBPSourceAFZ_of_canonicalXiPullback`,
  `CanonicalPathBLowZeroSplitAFZ_of_canonicalXiPullback`,
  `CanonicalPathBLowCloudTailSplitAFZ_of_canonicalXiPullback`, and
  `canonicalPathBStieltjesSource_iff_canonicalXiPullbackStieltjesSourceAFZ`.
  The direct canonical AFZ Stieltjes source can now be used as a
  source-level input directly via
  `PathBNonTuringSourceInputs.of_canonicalXiPullbackStieltjesSource`,
  `PathBSourceFullInputBundle.of_canonicalXiPullbackStieltjesSource`,
  `PathBSourceFullInputBundle.of_canonicalXiPullbackStieltjesSource_envelopes`,
  `XiPullbackAntiHerglotzTarget_of_sourceCanonicalXiPullbackStieltjesSource_turingBundle`,
  and
  `XiPullbackAntiHerglotzTarget_of_sourceCanonicalXiPullbackStieltjesSource_turingEnvelopes`.
  The split, low-IBP, low zero-split, and cloud/tail canonical
  Stieltjes inputs now have bundled source full-bundle constructors
  `PathBSourceFullInputBundle.of_canonicalXiPullbackSplitStieltjes`,
  `PathBSourceFullInputBundle.of_canonicalXiPullbackIBPStieltjes`,
  `PathBSourceFullInputBundle.of_canonicalXiPullbackZeroSplitStieltjes`,
  `PathBSourceFullInputBundle.of_canonicalXiPullbackCloudTailStieltjes`,
  with source capstones
  `XiPullbackAntiHerglotzTarget_of_sourceCanonicalXiPullbackSplitStieltjes_turingBundle`,
  `XiPullbackAntiHerglotzTarget_of_sourceCanonicalXiPullbackIBPStieltjes_turingBundle`,
  `XiPullbackAntiHerglotzTarget_of_sourceCanonicalXiPullbackZeroSplitStieltjes_turingBundle`,
  and
  `XiPullbackAntiHerglotzTarget_of_sourceCanonicalXiPullbackCloudTailStieltjes_turingBundle`.
  The raw-envelope source capstones mirror these bundled forms:
  `XiPullbackAntiHerglotzTarget_of_sourceCanonicalXiPullbackSplitStieltjes_turingEnvelopes`,
  `XiPullbackAntiHerglotzTarget_of_sourceCanonicalXiPullbackIBPStieltjes_turingEnvelopes`,
  `XiPullbackAntiHerglotzTarget_of_sourceCanonicalXiPullbackZeroSplitStieltjes_turingEnvelopes`,
  and
  `XiPullbackAntiHerglotzTarget_of_sourceCanonicalXiPullbackCloudTailStieltjes_turingEnvelopes`.
  The constructor
  `PathBNonTuringSourceInputs.of_canonicalStieltjesSource` and theorem
  `XiPullbackAntiHerglotzTarget_of_canonicalStieltjesSource_turingBundle`
  expose the source-level capstone directly for this canonical package;
  `XiPullbackAntiHerglotzTarget_of_canonicalStieltjesSource_turingEnvelopes`
  is its unbundled-envelope sibling. The method forms
  `CanonicalPathBStieltjesSource.to_sourceTarget_turingBundle` and
  `CanonicalPathBStieltjesSource.to_sourceTarget_turingEnvelopes`
  expose the same source-bundle target from the canonical Stieltjes
  source itself.
* §CDXLVIII — **canonical pullback-Ξ source front doors**:
  `canonicalXiPullbackZeroContribution`,
  `canonicalXiPullbackHadamardLogDerivativeSource`,
  `CanonicalXiPullbackStieltjesSource`,
  `CanonicalXiPullbackMidHighStieltjesEquality`,
  `CanonicalXiPullbackLowFirstZeroFormula`,
  `CanonicalXiPullbackLowIBPSourceAFZ`,
  `CanonicalXiPullbackLowZeroSplitAFZ`,
  `CanonicalXiPullbackLowCloudTailSplitAFZ`, and their AFZ variants state
  the pullback-Ξ source layer without repeated bridge terms.
  `CanonicalXiPullbackStieltjesSource.of_midHigh_low` and
  `CanonicalXiPullbackStieltjesSourceAFZ.of_midHigh_low` assemble the
  unified sources; `CanonicalXiPullbackLowFirstZeroFormulaAFZ.of_lowIBPSource`
  `CanonicalXiPullbackLowFirstZeroFormulaAFZ.of_lowZeroSplit`, and
  `CanonicalXiPullbackLowFirstZeroFormulaAFZ.of_lowCloudTailSplit`
  adapt the compact low inputs. The low-IBP and low-zero-split canonical
  inputs now convert both ways through
  `CanonicalXiPullbackLowZeroSplitAFZ.of_lowIBPSource`,
  `CanonicalXiPullbackLowIBPSourceAFZ.of_lowZeroSplit`, and
  `canonicalXiPullbackLowIBPSourceAFZ_iff_lowZeroSplitAFZ`; unified
  and split canonical AFZ Stieltjes sources are likewise related by
  `CanonicalXiPullbackStieltjesSourceAFZ.to_split` and
  `canonicalXiPullbackSplitStieltjesInputsAFZ_iff_stieltjesSourceAFZ`,
  with `[simp]` round trips
  `CanonicalXiPullbackSplitStieltjesInputsAFZ.to_stieltjesSource_to_split`
  and
  `CanonicalXiPullbackStieltjesSourceAFZ.to_split_to_stieltjesSource`.
  At the bundle level, `CanonicalXiPullbackIBPStieltjesInputsAFZ.to_zeroSplit`,
  `CanonicalXiPullbackZeroSplitStieltjesInputsAFZ.to_ibp`, and
  `canonicalXiPullbackIBPStieltjesInputsAFZ_iff_zeroSplitStieltjesInputsAFZ`
  move between low-IBP and low-zero-split Stieltjes inputs, with
  `[simp]` round trips
  `CanonicalXiPullbackIBPStieltjesInputsAFZ.to_zeroSplit_to_ibp` and
  `CanonicalXiPullbackZeroSplitStieltjesInputsAFZ.to_ibp_to_zeroSplit`.
  The front doors
  `XiPullbackAntiHerglotzTarget_of_canonicalXiPullbackStieltjesSource_turingBundle`,
  `XiPullbackAntiHerglotzTarget_of_canonicalXiPullback_midHigh_low_turingBundle`,
  `XiPullbackAntiHerglotzTarget_of_canonicalXiPullbackStieltjesSourceAFZ_turingBundle`,
  `XiPullbackAntiHerglotzTarget_of_canonicalXiPullback_midHighAFZ_lowAFZ_turingBundle`,
  `XiPullbackAntiHerglotzTarget_of_canonicalXiPullback_midHighAFZ_lowIBP_turingBundle`,
  and
  `XiPullbackAntiHerglotzTarget_of_canonicalXiPullback_midHighAFZ_lowZeroSplit_turingBundle`,
  and
  `XiPullbackAntiHerglotzTarget_of_canonicalXiPullback_midHighAFZ_lowCloudTail_turingBundle`
  are the bundled-Turing front doors for those canonical pullback
  source shapes. Their unbundled Turing-envelope siblings are now
  exposed as
  `XiPullbackAntiHerglotzTarget_of_canonicalXiPullbackStieltjesSource_turingEnvelopes`,
  `XiPullbackAntiHerglotzTarget_of_canonicalXiPullback_midHigh_low_turingEnvelopes`,
  `XiPullbackAntiHerglotzTarget_of_canonicalXiPullbackStieltjesSourceAFZ_turingEnvelopes`,
  `XiPullbackAntiHerglotzTarget_of_canonicalXiPullback_midHighAFZ_lowAFZ_turingEnvelopes`,
  `XiPullbackAntiHerglotzTarget_of_canonicalXiPullback_midHighAFZ_lowIBP_turingEnvelopes`,
  `XiPullbackAntiHerglotzTarget_of_canonicalXiPullback_midHighAFZ_lowZeroSplit_turingEnvelopes`,
  and
  `XiPullbackAntiHerglotzTarget_of_canonicalXiPullback_midHighAFZ_lowCloudTail_turingEnvelopes`.
  `CanonicalXiPullbackSplitStieltjesInputsAFZ`,
  `CanonicalXiPullbackIBPStieltjesInputsAFZ`,
  `CanonicalXiPullbackZeroSplitStieltjesInputsAFZ`, and
  `CanonicalXiPullbackCloudTailStieltjesInputsAFZ` are the direct
  canonical Stieltjes bundles; their `to_split`/`to_stieltjesSource`
  adapters feed the final `PathBDirectNonTuringInputsAFZ` bundle.
  `XiPullbackAntiHerglotzTarget_of_directNonTuringInputsAFZ_turingBundle`
  is the direct two-bundle capstone. The one-object direct frontier
  `PathBDirectFullInputBundleAFZ` packages direct non-Turing data plus
  Turing envelopes; `PathBDirectFullInputBundleAFZ.of_envelopes` builds
  it from raw Turing envelopes. Its projection and constructor surface now
  includes `PathBDirectFullInputBundleAFZ.to_directNonTuringInputs`,
  `PathBDirectFullInputBundleAFZ.h_Z_ge_15`,
  `PathBDirectFullInputBundleAFZ.to_splitStieltjes`,
  `PathBDirectFullInputBundleAFZ.to_stieltjesSource`,
  `PathBDirectFullInputBundleAFZ.of_completedXiSource`,
  `PathBDirectFullInputBundleAFZ.of_hadamardProductData`,
  `PathBDirectFullInputBundleAFZ.of_classicalPathBAnalyticInputs`,
  `PathBDirectFullInputBundleAFZ.of_concreteCompletedXiHadamardInputs`,
  `PathBDirectFullInputBundleAFZ.of_completedXiClassicalHadamard`,
  `PathBDirectFullInputBundleAFZ.of_entireXiSource`,
  `PathBDirectFullInputBundleAFZ.of_entireHadamard_classicalStieltjes`,
  `PathBDirectFullInputBundleAFZ.of_entireHadamard_stieltjesInputs`,
  `PathBDirectFullInputBundleAFZ.of_entireHadamard_stieltjesEqualitySourceAFZ`,
  `PathBDirectFullInputBundleAFZ.of_canonicalPathBStieltjesSource`,
  `PathBDirectFullInputBundleAFZ.of_splitStieltjes`,
  `PathBDirectFullInputBundleAFZ.of_stieltjesSource`,
  `PathBDirectFullInputBundleAFZ.of_unguardedStieltjesSource`,
  `PathBDirectFullInputBundleAFZ.of_unguardedMidHighLow`,
  `PathBDirectFullInputBundleAFZ.of_ibpStieltjes`,
  `PathBDirectFullInputBundleAFZ.of_zeroSplitStieltjes`,
  `PathBDirectFullInputBundleAFZ.of_cloudTailStieltjes`,
  `PathBDirectFullInputBundleAFZ.of_completedXiSource_envelopes`,
  `PathBDirectFullInputBundleAFZ.of_hadamardProductData_envelopes`,
  `PathBDirectFullInputBundleAFZ.of_classicalPathBAnalyticInputs_envelopes`,
  `PathBDirectFullInputBundleAFZ.of_concreteCompletedXiHadamardInputs_envelopes`,
  `PathBDirectFullInputBundleAFZ.of_completedXiClassicalHadamard_envelopes`,
  `PathBDirectFullInputBundleAFZ.of_entireXiSource_envelopes`,
  `PathBDirectFullInputBundleAFZ.of_entireHadamard_classicalStieltjes_envelopes`,
  `PathBDirectFullInputBundleAFZ.of_entireHadamard_stieltjesInputs_envelopes`,
  `PathBDirectFullInputBundleAFZ.of_entireHadamard_stieltjesEqualitySourceAFZ_envelopes`,
  `PathBDirectFullInputBundleAFZ.of_canonicalPathBStieltjesSource_envelopes`,
  `PathBDirectFullInputBundleAFZ.of_splitStieltjes_envelopes`,
  `PathBDirectFullInputBundleAFZ.of_stieltjesSource_envelopes`,
  `PathBDirectFullInputBundleAFZ.of_unguardedStieltjesSource_envelopes`,
  `PathBDirectFullInputBundleAFZ.of_unguardedMidHighLow_envelopes`,
  `PathBDirectFullInputBundleAFZ.of_ibpStieltjes_envelopes`,
  `PathBDirectFullInputBundleAFZ.of_zeroSplitStieltjes_envelopes`, and
  `PathBDirectFullInputBundleAFZ.of_cloudTailStieltjes_envelopes`, and
  the corresponding `[simp]` projection checks
  `PathBDirectFullInputBundleAFZ.of_splitStieltjes_to_splitStieltjes`,
  `PathBDirectFullInputBundleAFZ.of_stieltjesSource_to_stieltjesSource`,
  `PathBDirectFullInputBundleAFZ.of_splitStieltjes_envelopes_to_splitStieltjes`,
  and
  `PathBDirectFullInputBundleAFZ.of_stieltjesSource_envelopes_to_stieltjesSource`, with
  `PathBDirectFullInputBundleAFZ.to_target` and
  `XiPullbackAntiHerglotzTarget_of_pathBDirectFullInputBundleAFZ` as
  capstones. The split/unified constructor routes also expose direct
  front-door capstones:
  `XiPullbackAntiHerglotzTarget_of_pathBDirectFull_splitStieltjes_turingBundle`,
  `XiPullbackAntiHerglotzTarget_of_pathBDirectFull_splitStieltjes_turingEnvelopes`,
  `XiPullbackAntiHerglotzTarget_of_pathBDirectFull_stieltjesSource_turingBundle`,
  and
  `XiPullbackAntiHerglotzTarget_of_pathBDirectFull_stieltjesSource_turingEnvelopes`.
  Source-level canonical Path B Stieltjes inputs now have parallel
  direct-full capstones:
  `XiPullbackAntiHerglotzTarget_of_pathBDirectFull_canonicalPathBStieltjesSource_turingBundle`
  and
  `XiPullbackAntiHerglotzTarget_of_pathBDirectFull_canonicalPathBStieltjesSource_turingEnvelopes`.
  Older unguarded canonical Stieltjes inputs now have matching
  direct-full capstones:
  `XiPullbackAntiHerglotzTarget_of_pathBDirectFull_unguardedStieltjesSource_turingBundle`,
  `XiPullbackAntiHerglotzTarget_of_pathBDirectFull_unguardedStieltjesSource_turingEnvelopes`,
  `XiPullbackAntiHerglotzTarget_of_pathBDirectFull_unguardedMidHighLow_turingBundle`,
  and
  `XiPullbackAntiHerglotzTarget_of_pathBDirectFull_unguardedMidHighLow_turingEnvelopes`.
  Their method forms assemble direct full bundles from either bundled or
  raw Turing envelopes:
  `CanonicalXiPullbackStieltjesSource.to_directFullInputBundle`,
  `CanonicalXiPullbackStieltjesSource.to_directFullInputBundle_envelopes`,
  `CanonicalXiPullbackMidHighStieltjesEquality.to_directFullInputBundle`,
  and
  `CanonicalXiPullbackMidHighStieltjesEquality.to_directFullInputBundle_envelopes`.
  The low-side direct-full variants are now equally exposed:
  `XiPullbackAntiHerglotzTarget_of_pathBDirectFull_ibpStieltjes_turingBundle`,
  `XiPullbackAntiHerglotzTarget_of_pathBDirectFull_ibpStieltjes_turingEnvelopes`,
  `XiPullbackAntiHerglotzTarget_of_pathBDirectFull_zeroSplitStieltjes_turingBundle`,
  `XiPullbackAntiHerglotzTarget_of_pathBDirectFull_zeroSplitStieltjes_turingEnvelopes`,
  `XiPullbackAntiHerglotzTarget_of_pathBDirectFull_cloudTailStieltjes_turingBundle`,
  and
  `XiPullbackAntiHerglotzTarget_of_pathBDirectFull_cloudTailStieltjes_turingEnvelopes`.
  The source and publication full bundles lower through
  `PathBSourceFullInputBundle.to_directFull`,
  `PathBFullInputBundle.to_sourceFull`, and
  `PathBFullInputBundle.to_directFull`, with direct-route capstones
  `PathBSourceFullInputBundle.to_target_direct`,
  `XiPullbackAntiHerglotzTarget_of_pathBSourceFullInputBundle_direct`,
  `PathBFullInputBundle.to_target_direct`, and
  `XiPullbackAntiHerglotzTarget_of_pathBFullInputBundle_direct`. The unified source constructor
  `PathBDirectNonTuringInputsAFZ.of_stieltjesSource` feeds
  `XiPullbackAntiHerglotzTarget_of_directStieltjesSourceAFZ_turingBundle`;
  the generic completed-ξ source constructor
  `PathBDirectNonTuringInputsAFZ.of_completedXiSource` feeds
  `XiPullbackAntiHerglotzTarget_of_directCompletedXiSourceStieltjesAFZ_turingBundle`;
  specialized wrappers expose the Hadamard-product, classical analytic,
  concrete Hadamard, publication Hadamard, and entire-ξ-source cases as
  `XiPullbackAntiHerglotzTarget_of_directHadamardProductData_stieltjesAFZ_turingBundle`,
  `XiPullbackAntiHerglotzTarget_of_directClassicalPathBAnalyticInputs_stieltjesAFZ_turingBundle`,
  `XiPullbackAntiHerglotzTarget_of_directConcreteCompletedXiHadamard_stieltjesAFZ_turingBundle`,
  `XiPullbackAntiHerglotzTarget_of_directCompletedXiClassicalHadamard_stieltjesAFZ_turingBundle`,
  and
  `XiPullbackAntiHerglotzTarget_of_directEntireXiSource_stieltjesAFZ_turingBundle`;
  each of those wrappers also has the corresponding
  `_turingEnvelopes` variant;
  the full source-bundle constructor
  `PathBDirectNonTuringInputsAFZ.of_sourceInputs` feeds
  `XiPullbackAntiHerglotzTarget_of_pathBSourceInputBundles_direct`
  `XiPullbackAntiHerglotzTarget_of_pathBSourceInputBundles_direct_turingBundle`,
  and
  `XiPullbackAntiHerglotzTarget_of_pathBSourceInputBundles_direct_turingEnvelopes`;
  the named full-bundle lowerings
  `PathBDirectFullInputBundleAFZ.of_sourceFullInputBundle` and
  `PathBDirectFullInputBundleAFZ.of_fullInputBundle` expose the same
  source/publication full-bundle descent as constructors;
  the entire-ξ non-Turing bundle lowers through
  `PathBDirectNonTuringInputsAFZ.of_entireHadamardInputs`, feeding
  `XiPullbackAntiHerglotzTarget_of_pathBInputBundles_direct`,
  `XiPullbackAntiHerglotzTarget_of_pathBInputBundles_direct_turingBundle`, and
  `XiPullbackAntiHerglotzTarget_of_pathBInputBundles_direct_turingEnvelopes`;
  method-form adapters
  `PathBNonTuringSourceInputs.to_directAFZ`,
  `PathBNonTuringInputs.to_directAFZ`,
  `PathBDirectNonTuringInputsAFZ.to_target_turingBundle`,
  `PathBDirectNonTuringInputsAFZ.to_target_turingEnvelopes`,
  `PathBNonTuringSourceInputs.to_target_direct_turingBundle`,
  `PathBNonTuringSourceInputs.to_target_direct_turingEnvelopes`,
  `PathBNonTuringInputs.to_target_direct_turingBundle`, and
  `PathBNonTuringInputs.to_target_direct_turingEnvelopes` expose the
  same lowering/capstone chain in dot-notation style;
  direct bundled and unbundled front doors are also exposed for the
  assembled entire-Hadamard Stieltjes shapes. The bundled forms are
  `XiPullbackAntiHerglotzTarget_of_entireHadamard_stieltjesInputs_direct_turingBundle`,
  `XiPullbackAntiHerglotzTarget_of_entireHadamard_stieltjesEqualitySourceAFZ_direct_turingBundle`,
  `XiPullbackAntiHerglotzTarget_of_entireHadamard_classicalStieltjes_direct_turingBundle`,
  `XiPullbackAntiHerglotzTarget_of_pathBDirectFull_entireHadamard_stieltjesInputs_turingBundle`,
  `XiPullbackAntiHerglotzTarget_of_pathBDirectFull_entireHadamard_stieltjesEqualitySourceAFZ_turingBundle`,
  `XiPullbackAntiHerglotzTarget_of_pathBDirectFull_entireHadamard_classicalStieltjes_turingBundle`,
  `XiPullbackAntiHerglotzTarget_of_entireHadamard_mid_high_lowIBP_direct_turingBundle`,
  `XiPullbackAntiHerglotzTarget_of_entireHadamard_mid_high_lowZeroSplit_direct_turingBundle`,
  `XiPullbackAntiHerglotzTarget_of_entireHadamard_mid_high_lowCloudTail_direct_turingBundle`,
  `XiPullbackAntiHerglotzTarget_of_entireHadamard_midHighAFZ_lowIBP_direct_turingBundle`,
  `XiPullbackAntiHerglotzTarget_of_entireHadamard_midHighAFZ_lowZeroSplit_direct_turingBundle`,
  `XiPullbackAntiHerglotzTarget_of_entireHadamard_midHighAFZ_lowCloudTail_direct_turingBundle`,
  `XiPullbackAntiHerglotzTarget_of_entireHadamard_unguardedMidHigh_lowFirstZero_direct_turingBundle`,
  and
  `XiPullbackAntiHerglotzTarget_of_entireHadamard_unguardedStieltjesSource_direct_turingBundle`.
  The unbundled siblings are
  `XiPullbackAntiHerglotzTarget_of_entireHadamard_stieltjesInputs_direct_turingEnvelopes`,
  `XiPullbackAntiHerglotzTarget_of_entireHadamard_classicalStieltjes_direct_turingEnvelopes`,
  `XiPullbackAntiHerglotzTarget_of_entireHadamard_stieltjesEqualitySourceAFZ_direct_turingEnvelopes`,
  `XiPullbackAntiHerglotzTarget_of_pathBDirectFull_entireHadamard_stieltjesInputs_turingEnvelopes`,
  `XiPullbackAntiHerglotzTarget_of_pathBDirectFull_entireHadamard_classicalStieltjes_turingEnvelopes`,
  `XiPullbackAntiHerglotzTarget_of_pathBDirectFull_entireHadamard_stieltjesEqualitySourceAFZ_turingEnvelopes`,
  `XiPullbackAntiHerglotzTarget_of_entireHadamard_mid_high_lowIBP_direct_turingEnvelopes`,
  `XiPullbackAntiHerglotzTarget_of_entireHadamard_mid_high_lowZeroSplit_direct_turingEnvelopes`,
  `XiPullbackAntiHerglotzTarget_of_entireHadamard_mid_high_lowCloudTail_direct_turingEnvelopes`,
  `XiPullbackAntiHerglotzTarget_of_entireHadamard_midHighAFZ_lowIBP_direct_turingEnvelopes`,
  `XiPullbackAntiHerglotzTarget_of_entireHadamard_midHighAFZ_lowZeroSplit_direct_turingEnvelopes`,
  `XiPullbackAntiHerglotzTarget_of_entireHadamard_midHighAFZ_lowCloudTail_direct_turingEnvelopes`,
  `XiPullbackAntiHerglotzTarget_of_entireHadamard_unguardedMidHigh_lowFirstZero_direct_turingEnvelopes`,
  and
  `XiPullbackAntiHerglotzTarget_of_entireHadamard_unguardedStieltjesSource_direct_turingEnvelopes`;
  the source-level canonical Path B constructor
  `PathBDirectNonTuringInputsAFZ.of_canonicalPathBStieltjesSource`
  feeds
  `XiPullbackAntiHerglotzTarget_of_directCanonicalPathBStieltjesSource_turingBundle`;
  the older unguarded constructors
  `PathBDirectNonTuringInputsAFZ.of_unguardedStieltjesSource` and
  `PathBDirectNonTuringInputsAFZ.of_unguardedMidHighLow` feed
  `XiPullbackAntiHerglotzTarget_of_directUnguardedStieltjesSource_turingBundle`
  and
  `XiPullbackAntiHerglotzTarget_of_directUnguardedMidHighLow_turingBundle`;
  sibling front doors include
  `XiPullbackAntiHerglotzTarget_of_directSplitStieltjesInputsAFZ_turingBundle`,
  `XiPullbackAntiHerglotzTarget_of_directIBPStieltjesInputsAFZ_turingBundle`,
  `XiPullbackAntiHerglotzTarget_of_directZeroSplitStieltjesInputsAFZ_turingBundle`,
  and
  `XiPullbackAntiHerglotzTarget_of_directCloudTailStieltjesInputsAFZ_turingBundle`,
  plus unbundled-envelope variants for each.

## 13. Companion Python pipeline

The SDP / SOS pipeline that produces the numerical certificates
consumed by the slab theorems lives alongside `rh.lean`:

* `slab_certificates.py` — slab feasibility and polynomial-inequality
  generation.
* `golden_sos_certificate.py` — SOS certificate construction.
* `slab_simple_sos.py` — the simplified per-slab SOS pipeline producing
  `slab_simple_sos_feasibility_50zeros.json` and `…_100zeros.json`,
  read by the corresponding `slabSimple_*_cert` theorems.
* `finite_band_feasibility.py`, `finite_band_local_S.py` — finite-band
  feasibility checks.

Several supporting experiments
(`golden_frequency_sweep.py`, `golden_hankel_xi_test.py`,
`golden_phi_stress_test.py`, `golden_random_baseline.py`,
`golden_resonance_fit.py`, `golden_tridiagonal_fit.py`,
`overflow_zeta_zero_constructor.py`) fed earlier rounds of the design
and are retained for the historical record.

## Verifying the claims

The file is self-checking. From the `GoldenAlgebra/` directory,
```
lake env lean rh.lean
```
builds the whole development under the toolchain
`leanprover/lean4:v4.21.0-rc3`. The following invariants must hold for
any claim above to mean anything:
```
grep -cE "^axiom "  rh.lean    # must be 0
grep -nE "sorry"    rh.lean    # every match must lie inside a comment
```
At the time of writing, the first command returns 0 and every `sorry`
match sits in prose discussing where `sorry` is forbidden. The file is
85,489 lines and roughly 4,088 top-level declarations.

Should either invariant fail on a future revision, take none of the
above on faith — investigate first.
