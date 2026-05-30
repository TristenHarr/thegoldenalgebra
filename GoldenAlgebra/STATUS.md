# STATUS — Dependency Audit & Battle Map

Machine-checked status of `GoldenAlgebra/GoldenAlgebra.lean` (~25,500 lines).
This file exists so that the project cannot fool itself: it records what is
*actually* proven, what is *assumed*, and where the real obstruction sits.

Last updated: 2026-05-21.

---

## How to reproduce this audit

```
cd GoldenAlgebra
lake build                 # compiles GoldenAlgebra.lean against Mathlib
lake env lean Audit.lean   # prints `#print axioms` for the load-bearing theorems
```

`Audit.lean` is the reproducible audit script. `#print axioms D` lists every
axiom declaration `D` transitively depends on. Re-run it after any change.

Toolchain: `leanprover/lean4:v4.21.0-rc3`, Mathlib pinned in `lake-manifest.json`.

---

## Headline (read this first)

1. **The file is sound.** It compiles with no `sorry` in active code, and
   `#print axioms` shows no `sorryAx` in any audited theorem. Every theorem
   in it is a *true* theorem. The file does **not** assert a false statement.

2. **The file does NOT contain an unconditional proof of the Riemann
   Hypothesis**, and no audited theorem claims to. Every RH-shaped result is
   an *implication* `(hypothesis) → critical line`.

3. **A clean `#print axioms` does not mean progress.** This is the central
   pitfall. See the two-axis classification below.

4. Adding more `structure`s of the form `XZetaSource extends YZetaSource`
   with `Prop` fields does not change items 2–3. It has been done ~150 times.

---

## The two-axis classification

A theorem must be judged on **two independent axes**. Judging on only the
first is how a project convinces itself it is winning when it is standing
still.

### Axis A — Axiom debt (what `#print axioms` measures)

| Tag | Meaning |
|-----|---------|
| 🟢 GREEN  | depends only on Lean built-ins `propext`, `Classical.choice`, `Quot.sound` |
| 🟠 ORANGE | depends on a GoldenAlgebra `axiom` (analytic debt) |
| 🔴 RED    | depends on `sorryAx` (an admitted hole) — **none exist in this file** |

### Axis B — Hypothesis strength (requires reading the *statement*)

`#print axioms` is **blind to hypotheses**. A theorem

```lean
theorem foo (h : RiemannHypothesis) : RiemannHypothesis := h
```

prints 🟢 GREEN on Axis A — zero axioms — yet proves nothing. The hard
content is the *argument* `h`, not an axiom.

| Tag | Meaning |
|-----|---------|
| ⭐ UNCONDITIONAL | the conclusion holds outright; no RH-strength hypothesis |
| ⚠️ CONDITIONAL   | shape is `(S : SomeStructure) → RH`, where inhabiting `SomeStructure` is **at least as hard as RH** |

**A result is real progress only if it is GREEN *and* UNCONDITIONAL** (or
GREEN + CONDITIONAL on something *strictly easier* than RH — none of the
RH-conditional theorems here are).

---

## Axiom inventory (2 remaining)

Down from 3: `council_C077_functional_equation_axiom` was discharged to a
theorem on 2026-05-21 (see change log).

| # | Axiom | Status | Honest assessment |
|---|-------|--------|-------------------|
| 1 | `centralBinomSeries_closed_form_lambdaG1` (`:2188`) | analytic debt | A true classical identity ((1−z)^(−1/2) generalized binomial series). Not RH-related. Discharge needs Mathlib's convergent generalized-binomial expansion. Honest to assume; should be a theorem eventually. |
| 2 | `harmonic_cotangent_zeta_identity` (`:2269`) | analytic debt | A true classical identity (polygamma/cotangent reflection vs ζ values). Not RH-related. Discharge needs Mathlib polygamma reflection theory. Honest to assume; should be a theorem eventually. |

Neither axiom is RH-strength, and **neither appears in any audited flagship
RH theorem** — the RH tower does not even depend on them. They are debts of
the Golden-Algebra *identity* layer, not the RH layer.

---

## Flagship theorem classification

From `lake env lean Audit.lean` (2026-05-21):

| Theorem | Axis A | Axis B | Notes |
|---------|--------|--------|-------|
| `T_add_J_eq_one_half` | 🟢 | ⭐ | genuine unconditional theorem |
| `council_C077_functional_equation` | 🟢 | ⭐ | **discharged this session** — real theorem |
| `council_C078_critical_symmetry` | 🟢 | ⭐ | was 🟠; upgraded by the C077 discharge |
| `GoldenHPConjecture_implies_critical_line` | 🟢 | ⚠️ | hypothesis = a Hilbert–Pólya operator capturing all zeros — RH-hard |
| `GoldenHPConjecture_for_zeta_implies_critical_line` | 🟢 | ⚠️ | same, specialised to ζ |
| `LocalGlobalZetaSource_implies_zeta_critical_line` | 🟢 | ⚠️ | hypothesis bundles positivity/duality/Euler-Hadamard `Prop`s |
| `BoundedHPBridge_implies_zeta_critical_line` | 🟢 | ⚠️ | hypothesis is an RH-strength bridge structure |
| `WeilPositivityPackage_implies_zeta_critical_line` | 🟢 | ⚠️ | hypothesis bundles Weil positivity |
| `FinalRHProofPackage_implies_zeta_critical_line` | 🟢 | ⚠️ | hypothesis contains `ClassicalWeilPositivityCriterion` |
| `GOLDENALGEBRA_FINAL_RH_CONDITIONAL` | 🟢 | ⚠️ | the file's own comment calls its core "the classical Weil positivity / **RH-equivalent** step" |
| `one_shot_RH_from_explicit_formula_and_weil_positivity` | 🟢 | ⚠️ | hypothesis = explicit formula + Weil positivity package |
| `diamond_RH_from_Xi_HP_approximation` | 🟢 | ⚠️ | hypothesis = an Xi/HP approximation package |

**Every RH-shaped theorem is 🟢 + ⚠️.** Green on Axis A (no hidden axioms,
no `sorry` — genuinely good), but ⚠️ on Axis B: the hypothesis is a
structure whose `Prop` fields are exactly the unsolved mathematics. To
*use* any of these theorems to prove RH you must first construct a term of
the hypothesis structure — and that construction is RH itself (or harder).

This is not a flaw to be patched by a cleverer structure. It is a fact
about the problem: the file has correctly *reduced RH to RH*.

---

## What is genuinely proven (UNCONDITIONAL, real)

- Golden-Algebra core identities (`T_add_J_eq_one_half`, determinant
  identities, norm/pitch lemmas, etc.) — genuine finite algebra.
- `council_C077_functional_equation` — a symmetric kernel `Ξ` exists with
  `Ξ(s)=Ξ(1−s)` and strip zero-set `= ` nontrivial ζ-zeros.
- `council_C078_critical_symmetry` — zero-set symmetric under `s ↦ 1−s`.
- A large library of *forgetful reductions* between candidate-operator
  structures: true statements of the form "structure X refines structure Y".
  These are correct and sometimes useful for organising the search — but
  they are reductions *between hypotheses*, not steps toward discharging one.

## What is NOT proven

- The Riemann Hypothesis, conditionally or otherwise, beyond `(RH-strength
  hypothesis) → RH`.
- Any construction of a Hilbert–Pólya operator, a `LocalGlobalZetaSource`,
  a `WeilPositivityPackage`, or a `ClassicalWeilPositivityCriterion`. No
  term of any RH-strength structure is ever built in the file.
- Weil positivity, the explicit formula as a Lefschetz trace, or any
  arithmetic cohomology of `Spec ℤ`.

---

## The discipline rule

A new section earns its place **only** if it does one of:

1. **Removes an axiom** (`#print axioms` debt strictly decreases), or
2. **Replaces a `Prop` placeholder with actual data** (a real definition,
   not a named hole), or
3. **Constructs a real term** of a previously-only-assumed structure
   (even a toy/finite-dimensional one).

A new `theorem (S : NewStructure) → RH` is **not** progress and should not
be added. The honest metric is: *number of axioms* (now 2) and *number of
`Prop` placeholder fields* (large — the real backlog). Both should only
ever go down.

---

## Change log

### 2026-05-21 — C077 discharged (axiom → theorem)

- `axiom council_C077_functional_equation_axiom` → `theorem
  council_C077_functional_equation` (with a compatibility alias keeping the
  old name resolving, now also a theorem).
- Witness: `Ξ(s) := ζ(s)·ζ(1−s)`. Symmetry by `mul_comm`; strip zero-set
  via Mathlib `riemannZeta_one_sub` + non-vanishing of the
  functional-equation factor on `0 < Re ρ < 1`.
- Scope honesty: the statement does not require `Ξ` entire (`ζ(s)·ζ(1−s)`
  has poles at `0,1`); only the strip identity + symmetry are claimed and
  proven.
- Effect: axiom count 3 → 2; `council_C078_critical_symmetry` upgraded
  🟠 → 🟢. Verified by `lake build` + `lake env lean Audit.lean`.
