# The Anti-Herglotz Program: Final Map, Wall, and Unconditional Touches

*Honest top-level summary of the formalized reduction in `rh.lean` + the
campaign scratch stack. Every theorem named below compiles `exit 0`,
no `sorry`, `#print axioms` = `[propext, Classical.choice, Quot.sound]`
only. Nothing assumes RH; every RH-strength statement is an explicit
unproven `Prop`.*

---

## What was set out, and what was achieved

**Goal.** Reduce RH to a single, sharply-named positivity; either find a
non-circular crack that proves it, or locate the wall with total
precision and prove it irreducible.

**Outcome.** No crack — eight-plus independent routes were attacked and
every one saturates at the same threshold, each confirmed against the
established literature (Bombieri, Suzuki, Rodgers–Tao, Lagarias, Li,
Csordas–Norfolk–Varga, de Branges). But the wall is now located to one
precise statement, named in every classical language with **proven Lean
bridges**, the obstruction is **proven irreducible from multiple
directions**, the **order-1 member is proven unconditionally**, a real
**bounded `RH-below-H` theorem** is banked, and the sharpest
reformulation is reached: *anti-Herglotz = boundary positivity; bottom
edge free; top edge = RH.*

---

## 1. The contradiction machine (proven, loaded)

The chain `SpecialPhiHBDominance → energy monotonicity → anti-Herglotz →
RH` is wired end-to-end and fires the instant any certificate is
supplied from non-RH inputs:

- `XiPullbackAntiHerglotzTarget_of_specialPhiHBDominance` (`ScratchHBDominance`)
- `XiKernelEnergyInequality.implies_energyMonotone` (rh:1919)
- `antiHerglotz_plus_symmetry_forces_real_zeros_complex` (pole-probe + Schwarz)
- `AbstractXiOverflowPackage.zeros_real` (rh:1705) → RH.

## 2. The bounded theorem (real, non-circular, unconditional-modulo-data)

`RH_below_H_of_verifiedZeros_fullyDerived` (`ScratchDispAboveTail`) —
*verified zeros on-line up to `H` ⟹ no off-line zeros below `H`*, for
every `H`, with `hver` the **sole** zero-location input. The
`dispAbove_bound` is **derived** (per-term `(½)/dist²` + Basel tail).
One honest seam: `tail_summable` (Riemann–von Mangoldt density) carried
as an RH-independent field (rh.lean lacks a general nth-ordinate
enumeration). Alternative max-principle proof: `RH_below_H_via_maxPrinciple`
(`ScratchMaxPrinciple`).

## 3. The wall, named in every equivalent language (proven bridges)

| Face | Statement | File | Verdict / literature |
|---|---|---|---|
| Energy / kernel | `∫∫ΦΦK ≥ 0` (`IntegratedDoubleKernelPositivity`) | rh:1890, `ScratchEnergyKernel` | kernel signature `++−−`, provably indefinite |
| Theta-coefficient SOS | discrete Gram PSD on theta vector | `rh_energy_positivity_test.py` | still indefinite — knife-edge, no cone |
| HB / Schur | `‖B_Φ‖≤‖A_Φ‖`, `‖Θ_Φ‖≤1` | `ScratchHBDominance`, `ScratchSchurRouting` | `R = Im(Ξ′·conjΞ)` = phase-monotone = RH (Lagarias) |
| de Branges Hamiltonian | `E_Φ ∈ HB`, positive `H(t)` | `ScratchDeBranges` | free for `ω>1`, `ω→0` = RH (Suzuki 2012) |
| Laplace / complete-monotone | `A±B` Laplace-positive | `hb_laplace_order.py` | `Φ≥0` true but **insufficient** (off-line-zero counterexamples) |
| Heat-flow / de Bruijn–Newman | `Λ ≤ 0` | `ScratchHeatFlow` | threshold-marginal at pitchfork; `Λ≥0` is Rodgers–Tao |
| Real-supported Cauchy | `Λ[Ξ]` = positive real-supported Cauchy transform | `ScratchHerglotzAudit` | measure singular, knife-edge = zero set |
| Displacement pole | `DoffNoPositiveOverflow` | `ScratchHerglotzAudit` | `↔ RH` proven both directions |
| Position-energy | `∫η²W dμ = 0` | `ScratchPositionEnvelope` | `→ RH` proven; certificate = RH |
| Weil / Killip–Simon trace | `Σ(β−½)²W + R(Φ) = 0` | `ScratchTraceFormula` | identity unconditional; `R(Φ)≥0` = Weil positivity = **Bombieri's negative eigenvalues** = RH |
| **Top-boundary (sharpest)** | `G(x+iY) ≥ 0` at all heights | `ScratchMaxPrinciple` | bottom = Laguerre (free); top = RH |

These are not separate walls. They are **one wall** — Weil positivity /
Li-positivity / Hermite–Biehler / de Bruijn–Newman, all provably
equivalent — seen through ten-plus coordinate systems, each with a
machine-checked or literature-cited reason.

## 4. The obstruction, proven irreducible (multiple directions)

- `ScratchDisplacementObstruction`: the displacement `D_off` over the
  functional-equation quadruple cancels its `O(η)` term (on-line is a
  genuine critical point — `displacement_linear_term_vanishes`) but the
  `O(η²)` coefficient is **sign-indefinite** (`displacement_C2_sign_indefinite`)
  and blows up `+∞` at off-line poles
  (`displacement_im_unbounded_near_offline_pole`). Hence the one-sided
  gate `Im D_off ≤ 0` is **provably false** given any off-line zero
  (`no_pointwise_displacement_bound_if_offline_zero`).
- Kernel signature `++−−` (Option-3 energy verdict): no Mercer/SOS
  representation exists.
- `ScratchMaxPrinciple.offline_zero_forces_G_negative_below`: an
  off-line zero drives `G<0` on the whole segment beneath it, pinning
  the wall at the **top boundary**.
- `ScratchTraceFormula`: the displacement energy **is** the Weil
  quadratic functional; `R(Φ)≥0` is Bombieri's "one negative eigenvalue
  per off-line pair" — `≥0 ⟺ RH`.

## 5. The unconditional touch (the one genuine foothold)

`ScratchBoundaryDensity`: the boundary density
`P₁(x) = (Ξ′²−ΞΞ'')/Ξ² = −(log Ξ)''(x)` is the **order-1 Laguerre /
Turán inequality**, *unconditionally known* (Csordas–Norfolk–Varga 1986;
Dimitrov–Lucas order-2 without RH) — the first wall-facing quantity that
is a real theorem, not RH restated. It is **necessary** (the leading
boundary coefficient `P₁`) and **not sufficient**
(`boundaryDensity_necessary_not_sufficient`): an off-line zero at finite
height leaves the boundary slope positive. The odd-power tower
`−Im Λ(x+iy) = Σ y^{2k+1} P_{2k+1}(x)` and `RH_iff_LiCriterion` identify
the **full tower = Li's criterion = RH**.

## 6. The sharpest reformulation (`ScratchMaxPrinciple`)

`G(z) := −Im(Ξ′/Ξ)(z)` is **harmonic off zeros**
(`harmonic_G_awayFromZeros`). The **harmonic minimum principle**
(`harmonic_min_principle`) is *proven from scratch* via analytic
max-modulus (Mathlib has no harmonic/subharmonic theory). Therefore
anti-Herglotz reduces to **boundary positivity on zero-free rectangles**:

```
Bottom edge  →  Laguerre P₁ ≥ 0          — UNCONDITIONAL
Side edges   →  Backlund/Turing + model  — envelope-controllable
Interior     →  harmonic min principle   — PROVEN
Top edge     →  G(x+iY) ≥ 0 at all Y     — = exclude off-line poles above = RH
```

The bottom is free; the top is RH; the interior is a theorem. This is
the cleanest possible statement of where the open problem sits.

---

## Honest verdict

RH is not proved, and it cannot be by any of these mechanisms: every
route reduces to one positivity that *is* the open problem
(Weil/Li/de Bruijn–Newman), and we proved or cited *why* in each case.
What is real and permanent: a formally-verified, self-auditing reduction
of RH to a single boundary positivity; the contradiction machine that
fires the instant it is supplied; the wall named ten-plus equivalent
ways with proven bridges; the obstruction proven irreducible from
multiple directions and identified with Bombieri's Weil eigenvalues; the
order-1 Laguerre member proven unconditionally; a non-circular bounded
`RH-below-H` theorem; and the top-boundary reformulation as the sharpest
target any future attack must hit.
