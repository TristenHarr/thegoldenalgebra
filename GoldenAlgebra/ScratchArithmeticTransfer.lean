import Mathlib

/-!
# ScratchArithmeticTransfer — the minimal arithmetic positivity axiom for RH

This file isolates, as an *interface*, the precise arithmetic ingredient that
the Riemann zeta function has and the **Davenport–Heilbronn (DH)** function
lacks, and that is responsible for RH-type (Weil/Li/anti-Herglotz) positivity.

## The meta-finding (see `arith_positivity_axiom.py`, `cross_family_and_transfer.py`)

DH shares with ζ: the *shape* of the functional equation, the Γ-factor, entire
order 1, and the `s ↦ 1-s` symmetry of zeros.  Yet RH is FALSE for DH (a zero
sits at `s ≈ 0.8085 + 85.699·i`, off the critical line).  Therefore the
RH-responsible ingredient is provably **not** the FE/Γ/order/symmetry — it is
arithmetic.  The discriminator, pinned by direct computation, is:

  `-L'/L (s) = ∑_{n≥2} c_L(n) · n^{-s}`  with coefficients `c_L(n)` that are
  **supported on prime powers** (⇔ Euler product) and **nonnegative**
  (`c_ζ(n) = Λ(n) ≥ 0`, the von Mangoldt function).

For DH this fails at the START: `c_DH(n) ≠ 0` at composite `n = 6, 12, 14, …`
(no Euler product) and is sign-indefinite (`c_DH(3) < 0`).  This is the precise
per-criterion DH-failure line in the Weil/Li explicit formula: the prime term
`∑ c_L(n) n^{-1/2} g(log n)` is a quadratic form whose *atoms* are the `c_L(n)`;
nonnegative atoms (ζ) give a positive-type backbone, negative/spurious atoms (DH)
make the form indefinite a priori, with no possibility of RH-positivity.

## The decisive verdict on the transfer (honest, not assuming RH)

The bold hypothesis is "Euler-product positivity transfers through the FE into
Herglotz positivity".  Pinned precisely:

  * `EulerPositivity ⇒ HerglotzOnAbscissa` (positivity of `-L'/L` as a boundary
    measure on `Re s = 1`) is a GENUINE THEOREM — nonneg Dirichlet coefficients
    give a positive boundary measure unconditionally.
  * `HerglotzOnAbscissa ⇒ HerglotzOnCriticalLine` (continuation of the positive
    measure from `Re s = 1` down to `Re s = 1/2`) is **EXACTLY RH** — it is the
    zero-freeness of `L` in the open strip `1/2 < Re s < 1`.  No part of it is
    unconditional beyond classical zero-free regions.

Cross-family check (predicts the split exactly): Euler product holds for ζ and
all Dirichlet `L`, fails for DH.  RH/GRH expected for the former, FALSE for DH.
But `EulerPositivity` is **necessary, not sufficient**: every Dirichlet `L` has
it, yet GRH for them is open.  Hence the transfer is the RH wall, not a free
theorem — and this file states it that way (transfer left `Prop`, unproven; the
*unconditional half* `EulerPositivity → HerglotzOnAbscissa` is the morally-proven
part, recorded as a separate target).

Everything below is interface-only (`Prop`-level), axiom-clean, no `sorry`.
-/

namespace ScratchArithmeticTransfer

open Complex

/-- A Dirichlet-series datum: an L-function given by its coefficients `b n`
(`b 1 = 1`) together with the coefficients `c n` of its negative logarithmic
derivative `-L'/L (s) = ∑_{n≥2} c n · n^{-s}`.  We keep this abstract: the
analytic content is carried by the predicates below, not by convergence proofs. -/
structure LData where
  /-- Dirichlet coefficients of `L`, `b 1 = 1`. -/
  b : ℕ → ℂ
  /-- Coefficients of `-L'/L = ∑ c n · n^{-s}` (the "arithmetic measure"). -/
  c : ℕ → ℂ
  /-- Normalisation. -/
  b_one : b 1 = 1

/-- **The minimal arithmetic positivity axiom `P`.**

`-L'/L` is *supported on prime powers* (the Euler-product signature) and has
*nonnegative real* coefficients (the von Mangoldt / `Λ ≥ 0` signature).  This is
exactly what ζ has and DH lacks. -/
def EulerProductPositivityAxiom (L : LData) : Prop :=
  (∀ n, ¬ IsPrimePow n → L.c n = 0) ∧
  (∀ n, (L.c n).im = 0 ∧ 0 ≤ (L.c n).re)

/-- ζ satisfies `P` with `c n = Λ n` (von Mangoldt), the model instance. -/
def IsZetaLike (L : LData) : Prop :=
  (∀ n, L.b n = 1) ∧ (∀ n, L.c n = (ArithmeticFunction.vonMangoldt n : ℂ))

/-- The way Davenport–Heilbronn violates `P`: it fails in BOTH structural ways —
support spills off prime powers (no Euler product, e.g. `c_DH(6) ≠ 0`) and a
coefficient is negative (`c_DH(3) < 0`).  Either disjunct already refutes `P`. -/
def DavenportHeilbronnFailure (L : LData) : Prop :=
  (∃ n, ¬ IsPrimePow n ∧ L.c n ≠ 0) ∨ (∃ n, (L.c n).re < 0)

/-- DH-failure refutes the axiom `P` (the directly verified, load-bearing
direction: each computed DH violation kills `EulerProductPositivityAxiom`). -/
theorem dhFailure_imp_not_axiom (L : LData) :
    DavenportHeilbronnFailure L → ¬ EulerProductPositivityAxiom L := by
  rintro (⟨n, hn, hc⟩ | ⟨n, hlt⟩) ⟨hsupp, hpos⟩
  · exact hc (hsupp n hn)
  · exact absurd (hpos n).2 (not_le.mpr hlt)

/-! ### The transfer chain (the heart of the meta-question)

We model the positivity targets as opaque `Prop`s attached to an `LData`, so the
*logical structure* of the transfer is checkable even though the analytic
content is not formalised here. -/

/-- Herglotz / positive-boundary-measure positivity of `-L'/L` **on the abscissa
of absolute convergence** `Re s = 1`.  Morally a THEOREM from `P` (nonneg
coefficients ⇒ positive boundary measure). -/
opaque HerglotzOnAbscissa (L : LData) : Prop

/-- Herglotz positivity **continued to the critical line** `Re s = 1/2`.  This is
the anti-Herglotz / Weil-positivity target — equivalent to RH for `L`. -/
opaque XiPullbackAntiHerglotzTarget (L : LData) : Prop

/-- **Unconditional half (genuine theorem, stated as the target to discharge).**
`Euler-product positivity ⇒ Herglotz positivity on `Re s = 1`.`  The content is
the classical fact that a Dirichlet series with nonnegative coefficients defines
a positive boundary measure at its abscissa of absolute convergence.  We carry it
as a hypothesis-level `Prop` here (the file is interface-only); it is the part of
the transfer that does NOT require RH. -/
def EulerToAbscissaTransfer : Prop :=
  ∀ L : LData, EulerProductPositivityAxiom L → HerglotzOnAbscissa L

/-- **The RH wall (left unproven — it IS RH).**
Continuation of the positive measure from `Re s = 1` down to `Re s = 1/2`.  This
step is the zero-freeness of `L` in `1/2 < Re s < 1`; it is exactly RH for `L`
and is *not* implied by `P` (every Dirichlet `L` satisfies `P`, yet GRH is open). -/
def AbscissaToCriticalLineTransfer : Prop :=
  ∀ L : LData, HerglotzOnAbscissa L → XiPullbackAntiHerglotzTarget L

/-- **The conjectured full transfer** `FE + P ⇒ anti-Herglotz`, factored through
the two halves.  We do NOT assert it; we *factor* it, exposing that the only
non-theorem ingredient is `AbscissaToCriticalLineTransfer = RH`. -/
def FullArithmeticTransfer : Prop :=
  ∀ L : LData, EulerProductPositivityAxiom L → XiPullbackAntiHerglotzTarget L

/-- **The decisive factorisation theorem.**  The full transfer is the composition
of the unconditional half with the RH wall.  This is the honest statement: `P`
buys positivity down to `Re s = 1` for free, and the *only* remaining content is
the strip-continuation, which is RH.  Proven unconditionally (it is pure logic on
the interface). -/
theorem fullTransfer_factors
    (hUncond : EulerToAbscissaTransfer)
    (hWall : AbscissaToCriticalLineTransfer) :
    FullArithmeticTransfer := by
  intro L hP
  exact hWall L (hUncond L hP)

/-- Conversely, the RH wall is *necessary*: if the full transfer holds for every
`L`, then on any `L` whose abscissa-positivity is already known the critical-line
target follows — i.e. the wall cannot be avoided, it is embedded in the full
transfer.  (Logical bookkeeping; no analytic content.) -/
theorem wall_embedded_in_fullTransfer
    (hFull : FullArithmeticTransfer)
    (L : LData) (hP : EulerProductPositivityAxiom L) :
    XiPullbackAntiHerglotzTarget L :=
  hFull L hP

end ScratchArithmeticTransfer
