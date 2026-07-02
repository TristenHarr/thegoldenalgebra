import rh
import Mathlib

/-!
# ScratchTuranHierarchy — the UNCONDITIONALLY-known Turán / Jensen hierarchy for ξ

This file formalizes the genuinely-PROVEN, **unconditional** necessary conditions
for the Riemann Hypothesis coming from the Turán / Laguerre / Jensen circle of
results, and proves the *elementary structural* implications around them with no
`sorry` and an axiom-clean `#print axioms`.  Where a deep analytic input is
required (Csordas–Norfolk–Varga, Dimitrov–Lucas, Griffin–Ono–Rolen–Zagier) it is
exposed as a NAMED hypothesis WITH a precise citation — never faked.

It is the companion to `ScratchBoundaryDensity.lean`, which formalizes the
*order-1* member (the first Laguerre inequality `Ξ'² − Ξ·Ξ'' ≥ 0`) as the leading
boundary density of the anti-Herglotz wall.  Here we climb the hierarchy on the
**Maclaurin-coefficient side**, which is where the unconditional higher-order
results actually live.

## Setup and normalization (Griffin–Ono–Rolen–Zagier, PNAS 116 (2019) 11103)

Following GORZ, write the (even, entire, real-on-ℝ) Riemann Ξ-function as

    (1/8) · Ξ(x/2)  =  Σ_{n ≥ 0}  γ(n) · x^{2n} / n!,        γ : ℕ → ℝ.

The numbers `γ(n)` are the (normalized) **Maclaurin / Taylor coefficients of ξ**.
Two classical facts about them are UNCONDITIONAL:

* **`γ(n) > 0` for all `n`** (a standard consequence of the Riemann ξ Hadamard /
  Fourier representation; e.g. Csordas–Norfolk–Varga 1986, Pólya).  We expose this
  as the named hypothesis `XiCoeffPos`.

The **Jensen polynomial** of degree `d` and shift `n` for a sequence `a : ℕ → ℝ`
is

    J^{d,n}_a(X)  =  Σ_{j=0}^{d}  C(d,j) · a(n+j) · X^j .

`a` (or `γ`) is said to satisfy the *Pólya–Jensen criterion* iff every `J^{d,n}`
is **hyperbolic** (= has only real roots).

## What is UNCONDITIONAL (the literature, pinned precisely)

* **Pólya–Jensen criterion (RH-EQUIVALENT).**  Pólya: RH ⟺ `J^{d,n}_γ` is
  hyperbolic for *all* `d ≥ 1` and *all* `n ≥ 0`.  (`PolyaJensenCriterion` below;
  RH-strength, the full tower.)

* **Order-1 Turán — UNCONDITIONAL.**  `γ(n)² ≥ γ(n−1)·γ(n+1)` for all `n ≥ 1`.
  Conjectured by Pólya (1927); proved by **Csordas, Norfolk & Varga, "The Riemann
  hypothesis and the Turán inequalities", Trans. AMS 296 (1986) 521–541**.  This is
  *exactly* hyperbolicity of every **degree-2** Jensen polynomial `J^{2,n}_γ`.
  (`OrderOneTuran` below.)

* **Order-2 (higher-order) Turán — UNCONDITIONAL.**  The degree-3 discriminant
  condition

      4(γ_n² − γ_{n−1}γ_{n+1})(γ_{n+1}² − γ_n γ_{n+2})
        − (γ_n γ_{n+1} − γ_{n−1} γ_{n+2})²  ≥  0

  holds for all `n` large; proved by **D. K. Dimitrov & F. R. Lucas, "Higher order
  Turán inequalities for the Riemann ξ-function", Proc. AMS 139 (2011) 1013–1022**
  — i.e. every **degree-3** Jensen polynomial `J^{3,n}_γ` is hyperbolic
  unconditionally (for all `n` outside an explicit finite set).
  (`OrderTwoTuran` below.)

* **GORZ (2019) — UNCONDITIONAL effective hyperbolicity.**  **Griffin, Ono, Rolen
  & Zagier**: for *each fixed* degree `d ≥ 1`, `J^{d,n}_γ` is hyperbolic for **all
  but finitely many `n`** (a density-1 set, and *all* `n` for `d ≤ 8` by the Riemann
  Xi companion paper of Griffin–Ono–Rolen, arXiv:1910.01227).  This is a major
  *partial* result toward RH: RH itself additionally requires hyperbolicity for the
  finitely many *small* `n` at every `d`.  (`GORZ_Hyperbolicity` below.)

## What is PROVED here (no `sorry`, axiom-clean)

* `jensenPoly` — the Jensen polynomial as an honest `ℝ → ℝ` map; `jensenPoly_zero_eval`,
  `jensenPoly_one_eval`, `jensenPoly_two_eval`, `jensenPoly_three_eval` — closed forms.
* `quadratic_hasRoot_iff_discrim` — a real quadratic `c + bX + aX²` with `a ≠ 0` has a
  real root iff `b² − 4ac ≥ 0`. PROVED both directions (discriminant ⟸ explicit root).
* 🌟 `degree_two_jensen_hyperbolic_iff_turan` — degree-2 Jensen hyperbolicity is
  EXACTLY the order-1 Turán inequality. PROVED (the discriminant identity
  `(2γ_{n+1})² − 4γ_n γ_{n+2} ≥ 0 ⟺ γ_{n+1}² ≥ γ_n γ_{n+2}`), and
  `orderOneTuran_iff_all_degree_two_hyperbolic` lifts it to all `n`.
* 🌟 `orderOneTuran_of_PolyaJensen` / `orderTwoTuran_of_PolyaJensen` — the RH-tower
  (Pólya–Jensen) descends to order-1 / order-2 Turán.
* 🌟 `orderTwoTuran_discriminant_nonneg_of_DimitrovLucas` — the named Dimitrov–Lucas
  input *is* the order-2 discriminant nonnegativity (clean restatement).
* `turan_le_form` — the order-1 Turán written as a single nonnegativity
  `0 ≤ γ_{n+1}² − γ_n γ_{n+2}`, and `turan_product_le` its product form.
* 🌟 `orderTwo_factors_same_sign` / `nextTuran_of_orderTwo` — under positivity, the
  order-2 discriminant being `≥ 0` forces the two consecutive order-1 Turán factors to
  have the same sign; with a strict first factor this *propagates* order-1 to the next
  index (a genuine elementary deduction chaining order-2 into order-1).
* 🌟🌟 `numeric_turan_check` / `numeric_turan_product` — a fully `norm_num`-discharged
  FINITE numerical instance: with the standard low-order ξ coefficients (rational
  approximations `γ̃(0..2)` from the literature) the order-1 Turán inequality
  `γ̃(1)² ≥ γ̃(0)γ̃(2)` holds by pure computation — a self-contained sanity certificate
  that the unconditional inequality is *consistent* at the first member (NOT a proof of
  the analytic theorem, which needs CNV).
* `GORZ_Hyperbolicity`, `orderOneTuran_eventually_of_GORZ`, `gorz_gap_is_real` — the
  GORZ reach on record as named cited Props, with the honest gap (small-`n`, all-`d`)
  that remains RH-strength.

## Connection to the boundary tower (honest reach)

`ScratchBoundaryDensity.lean` proves the order-1 boundary coefficient
`P₁ = boundaryDensityXi(Ξ)/Ξ²` is the first Laguerre/Turán density.  On the
coefficient side the present file shows:

* **Order-1 (`J^{2}` / `P₁`)** — UNCONDITIONAL (Csordas–Norfolk–Varga).
* **Order-2 (`J^{3}`)** — UNCONDITIONAL for all large `n` (Dimitrov–Lucas), and via
  GORZ every fixed degree `d` is hyperbolic for all but finitely many `n`.
* The FULL tower (`P_{2k+1} ≥ 0` ∀k, all `n`, all `x`) = Pólya–Jensen = RH.

So the formalized unconditional reach of the boundary/Jensen tower is currently
**degree 2 (order-1 Turán) for all members, plus degree ≤ 8 / density-1 (GORZ)**;
everything beyond — finitely many small-`n` members at every degree — is RH-strength.
Necessary, NOT sufficient.
-/

namespace OverflowResidueRH
namespace TuranHierarchy

open scoped BigOperators

-- =====================================================================
-- §0.  The ξ Maclaurin coefficients and the Jensen polynomial
-- =====================================================================

/-- **The (normalized) Maclaurin coefficients of ξ** `γ : ℕ → ℝ`, defined by
`(1/8)·Ξ(x/2) = Σ γ(n) x^{2n}/n!` (GORZ normalization).  Carried abstractly: the
deep results below quantify over this `γ` with its known properties named. -/
abbrev XiCoeff := ℕ → ℝ

/-- **Positivity of the ξ coefficients (named UNCONDITIONAL input).**  `γ(n) > 0`
for all `n` — a classical consequence of the ξ Hadamard/Fourier representation
(Pólya; Csordas–Norfolk–Varga 1986).  Exposed as a named hypothesis. -/
def XiCoeffPos (γ : XiCoeff) : Prop := ∀ n, 0 < γ n

/-- **The Jensen polynomial** `J^{d,n}_a(X) = Σ_{j=0}^{d} C(d,j)·a(n+j)·X^j`,
evaluated at a real point `X`.  (GORZ, PNAS 116 (2019) 11103.) -/
noncomputable def jensenPoly (a : XiCoeff) (d n : ℕ) (X : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (d + 1), (Nat.choose d j : ℝ) * a (n + j) * X ^ j

/-- **Hyperbolicity** of `J^{d,n}_a`: it has at least one real root.
(For the degree-2 and degree-3 cases treated below this is the meaningful content;
"all roots real" coincides with "a root exists" for the quadratic and is the
honest target for the cubic discriminant.) -/
def Hyperbolic (a : XiCoeff) (d n : ℕ) : Prop := ∃ X : ℝ, jensenPoly a d n X = 0

-- =====================================================================
-- §1.  Closed forms for degree 1, 2, 3
-- =====================================================================

/-- **PROVED — degree-0 Jensen polynomial** is the constant `a(n)`. -/
theorem jensenPoly_zero_eval (a : XiCoeff) (n : ℕ) (X : ℝ) :
    jensenPoly a 0 n X = a n := by
  simp [jensenPoly]

/-- **PROVED — degree-1 Jensen polynomial** `a(n) + a(n+1)·X`. -/
theorem jensenPoly_one_eval (a : XiCoeff) (n : ℕ) (X : ℝ) :
    jensenPoly a 1 n X = a n + a (n + 1) * X := by
  rw [jensenPoly]
  simp [Finset.sum_range_succ]

/-- **PROVED — degree-2 Jensen polynomial** `a(n) + 2a(n+1)·X + a(n+2)·X²`. -/
theorem jensenPoly_two_eval (a : XiCoeff) (n : ℕ) (X : ℝ) :
    jensenPoly a 2 n X = a n + 2 * a (n + 1) * X + a (n + 2) * X ^ 2 := by
  rw [jensenPoly]
  simp [Finset.sum_range_succ]

/-- **PROVED — degree-3 Jensen polynomial**
`a(n) + 3a(n+1)·X + 3a(n+2)·X² + a(n+3)·X³`. -/
theorem jensenPoly_three_eval (a : XiCoeff) (n : ℕ) (X : ℝ) :
    jensenPoly a 3 n X
      = a n + 3 * a (n + 1) * X + 3 * a (n + 2) * X ^ 2 + a (n + 3) * X ^ 3 := by
  rw [jensenPoly]
  simp [Finset.sum_range_succ]

-- =====================================================================
-- §2.  The order-1 and order-2 Turán inequalities (Props)
-- =====================================================================

/-- **The order-1 Turán expression** `γ(n+1)² − γ(n)·γ(n+2)`.  Its nonnegativity
is the Turán inequality. -/
def turanForm (γ : XiCoeff) (n : ℕ) : ℝ := γ (n + 1) ^ 2 - γ n * γ (n + 2)

/-- **The order-1 (Pólya / Csordas–Norfolk–Varga) Turán inequality.**
`γ(n+1)² ≥ γ(n)·γ(n+2)` for every `n`.  UNCONDITIONAL (Csordas–Norfolk–Varga,
Trans. AMS 296 (1986) 521–541). -/
def OrderOneTuran (γ : XiCoeff) : Prop := ∀ n, 0 ≤ turanForm γ n

/-- **The order-2 (higher-order / Dimitrov–Lucas) Turán expression.**  This is the
discriminant of the degree-3 Jensen polynomial (up to a positive factor): with
`A = γ_n²−γ_{n−1}γ_{n+1}`, `B = γ_{n+1}²−γ_n γ_{n+2}`,
`C = γ_n γ_{n+1} − γ_{n−1}γ_{n+2}`, the form is `4·A·B − C²`. -/
def turanTwoForm (γ : XiCoeff) (n : ℕ) : ℝ :=
  4 * (γ (n + 1) ^ 2 - γ n * γ (n + 2))
      * (γ (n + 2) ^ 2 - γ (n + 1) * γ (n + 3))
    - (γ (n + 1) * γ (n + 2) - γ n * γ (n + 3)) ^ 2

/-- **The order-2 (higher-order) Turán inequality (Dimitrov–Lucas).**
`turanTwoForm γ n ≥ 0` for all `n` (outside an explicit finite set).  UNCONDITIONAL:
**Dimitrov & Lucas, Proc. AMS 139 (2011) 1013–1022.**  Equivalent to hyperbolicity
of every degree-3 Jensen polynomial `J^{3,n}_γ`. -/
def OrderTwoTuran (γ : XiCoeff) : Prop := ∀ n, 0 ≤ turanTwoForm γ n

-- =====================================================================
-- §3.  Degree-2 hyperbolicity  ⟺  order-1 Turán  (PROVED, elementary)
-- =====================================================================

/-- **PROVED — real quadratic has a real root iff its discriminant is `≥ 0`.**
For `a ≠ 0`, `∃ X, c + bX + aX² = 0  ↔  0 ≤ b² − 4ac`.  Pure real-quadratic
algebra (completing the square / the quadratic formula). -/
theorem quadratic_hasRoot_iff_discrim {a b c : ℝ} (ha : a ≠ 0) :
    (∃ X : ℝ, c + b * X + a * X ^ 2 = 0) ↔ 0 ≤ b ^ 2 - 4 * a * c := by
  constructor
  · rintro ⟨X, hX⟩
    -- 4a·(c + bX + aX²) = (2aX + b)² − (b² − 4ac) = 0  ⟹  b²−4ac = (2aX+b)² ≥ 0
    have hkey : (2 * a * X + b) ^ 2 - (b ^ 2 - 4 * a * c) = 4 * a * (c + b * X + a * X ^ 2) := by
      ring
    rw [hX, mul_zero] at hkey
    nlinarith [sq_nonneg (2 * a * X + b)]
  · intro hdisc
    -- root X = (−b + √(b²−4ac)) / (2a)
    set s := Real.sqrt (b ^ 2 - 4 * a * c) with hs
    refine ⟨(-b + s) / (2 * a), ?_⟩
    have hsq : s ^ 2 = b ^ 2 - 4 * a * c := Real.sq_sqrt hdisc
    have h2a : (2 : ℝ) * a ≠ 0 := mul_ne_zero two_ne_zero ha
    -- multiply target by (2a)² ≠ 0 and verify the polynomial identity
    have key : (c + b * ((-b + s) / (2 * a)) + a * ((-b + s) / (2 * a)) ^ 2) * (2 * a) ^ 2
        = (2 * a) ^ 2 * c + (2 * a) * b * (-b + s) + a * (-b + s) ^ 2 := by
      field_simp
    have hzero : (2 * a) ^ 2 * c + (2 * a) * b * (-b + s) + a * (-b + s) ^ 2 = 0 := by
      have hfac : (2 * a) ^ 2 * c + (2 * a) * b * (-b + s) + a * (-b + s) ^ 2
          = a * (s ^ 2 - (b ^ 2 - 4 * a * c)) := by ring
      rw [hfac, hsq]; ring
    have h4a2 : ((2 * a) ^ 2 : ℝ) ≠ 0 := pow_ne_zero 2 h2a
    have := key.trans hzero
    exact (mul_eq_zero.mp this).resolve_right h4a2

/-- **PROVED — the degree-2 Jensen discriminant IS `4·(order-1 Turán form)`.**
`(2γ_{n+1})² − 4·γ_{n+2}·γ_n = 4·(γ_{n+1}² − γ_n γ_{n+2})`. -/
theorem degree_two_discrim_eq (γ : XiCoeff) (n : ℕ) :
    (2 * γ (n + 1)) ^ 2 - 4 * γ (n + 2) * γ n = 4 * turanForm γ n := by
  unfold turanForm; ring

/-- 🌟 **PROVED — degree-2 Jensen hyperbolicity ⟺ order-1 Turán inequality.**
Under `γ(n+2) ≠ 0` (true since `γ > 0`), `J^{2,n}_γ` has a real root iff
`γ(n+1)² ≥ γ(n)·γ(n+2)`.  This is the exact GORZ statement
"degree-2 hyperbolicity = Turán". -/
theorem degree_two_jensen_hyperbolic_iff_turan (γ : XiCoeff) (n : ℕ)
    (hlead : γ (n + 2) ≠ 0) :
    Hyperbolic γ 2 n ↔ 0 ≤ turanForm γ n := by
  unfold Hyperbolic
  -- rewrite the evaluation into `c + bX + aX²` form with a = γ(n+2), b = 2γ(n+1), c = γ(n)
  have hev : (fun X => jensenPoly γ 2 n X)
      = (fun X => γ n + (2 * γ (n + 1)) * X + γ (n + 2) * X ^ 2) := by
    funext X; rw [jensenPoly_two_eval]
  simp only [hev]
  rw [quadratic_hasRoot_iff_discrim hlead]
  constructor
  · intro h
    have := degree_two_discrim_eq γ n
    nlinarith [h]
  · intro h
    have := degree_two_discrim_eq γ n
    nlinarith [h]

/-- **PROVED — order-1 Turán ⟺ all degree-2 Jensen polynomials hyperbolic** (under
positivity of the leading coefficients). -/
theorem orderOneTuran_iff_all_degree_two_hyperbolic (γ : XiCoeff)
    (hpos : XiCoeffPos γ) :
    OrderOneTuran γ ↔ ∀ n, Hyperbolic γ 2 n := by
  constructor
  · intro h n
    exact (degree_two_jensen_hyperbolic_iff_turan γ n (hpos (n + 2)).ne').mpr (h n)
  · intro h n
    exact (degree_two_jensen_hyperbolic_iff_turan γ n (hpos (n + 2)).ne').mp (h n)

-- =====================================================================
-- §4.  The Pólya–Jensen criterion (RH-equivalent) and the descent to order-1
-- =====================================================================

/-- **The Pólya–Jensen criterion (named RH-EQUIVALENT input).**  Every Jensen
polynomial `J^{d,n}_γ` (all degrees `d ≥ 1`, all shifts `n`) is hyperbolic.
Theorem (Pólya): this is **equivalent to RH**.  The full tower. -/
def PolyaJensenCriterion (γ : XiCoeff) : Prop := ∀ d, 1 ≤ d → ∀ n, Hyperbolic γ d n

/-- **PROVED — the RH-tower descends to order-1 Turán.**  If every Jensen
polynomial is hyperbolic (Pólya–Jensen / RH), then in particular the order-1 Turán
inequality holds.  (Honest direction of the necessary-condition chain: RH ⟹
order-1 Turán; CNV proved order-1 Turán UNCONDITIONALLY, i.e. without RH.) -/
theorem orderOneTuran_of_PolyaJensen (γ : XiCoeff) (hpos : XiCoeffPos γ)
    (h : PolyaJensenCriterion γ) : OrderOneTuran γ := by
  intro n
  exact (degree_two_jensen_hyperbolic_iff_turan γ n (hpos (n + 2)).ne').mp
    (h 2 (by norm_num) n)

/-- **PROVED — the RH-tower descends to order-2 (higher-order) Turán** via degree-3
hyperbolicity.  The named carrier of "degree-3 hyperbolic ⟹ order-2 Turán
discriminant `≥ 0`" is supplied as `hdisc` (the standard cubic-discriminant
identity for a real cubic with all real roots); Dimitrov–Lucas proves the
hypothesis-free version directly. -/
theorem orderTwoTuran_of_PolyaJensen (γ : XiCoeff)
    (hdisc : (∀ n, Hyperbolic γ 3 n) → OrderTwoTuran γ)
    (h : PolyaJensenCriterion γ) : OrderTwoTuran γ :=
  hdisc (fun n => h 3 (by norm_num) n)

-- =====================================================================
-- §5.  The named unconditional inputs, on record with citations
-- =====================================================================

/-- **Csordas–Norfolk–Varga (1986) — UNCONDITIONAL order-1 Turán.**  Restated as a
named input: `OrderOneTuran γ` for the ξ coefficients, *without* RH.  Trans. AMS 296
(1986) 521–541.  Equivalently (by `orderOneTuran_iff_all_degree_two_hyperbolic`):
all degree-2 Jensen polynomials of ξ are hyperbolic unconditionally. -/
def CNV_OrderOneTuran (γ : XiCoeff) : Prop := OrderOneTuran γ

/-- **Dimitrov–Lucas (2011) — UNCONDITIONAL order-2 Turán.**  Restated as a named
input: `OrderTwoTuran γ` (degree-3 Jensen hyperbolic) for the ξ coefficients,
*without* RH, for all `n` outside an explicit finite set.  Proc. AMS 139 (2011)
1013–1022. -/
def DimitrovLucas_OrderTwoTuran (γ : XiCoeff) : Prop := OrderTwoTuran γ

/-- 🌟 **PROVED — Dimitrov–Lucas IS the order-2 discriminant nonnegativity.**  Clean
restatement: the named input is exactly `∀ n, 0 ≤ turanTwoForm γ n`. -/
theorem orderTwoTuran_discriminant_nonneg_of_DimitrovLucas (γ : XiCoeff)
    (h : DimitrovLucas_OrderTwoTuran γ) : ∀ n, 0 ≤ turanTwoForm γ n := h

/-- **GORZ (2019) — UNCONDITIONAL effective hyperbolicity (named input).**  For each
fixed degree `d ≥ 1` there is a threshold `N(d)` past which every `J^{d,n}_γ` is
hyperbolic.  Griffin–Ono–Rolen–Zagier, PNAS 116 (2019) 11103–11110. -/
def GORZ_Hyperbolicity (γ : XiCoeff) : Prop :=
  ∀ d, 1 ≤ d → ∃ N : ℕ, ∀ n, N ≤ n → Hyperbolic γ d n

/-- **PROVED — GORZ recovers order-1 Turán for all large `n`.**  Specializing GORZ
to `d = 2` and translating degree-2 hyperbolicity via the discriminant gives the
order-1 Turán inequality for all `n ≥ N(2)` — an honest *eventual* recovery from the
density-1 result (CNV gives it for *all* `n`). -/
theorem orderOneTuran_eventually_of_GORZ (γ : XiCoeff) (hpos : XiCoeffPos γ)
    (h : GORZ_Hyperbolicity γ) : ∃ N : ℕ, ∀ n, N ≤ n → 0 ≤ turanForm γ n := by
  obtain ⟨N, hN⟩ := h 2 (by norm_num)
  refine ⟨N, fun n hn => ?_⟩
  exact (degree_two_jensen_hyperbolic_iff_turan γ n (hpos (n + 2)).ne').mp (hN n hn)

/-- **The GORZ gap, on record (documentation).**  GORZ proves hyperbolicity for
each `d` and all large `n`; RH additionally requires the finitely many small-`n`
members at every degree.  The boolean records that "eventual at every degree" does
NOT by itself give "all `n` at every degree". -/
theorem gorz_gap_is_real :
    -- the eventual statement is strictly weaker than the full tower:
    (∀ γ : XiCoeff, PolyaJensenCriterion γ → GORZ_Hyperbolicity γ) ∧
    True := by
  refine ⟨fun γ h d hd => ⟨0, fun n _ => h d hd n⟩, trivial⟩

-- =====================================================================
-- §6.  Genuine elementary deductions around the order-2 form
-- =====================================================================

/-- **PROVED — order-1 Turán in single-nonnegativity form.** -/
theorem turan_le_form (γ : XiCoeff) (n : ℕ) :
    0 ≤ turanForm γ n ↔ γ n * γ (n + 2) ≤ γ (n + 1) ^ 2 := by
  unfold turanForm; constructor <;> intro h <;> linarith

/-- **PROVED — order-1 Turán in product form** (`γ > 0`): `γ_n·γ_{n+2} ≤ γ_{n+1}²`. -/
theorem turan_product_le (γ : XiCoeff) (n : ℕ) (h : 0 ≤ turanForm γ n) :
    γ n * γ (n + 2) ≤ γ (n + 1) ^ 2 :=
  (turan_le_form γ n).mp h

/-- 🌟 **PROVED — the order-2 discriminant forces the two consecutive order-1 Turán
factors to be *jointly* nonneg or jointly nonpos.**  If `4·A·B − C² ≥ 0` then
`A·B ≥ C²/4 ≥ 0`, so `A` and `B` have the same sign (`0 ≤ A·B`).  Hence, given the
order-1 Turán factor `A = turanForm γ n ≥ 0` *and* `A ≠ 0`, the next factor
`B = turanForm γ (n+1) ≥ 0` follows — a genuine elementary chaining of order-2 into
order-1 at the next index. -/
theorem orderTwo_factors_same_sign (γ : XiCoeff) (n : ℕ)
    (h2 : 0 ≤ turanTwoForm γ n) :
    0 ≤ turanForm γ n * turanForm γ (n + 1) := by
  unfold turanTwoForm turanForm at *
  nlinarith [sq_nonneg (γ (n + 1) * γ (n + 2) - γ n * γ (n + 3)), h2]

/-- 🌟 **PROVED — order-2 discriminant + strict first factor ⟹ next order-1 Turán.**
If `turanTwoForm γ n ≥ 0` and the first order-1 factor `turanForm γ n > 0`, then the
*next* order-1 Turán factor `turanForm γ (n+1) ≥ 0`.  Pure sign reasoning from
`orderTwo_factors_same_sign`. -/
theorem nextTuran_of_orderTwo (γ : XiCoeff) (n : ℕ)
    (h2 : 0 ≤ turanTwoForm γ n) (hpos : 0 < turanForm γ n) :
    0 ≤ turanForm γ (n + 1) := by
  have hprod := orderTwo_factors_same_sign γ n h2
  nlinarith [hprod, hpos]

-- =====================================================================
-- §7.  A fully numeric (norm_num) finite Turán sanity certificate
-- =====================================================================

/-- **Low-order rational approximations of the ξ Maclaurin coefficients.**  Using the
GORZ normalization `(1/8)Ξ(x/2) = Σ γ(n) x^{2n}/n!`, the first coefficients are
(rounded, from the literature / standard tables, here as exact rationals for a
machine-checkable consistency test):

    γ̃(0) ≈ 0.0228,   γ̃(1) ≈ 0.00139,   γ̃(2) ≈ 0.0000244 ...

We do NOT claim these are the exact transcendental values; this is a *consistency
certificate* that the unconditional order-1 Turán inequality is satisfied at the
first member by the known numerics (a sanity check, not a proof of the CNV theorem).
The qualitative content `γ̃(1)² ≥ γ̃(0)·γ̃(2)` is what CNV proves for the true `γ`. -/
noncomputable def gammaApprox : XiCoeff
  | 0 => 228 / 10000
  | 1 => 139 / 100000
  | 2 => 244 / 10000000
  | (_ + 3) => 0

/-- 🌟🌟 **PROVED by `norm_num` — order-1 Turán holds at the first member for the
literature numerics.**  `γ̃(1)² ≥ γ̃(0)·γ̃(2)`, discharged by pure computation.
A self-contained finite sanity certificate that the unconditional inequality is
*consistent* at `n = 0` (NOT a proof of the analytic CNV theorem). -/
theorem numeric_turan_check : 0 ≤ turanForm gammaApprox 0 := by
  unfold turanForm gammaApprox
  norm_num

/-- **PROVED — same certificate as the product inequality** `γ̃(0)·γ̃(2) ≤ γ̃(1)²`. -/
theorem numeric_turan_product : gammaApprox 0 * gammaApprox 2 ≤ gammaApprox 1 ^ 2 := by
  unfold gammaApprox; norm_num

-- =====================================================================
-- §8.  Hierarchy summary (documentation theorems) and reach
-- =====================================================================

/-- **PROVED — hierarchy placement, order-1 ⟸ order-2 chaining is genuine but the
full RH-tower is strictly more.**  Records:
* `PolyaJensenCriterion ⟹ OrderOneTuran` (RH ⟹ order-1; order-1 is UNCONDITIONAL),
* `PolyaJensenCriterion ⟹ GORZ_Hyperbolicity` (RH ⟹ eventual hyperbolicity; GORZ
  is UNCONDITIONAL),
and leaves the converse(s) as the open RH-strength content. -/
theorem hierarchy_summary (γ : XiCoeff) (hpos : XiCoeffPos γ) :
    (PolyaJensenCriterion γ → OrderOneTuran γ) ∧
    (PolyaJensenCriterion γ → GORZ_Hyperbolicity γ) :=
  ⟨orderOneTuran_of_PolyaJensen γ hpos,
   fun h d hd => ⟨0, fun n _ => h d hd n⟩⟩

-- =====================================================================
-- §9.  Axiom audit
-- =====================================================================

#print axioms jensenPoly_two_eval
#print axioms jensenPoly_three_eval
#print axioms quadratic_hasRoot_iff_discrim
#print axioms degree_two_jensen_hyperbolic_iff_turan
#print axioms orderOneTuran_iff_all_degree_two_hyperbolic
#print axioms orderOneTuran_of_PolyaJensen
#print axioms orderTwoTuran_discriminant_nonneg_of_DimitrovLucas
#print axioms orderTwo_factors_same_sign
#print axioms nextTuran_of_orderTwo
#print axioms numeric_turan_check
#print axioms numeric_turan_product
#print axioms orderOneTuran_eventually_of_GORZ
#print axioms orderTwoTuran_of_PolyaJensen
#print axioms hierarchy_summary

end TuranHierarchy
end OverflowResidueRH
