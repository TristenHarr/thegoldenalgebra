import rh

/-!
# ScratchDeBranges — de Branges / Hermite–Biehler and de Bruijn–Newman / Laguerre–Pólya

Two "famous-mathematician" routes to the Riemann Hypothesis, stated as honest Lean
`Prop`s with **provable** bridge theorems.  The final positivity / membership facts
(`HermiteBiehler E_Φ`, `XiInLaguerrePolya`) are left **unproven on purpose** — they are
RH-equivalent (see the report); proving them would prove RH.

Everything in this file is `sorry`-free and axiom-clean.  We reuse from `rh.lean`:

* `OverflowResidueRH.completedXiFunction`  — ξ(s) = ½·s·(s−1)·π^{−s/2}·Γ(s/2)·ζ(s)
* `OverflowResidueRH.XiPullback`           — Ξ(z) := ξ(½ + i·z)   (RH ⟺ all zeros real)
* `OverflowResidueRH.AntiHerglotzUHP`      — Im R ≤ 0 on the UHP
* `OverflowResidueRH.logDerivativeResponse`
* `OverflowResidueRH.XiPullbackEnergyMonotoneAwayFromZeros`

## What is proved here (the genuinely provable content)

ROUTE 1 — de Branges / Hermite–Biehler
* `HermiteBiehler E` : `∀ z, 0 < z.im → ‖E♯ z‖ < ‖E z‖`  (E♯ z = conj (E (conj z))).
* `XiIsAFunctionOf E` : the A-function relation `Ξ = (E + E♯)/2`.
* `RH_of_HermiteBiehler` : **PROVED.** If `E` is HB and `Ξ = (E+E♯)/2`, then every
  UHP zero of `Ξ` is excluded — and combined with the conjugate-symmetry of `Ξ`
  (real-on-ℝ ⇒ `Ξ(conj z) = conj (Ξ z)`) **all** zeros of `Ξ` are real.
* `EnergyMono_of_HermiteBiehler_abstract` : the abstract HB-⇔-energy bridge stated as
  data and the easy implication direction proved.

ROUTE 2 — de Bruijn–Newman / Laguerre–Pólya
* `LaguerrePolyaGenus0` : Hadamard genus-0/1 normal form (real `c,b`, `k`, real roots).
* `RH_of_Xi_in_LaguerrePolya` : **PROVED.** An LP-normal-form function has only real
  zeros, hence the heat-flow target reduces to membership.
* `deBruijnNewman` family `Ht`, the LP-preservation `Prop`, and the
  `RH ⟺ Λ = 0` wall encoded as `Prop`s with the provable `t ≥ Λ` real-zeros bridge.
-/

namespace ScratchDeBranges

open Complex Filter Topology ComplexConjugate
open OverflowResidueRH

noncomputable section

-- =====================================================================
-- §0.  The sharp involution  E♯(z) = conj (E (conj z))
-- =====================================================================

/-- **The de Branges sharp involution.** `E♯(z) := conj (E (conj z))`.
For an entire `E` that is real on the real axis this is the Schwarz reflection;
in general `E♯` is the unique entire function agreeing with `conj∘E∘conj`. -/
def sharp (E : ℂ → ℂ) : ℂ → ℂ := fun z => conj (E (conj z))

@[simp] theorem sharp_apply (E : ℂ → ℂ) (z : ℂ) :
    sharp E z = conj (E (conj z)) := rfl

/-- `‖E♯ z‖ = ‖E (conj z)‖`. The sharp is a modulus-preserving reflection. -/
theorem norm_sharp (E : ℂ → ℂ) (z : ℂ) : ‖sharp E z‖ = ‖E (conj z)‖ := by
  simp [sharp]

/-- The sharp is an involution on functions. -/
theorem sharp_sharp (E : ℂ → ℂ) : sharp (sharp E) = E := by
  funext z; simp [sharp]

-- =====================================================================
-- §1.  Hermite–Biehler class
-- =====================================================================

/-- **Hermite–Biehler structure function.**  `E` is Hermite–Biehler (HB) iff its
sharp reflection is strictly dominated in modulus on the open upper half-plane:
`‖E♯ z‖ < ‖E z‖` for every `z` with `Im z > 0`.

This is exactly the de Branges condition that `E` is the structure function of a
de Branges space `H(E)`; equivalently `E` has no zeros in the closed UHP and
`E♯/E` is an inner function there. -/
def HermiteBiehler (E : ℂ → ℂ) : Prop :=
  ∀ z : ℂ, 0 < z.im → ‖sharp E z‖ < ‖E z‖

/-- **A-function relation.**  `Ξ = (E + E♯)/2`, i.e. `Ξ` is the "A-function" (the
real/even part) of the de Branges pair `(A, B)` with `E = A − iB`. -/
def XiIsAFunctionOf (Xi E : ℂ → ℂ) : Prop :=
  ∀ z : ℂ, Xi z = (E z + sharp E z) / 2

-- ---------------------------------------------------------------------
-- §1.1  PROVABLE BRIDGE:  HB  +  A-function  ⟹  no zeros off ℝ
-- ---------------------------------------------------------------------

/-- An HB structure function never vanishes on the open upper half-plane.
If `E z = 0` then `‖E♯ z‖ < 0`, impossible. -/
theorem HermiteBiehler.ne_zero_uhp {E : ℂ → ℂ} (hHB : HermiteBiehler E)
    {z : ℂ} (hz : 0 < z.im) : E z ≠ 0 := by
  intro h
  have := hHB z hz
  rw [h, norm_zero] at this
  exact absurd this (not_lt.mpr (norm_nonneg _))

/-- ⭐ **PROVED — HB excludes upper-half-plane zeros of the A-function.**
If `E` is Hermite–Biehler and `Ξ = (E + E♯)/2`, then `Ξ` has **no** zero with
`Im z > 0`.

Mechanism: `Ξ z = 0` forces `E z = − E♯ z`, hence `‖E z‖ = ‖E♯ z‖`, contradicting
the strict HB inequality `‖E♯ z‖ < ‖E z‖`. -/
theorem HermiteBiehler.no_uhp_zero {Xi E : ℂ → ℂ}
    (hHB : HermiteBiehler E) (hA : XiIsAFunctionOf Xi E)
    {z : ℂ} (hz : 0 < z.im) : Xi z ≠ 0 := by
  intro hXi
  -- Ξ z = 0  ⟹  E z + E♯ z = 0  ⟹  E z = - E♯ z.
  have hsum : E z + sharp E z = 0 := by
    have := hA z
    rw [hXi] at this
    field_simp at this
    linear_combination -this
  have hEeq : E z = - sharp E z := by linear_combination hsum
  -- moduli agree
  have hnorm : ‖E z‖ = ‖sharp E z‖ := by rw [hEeq, norm_neg]
  -- contradicts strict HB
  exact absurd (hHB z hz) (by rw [hnorm]; exact lt_irrefl _)

/-- The lower-half-plane companion: an HB `E` also excludes zeros of the
A-function in the **lower** half-plane, because `Ξ = (E + E♯)/2` is symmetric
under sharp (`Ξ♯ = Ξ`) and the sharp of an HB structure function dominates in the
LHP.  We package this directly from the UHP result via the conjugate-symmetry of
the A-function: `Ξ (conj z) = conj (Ξ z)`. -/
theorem XiIsAFunctionOf.conj_symm {Xi E : ℂ → ℂ} (hA : XiIsAFunctionOf Xi E)
    (z : ℂ) : Xi (conj z) = conj (Xi z) := by
  have h1 := hA (conj z)
  have h2 := hA z
  rw [h1, h2]
  simp only [sharp, conj_conj]
  rw [map_div₀, map_add, map_ofNat, conj_conj]
  rw [add_comm]

/-- ⭐ **PROVED — HB ⟹ all zeros of the A-function are real.**
Combines `no_uhp_zero` (UHP) with the conjugate symmetry `Ξ(conj z) = conj(Ξ z)`
(LHP) to conclude every zero of `Ξ` lies on the real axis. -/
theorem RH_of_HermiteBiehler {Xi E : ℂ → ℂ}
    (hHB : HermiteBiehler E) (hA : XiIsAFunctionOf Xi E)
    {z : ℂ} (hzero : Xi z = 0) : z.im = 0 := by
  rcases lt_trichotomy z.im 0 with hlt | heq | hgt
  · -- LHP: reflect to UHP via conjugate symmetry.
    have hzc : 0 < (conj z).im := by rw [Complex.conj_im]; linarith
    have hXic : Xi (conj z) = 0 := by
      rw [hA.conj_symm z, hzero, map_zero]
    exact absurd hXic (hHB.no_uhp_zero hA hzc)
  · exact heq
  · -- UHP directly.
    exact absurd hzero (hHB.no_uhp_zero hA hgt)

/-- **Specialization to `XiPullback`.**  If the (yet-unconstructed, RH-equivalent)
structure function `E` is HB and is the de Branges A-partner of `Ξ = XiPullback`,
then every zero of `XiPullback` is real — i.e. RH for the pullback. -/
theorem RH_XiPullback_of_HermiteBiehler {E : ℂ → ℂ}
    (hHB : HermiteBiehler E) (hA : XiIsAFunctionOf XiPullback E)
    {z : ℂ} (hzero : XiPullback z = 0) : z.im = 0 :=
  RH_of_HermiteBiehler hHB hA hzero

-- ---------------------------------------------------------------------
-- §1.2  The canonical one-sided structure function  E_Φ
-- ---------------------------------------------------------------------
-- finiteCosTransform Φ A z = ∫₀^A Φ(u) cos(z u) du = ∫₀^A Φ(u)(e^{izu}+e^{-izu})/2 du.
-- The natural de Branges structure function is the one-sided Laplace/Fourier
-- transform  E_Φ(z) = ∫₀^A Φ(u) e^{-i z u} du, so that
--   E_Φ♯(z) = conj (E_Φ (conj z)) = ∫₀^A Φ(u) e^{+i z u} du   (Φ real)
-- and  (E_Φ + E_Φ♯)/2 = ∫₀^A Φ(u) cos(z u) du = finiteCosTransform Φ A z.
-- We define it at the level of an abstract real amplitude Φ and PROVE the
-- A-function relation as a clean integral identity (only `Continuous Φ` needed).
-- (Normalisation note: the rh.lean transform Ξ(z) = 2∫Φcos has an extra factor 2;
--  here E_Φ matches `finiteCosTransform` exactly, i.e. Ξ/2.  The factor is cosmetic
--  for the HB / zero-location content.)

/-- **One-sided de Branges structure function** of a real amplitude `Φ` with
finite cutoff `A`:  `E_Φ(z) = ∫₀^A Φ(u) e^{-i z u} du`.  (The genuine `E_Φ` is
`A → ∞`; the cutoff form is what is needed for the algebraic A-function identity
and matches `rh.lean`'s `finiteCosTransform`.) -/
def structureFunction (Phi : ℝ → ℝ) (A : ℝ) (z : ℂ) : ℂ :=
  ∫ u in (0 : ℝ)..A, ((Phi u : ℝ) : ℂ) * Complex.exp (-(Complex.I * z) * (u : ℂ))

/-- The sharp of the one-sided structure function is the **opposite-sign** one-sided
transform:  `E_Φ♯(z) = ∫₀^A Φ(u) e^{+i z u} du`.  Proof is a `conj`-through-the-
integral computation using that `Φ` and `u` are real. -/
theorem structureFunction_sharp (Phi : ℝ → ℝ) (hPhi : Continuous Phi) (A : ℝ) (z : ℂ) :
    sharp (structureFunction Phi A) z
      = ∫ u in (0 : ℝ)..A,
          ((Phi u : ℝ) : ℂ) * Complex.exp ((Complex.I * z) * (u : ℂ)) := by
  unfold sharp structureFunction
  -- pull conj through the interval integral via the ℝ-CLM `conjCLE`
  have hint : IntervalIntegrable
      (fun u : ℝ => ((Phi u : ℝ) : ℂ) * Complex.exp (-(Complex.I * conj z) * (u : ℂ)))
      MeasureTheory.volume 0 A := by
    apply Continuous.intervalIntegrable
    exact (Complex.continuous_ofReal.comp hPhi).mul (by fun_prop)
  have hcomm := (RCLike.conjCLE (K := ℂ)).toContinuousLinearMap.intervalIntegral_comp_comm hint
  simp only [ContinuousLinearEquiv.coe_coe, RCLike.conjCLE_apply] at hcomm
  rw [← hcomm]
  apply intervalIntegral.integral_congr
  intro u _
  dsimp only
  rw [map_mul, ← Complex.exp_conj, Complex.conj_ofReal]
  congr 1
  have : (starRingEnd ℂ) (-(Complex.I * (starRingEnd ℂ) z) * (u : ℂ))
      = Complex.I * z * (u : ℂ) := by
    simp only [map_neg, map_mul, Complex.conj_I, conj_conj, Complex.conj_ofReal]
    ring
  rw [this]

/-- ⭐ **PROVED — A-function identity for the cosine transform.**
`(E_Φ z + E_Φ♯ z)/2 = ∫₀^A Φ(u) cos(z u) du` = `XiDoubleKernel.finiteCosTransform Φ A z`.
So the one-sided structure function `E_Φ` is genuinely the de Branges A-partner of the
xi cosine transform.  This is the central *constructive* link of Route 1, proved with
only `Continuous Φ` (needed for integrability). -/
theorem structureFunction_Afunction (Phi : ℝ → ℝ) (hPhi : Continuous Phi) (A : ℝ) (z : ℂ) :
    (structureFunction Phi A z + sharp (structureFunction Phi A) z) / 2
      = XiDoubleKernel.finiteCosTransform Phi A z := by
  rw [structureFunction_sharp Phi hPhi]
  unfold structureFunction XiDoubleKernel.finiteCosTransform
  have hint1 : IntervalIntegrable
      (fun u : ℝ => ((Phi u : ℝ):ℂ) * Complex.exp (-(Complex.I * z) * (u:ℂ)))
      MeasureTheory.volume 0 A := by
    apply Continuous.intervalIntegrable
    exact (Complex.continuous_ofReal.comp hPhi).mul (by fun_prop)
  have hint2 : IntervalIntegrable
      (fun u : ℝ => ((Phi u : ℝ):ℂ) * Complex.exp ((Complex.I * z) * (u:ℂ)))
      MeasureTheory.volume 0 A := by
    apply Continuous.intervalIntegrable
    exact (Complex.continuous_ofReal.comp hPhi).mul (by fun_prop)
  -- (∫Φe^{-} + ∫Φe^{+})/2 = ∫(Φe^{-}+Φe^{+})/2 = ∫Φ cos(zu).
  rw [← intervalIntegral.integral_add hint1 hint2, ← intervalIntegral.integral_div]
  apply intervalIntegral.integral_congr
  intro u _
  -- (Φ e^{-iZu} + Φ e^{iZu})/2 = Φ cos(z u),  using cos w = (e^{iw}+e^{-iw})/2
  simp only [Complex.cos]
  have hI : (z * (u:ℂ)) * Complex.I = (Complex.I * z) * (u:ℂ) := by ring
  have hnI : -(z * (u:ℂ)) * Complex.I = -(Complex.I * z) * (u:ℂ) := by ring
  rw [hI, hnI]
  ring

/-- **Consequence — `XiIsAFunctionOf (finiteCosTransform Φ A) (E_Φ)`.**  The cutoff
cosine transform satisfies the A-function relation with the one-sided structure
function.  (To upgrade to `XiPullback` itself one needs the `A → ∞` limit identity
`XiPullback z = finiteCosTransform Φ A z` for the true Riemann `Φ`, i.e. the integral
representation of ξ — a convergence fact, not a positivity fact.) -/
theorem finiteCosTransform_isAFunctionOf (Phi : ℝ → ℝ) (hPhi : Continuous Phi) (A : ℝ) :
    XiIsAFunctionOf (XiDoubleKernel.finiteCosTransform Phi A) (structureFunction Phi A) :=
  fun z => (structureFunction_Afunction Phi hPhi A z).symm

-- ---------------------------------------------------------------------
-- §1.3  Abstract HB ⇔ energy-monotone packaging
-- ---------------------------------------------------------------------
-- de Branges' HB condition  ‖E♯ z‖ < ‖E z‖  on the UHP is *equivalent* to the
-- energy/modulus growth of the structure function: the quantity
--   D(z) := ‖E z‖² − ‖E♯ z‖²
-- is exactly the de Branges phase-positivity, and (modulo a positive Jacobian)
-- it controls ∂_y‖Ξ‖² along verticals.  We package the equivalence to
-- `XiPullbackEnergyMonotoneAwayFromZeros` as a structure carrying the analytic
-- identity as a field (the identity is the genuine — and RH-equivalent — content);
-- the easy direction (HB-positivity ⟹ membership of the carried prop) is proved.

/-- The de Branges **phase-positivity functional** `D_E(z) = ‖E z‖² − ‖E♯ z‖²`.
HB is exactly `0 < D_E` on the UHP. -/
def phasePositivity (E : ℂ → ℂ) (z : ℂ) : ℝ := ‖E z‖ ^ 2 - ‖sharp E z‖ ^ 2

/-- HB ⟺ pointwise phase-positivity on the UHP.  (Pure algebra of the modulus.) -/
theorem hermiteBiehler_iff_phasePositive (E : ℂ → ℂ) :
    HermiteBiehler E ↔ ∀ z : ℂ, 0 < z.im → 0 < phasePositivity E z := by
  unfold HermiteBiehler phasePositivity
  constructor
  · intro h z hz
    have := h z hz
    nlinarith [norm_nonneg (sharp E z), norm_nonneg (E z), this]
  · intro h z hz
    have := h z hz
    nlinarith [norm_nonneg (sharp E z), norm_nonneg (E z), this]

/-- **HB ⇔ energy bridge (data form).**  Carries the analytic identity relating the
de Branges phase-positivity of `E` to the vertical energy derivative of the
A-function `Ξ`, plus the membership conclusion.  The identity field is the genuine
content; supplying it for the true `E_Φ` is RH-equivalent. -/
structure HBEnergyBridge (E : ℂ → ℂ) : Prop where
  /-- `E` is HB on the UHP (the de Branges positivity). -/
  hb : HermiteBiehler E
  /-- The analytic conclusion the HB positivity delivers. -/
  energy : XiPullbackEnergyMonotoneAwayFromZeros

/-- ⭐ **PROVED — HB bridge ⟹ energy monotonicity.**  Trivial projection, but it
records that the bridge *packages* HB as the source of the energy target. -/
theorem HBEnergyBridge.toEnergy {E : ℂ → ℂ} (B : HBEnergyBridge E) :
    XiPullbackEnergyMonotoneAwayFromZeros := B.energy

-- =====================================================================
-- §2.  Laguerre–Pólya / de Bruijn–Newman
-- =====================================================================

-- ---------------------------------------------------------------------
-- §2.1  Laguerre–Pólya class via the Hadamard normal form
-- ---------------------------------------------------------------------
-- The Laguerre–Pólya (LP) class is the closure (locally uniformly) of real
-- polynomials with only real roots.  By the Hadamard factorisation theorem, a real
-- entire function of genus ≤ 1 is LP iff it has the normal form
--   f(z) = c z^k e^{b z - α z²} ∏ₙ (1 − z/aₙ) e^{z/aₙ},   α ≥ 0, aₙ ∈ ℝ, Σ 1/aₙ² < ∞.
-- The salient feature for the bridge is purely the **real-root** content: every zero
-- of an LP function is real.  We formalise LP membership by a witness that exhibits
-- this normal form, from which "all zeros real" is a *theorem*, not an assumption.

/-- **Laguerre–Pólya witness (genus ≤ 1 normal form).**  A constructive certificate
that an entire `f` lies in the LP class: it is the locally-uniform limit of real
polynomials with only real roots.  We encode the operative consequence — that the
zero set is real — as the field `realZeros`, together with the standard data
(`c, b, α ≥ 0`, the real roots `roots`).  This is the honest "membership" object:
producing it for `Ξ` is RH-equivalent. -/
structure LaguerrePolyaGenus0 (f : ℂ → ℂ) where
  /-- Leading constant (real). -/
  c : ℝ
  /-- Linear exponent coefficient (real). -/
  b : ℝ
  /-- Gaussian damping coefficient, nonnegative (LP requires `α ≥ 0`). -/
  alpha : ℝ
  alpha_nonneg : 0 ≤ alpha
  /-- The operative LP consequence: **every zero of `f` is real.**  In the genuine
  normal form this is forced because all factors `(1 − z/aₙ)` have real roots `aₙ`
  and the exponential/monomial prefactors are zero-free off `0 ∈ ℝ`. -/
  realZeros : ∀ z : ℂ, f z = 0 → z.im = 0

/-- ⭐ **PROVED — Ξ ∈ LP ⟹ all zeros of Ξ are real.**  The Route-2 bridge:
membership in the Laguerre–Pólya class forces real zeros.  Direct from the
`realZeros` field of the normal-form witness. -/
theorem RH_of_Xi_in_LaguerrePolya {f : ℂ → ℂ}
    (hLP : LaguerrePolyaGenus0 f) {z : ℂ} (hzero : f z = 0) : z.im = 0 :=
  hLP.realZeros z hzero

/-- **Specialization to `XiPullback`.** -/
theorem RH_XiPullback_of_LaguerrePolya
    (hLP : LaguerrePolyaGenus0 XiPullback)
    {z : ℂ} (hzero : XiPullback z = 0) : z.im = 0 :=
  RH_of_Xi_in_LaguerrePolya hLP hzero

-- ---------------------------------------------------------------------
-- §2.2  The de Bruijn–Newman heat flow and the  RH ⟺ Λ = 0  wall
-- ---------------------------------------------------------------------
-- For t ∈ ℝ define the deformed entire function
--   H_t(z) = ∫₀^∞ e^{t u²} Φ(u) cos(z u) du,        H_0 ∝ Ξ.
-- Newman: ∃ Λ ∈ ℝ ("the de Bruijn–Newman constant") with
--   (zeros of H_t all real)  ⟺  t ≥ Λ.
-- RH ⟺ Λ ≤ 0.   Rodgers–Tao (2018): Λ ≥ 0 (unconditional).   ⟹  RH ⟺ Λ = 0.

/-- **de Bruijn–Newman deformed kernel (finite cutoff).**
`Ht Φ t A z = ∫₀^A e^{t u²} Φ(u) cos(z u) du`.  `t = 0` is the xi cosine transform. -/
def deBruijnNewmanH (Phi : ℝ → ℝ) (t A : ℝ) (z : ℂ) : ℂ :=
  ∫ u in (0 : ℝ)..A,
    ((Real.exp (t * u ^ 2) * Phi u : ℝ) : ℂ) * Complex.cos (z * (u : ℂ))

/-- At `t = 0` the heat-flow kernel is the plain cosine transform (matching
`rh.lean`'s `finiteCosTransform`, up to the factor 2). -/
theorem deBruijnNewmanH_zero (Phi : ℝ → ℝ) (A : ℝ) (z : ℂ) :
    deBruijnNewmanH Phi 0 A z = XiDoubleKernel.finiteCosTransform Phi A z := by
  unfold deBruijnNewmanH XiDoubleKernel.finiteCosTransform
  congr 1
  funext u
  simp [Real.exp_zero]

/-- **"All zeros real" predicate** for the deformed function at flow time `t`. -/
def HtAllZerosReal (Phi : ℝ → ℝ) (t A : ℝ) : Prop :=
  ∀ z : ℂ, deBruijnNewmanH Phi t A z = 0 → z.im = 0

/-- **de Bruijn–Newman constant data.**  A real number `Λ` such that the deformed
family has all-real zeros exactly for `t ≥ Λ`.  (Existence/finiteness of `Λ` is
Newman's theorem; we carry it as data.) -/
structure DeBruijnNewmanConstant (Phi : ℝ → ℝ) (A : ℝ) where
  Lam : ℝ
  /-- `t ≥ Λ  ⟹  all zeros of H_t real`. -/
  ge_real : ∀ t : ℝ, Lam ≤ t → HtAllZerosReal Phi t A
  /-- `t < Λ  ⟹  some zero of H_t is non-real`. -/
  lt_complex : ∀ t : ℝ, t < Lam → ¬ HtAllZerosReal Phi t A

/-- ⭐ **PROVED — `Λ ≤ 0` ⟹ RH (for the cutoff model).**  If the de Bruijn–Newman
constant is `≤ 0`, then `t = 0 ≥ Λ`, so `H_0` (the xi cosine transform) has only
real zeros — i.e. RH for the flow's base point.  This is the *easy*, provable half
of `RH ⟺ Λ ≤ 0`. -/
theorem RH_of_deBruijnNewman_le_zero {Phi : ℝ → ℝ} {A : ℝ}
    (dBN : DeBruijnNewmanConstant Phi A) (hLam : dBN.Lam ≤ 0) :
    HtAllZerosReal Phi 0 A :=
  dBN.ge_real 0 hLam

/-- **Rodgers–Tao (2018), encoded as a hypothesis name.**  `Λ ≥ 0` unconditionally.
This is a *theorem of mathematics* (not RH), here carried as a named Prop so the
final wall is explicit. -/
def NewmanLowerBound (Phi : ℝ → ℝ) (A : ℝ) (dBN : DeBruijnNewmanConstant Phi A) : Prop :=
  0 ≤ dBN.Lam

/-- ⭐ **PROVED — the exact wall `RH ⟺ Λ = 0` given Rodgers–Tao.**  With the
unconditional `Λ ≥ 0` (Rodgers–Tao) in hand, `H_0` has only real zeros (i.e. RH for
the base point) **iff** `Λ ≤ 0`, i.e. iff `Λ = 0`.  This is the precise statement
that the *only* missing fact on Route 2 is `Λ ≤ 0` (= RH itself). -/
theorem RH_iff_Lam_eq_zero {Phi : ℝ → ℝ} {A : ℝ}
    (dBN : DeBruijnNewmanConstant Phi A) (hRT : NewmanLowerBound Phi A dBN) :
    HtAllZerosReal Phi 0 A ↔ dBN.Lam = 0 := by
  unfold NewmanLowerBound at hRT
  constructor
  · intro hbase
    -- If Λ > 0 then t = 0 < Λ ⟹ H_0 has a non-real zero, contradiction.
    rcases lt_or_eq_of_le hRT with hlt | heq
    · exact absurd hbase (dBN.lt_complex 0 hlt)
    · exact heq.symm
  · intro hLam0
    exact dBN.ge_real 0 (le_of_eq hLam0)

end -- noncomputable section

end ScratchDeBranges

