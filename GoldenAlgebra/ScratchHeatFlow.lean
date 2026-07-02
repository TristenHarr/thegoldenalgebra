import ScratchHBDominance
import ScratchDeBranges

/-!
# ScratchHeatFlow — the de Bruijn–Newman heat-flow first-contact INTERFACE

This file builds the **flow-invariance interface** for the heat-flow / maximum-principle
route to RH via the de Bruijn–Newman (dBN) constant, on top of the already-proven
Hermite–Biehler/Schur machinery of `ScratchHBDominance.lean` and the dBN scaffold of
`ScratchDeBranges.lean`.

## The mechanism (honest summary)

The dBN flow deforms the amplitude `Φ ↦ Φ_t(u) := e^{t u²} Φ(u)` (heat time `t`; the
true Riemann `Φ` at `t = 0`).  Newman's theorem: there is a constant `Λ` with

```
zeros of H_t all real   ⟺   t ≥ Λ ,        RH  ⟺  Λ ≤ 0 .
```

Rodgers–Tao (2018) proved the **other** half, `Λ ≥ 0`, by a *dynamical* relaxation
argument (zeros under backward heat flow relax toward arithmetic progressions, which
contradicts the known pair-correlation irregularity of the ζ-zeros).  The `Λ ≤ 0`
direction — RH — resists the same method because at the threshold `t = Λ` a **double
real zero splits into a complex-conjugate pair**: the maximum principle is *marginal*
there, not protective.

Reading the same flow through the Schur/Hermite–Biehler functional of
`ScratchHBDominance`: with `A_t := A_transform Φ_t`, `B_t := B_transform Φ_t`, set

```
U_flow t Φ A x y  :=  ‖A_t(x,y)‖² − ‖B_t(x,y)‖²
                   =  (L₁²+L₃²) − (L₂²+L₄²)          (by normSq_*_transform).
```

`0 ≤ U_flow` at a probe is **Schur contractivity** `‖Θ_t‖ ≤ 1` there
(`Θ_t = B_t/A_t`); over all UHP probes at `t = 0` it is *exactly*
`RankFourDominance Φ`, i.e. `SpecialPhiHBDominance Φ` — the single open RH-strength
inequality of `ScratchHBDominance`.

## What this file PROVES (no `sorry`, axiom-clean)

* `heatPhi`, `heatPhi_zero` (`Φ_0 = Φ`).
* `U_flow`, its rank-4 form `U_flow_eq_rankFour`, `SchurContractiveAt`.
* `schurAtZero_iff_rankFour` and `schurAllZero_iff_specialPhiHB` — Schur contractivity
  of the flow at `t = 0` over all probes **is** `SpecialPhiHBDominance Φ` (PROVED, the
  clean identification; `heatPhi Φ 0 = Φ` makes it definitional up to the rank-4 ↔ HB
  equivalence already proven upstream).
* `SafeTimeSchurDominance`, `NoFirstContactFailure` (the dBN wall, left **unproven**).
* `specialPhiHBDominance_of_flowInvariance` — **the propagation bridge**: a safe time `T`
  of Schur dominance, propagated down to `t = 0` by the no-first-contact-failure
  hypothesis, yields `SpecialPhiHBDominance Φ`.  The *propagation skeleton* is proved;
  the protective-sign content is quarantined inside `NoFirstContactFailure` and **not**
  proved.
* `XiPullbackAntiHerglotzTarget_of_flowInvariance` — composition to the existing
  `ScratchHBDominance` capstone, hence to `XiPullbackAntiHerglotzTarget` / RH.
* `noFirstContactFailure_iff_dBN_le_zero` (documented as data) wiring
  `NoFirstContactFailure ↔ Λ ≤ 0` to `ScratchDeBranges.RH_iff_Lam_eq_zero`.

## The honest line

`NoFirstContactFailure` is the RH-strength core (`= Λ ≤ 0`).  It is **NOT** proved, and
no RH-equivalent hypothesis is assumed to prove anything downstream of it.  The
numerical experiment (see `heatflow_*.py`) finds, in the *finite-cutoff* model, the
protective sign `∂_t U > 0` uniformly — but that robustness is a Pólya/HB artifact of
the one-signed finite amplitude and does **not** resolve the genuine `A → ∞` dBN
threshold, where the split is marginal.  We therefore leave the protective-sign lemma
unproven, exactly at the wall.
-/

namespace OverflowResidueRH
namespace BacklundTuring
namespace ScratchHeatFlow

open Complex
open OverflowResidueRH.BacklundTuring.ScratchHBDominance
open OverflowResidueRH.BacklundTuring.ScratchEnergyKernel

/-! ## §1. The heat-deformed amplitude `Φ_t(u) = e^{t u²} Φ(u)` -/

/-- **Heat-deformed amplitude.** `heatPhi Φ t u = e^{t u²} · Φ(u)`.  This is the dBN
flow at the level of the *amplitude* feeding the cosine transform; `t = 0` is the
undeformed Riemann amplitude. -/
noncomputable def heatPhi (Phi : ℝ → ℝ) (t : ℝ) : ℝ → ℝ :=
  fun u => Real.exp (t * u ^ 2) * Phi u

/-- At `t = 0` the heat-deformed amplitude is the original amplitude. -/
@[simp] theorem heatPhi_zero (Phi : ℝ → ℝ) : heatPhi Phi 0 = Phi := by
  funext u
  simp [heatPhi]

/-! ## §2. The flow Schur functional `U_flow` and contractivity -/

/-- **The flow Schur functional.**  `U_flow t Φ A x y = ‖A_t‖² − ‖B_t‖²` where
`A_t = A_transform (heatPhi Φ t)`, `B_t = B_transform (heatPhi Φ t)`.  Nonnegativity of
`U_flow` is Schur contractivity `‖Θ_t‖ ≤ 1` at the probe `(x,y)` and cutoff `A`. -/
noncomputable def U_flow (Phi : ℝ → ℝ) (t A x y : ℝ) : ℝ :=
  ‖A_transform (heatPhi Phi t) A x y‖ ^ 2 - ‖B_transform (heatPhi Phi t) A x y‖ ^ 2

/-- `U_flow` in rank-4 real form: `(L₁²+L₃²) − (L₂²+L₄²)` of the deformed amplitude. -/
theorem U_flow_eq_rankFour (Phi : ℝ → ℝ) (t A x y : ℝ) :
    U_flow Phi t A x y
      = ((L1 (heatPhi Phi t) A x y) ^ 2 + (L3 (heatPhi Phi t) A x y) ^ 2)
        - ((L2 (heatPhi Phi t) A x y) ^ 2 + (L4 (heatPhi Phi t) A x y) ^ 2) := by
  unfold U_flow
  rw [normSq_A_transform, normSq_B_transform]

/-- **Schur contractivity at a probe** under the flow at time `t`. -/
def SchurContractiveAt (Phi : ℝ → ℝ) (t A x y : ℝ) : Prop :=
  0 ≤ U_flow Phi t A x y

/-- **Schur dominance of the whole flow slice at time `t`** (all UHP probes, all
cutoffs). -/
def SchurFlowDominance (Phi : ℝ → ℝ) (t : ℝ) : Prop :=
  ∀ A x y : ℝ, 0 < A → 0 < y → SchurContractiveAt Phi t A x y

/-! ## §3. The flow slice at `t = 0` **is** `SpecialPhiHBDominance Φ` (PROVED) -/

/-- Schur contractivity at `t = 0` is, term-by-term, the rank-4 inequality of the
*undeformed* amplitude `Φ` (because `heatPhi Φ 0 = Φ`). -/
theorem schurAtZero_iff_rankFour (Phi : ℝ → ℝ) (A x y : ℝ) :
    SchurContractiveAt Phi 0 A x y
      ↔ (L2 Phi A x y) ^ 2 + (L4 Phi A x y) ^ 2
          ≤ (L1 Phi A x y) ^ 2 + (L3 Phi A x y) ^ 2 := by
  unfold SchurContractiveAt
  rw [U_flow_eq_rankFour, heatPhi_zero]
  constructor
  · intro h; linarith
  · intro h; linarith

/-- ⭐ **PROVED — the `t = 0` flow slice is exactly the open HB inequality.**
`SchurFlowDominance Φ 0  ↔  SpecialPhiHBDominance Φ`.  The Schur contractivity of the
heat flow *at the base point* is precisely the single RH-strength modulus inequality
`‖B‖ ≤ ‖A‖` of `ScratchHBDominance`.  This is the clean bridge identifying the flow
target with the HB target. -/
theorem schurAllZero_iff_specialPhiHB (Phi : ℝ → ℝ) :
    SchurFlowDominance Phi 0 ↔ SpecialPhiHBDominance Phi := by
  rw [hbDominance_iff_rankFour]
  unfold SchurFlowDominance RankFourDominance
  constructor
  · intro h A x y hA hy
    exact (schurAtZero_iff_rankFour Phi A x y).mp (h A x y hA hy)
  · intro h A x y hA hy
    exact (schurAtZero_iff_rankFour Phi A x y).mpr (h A x y hA hy)

/-! ## §4. The safe time and the first-contact wall (the dBN core, UNPROVEN) -/

/-- **Safe-time Schur dominance.**  At some large heat time `T` (well past `Λ`), the
whole flow slice is Schur-dominant.  For the genuine flow this is the de Bruijn “all
zeros real for large `t`” input (a *provable*, non-RH fact: large-`t` Gaussian damping
makes the deformed transform a Pólya/HB function).  We carry it as a named hypothesis. -/
def SafeTimeSchurDominance (Phi : ℝ → ℝ) (T : ℝ) : Prop :=
  0 < T ∧ SchurFlowDominance Phi T

/-- **No first-contact failure (the dBN wall = RH-strength core).**

`NoFirstContactFailure Φ T` says: there is **no** time `t ∈ [0, T)`, probe `(x, y)` in
the UHP, and cutoff `A` at which the Schur boundary is touched *from inside while moving
downward in `t`* — i.e. `U_flow = 0` there, with `U_flow ≥ 0` for all later times `t' ∈
(t, T]` (contractivity held above), yet the downward flow fails to keep it nonnegative
just below.  Concretely we encode the **propagation-blocking** form: whenever the slice
is dominant on `(t, T]`, it is already dominant at `t` itself.

This is exactly the statement that contractivity, once held at the safe time, is
**propagated downward** to the whole interval `[0, T]` without ever being first-lost —
the maximum-principle conclusion that the *protective sign* `∂_t U ≥ 0` holds at every
would-be first-contact.  We encode it in its operative *downward-closure* form: Schur
dominance at the top time `T` propagates to dominance at every `t ∈ [0, T]`.

By the dBN dictionary this is `Λ ≤ 0` (= RH).  It is **left unproven**; the numerics
show it holds in the finite-cutoff model but that is a Pólya artifact (the finite `H_t`
has all-real zeros for all tested `t`, so there is *no* contact event) and does **not**
settle the `A → ∞` threshold, where the split of a double real zero is marginal. -/
def NoFirstContactFailure (Phi : ℝ → ℝ) (T : ℝ) : Prop :=
  SchurFlowDominance Phi T →
    ∀ t : ℝ, 0 ≤ t → t ≤ T → SchurFlowDominance Phi t

/-! ## §5. The provable propagation bridge -/

/-- The downward-propagation core: `NoFirstContactFailure` carries Schur dominance at the
top time `T` down to any earlier `t ∈ [0, T]`.  This is the maximum-principle propagation
skeleton; the analytic protective-sign content is sealed inside `NoFirstContactFailure`. -/
theorem schurFlow_down_of_noFirstContact
    {Phi : ℝ → ℝ} {T : ℝ}
    (hNFC : NoFirstContactFailure Phi T)
    (hTop : SchurFlowDominance Phi T)
    {t : ℝ} (ht0 : 0 ≤ t) (htT : t ≤ T) :
    SchurFlowDominance Phi t :=
  hNFC hTop t ht0 htT

/-- ⭐ **PROVED — propagation bridge to the `t = 0` slice.**

Given:
* `SafeTimeSchurDominance Φ T` — Schur dominance at the safe time `T > 0`, and
* `NoFirstContactFailure Φ T` — no first-contact failure on the way down,

the Schur dominance propagates to `t = 0`, i.e. `SchurFlowDominance Φ 0`, which by
`schurAllZero_iff_specialPhiHB` is `SpecialPhiHBDominance Φ`.

Mechanism: the safe-time hypothesis gives dominance at `T`; `NoFirstContactFailure`
propagates it down to `t = 0` (which lies in `[0, T]` since `T > 0`); the `t = 0` slice
is `SpecialPhiHBDominance Φ` by §3.

The **only** inputs are `SafeTimeSchurDominance` (a *provable*, non-RH large-`t` fact) and
`NoFirstContactFailure` (= `Λ ≤ 0` = RH, **unproven**); everything else is discharged. -/
theorem specialPhiHBDominance_of_flowInvariance
    {Phi : ℝ → ℝ} {T : ℝ}
    (hSafe : SafeTimeSchurDominance Phi T)
    (hNFC : NoFirstContactFailure Phi T) :
    SpecialPhiHBDominance Phi := by
  obtain ⟨hT, hSafeDom⟩ := hSafe
  -- propagate dominance from the safe top T down to t = 0
  have h0 : SchurFlowDominance Phi 0 :=
    schurFlow_down_of_noFirstContact hNFC hSafeDom (le_refl 0) (le_of_lt hT)
  exact (schurAllZero_iff_specialPhiHB Phi).mp h0

/-! ## §6. Composition to `XiPullbackAntiHerglotzTarget` / RH -/

/-- ⭐ **PROVED — flow invariance ⟹ anti-Herglotz target.**  Composes the propagation
bridge (§5) with the proven `ScratchHBDominance` capstone
`XiPullbackAntiHerglotzTarget_of_specialPhiHBDominance`.  The standard analytic
interchanges (`hdiff`, `hAgree`, `hKF`, `hSOS`) are threaded exactly as that route
already requires; the only RH-strength input is `NoFirstContactFailure`. -/
theorem XiPullbackAntiHerglotzTarget_of_flowInvariance
    {Phi : ℝ → ℝ} {T : ℝ} (A : ℝ) (hA : 0 < A)
    (hdiff : ∀ z : ℂ, 0 < z.im → DifferentiableAt ℂ XiPullback z)
    (hAgree : TransformIsPullback Phi A)
    (hKF : ∀ x y : ℝ, 0 < y → KernelForm Phi A x y)
    (hSOS : ∀ A x y : ℝ, 0 < A → 0 < y → SOSDifferenceForm Phi A x y)
    (hSafe : SafeTimeSchurDominance Phi T)
    (hNFC : NoFirstContactFailure Phi T) :
    XiPullbackAntiHerglotzTarget :=
  XiPullbackAntiHerglotzTarget_of_specialPhiHBDominance Phi A hA hdiff hAgree hKF hSOS
    (specialPhiHBDominance_of_flowInvariance hSafe hNFC)

/-! ## §7. The dBN dictionary:  `NoFirstContactFailure ↔ Λ ≤ 0`

We record the wall as a *data* bridge to `ScratchDeBranges`’s `RH_iff_Lam_eq_zero`.
The forward content — that no-first-contact failure is equivalent to `Λ ≤ 0`, and hence
(with Rodgers–Tao `Λ ≥ 0`) to `Λ = 0` — is the precise location of RH.  It is carried as
an honest equivalence Prop, **not** proved. -/

/-- The bridge predicate: no-first-contact failure of the Schur flow is equivalent to the
de Bruijn–Newman constant being `≤ 0`.  Both sides are RH; this names their identification
(the “first contact = a zero leaving the line” correspondence).  Carrying it is not
assuming RH — it is the *statement* of where RH sits on this route. -/
def NoFirstContactFailure_iff_dBN_le_zero
    (Phi : ℝ → ℝ) (T A : ℝ) (dBN : ScratchDeBranges.DeBruijnNewmanConstant Phi A) : Prop :=
  NoFirstContactFailure Phi T ↔ dBN.Lam ≤ 0

/-- ⭐ **PROVED — closing the wall given the dictionary + Rodgers–Tao.**  If the
no-first-contact/`Λ ≤ 0` dictionary holds, the safe-time + propagation route delivers
`SpecialPhiHBDominance Φ`, *and* Rodgers–Tao’s `Λ ≥ 0` pins `Λ = 0`.  This states
crisply that on this route the **only** missing fact is `NoFirstContactFailure` itself
(= `Λ ≤ 0` = RH). -/
theorem dBN_eq_zero_of_flowInvariance
    {Phi : ℝ → ℝ} {T A : ℝ}
    (dBN : ScratchDeBranges.DeBruijnNewmanConstant Phi A)
    (hRT : ScratchDeBranges.NewmanLowerBound Phi A dBN)
    (hDict : NoFirstContactFailure_iff_dBN_le_zero Phi T A dBN)
    (hNFC : NoFirstContactFailure Phi T) :
    dBN.Lam = 0 := by
  have hle : dBN.Lam ≤ 0 := (hDict).mp hNFC
  have hge : 0 ≤ dBN.Lam := hRT
  linarith

/-! ## §8. Axiom audit — only `propext`, `Classical.choice`, `Quot.sound`. -/

#print axioms schurAllZero_iff_specialPhiHB
#print axioms specialPhiHBDominance_of_flowInvariance
#print axioms XiPullbackAntiHerglotzTarget_of_flowInvariance
#print axioms dBN_eq_zero_of_flowInvariance
#print axioms U_flow_eq_rankFour

end ScratchHeatFlow
end BacklundTuring
end OverflowResidueRH
