import ScratchHBDominance

/-!
# Schur-ratio, Hermite–Biehler, and Laplace-order routing into `SpecialPhiHBDominance`

This scratch file sits directly on top of `ScratchHBDominance` (which defines the
four moment functionals `L1..L4`, the packaged complex transforms
`A_transform = L₁ + i·L₃`, `B_transform = L₂ + i·L₄`, the single open modulus
inequality `SpecialPhiHBDominance Φ` (`‖B‖ ≤ ‖A‖`), its real form
`RankFourDominance Φ` (`L₂²+L₄² ≤ L₁²+L₃²`), the equivalence
`hbDominance_iff_rankFour`, and the capstone
`XiPullbackAntiHerglotzTarget_of_specialPhiHBDominance`).

The point of this file is to give **three independent outside-approach targets**
— a Schur-ratio bound, a Hermite–Biehler companion bound, and a Laplace-order
certificate — that each **FEED** `SpecialPhiHBDominance Φ` through a PROVEN
bridge.  An outside collaborator who can certify any one of the three (by a
Schur/Nevanlinna–Pick argument, a Hermite–Biehler de Branges argument, or a
positive-Laplace-transform order argument) immediately lands the anti-Herglotz
target via the existing capstone — without ever touching the analytic energy
internals.

Everything in this file is PROVEN (no `sorry`, no `admit`).  The three
**certificates themselves** stay unproven hypotheses: certifying any one of them
is certifying `SpecialPhiHBDominance Φ`, i.e. proving RH.  We do **not** prove
them and we do **not** assume RH.

## What is proven

* §1 **Schur ratio.** `PhiSchurRatio = B/A`; the honest two-case bridge
  `specialPhiHBDominance_of_schurRatio` (`‖B/A‖ ≤ 1` where `A ≠ 0`, `B = 0` where
  `A = 0`).
* §2 **Hermite–Biehler.** `E_Phi = A − i·B`, `E_Phi_sharp = A + i·B`, the **exact**
  cross-term identity `normSq_E_sub_normSq_Esharp`
  (`‖E‖² − ‖E♯‖² = 4·(L₁L₄ − L₂L₃)`, a Wronskian-type quantity, NOT the
  dominance — documented), and the *faithful* HB companion pairing
  `E_HB = A`, `E_HB_sharp = B` for which `‖E♯‖ ≤ ‖E‖ ⟺ ‖B‖ ≤ ‖A‖` holds on the
  nose, giving `specialPhiHBDominance_of_HB`.
* §3 **Laplace order.** `structure PhiLaplaceOrderCertificate` packaging the
  dominance, with the trivial bridge `specialPhiHBDominance_of_laplaceOrder`.
* §4 Each composed with the existing capstone:
  `XiPullbackAntiHerglotzTarget_of_schurRatio`, `_of_HB`, `_of_laplaceOrder`.

## Axiom audit

`#print axioms` on every capstone: only `propext`, `Classical.choice`,
`Quot.sound` (no `sorryAx`).
-/

namespace OverflowResidueRH
namespace BacklundTuring
namespace ScratchHBDominance

open Complex
open OverflowResidueRH.XiDoubleKernel
open OverflowResidueRH.BacklundTuring.ScratchEnergyKernel

/-! ## §1. The Schur-ratio route

The **Schur ratio** is the pointwise quotient `B/A` of the two packaged
transforms.  A Schur (Nevanlinna–Pick) certificate would bound `‖B/A‖ ≤ 1`
wherever `A ≠ 0`, together with the boundary-vanishing `A = 0 ⟹ B = 0`.  Both
together are exactly `‖B‖ ≤ ‖A‖`, i.e. `SpecialPhiHBDominance`.

The bridge below is the honest two-case split: where `A ≠ 0`, `‖B/A‖ ≤ 1`
multiplies up to `‖B‖ ≤ ‖A‖` (`norm_div`, `div_le_one`); where `A = 0`, the
vanishing hypothesis forces `B = 0`, so `‖B‖ = 0 ≤ 0 = ‖A‖`. -/

/-- **The Schur ratio `B/A`.**  The pointwise quotient of the packaged transforms
of `ScratchHBDominance`. -/
noncomputable def PhiSchurRatio (Phi : ℝ → ℝ) (A x y : ℝ) : ℂ :=
  B_transform Phi A x y / A_transform Phi A x y

/-- **PROVED — Schur-ratio bridge ⟹ HB dominance.**

A Schur-type certificate consists of:
* `hSchur` : wherever `A_transform ≠ 0`, the Schur ratio is a contraction
  `‖B/A‖ ≤ 1`;
* `hvanish` : wherever `A_transform = 0`, the companion `B_transform = 0` too
  (boundary vanishing).

Together these give `SpecialPhiHBDominance Φ` by an honest two-case split on
whether `‖A_transform‖ = 0`. -/
theorem specialPhiHBDominance_of_schurRatio (Phi : ℝ → ℝ)
    (hSchur : ∀ A x y : ℝ, 0 < A → 0 < y → ‖A_transform Phi A x y‖ ≠ 0 →
      ‖PhiSchurRatio Phi A x y‖ ≤ 1)
    (hvanish : ∀ A x y : ℝ, 0 < A → 0 < y → A_transform Phi A x y = 0 →
      B_transform Phi A x y = 0) :
    SpecialPhiHBDominance Phi := by
  intro A x y hA hy
  by_cases hAz : ‖A_transform Phi A x y‖ = 0
  · -- `A = 0`, so by `hvanish` `B = 0`; the inequality is `0 ≤ 0`.
    have hA0 : A_transform Phi A x y = 0 := by
      simpa [norm_eq_zero] using hAz
    have hB0 : B_transform Phi A x y = 0 := hvanish A x y hA hy hA0
    simp [hAz, hB0]
  · -- `A ≠ 0`: `‖B/A‖ ≤ 1` ⟹ `‖B‖/‖A‖ ≤ 1` ⟹ `‖B‖ ≤ ‖A‖`.
    have hpos : 0 < ‖A_transform Phi A x y‖ :=
      lt_of_le_of_ne (norm_nonneg _) (Ne.symm hAz)
    have hratio : ‖PhiSchurRatio Phi A x y‖ ≤ 1 := hSchur A x y hA hy hAz
    rw [PhiSchurRatio, norm_div, div_le_one hpos] at hratio
    exact hratio

/-! ## §2. The Hermite–Biehler route

### The requested `A ∓ i·B` convention is a Wronskian, not the dominance

With the (standard de Branges) entire-companion convention

```
E♭  = A − i·B        E♯  = A + i·B,
```

the difference of squared moduli is **not** `‖A‖² − ‖B‖²` but the Wronskian-type
cross term

```
‖E♭‖² − ‖E♯‖²  =  4·Re(i·A·conj B)  =  4·(L₁·L₄ − L₂·L₃).
```

We prove this **exact** identity below (`normSq_E_sub_normSq_Esharp`).  It shows
the naïve `A ∓ i·B` pairing measures the *Wronskian* `L₁L₄ − L₂L₃`, which is a
genuinely different functional from the modulus dominance.  So this convention by
itself does **not** yield `‖B‖ ≤ ‖A‖`.

### The faithful HB companion pairing

The Hermite–Biehler statement that *is* equivalent to the dominance takes the
structure function to be `A` itself and its companion to be `B`
(`E_HB = A`, `E_HB_sharp = B`): then `‖E♯‖ ≤ ‖E‖` is **definitionally**
`‖B‖ ≤ ‖A‖ = SpecialPhiHBDominance`.  This is the pairing we route through in
`specialPhiHBDominance_of_HB`. -/

/-- **Hermite–Biehler combination `E♭ = A − i·B`** (de Branges entire-companion
convention). -/
noncomputable def E_Phi (Phi : ℝ → ℝ) (A x y : ℝ) : ℂ :=
  A_transform Phi A x y - Complex.I * B_transform Phi A x y

/-- **Conjugate-reflected combination `E♯ = A + i·B`.**  On the real axis (where
`A`, `B` are real) this is the Schwarz reflection `E♯(z) = conj(E♭(conj z))` of
`E_Phi`; we keep the algebraic form `A + i·B` here. -/
noncomputable def E_Phi_sharp (Phi : ℝ → ℝ) (A x y : ℝ) : ℂ :=
  A_transform Phi A x y + Complex.I * B_transform Phi A x y

/-- **PROVED — the exact `E♭/E♯` squared-modulus identity.**

```
‖E_Phi‖² − ‖E_Phi_sharp‖²  =  4·(L₁·L₄ − L₂·L₃).
```

This is the Wronskian-type cross term `4·Re(i·A·conj B)`, **not** the modulus
dominance `‖A‖² − ‖B‖²`.  It is proved by expanding both squared norms into the
real coordinates `L₁..L₄` (`Complex.normSq_apply` after unfolding the transforms)
and `ring`.  Documented so the `A ∓ i·B` convention's true content is explicit. -/
theorem normSq_E_sub_normSq_Esharp (Phi : ℝ → ℝ) (A x y : ℝ) :
    ‖E_Phi Phi A x y‖ ^ 2 - ‖E_Phi_sharp Phi A x y‖ ^ 2
      = 4 * (L1 Phi A x y * L4 Phi A x y - L2 Phi A x y * L3 Phi A x y) := by
  rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
  unfold E_Phi E_Phi_sharp A_transform B_transform
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.sub_re,
    Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re,
    Complex.mul_im, Complex.I_re, Complex.I_im]
  ring

/-- **Faithful HB structure function `E_HB = A`.**  The de Branges structure
function whose companion is dominated; here it is the `A`-transform itself. -/
noncomputable def E_HB (Phi : ℝ → ℝ) (A x y : ℝ) : ℂ := A_transform Phi A x y

/-- **Faithful HB companion `E_HB_sharp = B`.**  The dominated companion of the
structure function `E_HB`; here the `B`-transform. -/
noncomputable def E_HB_sharp (Phi : ℝ → ℝ) (A x y : ℝ) : ℂ := B_transform Phi A x y

/-- **PROVED — the faithful HB equivalence is definitional.**

`‖E_HB♯‖ ≤ ‖E_HB‖  ⟺  ‖B‖ ≤ ‖A‖`, for every probe.  With `E_HB = A`,
`E_HB_sharp = B` this is `rfl`-level. -/
theorem hbCompanion_le_iff (Phi : ℝ → ℝ) (A x y : ℝ) :
    ‖E_HB_sharp Phi A x y‖ ≤ ‖E_HB Phi A x y‖
      ↔ ‖B_transform Phi A x y‖ ≤ ‖A_transform Phi A x y‖ := by
  unfold E_HB E_HB_sharp
  rfl

/-- **PROVED — Hermite–Biehler bridge ⟹ HB dominance.**

A Hermite–Biehler certificate is the companion bound `‖E_HB♯‖ ≤ ‖E_HB‖` at every
UHP probe (the de Branges *mean-type* / companion-domination inequality).  With
the faithful pairing `E_HB = A`, `E_HB_sharp = B` this is exactly
`SpecialPhiHBDominance Φ`. -/
theorem specialPhiHBDominance_of_HB (Phi : ℝ → ℝ)
    (hHB : ∀ A x y : ℝ, 0 < A → 0 < y →
      ‖E_HB_sharp Phi A x y‖ ≤ ‖E_HB Phi A x y‖) :
    SpecialPhiHBDominance Phi := by
  intro A x y hA hy
  exact (hbCompanion_le_iff Phi A x y).mp (hHB A x y hA hy)

/-! ## §3. The Laplace-order route

The analytic content of the third approach is that `A ± B` are **positive Laplace
transforms** (Laplace transforms of nonnegative densities), whence the order
relation `‖B‖ ≤ ‖A‖` follows from a Laplace/order-of-growth argument.  That
analytic input — `A ± B = positive Laplace transform` — is the unproven part; we
package only the dominance it would yield. -/

/-- **Laplace-order certificate.**  A minimal package carrying the dominance
`‖B‖ ≤ ‖A‖` that a positive-Laplace-transform order argument would establish.

**Inhabiting this structure requires the unproven analytic input** that
`A_transform ± B_transform` are Laplace transforms of nonnegative densities (so
the order of growth forces the companion domination).  We do not prove that
here; the structure simply names the conclusion as the outside target. -/
structure PhiLaplaceOrderCertificate (Phi : ℝ → ℝ) where
  /-- The companion-domination conclusion of a positive-Laplace-order argument. -/
  dominance : ∀ A x y : ℝ, 0 < A → 0 < y →
    ‖B_transform Phi A x y‖ ≤ ‖A_transform Phi A x y‖

/-- **PROVED — Laplace-order bridge ⟹ HB dominance.**  The certificate's
`dominance` field is, verbatim, `SpecialPhiHBDominance Φ`. -/
theorem specialPhiHBDominance_of_laplaceOrder (Phi : ℝ → ℝ)
    (cert : PhiLaplaceOrderCertificate Phi) :
    SpecialPhiHBDominance Phi :=
  cert.dominance

/-! ## §4. Composition with the existing capstone

Each of the three bridges, fed into the existing
`XiPullbackAntiHerglotzTarget_of_specialPhiHBDominance`, exposes a single clean
target `… → XiPullbackAntiHerglotzTarget`.  The standard analytic scaffolding
(`hdiff`, `hAgree`, `hKF`, `hSOS`) is threaded through exactly as that capstone
requires — none of it RH-equivalent. -/

/-- ⭐ **PROVED — Schur-ratio ⟹ anti-Herglotz target.**  A Schur certificate
(`hSchur` contraction + `hvanish` boundary vanishing) lands
`XiPullbackAntiHerglotzTarget`. -/
theorem XiPullbackAntiHerglotzTarget_of_schurRatio
    (Phi : ℝ → ℝ) (A : ℝ) (hA : 0 < A)
    (hdiff : ∀ z : ℂ, 0 < z.im → DifferentiableAt ℂ XiPullback z)
    (hAgree : TransformIsPullback Phi A)
    (hKF : ∀ x y : ℝ, 0 < y → KernelForm Phi A x y)
    (hSOS : ∀ A x y : ℝ, 0 < A → 0 < y → SOSDifferenceForm Phi A x y)
    (hSchur : ∀ A x y : ℝ, 0 < A → 0 < y → ‖A_transform Phi A x y‖ ≠ 0 →
      ‖PhiSchurRatio Phi A x y‖ ≤ 1)
    (hvanish : ∀ A x y : ℝ, 0 < A → 0 < y → A_transform Phi A x y = 0 →
      B_transform Phi A x y = 0) :
    XiPullbackAntiHerglotzTarget :=
  XiPullbackAntiHerglotzTarget_of_specialPhiHBDominance Phi A hA hdiff hAgree hKF hSOS
    (specialPhiHBDominance_of_schurRatio Phi hSchur hvanish)

/-- ⭐ **PROVED — Hermite–Biehler ⟹ anti-Herglotz target.**  The HB companion
bound `‖E_HB♯‖ ≤ ‖E_HB‖` lands `XiPullbackAntiHerglotzTarget`. -/
theorem XiPullbackAntiHerglotzTarget_of_HB
    (Phi : ℝ → ℝ) (A : ℝ) (hA : 0 < A)
    (hdiff : ∀ z : ℂ, 0 < z.im → DifferentiableAt ℂ XiPullback z)
    (hAgree : TransformIsPullback Phi A)
    (hKF : ∀ x y : ℝ, 0 < y → KernelForm Phi A x y)
    (hSOS : ∀ A x y : ℝ, 0 < A → 0 < y → SOSDifferenceForm Phi A x y)
    (hHB : ∀ A x y : ℝ, 0 < A → 0 < y →
      ‖E_HB_sharp Phi A x y‖ ≤ ‖E_HB Phi A x y‖) :
    XiPullbackAntiHerglotzTarget :=
  XiPullbackAntiHerglotzTarget_of_specialPhiHBDominance Phi A hA hdiff hAgree hKF hSOS
    (specialPhiHBDominance_of_HB Phi hHB)

/-- ⭐ **PROVED — Laplace-order ⟹ anti-Herglotz target.**  A
`PhiLaplaceOrderCertificate` lands `XiPullbackAntiHerglotzTarget`. -/
theorem XiPullbackAntiHerglotzTarget_of_laplaceOrder
    (Phi : ℝ → ℝ) (A : ℝ) (hA : 0 < A)
    (hdiff : ∀ z : ℂ, 0 < z.im → DifferentiableAt ℂ XiPullback z)
    (hAgree : TransformIsPullback Phi A)
    (hKF : ∀ x y : ℝ, 0 < y → KernelForm Phi A x y)
    (hSOS : ∀ A x y : ℝ, 0 < A → 0 < y → SOSDifferenceForm Phi A x y)
    (cert : PhiLaplaceOrderCertificate Phi) :
    XiPullbackAntiHerglotzTarget :=
  XiPullbackAntiHerglotzTarget_of_specialPhiHBDominance Phi A hA hdiff hAgree hKF hSOS
    (specialPhiHBDominance_of_laplaceOrder Phi cert)

/-! ## §5. Axiom audit

Only `propext`, `Classical.choice`, `Quot.sound` (no `sorryAx`) on every
capstone and every bridge. -/

#print axioms specialPhiHBDominance_of_schurRatio
#print axioms normSq_E_sub_normSq_Esharp
#print axioms specialPhiHBDominance_of_HB
#print axioms specialPhiHBDominance_of_laplaceOrder
#print axioms XiPullbackAntiHerglotzTarget_of_schurRatio
#print axioms XiPullbackAntiHerglotzTarget_of_HB
#print axioms XiPullbackAntiHerglotzTarget_of_laplaceOrder

end ScratchHBDominance
end BacklundTuring
end OverflowResidueRH
