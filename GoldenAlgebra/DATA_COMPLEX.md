Basic.lean:
```
/-
Copyright (c) 2017 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Mario Carneiro
-/
import Mathlib.Algebra.Ring.CharZero
import Mathlib.Algebra.Star.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Set.UnorderedInterval
import Mathlib.Tactic.Ring

/-!
# The complex numbers

The complex numbers are modelled as ℝ^2 in the obvious way and it is shown that they form a field
of characteristic zero. For the result that the complex numbers are algebraically closed, see
`Complex.isAlgClosed` in `Mathlib.Analysis.Complex.Polynomial.Basic`.
-/

assert_not_exists Multiset Algebra

open Set Function

/-! ### Definition and basic arithmetic -/


/-- Complex numbers consist of two `Real`s: a real part `re` and an imaginary part `im`. -/
structure Complex : Type where
  /-- The real part of a complex number. -/
  re : ℝ
  /-- The imaginary part of a complex number. -/
  im : ℝ

@[inherit_doc] notation "ℂ" => Complex

namespace Complex

open ComplexConjugate

noncomputable instance : DecidableEq ℂ :=
  Classical.decEq _

/-- The equivalence between the complex numbers and `ℝ × ℝ`. -/
@[simps apply]
def equivRealProd : ℂ ≃ ℝ × ℝ where
  toFun z := ⟨z.re, z.im⟩
  invFun p := ⟨p.1, p.2⟩

@[simp]
theorem eta : ∀ z : ℂ, Complex.mk z.re z.im = z
  | ⟨_, _⟩ => rfl

-- We only mark this lemma with `ext` *locally* to avoid it applying whenever terms of `ℂ` appear.
theorem ext : ∀ {z w : ℂ}, z.re = w.re → z.im = w.im → z = w
  | ⟨_, _⟩, ⟨_, _⟩, rfl, rfl => rfl

attribute [local ext] Complex.ext

lemma «forall» {p : ℂ → Prop} : (∀ x, p x) ↔ ∀ a b, p ⟨a, b⟩ := by aesop
lemma «exists» {p : ℂ → Prop} : (∃ x, p x) ↔ ∃ a b, p ⟨a, b⟩ := by aesop

theorem re_surjective : Surjective re := fun x => ⟨⟨x, 0⟩, rfl⟩

theorem im_surjective : Surjective im := fun y => ⟨⟨0, y⟩, rfl⟩

@[simp]
theorem range_re : range re = univ :=
  re_surjective.range_eq

@[simp]
theorem range_im : range im = univ :=
  im_surjective.range_eq

/-- The natural inclusion of the real numbers into the complex numbers. -/
@[coe]
def ofReal (r : ℝ) : ℂ :=
  ⟨r, 0⟩
instance : Coe ℝ ℂ :=
  ⟨ofReal⟩

@[simp, norm_cast]
theorem ofReal_re (r : ℝ) : Complex.re (r : ℂ) = r :=
  rfl

@[simp, norm_cast]
theorem ofReal_im (r : ℝ) : (r : ℂ).im = 0 :=
  rfl

theorem ofReal_def (r : ℝ) : (r : ℂ) = ⟨r, 0⟩ :=
  rfl

@[simp, norm_cast]
theorem ofReal_inj {z w : ℝ} : (z : ℂ) = w ↔ z = w :=
  ⟨congrArg re, by apply congrArg⟩

theorem ofReal_injective : Function.Injective ((↑) : ℝ → ℂ) := fun _ _ => congrArg re

instance canLift : CanLift ℂ ℝ (↑) fun z => z.im = 0 where
  prf z hz := ⟨z.re, ext rfl hz.symm⟩

/-- The product of a set on the real axis and a set on the imaginary axis of the complex plane,
denoted by `s ×ℂ t`. -/
def reProdIm (s t : Set ℝ) : Set ℂ :=
  re ⁻¹' s ∩ im ⁻¹' t

@[deprecated (since := "2024-12-03")] protected alias Set.reProdIm := reProdIm

@[inherit_doc]
infixl:72 " ×ℂ " => reProdIm

theorem mem_reProdIm {z : ℂ} {s t : Set ℝ} : z ∈ s ×ℂ t ↔ z.re ∈ s ∧ z.im ∈ t :=
  Iff.rfl

instance : Zero ℂ :=
  ⟨(0 : ℝ)⟩

instance : Inhabited ℂ :=
  ⟨0⟩

@[simp]
theorem zero_re : (0 : ℂ).re = 0 :=
  rfl

@[simp]
theorem zero_im : (0 : ℂ).im = 0 :=
  rfl

@[simp, norm_cast]
theorem ofReal_zero : ((0 : ℝ) : ℂ) = 0 :=
  rfl

@[simp]
theorem ofReal_eq_zero {z : ℝ} : (z : ℂ) = 0 ↔ z = 0 :=
  ofReal_inj

theorem ofReal_ne_zero {z : ℝ} : (z : ℂ) ≠ 0 ↔ z ≠ 0 :=
  not_congr ofReal_eq_zero

instance : One ℂ :=
  ⟨(1 : ℝ)⟩

@[simp]
theorem one_re : (1 : ℂ).re = 1 :=
  rfl

@[simp]
theorem one_im : (1 : ℂ).im = 0 :=
  rfl

@[simp, norm_cast]
theorem ofReal_one : ((1 : ℝ) : ℂ) = 1 :=
  rfl

@[simp]
theorem ofReal_eq_one {z : ℝ} : (z : ℂ) = 1 ↔ z = 1 :=
  ofReal_inj

theorem ofReal_ne_one {z : ℝ} : (z : ℂ) ≠ 1 ↔ z ≠ 1 :=
  not_congr ofReal_eq_one

instance : Add ℂ :=
  ⟨fun z w => ⟨z.re + w.re, z.im + w.im⟩⟩

@[simp]
theorem add_re (z w : ℂ) : (z + w).re = z.re + w.re :=
  rfl

@[simp]
theorem add_im (z w : ℂ) : (z + w).im = z.im + w.im :=
  rfl

-- replaced by `re_ofNat`
-- replaced by `im_ofNat`

@[simp, norm_cast]
theorem ofReal_add (r s : ℝ) : ((r + s : ℝ) : ℂ) = r + s :=
  Complex.ext_iff.2 <| by simp [ofReal]

-- replaced by `Complex.ofReal_ofNat`

instance : Neg ℂ :=
  ⟨fun z => ⟨-z.re, -z.im⟩⟩

@[simp]
theorem neg_re (z : ℂ) : (-z).re = -z.re :=
  rfl

@[simp]
theorem neg_im (z : ℂ) : (-z).im = -z.im :=
  rfl

@[simp, norm_cast]
theorem ofReal_neg (r : ℝ) : ((-r : ℝ) : ℂ) = -r :=
  Complex.ext_iff.2 <| by simp [ofReal]

instance : Sub ℂ :=
  ⟨fun z w => ⟨z.re - w.re, z.im - w.im⟩⟩

instance : Mul ℂ :=
  ⟨fun z w => ⟨z.re * w.re - z.im * w.im, z.re * w.im + z.im * w.re⟩⟩

@[simp]
theorem mul_re (z w : ℂ) : (z * w).re = z.re * w.re - z.im * w.im :=
  rfl

@[simp]
theorem mul_im (z w : ℂ) : (z * w).im = z.re * w.im + z.im * w.re :=
  rfl

@[simp, norm_cast]
theorem ofReal_mul (r s : ℝ) : ((r * s : ℝ) : ℂ) = r * s :=
  Complex.ext_iff.2 <| by simp [ofReal]

theorem re_ofReal_mul (r : ℝ) (z : ℂ) : (r * z).re = r * z.re := by simp [ofReal]

theorem im_ofReal_mul (r : ℝ) (z : ℂ) : (r * z).im = r * z.im := by simp [ofReal]

lemma re_mul_ofReal (z : ℂ) (r : ℝ) : (z * r).re = z.re *  r := by simp [ofReal]
lemma im_mul_ofReal (z : ℂ) (r : ℝ) : (z * r).im = z.im *  r := by simp [ofReal]

theorem ofReal_mul' (r : ℝ) (z : ℂ) : ↑r * z = ⟨r * z.re, r * z.im⟩ :=
  ext (re_ofReal_mul _ _) (im_ofReal_mul _ _)

/-! ### The imaginary unit, `I` -/


/-- The imaginary unit. -/
def I : ℂ :=
  ⟨0, 1⟩

@[simp]
theorem I_re : I.re = 0 :=
  rfl

@[simp]
theorem I_im : I.im = 1 :=
  rfl

@[simp]
theorem I_mul_I : I * I = -1 :=
  Complex.ext_iff.2 <| by simp

theorem I_mul (z : ℂ) : I * z = ⟨-z.im, z.re⟩ :=
  Complex.ext_iff.2 <| by simp

@[simp] lemma I_ne_zero : (I : ℂ) ≠ 0 := mt (congr_arg im) zero_ne_one.symm

theorem mk_eq_add_mul_I (a b : ℝ) : Complex.mk a b = a + b * I :=
  Complex.ext_iff.2 <| by simp [ofReal]

@[simp]
theorem re_add_im (z : ℂ) : (z.re : ℂ) + z.im * I = z :=
  Complex.ext_iff.2 <| by simp [ofReal]

theorem mul_I_re (z : ℂ) : (z * I).re = -z.im := by simp

theorem mul_I_im (z : ℂ) : (z * I).im = z.re := by simp

theorem I_mul_re (z : ℂ) : (I * z).re = -z.im := by simp

theorem I_mul_im (z : ℂ) : (I * z).im = z.re := by simp

@[simp]
theorem equivRealProd_symm_apply (p : ℝ × ℝ) : equivRealProd.symm p = p.1 + p.2 * I := by
  ext <;> simp [Complex.equivRealProd, ofReal]

/-- The natural `AddEquiv` from `ℂ` to `ℝ × ℝ`. -/
@[simps! +simpRhs apply symm_apply_re symm_apply_im]
def equivRealProdAddHom : ℂ ≃+ ℝ × ℝ :=
  { equivRealProd with map_add' := by simp }

theorem equivRealProdAddHom_symm_apply (p : ℝ × ℝ) :
    equivRealProdAddHom.symm p = p.1 + p.2 * I := equivRealProd_symm_apply p

/-! ### Commutative ring instance and lemmas -/


/- We use a nonstandard formula for the `ℕ` and `ℤ` actions to make sure there is no
diamond from the other actions they inherit through the `ℝ`-action on `ℂ` and action transitivity
defined in `Data.Complex.Module`. -/
instance : Nontrivial ℂ :=
  domain_nontrivial re rfl rfl

namespace SMul

-- The useless `0` multiplication in `smul` is to make sure that
-- `RestrictScalars.module ℝ ℂ ℂ = Complex.module` definitionally.
-- instance made scoped to avoid situations like instance synthesis
-- of `SMul ℂ ℂ` trying to proceed via `SMul ℂ ℝ`.
/-- Scalar multiplication by `R` on `ℝ` extends to `ℂ`. This is used here and in
`Matlib.Data.Complex.Module` to transfer instances from `ℝ` to `ℂ`, but is not
needed outside, so we make it scoped. -/
scoped instance instSMulRealComplex {R : Type*} [SMul R ℝ] : SMul R ℂ where
  smul r x := ⟨r • x.re - 0 * x.im, r • x.im + 0 * x.re⟩

end SMul

open scoped SMul

section SMul

variable {R : Type*} [SMul R ℝ]

theorem smul_re (r : R) (z : ℂ) : (r • z).re = r • z.re := by simp [(· • ·), SMul.smul]

theorem smul_im (r : R) (z : ℂ) : (r • z).im = r • z.im := by simp [(· • ·), SMul.smul]

@[simp]
theorem real_smul {x : ℝ} {z : ℂ} : x • z = x * z :=
  rfl

end SMul

instance addCommGroup : AddCommGroup ℂ :=
  { zero := (0 : ℂ)
    add := (· + ·)
    neg := Neg.neg
    sub := Sub.sub
    nsmul := fun n z => n • z
    zsmul := fun n z => n • z
    zsmul_zero' := by intros; ext <;> simp [smul_re, smul_im]
    nsmul_zero := by intros; ext <;> simp [smul_re, smul_im]
    nsmul_succ := by intros; ext <;> simp [smul_re, smul_im] <;> ring
    zsmul_succ' := by intros; ext <;> simp [smul_re, smul_im] <;> ring
    zsmul_neg' := by intros; ext <;> simp [smul_re, smul_im] <;> ring
    add_assoc := by intros; ext <;> simp <;> ring
    zero_add := by intros; ext <;> simp
    add_zero := by intros; ext <;> simp
    add_comm := by intros; ext <;> simp <;> ring
    neg_add_cancel := by intros; ext <;> simp }


instance addGroupWithOne : AddGroupWithOne ℂ :=
  { Complex.addCommGroup with
    natCast := fun n => ⟨n, 0⟩
    natCast_zero := by
      ext <;> simp [Nat.cast, AddMonoidWithOne.natCast_zero]
    natCast_succ := fun _ => by ext <;> simp [Nat.cast, AddMonoidWithOne.natCast_succ]
    intCast := fun n => ⟨n, 0⟩
    intCast_ofNat := fun _ => by ext <;> rfl
    intCast_negSucc := fun n => by
      ext
      · simp [AddGroupWithOne.intCast_negSucc]
        show -(1 : ℝ) + (-n) = -(↑(n + 1))
        simp [Nat.cast_add, add_comm]
      · simp [AddGroupWithOne.intCast_negSucc]
        show im ⟨n, 0⟩ = 0
        rfl
    one := 1 }

instance commRing : CommRing ℂ :=
  { addGroupWithOne with
    mul := (· * ·)
    npow := @npowRec _ ⟨(1 : ℂ)⟩ ⟨(· * ·)⟩
    add_comm := by intros; ext <;> simp <;> ring
    left_distrib := by intros; ext <;> simp [mul_re, mul_im] <;> ring
    right_distrib := by intros; ext <;> simp [mul_re, mul_im] <;> ring
    zero_mul := by intros; ext <;> simp
    mul_zero := by intros; ext <;> simp
    mul_assoc := by intros; ext <;> simp <;> ring
    one_mul := by intros; ext <;> simp
    mul_one := by intros; ext <;> simp
    mul_comm := by intros; ext <;> simp <;> ring }

/-- This shortcut instance ensures we do not find `Ring` via the noncomputable `Complex.field`
instance. -/
instance : Ring ℂ := by infer_instance

/-- This shortcut instance ensures we do not find `CommSemiring` via the noncomputable
`Complex.field` instance. -/
instance : CommSemiring ℂ :=
  inferInstance

/-- This shortcut instance ensures we do not find `Semiring` via the noncomputable
`Complex.field` instance. -/
instance : Semiring ℂ :=
  inferInstance

/-- The "real part" map, considered as an additive group homomorphism. -/
def reAddGroupHom : ℂ →+ ℝ where
  toFun := re
  map_zero' := zero_re
  map_add' := add_re

@[simp]
theorem coe_reAddGroupHom : (reAddGroupHom : ℂ → ℝ) = re :=
  rfl

/-- The "imaginary part" map, considered as an additive group homomorphism. -/
def imAddGroupHom : ℂ →+ ℝ where
  toFun := im
  map_zero' := zero_im
  map_add' := add_im

@[simp]
theorem coe_imAddGroupHom : (imAddGroupHom : ℂ → ℝ) = im :=
  rfl

/-! ### Cast lemmas -/

instance instNNRatCast : NNRatCast ℂ where nnratCast q := ofReal q
instance instRatCast : RatCast ℂ where ratCast q := ofReal q

@[simp, norm_cast] lemma ofReal_ofNat (n : ℕ) [n.AtLeastTwo] : ofReal ofNat(n) = ofNat(n) := rfl
@[simp, norm_cast] lemma ofReal_natCast (n : ℕ) : ofReal n = n := rfl
@[simp, norm_cast] lemma ofReal_intCast (n : ℤ) : ofReal n = n := rfl
@[simp, norm_cast] lemma ofReal_nnratCast (q : ℚ≥0) : ofReal q = q := rfl
@[simp, norm_cast] lemma ofReal_ratCast (q : ℚ) : ofReal q = q := rfl

@[simp]
lemma re_ofNat (n : ℕ) [n.AtLeastTwo] : (ofNat(n) : ℂ).re = ofNat(n) := rfl
@[simp] lemma im_ofNat (n : ℕ) [n.AtLeastTwo] : (ofNat(n) : ℂ).im = 0 := rfl
@[simp, norm_cast] lemma natCast_re (n : ℕ) : (n : ℂ).re = n := rfl
@[simp, norm_cast] lemma natCast_im (n : ℕ) : (n : ℂ).im = 0 := rfl
@[simp, norm_cast] lemma intCast_re (n : ℤ) : (n : ℂ).re = n := rfl
@[simp, norm_cast] lemma intCast_im (n : ℤ) : (n : ℂ).im = 0 := rfl
@[simp, norm_cast] lemma re_nnratCast (q : ℚ≥0) : (q : ℂ).re = q := rfl
@[simp, norm_cast] lemma im_nnratCast (q : ℚ≥0) : (q : ℂ).im = 0 := rfl
@[simp, norm_cast] lemma ratCast_re (q : ℚ) : (q : ℂ).re = q := rfl
@[simp, norm_cast] lemma ratCast_im (q : ℚ) : (q : ℂ).im = 0 := rfl

lemma re_nsmul (n : ℕ) (z : ℂ) : (n • z).re = n • z.re := smul_re ..
lemma im_nsmul (n : ℕ) (z : ℂ) : (n • z).im = n • z.im := smul_im ..
lemma re_zsmul (n : ℤ) (z : ℂ) : (n • z).re = n • z.re := smul_re ..
lemma im_zsmul (n : ℤ) (z : ℂ) : (n • z).im = n • z.im := smul_im ..
@[simp] lemma re_nnqsmul (q : ℚ≥0) (z : ℂ) : (q • z).re = q • z.re := smul_re ..
@[simp] lemma im_nnqsmul (q : ℚ≥0) (z : ℂ) : (q • z).im = q • z.im := smul_im ..
@[simp] lemma re_qsmul (q : ℚ) (z : ℂ) : (q • z).re = q • z.re := smul_re ..
@[simp] lemma im_qsmul (q : ℚ) (z : ℂ) : (q • z).im = q • z.im := smul_im ..

@[norm_cast] lemma ofReal_nsmul (n : ℕ) (r : ℝ) : ↑(n • r) = n • (r : ℂ) := by simp
@[norm_cast] lemma ofReal_zsmul (n : ℤ) (r : ℝ) : ↑(n • r) = n • (r : ℂ) := by simp

/-! ### Complex conjugation -/


/-- This defines the complex conjugate as the `star` operation of the `StarRing ℂ`. It
is recommended to use the ring endomorphism version `starRingEnd`, available under the
notation `conj` in the locale `ComplexConjugate`. -/
instance : StarRing ℂ where
  star z := ⟨z.re, -z.im⟩
  star_involutive x := by simp only [eta, neg_neg]
  star_mul a b := by ext <;> simp [add_comm] <;> ring
  star_add a b := by ext <;> simp [add_comm]

@[simp]
theorem conj_re (z : ℂ) : (conj z).re = z.re :=
  rfl

@[simp]
theorem conj_im (z : ℂ) : (conj z).im = -z.im :=
  rfl

@[simp]
theorem conj_ofReal (r : ℝ) : conj (r : ℂ) = r :=
  Complex.ext_iff.2 <| by simp [star]

@[simp]
theorem conj_I : conj I = -I :=
  Complex.ext_iff.2 <| by simp

theorem conj_natCast (n : ℕ) : conj (n : ℂ) = n := map_natCast _ _

theorem conj_ofNat (n : ℕ) [n.AtLeastTwo] : conj (ofNat(n) : ℂ) = ofNat(n) :=
  map_ofNat _ _

theorem conj_neg_I : conj (-I) = I := by simp

theorem conj_eq_iff_real {z : ℂ} : conj z = z ↔ ∃ r : ℝ, z = r :=
  ⟨fun h => ⟨z.re, ext rfl <| eq_zero_of_neg_eq (congr_arg im h)⟩, fun ⟨h, e⟩ => by
    rw [e, conj_ofReal]⟩

theorem conj_eq_iff_re {z : ℂ} : conj z = z ↔ (z.re : ℂ) = z :=
  conj_eq_iff_real.trans ⟨by rintro ⟨r, rfl⟩; simp [ofReal], fun h => ⟨_, h.symm⟩⟩

theorem conj_eq_iff_im {z : ℂ} : conj z = z ↔ z.im = 0 :=
  ⟨fun h => add_self_eq_zero.mp (neg_eq_iff_add_eq_zero.mp (congr_arg im h)), fun h =>
    ext rfl (neg_eq_iff_add_eq_zero.mpr (add_self_eq_zero.mpr h))⟩

@[simp]
theorem star_def : (Star.star : ℂ → ℂ) = conj :=
  rfl

/-! ### Norm squared -/


/-- The norm squared function. -/
@[pp_nodot]
def normSq : ℂ →*₀ ℝ where
  toFun z := z.re * z.re + z.im * z.im
  map_zero' := by simp
  map_one' := by simp
  map_mul' z w := by
    dsimp
    ring

theorem normSq_apply (z : ℂ) : normSq z = z.re * z.re + z.im * z.im :=
  rfl

@[simp]
theorem normSq_ofReal (r : ℝ) : normSq r = r * r := by
  simp [normSq, ofReal]

@[simp]
theorem normSq_natCast (n : ℕ) : normSq n = n * n := normSq_ofReal _

@[simp]
theorem normSq_intCast (z : ℤ) : normSq z = z * z := normSq_ofReal _

@[simp]
theorem normSq_ratCast (q : ℚ) : normSq q = q * q := normSq_ofReal _

@[simp]
theorem normSq_ofNat (n : ℕ) [n.AtLeastTwo] :
    normSq (ofNat(n) : ℂ) = ofNat(n) * ofNat(n) :=
  normSq_natCast _

@[simp]
theorem normSq_mk (x y : ℝ) : normSq ⟨x, y⟩ = x * x + y * y :=
  rfl

theorem normSq_add_mul_I (x y : ℝ) : normSq (x + y * I) = x ^ 2 + y ^ 2 := by
  rw [← mk_eq_add_mul_I, normSq_mk, sq, sq]

theorem normSq_eq_conj_mul_self {z : ℂ} : (normSq z : ℂ) = conj z * z := by
  ext <;> simp [normSq, mul_comm, ofReal]

theorem normSq_zero : normSq 0 = 0 := by simp

theorem normSq_one : normSq 1 = 1 := by simp

@[simp]
theorem normSq_I : normSq I = 1 := by simp [normSq]

theorem normSq_nonneg (z : ℂ) : 0 ≤ normSq z :=
  add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)

theorem normSq_eq_zero {z : ℂ} : normSq z = 0 ↔ z = 0 :=
  ⟨fun h =>
    ext (eq_zero_of_mul_self_add_mul_self_eq_zero h)
      (eq_zero_of_mul_self_add_mul_self_eq_zero <| (add_comm _ _).trans h),
    fun h => h.symm ▸ normSq_zero⟩

@[simp]
theorem normSq_pos {z : ℂ} : 0 < normSq z ↔ z ≠ 0 :=
  (normSq_nonneg z).lt_iff_ne.trans <| not_congr (eq_comm.trans normSq_eq_zero)

@[simp]
theorem normSq_neg (z : ℂ) : normSq (-z) = normSq z := by simp [normSq]

@[simp]
theorem normSq_conj (z : ℂ) : normSq (conj z) = normSq z := by simp [normSq]

theorem normSq_mul (z w : ℂ) : normSq (z * w) = normSq z * normSq w :=
  normSq.map_mul z w

theorem normSq_add (z w : ℂ) : normSq (z + w) = normSq z + normSq w + 2 * (z * conj w).re := by
  dsimp [normSq]; ring

theorem re_sq_le_normSq (z : ℂ) : z.re * z.re ≤ normSq z :=
  le_add_of_nonneg_right (mul_self_nonneg _)

theorem im_sq_le_normSq (z : ℂ) : z.im * z.im ≤ normSq z :=
  le_add_of_nonneg_left (mul_self_nonneg _)

theorem mul_conj (z : ℂ) : z * conj z = normSq z :=
  Complex.ext_iff.2 <| by simp [normSq, mul_comm, sub_eq_neg_add, add_comm, ofReal]

theorem add_conj (z : ℂ) : z + conj z = (2 * z.re : ℝ) :=
  Complex.ext_iff.2 <| by simp [two_mul, ofReal]

/-- The coercion `ℝ → ℂ` as a `RingHom`. -/
def ofRealHom : ℝ →+* ℂ where
  toFun x := (x : ℂ)
  map_one' := ofReal_one
  map_zero' := ofReal_zero
  map_mul' := ofReal_mul
  map_add' := ofReal_add

@[simp] lemma ofRealHom_eq_coe (r : ℝ) : ofRealHom r = r := rfl

variable {α : Type*}

@[simp] lemma ofReal_comp_add (f g : α → ℝ) : ofReal ∘ (f + g) = ofReal ∘ f + ofReal ∘ g :=
  map_comp_add ofRealHom ..

@[simp] lemma ofReal_comp_sub (f g : α → ℝ) : ofReal ∘ (f - g) = ofReal ∘ f - ofReal ∘ g :=
  map_comp_sub ofRealHom ..

@[simp] lemma ofReal_comp_neg (f : α → ℝ) : ofReal ∘ (-f) = -(ofReal ∘ f) :=
  map_comp_neg ofRealHom _

lemma ofReal_comp_nsmul (n : ℕ) (f : α → ℝ) : ofReal ∘ (n • f) = n • (ofReal ∘ f) :=
  map_comp_nsmul ofRealHom ..

lemma ofReal_comp_zsmul (n : ℤ) (f : α → ℝ) : ofReal ∘ (n • f) = n • (ofReal ∘ f) :=
  map_comp_zsmul ofRealHom ..

@[simp] lemma ofReal_comp_mul (f g : α → ℝ) : ofReal ∘ (f * g) = ofReal ∘ f * ofReal ∘ g :=
  map_comp_mul ofRealHom ..

@[simp] lemma ofReal_comp_pow (f : α → ℝ) (n : ℕ) : ofReal ∘ (f ^ n) = (ofReal ∘ f) ^ n :=
  map_comp_pow ofRealHom ..

@[simp]
theorem I_sq : I ^ 2 = -1 := by rw [sq, I_mul_I]

@[simp]
lemma I_pow_three : I ^ 3 = -I := by rw [pow_succ, I_sq, neg_one_mul]

@[simp]
theorem I_pow_four : I ^ 4 = 1 := by rw [(by norm_num : 4 = 2 * 2), pow_mul, I_sq, neg_one_sq]

lemma I_pow_eq_pow_mod (n : ℕ) : I ^ n = I ^ (n % 4) := by
  conv_lhs => rw [← Nat.div_add_mod n 4]
  simp [pow_add, pow_mul, I_pow_four]

@[simp]
theorem sub_re (z w : ℂ) : (z - w).re = z.re - w.re :=
  rfl

@[simp]
theorem sub_im (z w : ℂ) : (z - w).im = z.im - w.im :=
  rfl

@[simp, norm_cast]
theorem ofReal_sub (r s : ℝ) : ((r - s : ℝ) : ℂ) = r - s :=
  Complex.ext_iff.2 <| by simp [ofReal]

@[simp, norm_cast]
theorem ofReal_pow (r : ℝ) (n : ℕ) : ((r ^ n : ℝ) : ℂ) = (r : ℂ) ^ n := by
  induction n <;> simp [*, ofReal_mul, pow_succ]

theorem sub_conj (z : ℂ) : z - conj z = (2 * z.im : ℝ) * I :=
  Complex.ext_iff.2 <| by simp [two_mul, sub_eq_add_neg, ofReal]

theorem normSq_sub (z w : ℂ) : normSq (z - w) = normSq z + normSq w - 2 * (z * conj w).re := by
  rw [sub_eq_add_neg, normSq_add]
  simp only [RingHom.map_neg, mul_neg, neg_re, normSq_neg]
  ring

/-! ### Inversion -/


noncomputable instance : Inv ℂ :=
  ⟨fun z => conj z * ((normSq z)⁻¹ : ℝ)⟩

theorem inv_def (z : ℂ) : z⁻¹ = conj z * ((normSq z)⁻¹ : ℝ) :=
  rfl

@[simp]
theorem inv_re (z : ℂ) : z⁻¹.re = z.re / normSq z := by simp [inv_def, division_def, ofReal]

@[simp]
theorem inv_im (z : ℂ) : z⁻¹.im = -z.im / normSq z := by simp [inv_def, division_def, ofReal]

@[simp, norm_cast]
theorem ofReal_inv (r : ℝ) : ((r⁻¹ : ℝ) : ℂ) = (r : ℂ)⁻¹ :=
  Complex.ext_iff.2 <| by simp [ofReal]

protected theorem inv_zero : (0⁻¹ : ℂ) = 0 := by
  rw [← ofReal_zero, ← ofReal_inv, inv_zero]

protected theorem mul_inv_cancel {z : ℂ} (h : z ≠ 0) : z * z⁻¹ = 1 := by
  rw [inv_def, ← mul_assoc, mul_conj, ← ofReal_mul, mul_inv_cancel₀ (mt normSq_eq_zero.1 h),
    ofReal_one]

noncomputable instance instDivInvMonoid : DivInvMonoid ℂ where

lemma div_re (z w : ℂ) : (z / w).re = z.re * w.re / normSq w + z.im * w.im / normSq w := by
  simp [div_eq_mul_inv, mul_assoc, sub_eq_add_neg]

lemma div_im (z w : ℂ) : (z / w).im = z.im * w.re / normSq w - z.re * w.im / normSq w := by
  simp [div_eq_mul_inv, mul_assoc, sub_eq_add_neg, add_comm]

/-! ### Field instance and lemmas -/

noncomputable instance instField : Field ℂ where
  mul_inv_cancel := @Complex.mul_inv_cancel
  inv_zero := Complex.inv_zero
  nnqsmul := (· • ·)
  qsmul := (· • ·)
  nnratCast_def q := by ext <;> simp [NNRat.cast_def, div_re, div_im, mul_div_mul_comm]
  ratCast_def q := by ext <;> simp [Rat.cast_def, div_re, div_im, mul_div_mul_comm]
  nnqsmul_def n z := Complex.ext_iff.2 <| by simp [NNRat.smul_def, smul_re, smul_im]
  qsmul_def n z := Complex.ext_iff.2 <| by simp [Rat.smul_def, smul_re, smul_im]

@[simp, norm_cast]
lemma ofReal_nnqsmul (q : ℚ≥0) (r : ℝ) : ofReal (q • r) = q • r := by simp [NNRat.smul_def]

@[simp, norm_cast]
lemma ofReal_qsmul (q : ℚ) (r : ℝ) : ofReal (q • r) = q • r := by simp [Rat.smul_def]

theorem conj_inv (x : ℂ) : conj x⁻¹ = (conj x)⁻¹ :=
  star_inv₀ _

@[simp, norm_cast]
theorem ofReal_div (r s : ℝ) : ((r / s : ℝ) : ℂ) = r / s := map_div₀ ofRealHom r s

@[simp, norm_cast]
theorem ofReal_zpow (r : ℝ) (n : ℤ) : ((r ^ n : ℝ) : ℂ) = (r : ℂ) ^ n := map_zpow₀ ofRealHom r n

@[simp]
theorem div_I (z : ℂ) : z / I = -(z * I) :=
  (div_eq_iff_mul_eq I_ne_zero).2 <| by simp [mul_assoc]

@[simp]
theorem inv_I : I⁻¹ = -I := by
  rw [inv_eq_one_div, div_I, one_mul]

theorem normSq_inv (z : ℂ) : normSq z⁻¹ = (normSq z)⁻¹ := by simp

theorem normSq_div (z w : ℂ) : normSq (z / w) = normSq z / normSq w := by simp

lemma div_ofReal (z : ℂ) (x : ℝ) : z / x = ⟨z.re / x, z.im / x⟩ := by
  simp_rw [div_eq_inv_mul, ← ofReal_inv, ofReal_mul']

lemma div_natCast (z : ℂ) (n : ℕ) : z / n = ⟨z.re / n, z.im / n⟩ :=
  mod_cast div_ofReal z n

lemma div_intCast (z : ℂ) (n : ℤ) : z / n = ⟨z.re / n, z.im / n⟩ :=
  mod_cast div_ofReal z n

lemma div_ratCast (z : ℂ) (x : ℚ) : z / x = ⟨z.re / x, z.im / x⟩ :=
  mod_cast div_ofReal z x

lemma div_ofNat (z : ℂ) (n : ℕ) [n.AtLeastTwo] :
    z / ofNat(n) = ⟨z.re / ofNat(n), z.im / ofNat(n)⟩ :=
  div_natCast z n

@[simp] lemma div_ofReal_re (z : ℂ) (x : ℝ) : (z / x).re = z.re / x := by rw [div_ofReal]
@[simp] lemma div_ofReal_im (z : ℂ) (x : ℝ) : (z / x).im = z.im / x := by rw [div_ofReal]
@[simp] lemma div_natCast_re (z : ℂ) (n : ℕ) : (z / n).re = z.re / n := by rw [div_natCast]
@[simp] lemma div_natCast_im (z : ℂ) (n : ℕ) : (z / n).im = z.im / n := by rw [div_natCast]
@[simp] lemma div_intCast_re (z : ℂ) (n : ℤ) : (z / n).re = z.re / n := by rw [div_intCast]
@[simp] lemma div_intCast_im (z : ℂ) (n : ℤ) : (z / n).im = z.im / n := by rw [div_intCast]
@[simp] lemma div_ratCast_re (z : ℂ) (x : ℚ) : (z / x).re = z.re / x := by rw [div_ratCast]
@[simp] lemma div_ratCast_im (z : ℂ) (x : ℚ) : (z / x).im = z.im / x := by rw [div_ratCast]

@[simp]
lemma div_ofNat_re (z : ℂ) (n : ℕ) [n.AtLeastTwo] :
    (z / ofNat(n)).re = z.re / ofNat(n) := div_natCast_re z n

@[simp]
lemma div_ofNat_im (z : ℂ) (n : ℕ) [n.AtLeastTwo] :
    (z / ofNat(n)).im = z.im / ofNat(n) := div_natCast_im z n

/-! ### Characteristic zero -/


instance instCharZero : CharZero ℂ :=
  charZero_of_inj_zero fun n h => by rwa [← ofReal_natCast, ofReal_eq_zero, Nat.cast_eq_zero] at h

/-- A complex number `z` plus its conjugate `conj z` is `2` times its real part. -/
theorem re_eq_add_conj (z : ℂ) : (z.re : ℂ) = (z + conj z) / 2 := by
  simp only [add_conj, ofReal_mul, ofReal_ofNat, mul_div_cancel_left₀ (z.re : ℂ) two_ne_zero]

/-- A complex number `z` minus its conjugate `conj z` is `2i` times its imaginary part. -/
theorem im_eq_sub_conj (z : ℂ) : (z.im : ℂ) = (z - conj z) / (2 * I) := by
  simp only [sub_conj, ofReal_mul, ofReal_ofNat, mul_right_comm,
    mul_div_cancel_left₀ _ (mul_ne_zero two_ne_zero I_ne_zero : 2 * I ≠ 0)]

/-- Show the imaginary number ⟨x, y⟩ as an "x + y*I" string

Note that the Real numbers used for x and y will show as cauchy sequences due to the way Real
numbers are represented.
-/
unsafe instance instRepr : Repr ℂ where
  reprPrec f p :=
    (if p > 65 then (Std.Format.bracket "(" · ")") else (·)) <|
      reprPrec f.re 65 ++ " + " ++ reprPrec f.im 70 ++ "*I"

section reProdIm

/-- The preimage under `equivRealProd` of `s ×ˢ t` is `s ×ℂ t`. -/
lemma preimage_equivRealProd_prod (s t : Set ℝ) : equivRealProd ⁻¹' (s ×ˢ t) = s ×ℂ t := rfl

/-- The inequality `s × t ⊆ s₁ × t₁` holds in `ℂ` iff it holds in `ℝ × ℝ`. -/
lemma reProdIm_subset_iff {s s₁ t t₁ : Set ℝ} : s ×ℂ t ⊆ s₁ ×ℂ t₁ ↔ s ×ˢ t ⊆ s₁ ×ˢ t₁ := by
  rw [← @preimage_equivRealProd_prod s t, ← @preimage_equivRealProd_prod s₁ t₁]
  exact Equiv.preimage_subset equivRealProd _ _

/-- If `s ⊆ s₁ ⊆ ℝ` and `t ⊆ t₁ ⊆ ℝ`, then `s × t ⊆ s₁ × t₁` in `ℂ`. -/
lemma reProdIm_subset_iff' {s s₁ t t₁ : Set ℝ} :
    s ×ℂ t ⊆ s₁ ×ℂ t₁ ↔ s ⊆ s₁ ∧ t ⊆ t₁ ∨ s = ∅ ∨ t = ∅ := by
  convert prod_subset_prod_iff
  exact reProdIm_subset_iff

variable {s t : Set ℝ}

@[simp] lemma reProdIm_nonempty : (s ×ℂ t).Nonempty ↔ s.Nonempty ∧ t.Nonempty := by
  simp [Set.Nonempty, reProdIm, Complex.exists]

@[simp] lemma reProdIm_eq_empty : s ×ℂ t = ∅ ↔ s = ∅ ∨ t = ∅ := by
  simp [← not_nonempty_iff_eq_empty, reProdIm_nonempty, -not_and, not_and_or]

end reProdIm

open scoped Interval

section Rectangle

/-- A `Rectangle` is an axis-parallel rectangle with corners `z` and `w`. -/
def Rectangle (z w : ℂ) : Set ℂ := [[z.re, w.re]] ×ℂ [[z.im, w.im]]

end Rectangle

section Segments

/-- A real segment `[a₁, a₂]` translated by `b * I` is the complex line segment. -/
lemma horizontalSegment_eq (a₁ a₂ b : ℝ) :
    (fun (x : ℝ) ↦ x + b * I) '' [[a₁, a₂]] = [[a₁, a₂]] ×ℂ {b} := by
  rw [← preimage_equivRealProd_prod]
  ext x
  constructor
  · intro hx
    obtain ⟨x₁, hx₁, hx₁'⟩ := hx
    simp [← hx₁', mem_preimage, mem_prod, hx₁]
  · intro hx
    obtain ⟨x₁, hx₁, hx₁', hx₁''⟩ := hx
    refine ⟨x.re, x₁, by simp⟩

/-- A vertical segment `[b₁, b₂]` translated by `a` is the complex line segment. -/
lemma verticalSegment_eq (a b₁ b₂ : ℝ) :
    (fun (y : ℝ) ↦ a + y * I) '' [[b₁, b₂]] = {a} ×ℂ [[b₁, b₂]] := by
  rw [← preimage_equivRealProd_prod]
  ext x
  constructor
  · intro hx
    obtain ⟨x₁, hx₁, hx₁'⟩ := hx
    simp [← hx₁', mem_preimage, mem_prod, hx₁]
  · intro hx
    simp only [equivRealProd_apply, singleton_prod, mem_image, Prod.mk.injEq,
      exists_eq_right_right, mem_preimage] at hx
    obtain ⟨x₁, hx₁, hx₁', hx₁''⟩ := hx
    refine ⟨x.im, x₁, by simp⟩

end Segments

end Complex

```

BigOperators.lean:
```
/-
Copyright (c) 2017 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Mario Carneiro
-/
import Mathlib.Algebra.BigOperators.Balance
import Mathlib.Data.Complex.Basic

/-!
# Finite sums and products of complex numbers
-/

open Fintype
open scoped BigOperators

namespace Complex

variable {α : Type*} (s : Finset α)

@[simp, norm_cast]
theorem ofReal_prod (f : α → ℝ) : ((∏ i ∈ s, f i : ℝ) : ℂ) = ∏ i ∈ s, (f i : ℂ) :=
  map_prod ofRealHom _ _

@[simp, norm_cast]
theorem ofReal_sum (f : α → ℝ) : ((∑ i ∈ s, f i : ℝ) : ℂ) = ∑ i ∈ s, (f i : ℂ) :=
  map_sum ofRealHom _ _

@[simp, norm_cast]
lemma ofReal_expect (f : α → ℝ) : (𝔼 i ∈ s, f i : ℝ) = 𝔼 i ∈ s, (f i : ℂ) :=
  map_expect ofRealHom ..

@[simp, norm_cast]
lemma ofReal_balance [Fintype α] (f : α → ℝ) (a : α) :
    ((balance f a : ℝ) : ℂ) = balance ((↑) ∘ f) a := by simp [balance]

@[simp] lemma ofReal_comp_balance {ι : Type*} [Fintype ι] (f : ι → ℝ) :
    ofReal ∘ balance f = balance (ofReal ∘ f : ι → ℂ) := funext <| ofReal_balance _

@[simp]
theorem re_sum (f : α → ℂ) : (∑ i ∈ s, f i).re = ∑ i ∈ s, (f i).re :=
  map_sum reAddGroupHom f s

@[simp]
lemma re_expect (f : α → ℂ) : (𝔼 i ∈ s, f i).re = 𝔼 i ∈ s, (f i).re :=
  map_expect (LinearMap.mk reAddGroupHom.toAddHom (by simp)) f s

@[simp]
lemma re_balance [Fintype α] (f : α → ℂ) (a : α) : re (balance f a) = balance (re ∘ f) a := by
  simp [balance]

@[simp] lemma re_comp_balance {ι : Type*} [Fintype ι] (f : ι → ℂ) :
    re ∘ balance f = balance (re ∘ f) := funext <| re_balance _

@[simp]
theorem im_sum (f : α → ℂ) : (∑ i ∈ s, f i).im = ∑ i ∈ s, (f i).im :=
  map_sum imAddGroupHom f s

@[simp]
lemma im_expect (f : α → ℂ) : (𝔼 i ∈ s, f i).im = 𝔼 i ∈ s, (f i).im :=
  map_expect (LinearMap.mk imAddGroupHom.toAddHom (by simp)) f s

@[simp]
lemma im_balance [Fintype α] (f : α → ℂ) (a : α) : im (balance f a) = balance (im ∘ f) a := by
  simp [balance]

@[simp] lemma im_comp_balance {ι : Type*} [Fintype ι] (f : ι → ℂ) :
    im ∘ balance f = balance (im ∘ f) := funext <| im_balance _

end Complex

```

Cardinality.lean:
```
/-
Copyright (c) 2022 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Cardinality

/-!
# The cardinality of the complex numbers

This file shows that the complex numbers have cardinality continuum, i.e. `#ℂ = 𝔠`.
-/

open Cardinal Set

open Cardinal

/-- The cardinality of the complex numbers, as a type. -/
@[simp]
theorem Cardinal.mk_complex : #ℂ = 𝔠 := by
  rw [mk_congr Complex.equivRealProd, mk_prod, lift_id, mk_real, continuum_mul_self]

@[deprecated Cardinal.mk_complex (since := "2025-03-13")] alias mk_complex := Cardinal.mk_complex

/-- The cardinality of the complex numbers, as a set. -/
theorem Cardinal.mk_univ_complex : #(Set.univ : Set ℂ) = 𝔠 := by rw [mk_univ, mk_complex]

@[deprecated Cardinal.mk_univ_complex (since := "2025-03-13")]
alias mk_univ_complex := Cardinal.mk_univ_complex

/-- The complex numbers are not countable. -/
theorem not_countable_complex : ¬(Set.univ : Set ℂ).Countable := by
  rw [← le_aleph0_iff_set_countable, not_le, Cardinal.mk_univ_complex]
  apply cantor

```

Determinant.lean:
```
/-
Copyright (c) 2022 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
import Mathlib.Data.Complex.Module
import Mathlib.LinearAlgebra.Determinant

/-!
# Determinants of maps in the complex numbers as a vector space over `ℝ`

This file provides results about the determinants of maps in the complex numbers as a vector
space over `ℝ`.

-/


namespace Complex

/-- The determinant of `conjAe`, as a linear map. -/
@[simp]
theorem det_conjAe : LinearMap.det conjAe.toLinearMap = -1 := by
  rw [← LinearMap.det_toMatrix basisOneI, toMatrix_conjAe, Matrix.det_fin_two_of]
  simp

/-- The determinant of `conjAe`, as a linear equiv. -/
@[simp]
theorem linearEquiv_det_conjAe : LinearEquiv.det conjAe.toLinearEquiv = -1 := by
  rw [← Units.eq_iff, LinearEquiv.coe_det, AlgEquiv.toLinearEquiv_toLinearMap, det_conjAe,
    Units.coe_neg_one]

end Complex

```

Exponential.lean:
```
/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Abhimanyu Pallavi Sudhir
-/
import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.Order.CauSeq.BigOperators
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Data.Complex.BigOperators
import Mathlib.Data.Complex.Norm
import Mathlib.Data.Nat.Choose.Sum

/-!
# Exponential Function

This file contains the definitions of the real and complex exponential function.

## Main definitions

* `Complex.exp`: The complex exponential function, defined via its Taylor series

* `Real.exp`: The real exponential function, defined as the real part of the complex exponential

-/

open CauSeq Finset IsAbsoluteValue
open scoped ComplexConjugate

namespace Complex

theorem isCauSeq_norm_exp (z : ℂ) :
    IsCauSeq abs fun n => ∑ m ∈ range n, ‖z ^ m / m.factorial‖ :=
  let ⟨n, hn⟩ := exists_nat_gt ‖z‖
  have hn0 : (0 : ℝ) < n := lt_of_le_of_lt (norm_nonneg _) hn
  IsCauSeq.series_ratio_test n (‖z‖ / n) (div_nonneg (norm_nonneg _) (le_of_lt hn0))
    (by rwa [div_lt_iff₀ hn0, one_mul]) fun m hm => by
      rw [abs_norm, abs_norm, Nat.factorial_succ, pow_succ', mul_comm m.succ, Nat.cast_mul,
        ← div_div, mul_div_assoc, mul_div_right_comm, Complex.norm_mul, Complex.norm_div,
        norm_natCast]
      gcongr
      exact le_trans hm (Nat.le_succ _)

@[deprecated (since := "2025-02-16")] alias isCauSeq_abs_exp := isCauSeq_norm_exp

noncomputable section

theorem isCauSeq_exp (z : ℂ) : IsCauSeq (‖·‖) fun n => ∑ m ∈ range n, z ^ m / m.factorial :=
  (isCauSeq_norm_exp z).of_abv

/-- The Cauchy sequence consisting of partial sums of the Taylor series of
the complex exponential function -/
@[pp_nodot]
def exp' (z : ℂ) : CauSeq ℂ (‖·‖) :=
  ⟨fun n => ∑ m ∈ range n, z ^ m / m.factorial, isCauSeq_exp z⟩

/-- The complex exponential function, defined via its Taylor series -/
@[pp_nodot]
def exp (z : ℂ) : ℂ :=
  CauSeq.lim (exp' z)

/-- scoped notation for the complex exponential function -/
scoped notation "cexp" => Complex.exp

end

end Complex

namespace Real

open Complex

noncomputable section

/-- The real exponential function, defined as the real part of the complex exponential -/
@[pp_nodot]
nonrec def exp (x : ℝ) : ℝ :=
  (exp x).re

/-- scoped notation for the real exponential function -/
scoped notation "rexp" => Real.exp

end

end Real

namespace Complex

variable (x y : ℂ)

@[simp]
theorem exp_zero : exp 0 = 1 := by
  rw [exp]
  refine lim_eq_of_equiv_const fun ε ε0 => ⟨1, fun j hj => ?_⟩
  convert (config := .unfoldSameFun) ε0 -- ε0 : ε > 0 but goal is _ < ε
  rcases j with - | j
  · exact absurd hj (not_le_of_gt zero_lt_one)
  · dsimp [exp']
    induction' j with j ih
    · dsimp [exp']; simp [show Nat.succ 0 = 1 from rfl]
    · rw [← ih (by simp [Nat.succ_le_succ])]
      simp only [sum_range_succ, pow_succ]
      simp

theorem exp_add : exp (x + y) = exp x * exp y := by
  have hj : ∀ j : ℕ, (∑ m ∈ range j, (x + y) ^ m / m.factorial) =
        ∑ i ∈ range j, ∑ k ∈ range (i + 1), x ^ k / k.factorial *
          (y ^ (i - k) / (i - k).factorial) := by
    intro j
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [add_pow, div_eq_mul_inv, sum_mul]
    refine Finset.sum_congr rfl fun I hi => ?_
    have h₁ : (m.choose I : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.2 (pos_iff_ne_zero.1 (Nat.choose_pos (Nat.le_of_lt_succ (mem_range.1 hi))))
    have h₂ := Nat.choose_mul_factorial_mul_factorial (Nat.le_of_lt_succ <| Finset.mem_range.1 hi)
    rw [← h₂, Nat.cast_mul, Nat.cast_mul, mul_inv, mul_inv]
    simp only [mul_left_comm (m.choose I : ℂ), mul_assoc, mul_left_comm (m.choose I : ℂ)⁻¹,
      mul_comm (m.choose I : ℂ)]
    rw [inv_mul_cancel₀ h₁]
    simp [div_eq_mul_inv, mul_comm, mul_assoc, mul_left_comm]
  simp_rw [exp, exp', lim_mul_lim]
  apply (lim_eq_lim_of_equiv _).symm
  simp only [hj]
  exact cauchy_product (isCauSeq_norm_exp x) (isCauSeq_exp y)

/-- the exponential function as a monoid hom from `Multiplicative ℂ` to `ℂ` -/
@[simps]
noncomputable def expMonoidHom : MonoidHom (Multiplicative ℂ) ℂ :=
  { toFun := fun z => exp z.toAdd,
    map_one' := by simp,
    map_mul' := by simp [exp_add] }

theorem exp_list_sum (l : List ℂ) : exp l.sum = (l.map exp).prod :=
  map_list_prod (M := Multiplicative ℂ) expMonoidHom l

theorem exp_multiset_sum (s : Multiset ℂ) : exp s.sum = (s.map exp).prod :=
  @MonoidHom.map_multiset_prod (Multiplicative ℂ) ℂ _ _ expMonoidHom s

theorem exp_sum {α : Type*} (s : Finset α) (f : α → ℂ) :
    exp (∑ x ∈ s, f x) = ∏ x ∈ s, exp (f x) :=
  map_prod (β := Multiplicative ℂ) expMonoidHom f s

lemma exp_nsmul (x : ℂ) (n : ℕ) : exp (n • x) = exp x ^ n :=
  @MonoidHom.map_pow (Multiplicative ℂ) ℂ _ _  expMonoidHom _ _

theorem exp_nat_mul (x : ℂ) : ∀ n : ℕ, exp (n * x) = exp x ^ n
  | 0 => by rw [Nat.cast_zero, zero_mul, exp_zero, pow_zero]
  | Nat.succ n => by rw [pow_succ, Nat.cast_add_one, add_mul, exp_add, ← exp_nat_mul _ n, one_mul]

@[simp]
theorem exp_ne_zero : exp x ≠ 0 := fun h =>
  zero_ne_one (α := ℂ) <| by rw [← exp_zero, ← add_neg_cancel x, exp_add, h]; simp

theorem exp_neg : exp (-x) = (exp x)⁻¹ := by
  rw [← mul_right_inj' (exp_ne_zero x), ← exp_add]; simp [mul_inv_cancel₀ (exp_ne_zero x)]

theorem exp_sub : exp (x - y) = exp x / exp y := by
  simp [sub_eq_add_neg, exp_add, exp_neg, div_eq_mul_inv]

theorem exp_int_mul (z : ℂ) (n : ℤ) : Complex.exp (n * z) = Complex.exp z ^ n := by
  cases n
  · simp [exp_nat_mul]
  · simp [exp_add, add_mul, pow_add, exp_neg, exp_nat_mul]

@[simp]
theorem exp_conj : exp (conj x) = conj (exp x) := by
  dsimp [exp]
  rw [← lim_conj]
  refine congr_arg CauSeq.lim (CauSeq.ext fun _ => ?_)
  dsimp [exp', Function.comp_def, cauSeqConj]
  rw [map_sum (starRingEnd _)]
  refine sum_congr rfl fun n _ => ?_
  rw [map_div₀, map_pow, ← ofReal_natCast, conj_ofReal]

@[simp]
theorem ofReal_exp_ofReal_re (x : ℝ) : ((exp x).re : ℂ) = exp x :=
  conj_eq_iff_re.1 <| by rw [← exp_conj, conj_ofReal]

@[simp, norm_cast]
theorem ofReal_exp (x : ℝ) : (Real.exp x : ℂ) = exp x :=
  ofReal_exp_ofReal_re _

@[simp]
theorem exp_ofReal_im (x : ℝ) : (exp x).im = 0 := by rw [← ofReal_exp_ofReal_re, ofReal_im]

theorem exp_ofReal_re (x : ℝ) : (exp x).re = Real.exp x :=
  rfl

end Complex

namespace Real

open Complex

variable (x y : ℝ)

@[simp]
theorem exp_zero : exp 0 = 1 := by simp [Real.exp]

nonrec theorem exp_add : exp (x + y) = exp x * exp y := by simp [exp_add, exp]

/-- the exponential function as a monoid hom from `Multiplicative ℝ` to `ℝ` -/
@[simps]
noncomputable def expMonoidHom : MonoidHom (Multiplicative ℝ) ℝ :=
  { toFun := fun x => exp x.toAdd,
    map_one' := by simp,
    map_mul' := by simp [exp_add] }

theorem exp_list_sum (l : List ℝ) : exp l.sum = (l.map exp).prod :=
  map_list_prod (M := Multiplicative ℝ) expMonoidHom l

theorem exp_multiset_sum (s : Multiset ℝ) : exp s.sum = (s.map exp).prod :=
  @MonoidHom.map_multiset_prod (Multiplicative ℝ) ℝ _ _ expMonoidHom s

theorem exp_sum {α : Type*} (s : Finset α) (f : α → ℝ) :
    exp (∑ x ∈ s, f x) = ∏ x ∈ s, exp (f x) :=
  map_prod (β := Multiplicative ℝ) expMonoidHom f s

lemma exp_nsmul (x : ℝ) (n : ℕ) : exp (n • x) = exp x ^ n :=
  @MonoidHom.map_pow (Multiplicative ℝ) ℝ _ _  expMonoidHom _ _

nonrec theorem exp_nat_mul (x : ℝ) (n : ℕ) : exp (n * x) = exp x ^ n :=
  ofReal_injective (by simp [exp_nat_mul])

@[simp]
nonrec theorem exp_ne_zero : exp x ≠ 0 := fun h =>
  exp_ne_zero x <| by rw [exp, ← ofReal_inj] at h; simp_all

nonrec theorem exp_neg : exp (-x) = (exp x)⁻¹ :=
  ofReal_injective <| by simp [exp_neg]

theorem exp_sub : exp (x - y) = exp x / exp y := by
  simp [sub_eq_add_neg, exp_add, exp_neg, div_eq_mul_inv]

open IsAbsoluteValue Nat

theorem sum_le_exp_of_nonneg {x : ℝ} (hx : 0 ≤ x) (n : ℕ) : ∑ i ∈ range n, x ^ i / i ! ≤ exp x :=
  calc
    ∑ i ∈ range n, x ^ i / i ! ≤ lim (⟨_, isCauSeq_re (exp' x)⟩ : CauSeq ℝ abs) := by
      refine le_lim (CauSeq.le_of_exists ⟨n, fun j hj => ?_⟩)
      simp only [exp', const_apply, re_sum]
      norm_cast
      refine sum_le_sum_of_subset_of_nonneg (range_mono hj) fun _ _ _ ↦ ?_
      positivity
    _ = exp x := by rw [exp, Complex.exp, ← cauSeqRe, lim_re]

lemma pow_div_factorial_le_exp (hx : 0 ≤ x) (n : ℕ) : x ^ n / n ! ≤ exp x :=
  calc
    x ^ n / n ! ≤ ∑ k ∈ range (n + 1), x ^ k / k ! :=
        single_le_sum (f := fun k ↦ x ^ k / k !) (fun k _ ↦ by positivity) (self_mem_range_succ n)
    _ ≤ exp x := sum_le_exp_of_nonneg hx _

theorem quadratic_le_exp_of_nonneg {x : ℝ} (hx : 0 ≤ x) : 1 + x + x ^ 2 / 2 ≤ exp x :=
  calc
    1 + x + x ^ 2 / 2 = ∑ i ∈ range 3, x ^ i / i ! := by
        simp only [sum_range_succ, range_one, sum_singleton, _root_.pow_zero, factorial, cast_one,
          ne_eq, one_ne_zero, not_false_eq_true, div_self, pow_one, mul_one, div_one, Nat.mul_one,
          cast_succ, add_right_inj]
        ring_nf
    _ ≤ exp x := sum_le_exp_of_nonneg hx 3

private theorem add_one_lt_exp_of_pos {x : ℝ} (hx : 0 < x) : x + 1 < exp x :=
  (by nlinarith : x + 1 < 1 + x + x ^ 2 / 2).trans_le (quadratic_le_exp_of_nonneg hx.le)

private theorem add_one_le_exp_of_nonneg {x : ℝ} (hx : 0 ≤ x) : x + 1 ≤ exp x := by
  rcases eq_or_lt_of_le hx with (rfl | h)
  · simp
  exact (add_one_lt_exp_of_pos h).le

theorem one_le_exp {x : ℝ} (hx : 0 ≤ x) : 1 ≤ exp x := by linarith [add_one_le_exp_of_nonneg hx]

@[bound]
theorem exp_pos (x : ℝ) : 0 < exp x :=
  (le_total 0 x).elim (lt_of_lt_of_le zero_lt_one ∘ one_le_exp) fun h => by
    rw [← neg_neg x, Real.exp_neg]
    exact inv_pos.2 (lt_of_lt_of_le zero_lt_one (one_le_exp (neg_nonneg.2 h)))

@[bound]
lemma exp_nonneg (x : ℝ) : 0 ≤ exp x := x.exp_pos.le

@[simp]
theorem abs_exp (x : ℝ) : |exp x| = exp x :=
  abs_of_pos (exp_pos _)

lemma exp_abs_le (x : ℝ) : exp |x| ≤ exp x + exp (-x) := by
  cases le_total x 0 <;> simp [abs_of_nonpos, abs_of_nonneg, exp_nonneg, *]

@[mono]
theorem exp_strictMono : StrictMono exp := fun x y h => by
  rw [← sub_add_cancel y x, Real.exp_add]
  exact (lt_mul_iff_one_lt_left (exp_pos _)).2
      (lt_of_lt_of_le (by linarith) (add_one_le_exp_of_nonneg (by linarith)))

@[gcongr]
theorem exp_lt_exp_of_lt {x y : ℝ} (h : x < y) : exp x < exp y := exp_strictMono h

@[mono]
theorem exp_monotone : Monotone exp :=
  exp_strictMono.monotone

@[gcongr, bound]
theorem exp_le_exp_of_le {x y : ℝ} (h : x ≤ y) : exp x ≤ exp y := exp_monotone h

@[simp]
theorem exp_lt_exp {x y : ℝ} : exp x < exp y ↔ x < y :=
  exp_strictMono.lt_iff_lt

@[simp]
theorem exp_le_exp {x y : ℝ} : exp x ≤ exp y ↔ x ≤ y :=
  exp_strictMono.le_iff_le

theorem exp_injective : Function.Injective exp :=
  exp_strictMono.injective

@[simp]
theorem exp_eq_exp {x y : ℝ} : exp x = exp y ↔ x = y :=
  exp_injective.eq_iff

@[simp]
theorem exp_eq_one_iff : exp x = 1 ↔ x = 0 :=
  exp_injective.eq_iff' exp_zero

@[simp]
theorem one_lt_exp_iff {x : ℝ} : 1 < exp x ↔ 0 < x := by rw [← exp_zero, exp_lt_exp]

@[bound] private alias ⟨_, Bound.one_lt_exp_of_pos⟩ := one_lt_exp_iff

@[simp]
theorem exp_lt_one_iff {x : ℝ} : exp x < 1 ↔ x < 0 := by rw [← exp_zero, exp_lt_exp]

@[simp]
theorem exp_le_one_iff {x : ℝ} : exp x ≤ 1 ↔ x ≤ 0 :=
  exp_zero ▸ exp_le_exp

@[simp]
theorem one_le_exp_iff {x : ℝ} : 1 ≤ exp x ↔ 0 ≤ x :=
  exp_zero ▸ exp_le_exp

end Real

namespace Complex

theorem sum_div_factorial_le {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]
    (n j : ℕ) (hn : 0 < n) :
    (∑ m ∈ range j with n ≤ m, (1 / m.factorial : α)) ≤ n.succ / (n.factorial * n) :=
  calc
    (∑ m ∈ range j with n ≤ m, (1 / m.factorial : α)) =
        ∑ m ∈ range (j - n), (1 / ((m + n).factorial : α)) := by
        refine sum_nbij' (· - n) (· + n) ?_ ?_ ?_ ?_ ?_ <;>
          simp +contextual [lt_tsub_iff_right, tsub_add_cancel_of_le]
    _ ≤ ∑ m ∈ range (j - n), ((n.factorial : α) * (n.succ : α) ^ m)⁻¹ := by
      simp_rw [one_div]
      gcongr
      rw [← Nat.cast_pow, ← Nat.cast_mul, Nat.cast_le, add_comm]
      exact Nat.factorial_mul_pow_le_factorial
    _ = (n.factorial : α)⁻¹ * ∑ m ∈ range (j - n), (n.succ : α)⁻¹ ^ m := by
      simp [mul_inv, ← mul_sum, ← sum_mul, mul_comm, inv_pow]
    _ = ((n.succ : α) - n.succ * (n.succ : α)⁻¹ ^ (j - n)) / (n.factorial * n) := by
      have h₁ : (n.succ : α) ≠ 1 :=
        @Nat.cast_one α _ ▸ mt Nat.cast_inj.1 (mt Nat.succ.inj (pos_iff_ne_zero.1 hn))
      have h₂ : (n.succ : α) ≠ 0 := by positivity
      have h₃ : (n.factorial * n : α) ≠ 0 := by positivity
      have h₄ : (n.succ - 1 : α) = n := by simp
      rw [geom_sum_inv h₁ h₂, eq_div_iff_mul_eq h₃, mul_comm _ (n.factorial * n : α),
          ← mul_assoc (n.factorial⁻¹ : α), ← mul_inv_rev, h₄, ← mul_assoc (n.factorial * n : α),
          mul_comm (n : α) n.factorial, mul_inv_cancel₀ h₃, one_mul, mul_comm]
    _ ≤ n.succ / (n.factorial * n : α) := by gcongr; apply sub_le_self; positivity

theorem exp_bound {x : ℂ} (hx : ‖x‖ ≤ 1) {n : ℕ} (hn : 0 < n) :
    ‖exp x - ∑ m ∈ range n, x ^ m / m.factorial‖ ≤
      ‖x‖ ^ n * ((n.succ : ℝ) * (n.factorial * n : ℝ)⁻¹) := by
  rw [← lim_const (abv := norm) (∑ m ∈ range n, _), exp, sub_eq_add_neg,
    ← lim_neg, lim_add, ← lim_norm]
  refine lim_le (CauSeq.le_of_exists ⟨n, fun j hj => ?_⟩)
  simp_rw [← sub_eq_add_neg]
  show
    ‖(∑ m ∈ range j, x ^ m / m.factorial) - ∑ m ∈ range n, x ^ m / m.factorial‖ ≤
      ‖x‖ ^ n * ((n.succ : ℝ) * (n.factorial * n : ℝ)⁻¹)
  rw [sum_range_sub_sum_range hj]
  calc
    ‖∑ m ∈ range j with n ≤ m, (x ^ m / m.factorial : ℂ)‖
      = ‖∑ m ∈ range j with n ≤ m, (x ^ n * (x ^ (m - n) / m.factorial) : ℂ)‖ := by
      refine congr_arg norm (sum_congr rfl fun m hm => ?_)
      rw [mem_filter, mem_range] at hm
      rw [← mul_div_assoc, ← pow_add, add_tsub_cancel_of_le hm.2]
    _ ≤ ∑ m ∈ range j with n ≤ m, ‖x ^ n * (x ^ (m - n) / m.factorial)‖ :=
      IsAbsoluteValue.abv_sum norm ..
    _ ≤ ∑ m ∈ range j with n ≤ m, ‖x‖ ^ n * (1 / m.factorial) := by
      simp_rw [Complex.norm_mul, Complex.norm_pow, Complex.norm_div, norm_natCast]
      gcongr
      rw [Complex.norm_pow]
      exact pow_le_one₀ (norm_nonneg _) hx
    _ = ‖x‖ ^ n * ∑ m ∈ range j with n ≤ m, (1 / m.factorial : ℝ) := by
      simp [abs_mul, abv_pow abs, abs_div, ← mul_sum]
    _ ≤ ‖x‖ ^ n * (n.succ * (n.factorial * n : ℝ)⁻¹) := by
      gcongr
      exact sum_div_factorial_le _ _ hn

theorem exp_bound' {x : ℂ} {n : ℕ} (hx : ‖x‖ / n.succ ≤ 1 / 2) :
    ‖exp x - ∑ m ∈ range n, x ^ m / m.factorial‖ ≤ ‖x‖ ^ n / n.factorial * 2 := by
  rw [← lim_const (abv := norm) (∑ m ∈ range n, _),
    exp, sub_eq_add_neg, ← lim_neg, lim_add, ← lim_norm]
  refine lim_le (CauSeq.le_of_exists ⟨n, fun j hj => ?_⟩)
  simp_rw [← sub_eq_add_neg]
  show ‖(∑ m ∈ range j, x ^ m / m.factorial) - ∑ m ∈ range n, x ^ m / m.factorial‖ ≤
    ‖x‖ ^ n / n.factorial * 2
  let k := j - n
  have hj : j = n + k := (add_tsub_cancel_of_le hj).symm
  rw [hj, sum_range_add_sub_sum_range]
  calc
    ‖∑ i ∈ range k, x ^ (n + i) / ((n + i).factorial : ℂ)‖ ≤
        ∑ i ∈ range k, ‖x ^ (n + i) / ((n + i).factorial : ℂ)‖ :=
      IsAbsoluteValue.abv_sum _ _ _
    _ ≤ ∑ i ∈ range k, ‖x‖ ^ (n + i) / (n + i).factorial := by
      simp [norm_natCast, Complex.norm_pow]
    _ ≤ ∑ i ∈ range k, ‖x‖ ^ (n + i) / ((n.factorial : ℝ) * (n.succ : ℝ) ^ i) := ?_
    _ = ∑ i ∈ range k, ‖x‖ ^ n / n.factorial * (‖x‖ ^ i / (n.succ : ℝ) ^ i) := ?_
    _ ≤ ‖x‖ ^ n / ↑n.factorial * 2 := ?_
  · gcongr
    exact mod_cast Nat.factorial_mul_pow_le_factorial
  · refine Finset.sum_congr rfl fun _ _ => ?_
    simp only [pow_add, div_eq_inv_mul, mul_inv, mul_left_comm, mul_assoc]
  · rw [← mul_sum]
    gcongr
    simp_rw [← div_pow]
    rw [geom_sum_eq, div_le_iff_of_neg]
    · trans (-1 : ℝ)
      · linarith
      · simp only [neg_le_sub_iff_le_add, div_pow, Nat.cast_succ, le_add_iff_nonneg_left]
        positivity
    · linarith
    · linarith

theorem norm_exp_sub_one_le {x : ℂ} (hx : ‖x‖ ≤ 1) : ‖exp x - 1‖ ≤ 2 * ‖x‖ :=
  calc
    ‖exp x - 1‖ = ‖exp x - ∑ m ∈ range 1, x ^ m / m.factorial‖ := by simp [sum_range_succ]
    _ ≤ ‖x‖ ^ 1 * ((Nat.succ 1 : ℝ) * ((Nat.factorial 1) * (1 : ℕ) : ℝ)⁻¹) :=
      (exp_bound hx (by decide))
    _ = 2 * ‖x‖ := by simp [two_mul, mul_two, mul_add, mul_comm, add_mul, Nat.factorial]

theorem norm_exp_sub_one_sub_id_le {x : ℂ} (hx : ‖x‖ ≤ 1) : ‖exp x - 1 - x‖ ≤ ‖x‖ ^ 2 :=
  calc
    ‖exp x - 1 - x‖ = ‖exp x - ∑ m ∈ range 2, x ^ m / m.factorial‖ := by
      simp [sub_eq_add_neg, sum_range_succ_comm, add_assoc, Nat.factorial]
    _ ≤ ‖x‖ ^ 2 * ((Nat.succ 2 : ℝ) * (Nat.factorial 2 * (2 : ℕ) : ℝ)⁻¹) :=
      (exp_bound hx (by decide))
    _ ≤ ‖x‖ ^ 2 * 1 := by gcongr; norm_num [Nat.factorial]
    _ = ‖x‖ ^ 2 := by rw [mul_one]

lemma norm_exp_sub_sum_le_exp_norm_sub_sum (x : ℂ) (n : ℕ) :
    ‖exp x - ∑ m ∈ range n, x ^ m / m.factorial‖
      ≤ Real.exp ‖x‖ - ∑ m ∈ range n, ‖x‖ ^ m / m.factorial := by
  rw [← CauSeq.lim_const (abv := norm) (∑ m ∈ range n, _), Complex.exp, sub_eq_add_neg,
    ← CauSeq.lim_neg, CauSeq.lim_add, ← lim_norm]
  refine CauSeq.lim_le (CauSeq.le_of_exists ⟨n, fun j hj => ?_⟩)
  simp_rw [← sub_eq_add_neg]
  calc ‖(∑ m ∈ range j, x ^ m / m.factorial) - ∑ m ∈ range n, x ^ m / m.factorial‖
  _ ≤ (∑ m ∈ range j, ‖x‖ ^ m / m.factorial) - ∑ m ∈ range n, ‖x‖ ^ m / m.factorial := by
    rw [sum_range_sub_sum_range hj, sum_range_sub_sum_range hj]
    refine (IsAbsoluteValue.abv_sum norm ..).trans_eq ?_
    congr with i
    simp [Complex.norm_pow]
  _ ≤ Real.exp ‖x‖ - ∑ m ∈ range n, ‖x‖ ^ m / m.factorial := by
    gcongr
    exact Real.sum_le_exp_of_nonneg (norm_nonneg _) _

lemma norm_exp_le_exp_norm (x : ℂ) : ‖exp x‖ ≤ Real.exp ‖x‖ := by
  convert norm_exp_sub_sum_le_exp_norm_sub_sum x 0 using 1 <;> simp

lemma norm_exp_sub_sum_le_norm_mul_exp (x : ℂ) (n : ℕ) :
    ‖exp x - ∑ m ∈ range n, x ^ m / m.factorial‖ ≤ ‖x‖ ^ n * Real.exp ‖x‖ := by
  rw [← CauSeq.lim_const (abv := norm) (∑ m ∈ range n, _), Complex.exp, sub_eq_add_neg,
    ← CauSeq.lim_neg, CauSeq.lim_add, ← lim_norm]
  refine CauSeq.lim_le (CauSeq.le_of_exists ⟨n, fun j hj => ?_⟩)
  simp_rw [← sub_eq_add_neg]
  show ‖(∑ m ∈ range j, x ^ m / m.factorial) - ∑ m ∈ range n, x ^ m / m.factorial‖ ≤ _
  rw [sum_range_sub_sum_range hj]
  calc
    ‖∑ m ∈ range j with n ≤ m, (x ^ m / m.factorial : ℂ)‖
      = ‖∑ m ∈ range j with n ≤ m, (x ^ n * (x ^ (m - n) / m.factorial) : ℂ)‖ := by
      refine congr_arg norm (sum_congr rfl fun m hm => ?_)
      rw [mem_filter, mem_range] at hm
      rw [← mul_div_assoc, ← pow_add, add_tsub_cancel_of_le hm.2]
    _ ≤ ∑ m ∈ range j with n ≤ m, ‖x ^ n * (x ^ (m - n) / m.factorial)‖ :=
      IsAbsoluteValue.abv_sum norm ..
    _ ≤ ∑ m ∈ range j with n ≤ m, ‖x‖ ^ n * (‖x‖ ^ (m - n) / (m - n).factorial) := by
      simp_rw [Complex.norm_mul, Complex.norm_pow, Complex.norm_div, norm_natCast]
      gcongr with i hi
      · rw [Complex.norm_pow]
      · simp
    _ = ‖x‖ ^ n * ∑ m ∈ range j with n ≤ m, (‖x‖ ^ (m - n) / (m - n).factorial) := by
      rw [← mul_sum]
    _ = ‖x‖ ^ n * ∑ m ∈ range (j - n), (‖x‖ ^ m / m.factorial) := by
      congr 1
      refine (sum_bij (fun m hm ↦ m + n) ?_ ?_ ?_ ?_).symm
      · intro a ha
        simp only [mem_filter, mem_range, le_add_iff_nonneg_left, zero_le, and_true]
        simp only [mem_range] at ha
        rwa [← lt_tsub_iff_right]
      · intro a ha b hb hab
        simpa using hab
      · intro b hb
        simp only [mem_range, exists_prop]
        simp only [mem_filter, mem_range] at hb
        refine ⟨b - n, ?_, ?_⟩
        · rw [tsub_lt_tsub_iff_right hb.2]
          exact hb.1
        · rw [tsub_add_cancel_of_le hb.2]
      · simp
    _ ≤ ‖x‖ ^ n * Real.exp ‖x‖ := by
      gcongr
      refine Real.sum_le_exp_of_nonneg ?_ _
      exact norm_nonneg _

@[deprecated (since := "2025-02-16")] alias abs_exp_sub_one_le := norm_exp_sub_one_le
@[deprecated (since := "2025-02-16")] alias abs_exp_sub_one_sub_id_le := norm_exp_sub_one_sub_id_le
@[deprecated (since := "2025-02-16")] alias  abs_exp_sub_sum_le_exp_abs_sub_sum :=
  norm_exp_sub_sum_le_exp_norm_sub_sum
@[deprecated (since := "2025-02-16")] alias abs_exp_le_exp_abs := norm_exp_le_exp_norm
@[deprecated (since := "2025-02-16")] alias abs_exp_sub_sum_le_abs_mul_exp :=
  norm_exp_sub_sum_le_norm_mul_exp

end Complex

namespace Real

open Complex Finset

nonrec theorem exp_bound {x : ℝ} (hx : |x| ≤ 1) {n : ℕ} (hn : 0 < n) :
    |exp x - ∑ m ∈ range n, x ^ m / m.factorial| ≤ |x| ^ n * (n.succ / (n.factorial * n)) := by
  have hxc : ‖(x : ℂ)‖ ≤ 1 := mod_cast hx
  convert exp_bound hxc hn using 2 <;>
  norm_cast

theorem exp_bound' {x : ℝ} (h1 : 0 ≤ x) (h2 : x ≤ 1) {n : ℕ} (hn : 0 < n) :
    Real.exp x ≤ (∑ m ∈ Finset.range n, x ^ m / m.factorial) +
      x ^ n * (n + 1) / (n.factorial * n) := by
  have h3 : |x| = x := by simpa
  have h4 : |x| ≤ 1 := by rwa [h3]
  have h' := Real.exp_bound h4 hn
  rw [h3] at h'
  have h'' := (abs_sub_le_iff.1 h').1
  have t := sub_le_iff_le_add'.1 h''
  simpa [mul_div_assoc] using t

theorem abs_exp_sub_one_le {x : ℝ} (hx : |x| ≤ 1) : |exp x - 1| ≤ 2 * |x| := by
  have : ‖(x : ℂ)‖ ≤ 1 := mod_cast hx
  exact_mod_cast Complex.norm_exp_sub_one_le (x := x) this

theorem abs_exp_sub_one_sub_id_le {x : ℝ} (hx : |x| ≤ 1) : |exp x - 1 - x| ≤ x ^ 2 := by
  rw [← sq_abs]
  have : ‖(x : ℂ)‖ ≤ 1 := mod_cast hx
  exact_mod_cast Complex.norm_exp_sub_one_sub_id_le this

/-- A finite initial segment of the exponential series, followed by an arbitrary tail.
For fixed `n` this is just a linear map wrt `r`, and each map is a simple linear function
of the previous (see `expNear_succ`), with `expNear n x r ⟶ exp x` as `n ⟶ ∞`,
for any `r`. -/
noncomputable def expNear (n : ℕ) (x r : ℝ) : ℝ :=
  (∑ m ∈ range n, x ^ m / m.factorial) + x ^ n / n.factorial * r

@[simp]
theorem expNear_zero (x r) : expNear 0 x r = r := by simp [expNear]

@[simp]
theorem expNear_succ (n x r) : expNear (n + 1) x r = expNear n x (1 + x / (n + 1) * r) := by
  simp [expNear, range_succ, mul_add, add_left_comm, add_assoc, pow_succ, div_eq_mul_inv,
      mul_inv, Nat.factorial]
  ac_rfl

theorem expNear_sub (n x r₁ r₂) : expNear n x r₁ -
    expNear n x r₂ = x ^ n / n.factorial * (r₁ - r₂) := by
  simp [expNear, mul_sub]

theorem exp_approx_end (n m : ℕ) (x : ℝ) (e₁ : n + 1 = m) (h : |x| ≤ 1) :
    |exp x - expNear m x 0| ≤ |x| ^ m / m.factorial * ((m + 1) / m) := by
  simp only [expNear, mul_zero, add_zero]
  convert exp_bound (n := m) h ?_ using 1
  · field_simp [mul_comm]
  · omega

theorem exp_approx_succ {n} {x a₁ b₁ : ℝ} (m : ℕ) (e₁ : n + 1 = m) (a₂ b₂ : ℝ)
    (e : |1 + x / m * a₂ - a₁| ≤ b₁ - |x| / m * b₂)
    (h : |exp x - expNear m x a₂| ≤ |x| ^ m / m.factorial * b₂) :
    |exp x - expNear n x a₁| ≤ |x| ^ n / n.factorial * b₁ := by
  refine (abs_sub_le _ _ _).trans ((add_le_add_right h _).trans ?_)
  subst e₁; rw [expNear_succ, expNear_sub, abs_mul]
  convert mul_le_mul_of_nonneg_left (a := |x| ^ n / ↑(Nat.factorial n))
      (le_sub_iff_add_le'.1 e) ?_ using 1
  · simp [mul_add, pow_succ', div_eq_mul_inv, abs_mul, abs_inv, ← pow_abs, mul_inv, Nat.factorial]
    ac_rfl
  · simp [div_nonneg, abs_nonneg]

theorem exp_approx_end' {n} {x a b : ℝ} (m : ℕ) (e₁ : n + 1 = m) (rm : ℝ) (er : ↑m = rm)
    (h : |x| ≤ 1) (e : |1 - a| ≤ b - |x| / rm * ((rm + 1) / rm)) :
    |exp x - expNear n x a| ≤ |x| ^ n / n.factorial * b := by
  subst er
  exact exp_approx_succ _ e₁ _ _ (by simpa using e) (exp_approx_end _ _ _ e₁ h)

theorem exp_1_approx_succ_eq {n} {a₁ b₁ : ℝ} {m : ℕ} (en : n + 1 = m) {rm : ℝ} (er : ↑m = rm)
    (h : |exp 1 - expNear m 1 ((a₁ - 1) * rm)| ≤ |1| ^ m / m.factorial * (b₁ * rm)) :
    |exp 1 - expNear n 1 a₁| ≤ |1| ^ n / n.factorial * b₁ := by
  subst er
  refine exp_approx_succ _ en _ _ ?_ h
  field_simp [show (m : ℝ) ≠ 0 by norm_cast; omega]

theorem exp_approx_start (x a b : ℝ) (h : |exp x - expNear 0 x a| ≤ |x| ^ 0 / Nat.factorial 0 * b) :
    |exp x - a| ≤ b := by simpa using h

theorem exp_bound_div_one_sub_of_interval' {x : ℝ} (h1 : 0 < x) (h2 : x < 1) :
    Real.exp x < 1 / (1 - x) := by
  have H : 0 < 1 - (1 + x + x ^ 2) * (1 - x) := calc
    0 < x ^ 3 := by positivity
    _ = 1 - (1 + x + x ^ 2) * (1 - x) := by ring
  calc
    exp x ≤ _ := exp_bound' h1.le h2.le zero_lt_three
    _ ≤ 1 + x + x ^ 2 := by
      -- Porting note: was `norm_num [Finset.sum] <;> nlinarith`
      -- This proof should be restored after the norm_num plugin for big operators is ported.
      -- (It may also need the positivity extensions in https://github.com/leanprover-community/mathlib4/pull/3907.)
      rw [show 3 = 1 + 1 + 1 from rfl]
      repeat rw [Finset.sum_range_succ]
      norm_num [Nat.factorial]
      nlinarith
    _ < 1 / (1 - x) := by rw [lt_div_iff₀] <;> nlinarith

theorem exp_bound_div_one_sub_of_interval {x : ℝ} (h1 : 0 ≤ x) (h2 : x < 1) :
    Real.exp x ≤ 1 / (1 - x) := by
  rcases eq_or_lt_of_le h1 with (rfl | h1)
  · simp
  · exact (exp_bound_div_one_sub_of_interval' h1 h2).le

theorem add_one_lt_exp {x : ℝ} (hx : x ≠ 0) : x + 1 < Real.exp x := by
  obtain hx | hx := hx.symm.lt_or_gt
  · exact add_one_lt_exp_of_pos hx
  obtain h' | h' := le_or_gt 1 (-x)
  · linarith [x.exp_pos]
  have hx' : 0 < x + 1 := by linarith
  simpa [add_comm, exp_neg, inv_lt_inv₀ (exp_pos _) hx']
    using exp_bound_div_one_sub_of_interval' (neg_pos.2 hx) h'

theorem add_one_le_exp (x : ℝ) : x + 1 ≤ Real.exp x := by
  obtain rfl | hx := eq_or_ne x 0
  · simp
  · exact (add_one_lt_exp hx).le

lemma one_sub_lt_exp_neg {x : ℝ} (hx : x ≠ 0) : 1 - x < exp (-x) :=
  (sub_eq_neg_add _ _).trans_lt <| add_one_lt_exp <| neg_ne_zero.2 hx

lemma one_sub_le_exp_neg (x : ℝ) : 1 - x ≤ exp (-x) :=
  (sub_eq_neg_add _ _).trans_le <| add_one_le_exp _

theorem one_sub_div_pow_le_exp_neg {n : ℕ} {t : ℝ} (ht' : t ≤ n) : (1 - t / n) ^ n ≤ exp (-t) := by
  rcases eq_or_ne n 0 with (rfl | hn)
  · simp
    rwa [Nat.cast_zero] at ht'
  calc
    (1 - t / n) ^ n ≤ rexp (-(t / n)) ^ n := by
      gcongr
      · exact sub_nonneg.2 <| div_le_one_of_le₀ ht' n.cast_nonneg
      · exact one_sub_le_exp_neg _
    _ = rexp (-t) := by rw [← Real.exp_nat_mul, mul_neg, mul_comm, div_mul_cancel₀]; positivity

lemma le_inv_mul_exp (x : ℝ) {c : ℝ} (hc : 0 < c) : x ≤ c⁻¹ * exp (c * x) := by
  rw [le_inv_mul_iff₀ hc]
  calc c * x
  _ ≤ c * x + 1 := le_add_of_nonneg_right zero_le_one
  _ ≤ _ := Real.add_one_le_exp (c * x)

end Real

namespace Mathlib.Meta.Positivity
open Lean.Meta Qq

/-- Extension for the `positivity` tactic: `Real.exp` is always positive. -/
@[positivity Real.exp _]
def evalExp : PositivityExt where eval {u α} _ _ e := do
  match u, α, e with
  | 0, ~q(ℝ), ~q(Real.exp $a) =>
    assertInstancesCommute
    pure (.positive q(Real.exp_pos $a))
  | _, _, _ => throwError "not Real.exp"

end Mathlib.Meta.Positivity

namespace Complex

@[simp]
theorem norm_exp_ofReal (x : ℝ) : ‖exp x‖ = Real.exp x := by
  rw [← ofReal_exp]
  exact Complex.norm_of_nonneg (le_of_lt (Real.exp_pos _))

@[deprecated (since := "2025-02-16")] alias abs_exp_ofReal := norm_exp_ofReal

end Complex

```

ExponentialBounds.lean:
```
/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Joseph Myers
-/
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Bounds on specific values of the exponential
-/


namespace Real

open IsAbsoluteValue Finset CauSeq Complex

theorem exp_one_near_10 : |exp 1 - 2244083 / 825552| ≤ 1 / 10 ^ 10 := by
  apply exp_approx_start
  iterate 13 refine exp_1_approx_succ_eq (by norm_num1; rfl) (by norm_cast) ?_
  norm_num1
  refine exp_approx_end' _ (by norm_num1; rfl) _ (by norm_cast) (by simp) ?_
  rw [_root_.abs_one, abs_of_pos] <;> norm_num1

theorem exp_one_near_20 : |exp 1 - 363916618873 / 133877442384| ≤ 1 / 10 ^ 20 := by
  apply exp_approx_start
  iterate 21 refine exp_1_approx_succ_eq (by norm_num1; rfl) (by norm_cast) ?_
  norm_num1
  refine exp_approx_end' _ (by norm_num1; rfl) _ (by norm_cast) (by simp) ?_
  rw [_root_.abs_one, abs_of_pos] <;> norm_num1

theorem exp_one_gt_d9 : 2.7182818283 < exp 1 :=
  lt_of_lt_of_le (by norm_num) (sub_le_comm.1 (abs_sub_le_iff.1 exp_one_near_10).2)

theorem exp_one_lt_d9 : exp 1 < 2.7182818286 :=
  lt_of_le_of_lt (sub_le_iff_le_add.1 (abs_sub_le_iff.1 exp_one_near_10).1) (by norm_num)

theorem exp_neg_one_gt_d9 : 0.36787944116 < exp (-1) := by
  rw [exp_neg, lt_inv_comm₀ _ (exp_pos _)]
  · refine lt_of_le_of_lt (sub_le_iff_le_add.1 (abs_sub_le_iff.1 exp_one_near_10).1) ?_
    norm_num
  · norm_num

theorem exp_neg_one_lt_d9 : exp (-1) < 0.3678794412 := by
  rw [exp_neg, inv_lt_comm₀ (exp_pos _) (by norm_num)]
  exact lt_of_lt_of_le (by norm_num) (sub_le_comm.1 (abs_sub_le_iff.1 exp_one_near_10).2)

theorem log_two_near_10 : |log 2 - 287209 / 414355| ≤ 1 / 10 ^ 10 := by
  suffices |log 2 - 287209 / 414355| ≤ 1 / 17179869184 + (1 / 10 ^ 10 - 1 / 2 ^ 34) by
    norm_num1 at *
    assumption
  have t : |(2⁻¹ : ℝ)| = 2⁻¹ := by rw [abs_of_pos]; norm_num
  have z := Real.abs_log_sub_add_sum_range_le (show |(2⁻¹ : ℝ)| < 1 by rw [t]; norm_num) 34
  rw [t] at z
  norm_num1 at z
  rw [one_div (2 : ℝ), log_inv, ← sub_eq_add_neg, _root_.abs_sub_comm] at z
  apply le_trans (_root_.abs_sub_le _ _ _) (add_le_add z _)
  simp_rw [sum_range_succ]
  norm_num
  rw [abs_of_pos] <;> norm_num

theorem log_two_gt_d9 : 0.6931471803 < log 2 :=
  lt_of_lt_of_le (by norm_num1) (sub_le_comm.1 (abs_sub_le_iff.1 log_two_near_10).2)

theorem log_two_lt_d9 : log 2 < 0.6931471808 :=
  lt_of_le_of_lt (sub_le_iff_le_add.1 (abs_sub_le_iff.1 log_two_near_10).1) (by norm_num)

end Real

```

FiniteDimensional.lean:
```
/-
Copyright (c) 2020 Alexander Bentkamp, Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp, Sébastien Gouëzel, Eric Wieser
-/
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Data.Complex.Cardinality
import Mathlib.Data.Complex.Module
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Order.Interval.Set.Infinite

/-!
# Complex number as a finite dimensional vector space over `ℝ`

This file contains the `FiniteDimensional ℝ ℂ` instance, as well as some results about the rank
(`finrank` and `Module.rank`).
-/

open Module

namespace Complex

instance : FiniteDimensional ℝ ℂ := .of_fintype_basis basisOneI

/-- `ℂ` is a finite extension of `ℝ` of degree 2, i.e `[ℂ : ℝ] = 2` -/
@[simp, stacks 09G4]
theorem finrank_real_complex : finrank ℝ ℂ = 2 := by
  rw [finrank_eq_card_basis basisOneI, Fintype.card_fin]

@[simp]
theorem rank_real_complex : Module.rank ℝ ℂ = 2 := by simp [← finrank_eq_rank, finrank_real_complex]

theorem rank_real_complex'.{u} : Cardinal.lift.{u} (Module.rank ℝ ℂ) = 2 := by
  rw [← finrank_eq_rank, finrank_real_complex, Cardinal.lift_natCast, Nat.cast_ofNat]

/-- `Fact` version of the dimension of `ℂ` over `ℝ`, locally useful in the definition of the
circle. -/
theorem finrank_real_complex_fact : Fact (finrank ℝ ℂ = 2) :=
  ⟨finrank_real_complex⟩

end Complex

instance (priority := 100) FiniteDimensional.complexToReal (E : Type*) [AddCommGroup E]
    [Module ℂ E] [FiniteDimensional ℂ E] : FiniteDimensional ℝ E :=
  FiniteDimensional.trans ℝ ℂ E

theorem rank_real_of_complex (E : Type*) [AddCommGroup E] [Module ℂ E] :
    Module.rank ℝ E = 2 * Module.rank ℂ E :=
  Cardinal.lift_inj.{_,0}.1 <| by
    rw [← lift_rank_mul_lift_rank ℝ ℂ E, Complex.rank_real_complex']
    simp only [Cardinal.lift_id']

theorem finrank_real_of_complex (E : Type*) [AddCommGroup E] [Module ℂ E] :
    Module.finrank ℝ E = 2 * Module.finrank ℂ E := by
  rw [← Module.finrank_mul_finrank ℝ ℂ E, Complex.finrank_real_complex]

section Rational

open Cardinal Module

@[simp]
lemma Real.rank_rat_real : Module.rank ℚ ℝ = continuum := by
  refine (Free.rank_eq_mk_of_infinite_lt ℚ ℝ ?_).trans mk_real
  simpa [mk_real] using aleph0_lt_continuum

/-- `C` has an uncountable basis over `ℚ`. -/
@[simp, stacks 09G0]
lemma Complex.rank_rat_complex : Module.rank ℚ ℂ = continuum := by
  refine (Free.rank_eq_mk_of_infinite_lt ℚ ℂ ?_).trans Cardinal.mk_complex
  simpa using aleph0_lt_continuum

/-- `ℂ` and `ℝ` are isomorphic as vector spaces over `ℚ`, or equivalently,
as additive groups. -/
theorem Complex.nonempty_linearEquiv_real : Nonempty (ℂ ≃ₗ[ℚ] ℝ) :=
  LinearEquiv.nonempty_equiv_iff_rank_eq.mpr <| by simp

end Rational

```

Module.lean:
```
/-
Copyright (c) 2020 Alexander Bentkamp, Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp, Sébastien Gouëzel, Eric Wieser
-/
import Mathlib.Algebra.Algebra.RestrictScalars
import Mathlib.Algebra.CharP.Invertible
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Data.Real.Star

/-!
# Complex number as a vector space over `ℝ`

This file contains the following instances:
* Any `•`-structure (`SMul`, `MulAction`, `DistribMulAction`, `Module`, `Algebra`) on
  `ℝ` imbues a corresponding structure on `ℂ`. This includes the statement that `ℂ` is an `ℝ`
  algebra.
* any complex vector space is a real vector space;
* any finite dimensional complex vector space is a finite dimensional real vector space;
* the space of `ℝ`-linear maps from a real vector space to a complex vector space is a complex
  vector space.

It also defines bundled versions of four standard maps (respectively, the real part, the imaginary
part, the embedding of `ℝ` in `ℂ`, and the complex conjugate):

* `Complex.reLm` (`ℝ`-linear map);
* `Complex.imLm` (`ℝ`-linear map);
* `Complex.ofRealAm` (`ℝ`-algebra (homo)morphism);
* `Complex.conjAe` (`ℝ`-algebra equivalence).

It also provides a universal property of the complex numbers `Complex.lift`, which constructs a
`ℂ →ₐ[ℝ] A` into any `ℝ`-algebra `A` given a square root of `-1`.

In addition, this file provides a decomposition into `realPart` and `imaginaryPart` for any
element of a `StarModule` over `ℂ`.

## Notation

* `ℜ` and `ℑ` for the `realPart` and `imaginaryPart`, respectively, in the locale
  `ComplexStarModule`.
-/

assert_not_exists NNReal
namespace Complex

open ComplexConjugate

open scoped SMul

variable {R : Type*} {S : Type*}

attribute [local ext] Complex.ext


/- The priority of the following instances has been manually lowered, as when they don't apply
they lead Lean to a very costly path, and most often they don't apply (most actions on `ℂ` don't
come from actions on `ℝ`). See https://github.com/leanprover-community/mathlib4/pull/11980 -/

-- priority manually adjusted in https://github.com/leanprover-community/mathlib4/pull/11980
instance (priority := 90) [SMul R ℝ] [SMul S ℝ] [SMulCommClass R S ℝ] : SMulCommClass R S ℂ where
  smul_comm r s x := by ext <;> simp [smul_re, smul_im, smul_comm]

-- priority manually adjusted in https://github.com/leanprover-community/mathlib4/pull/11980
instance (priority := 90) [SMul R S] [SMul R ℝ] [SMul S ℝ] [IsScalarTower R S ℝ] :
    IsScalarTower R S ℂ where
  smul_assoc r s x := by ext <;> simp [smul_re, smul_im, smul_assoc]

-- priority manually adjusted in https://github.com/leanprover-community/mathlib4/pull/11980
instance (priority := 90) [SMul R ℝ] [SMul Rᵐᵒᵖ ℝ] [IsCentralScalar R ℝ] :
    IsCentralScalar R ℂ where
  op_smul_eq_smul r x := by ext <;> simp [smul_re, smul_im, op_smul_eq_smul]

-- priority manually adjusted in https://github.com/leanprover-community/mathlib4/pull/11980
instance (priority := 90) mulAction [Monoid R] [MulAction R ℝ] : MulAction R ℂ where
  one_smul x := by ext <;> simp [smul_re, smul_im, one_smul]
  mul_smul r s x := by ext <;> simp [smul_re, smul_im, mul_smul]

-- priority manually adjusted in https://github.com/leanprover-community/mathlib4/pull/11980
instance (priority := 90) distribSMul [DistribSMul R ℝ] : DistribSMul R ℂ where
  smul_add r x y := by ext <;> simp [smul_re, smul_im, smul_add]
  smul_zero r := by ext <;> simp [smul_re, smul_im, smul_zero]

-- priority manually adjusted in https://github.com/leanprover-community/mathlib4/pull/11980
instance (priority := 90) [Semiring R] [DistribMulAction R ℝ] : DistribMulAction R ℂ :=
  { Complex.distribSMul, Complex.mulAction with }

-- priority manually adjusted in https://github.com/leanprover-community/mathlib4/pull/11980
instance (priority := 100) instModule [Semiring R] [Module R ℝ] : Module R ℂ where
  add_smul r s x := by ext <;> simp [smul_re, smul_im, add_smul]
  zero_smul r := by ext <;> simp [smul_re, smul_im, zero_smul]

-- priority manually adjusted in https://github.com/leanprover-community/mathlib4/pull/11980
instance (priority := 95) instAlgebraOfReal [CommSemiring R] [Algebra R ℝ] : Algebra R ℂ where
  algebraMap := Complex.ofRealHom.comp (algebraMap R ℝ)
  smul := (· • ·)
  smul_def' := fun r x => by ext <;> simp [smul_re, smul_im, Algebra.smul_def]
  commutes' := fun r ⟨xr, xi⟩ => by ext <;> simp [smul_re, smul_im, Algebra.commutes]

instance : StarModule ℝ ℂ :=
  ⟨fun r x => by simp only [star_def, star_trivial, real_smul, map_mul, conj_ofReal]⟩

@[simp]
theorem coe_algebraMap : (algebraMap ℝ ℂ : ℝ → ℂ) = ((↑) : ℝ → ℂ) :=
  rfl

section

variable {A : Type*} [Semiring A] [Algebra ℝ A]

/-- We need this lemma since `Complex.coe_algebraMap` diverts the simp-normal form away from
`AlgHom.commutes`. -/
@[simp]
theorem _root_.AlgHom.map_coe_real_complex (f : ℂ →ₐ[ℝ] A) (x : ℝ) : f x = algebraMap ℝ A x :=
  f.commutes x

/-- Two `ℝ`-algebra homomorphisms from `ℂ` are equal if they agree on `Complex.I`. -/
@[ext]
theorem algHom_ext ⦃f g : ℂ →ₐ[ℝ] A⦄ (h : f I = g I) : f = g := by
  ext ⟨x, y⟩
  simp only [mk_eq_add_mul_I, map_add, AlgHom.map_coe_real_complex, map_mul, h]

end

open Submodule

/-- `ℂ` has a basis over `ℝ` given by `1` and `I`. -/
noncomputable def basisOneI : Basis (Fin 2) ℝ ℂ :=
  Basis.ofEquivFun
    { toFun := fun z => ![z.re, z.im]
      invFun := fun c => c 0 + c 1 • I
      left_inv := fun z => by simp
      right_inv := fun c => by
        ext i
        fin_cases i <;> simp
      map_add' := fun z z' => by simp
      map_smul' := fun c z => by simp }

@[simp]
theorem coe_basisOneI_repr (z : ℂ) : ⇑(basisOneI.repr z) = ![z.re, z.im] :=
  rfl

@[simp]
theorem coe_basisOneI : ⇑basisOneI = ![1, I] :=
  funext fun i =>
    Basis.apply_eq_iff.mpr <|
      Finsupp.ext fun j => by
        fin_cases i <;> fin_cases j <;> simp

end Complex

/- Register as an instance (with low priority) the fact that a complex vector space is also a real
vector space. -/
instance (priority := 900) Module.complexToReal (E : Type*) [AddCommGroup E] [Module ℂ E] :
    Module ℝ E :=
  RestrictScalars.module ℝ ℂ E

/- Register as an instance (with low priority) the fact that a complex algebra is also a real
algebra. -/
instance (priority := 900) Algebra.complexToReal {A : Type*} [Semiring A] [Algebra ℂ A] :
    Algebra ℝ A :=
  RestrictScalars.algebra ℝ ℂ A

-- try to make sure we're not introducing diamonds but we will need
-- `reducible_and_instances` which currently fails https://github.com/leanprover-community/mathlib4/issues/10906
example : Prod.algebra ℝ ℂ ℂ = (Prod.algebra ℂ ℂ ℂ).complexToReal := rfl

-- try to make sure we're not introducing diamonds but we will need
-- `reducible_and_instances` which currently fails https://github.com/leanprover-community/mathlib4/issues/10906
example {ι : Type*} [Fintype ι] :
    Pi.algebra (R := ℝ) ι (fun _ ↦ ℂ) = (Pi.algebra (R := ℂ) ι (fun _ ↦ ℂ)).complexToReal :=
  rfl

example {A : Type*} [Ring A] [inst : Algebra ℂ A] :
    (inst.complexToReal).toModule = (inst.toModule).complexToReal := by
  with_reducible_and_instances rfl

@[simp, norm_cast]
theorem Complex.coe_smul {E : Type*} [AddCommGroup E] [Module ℂ E] (x : ℝ) (y : E) :
    (x : ℂ) • y = x • y :=
  rfl

/-- The scalar action of `ℝ` on a `ℂ`-module `E` induced by `Module.complexToReal` commutes with
another scalar action of `M` on `E` whenever the action of `ℂ` commutes with the action of `M`. -/
instance (priority := 900) SMulCommClass.complexToReal {M E : Type*} [AddCommGroup E] [Module ℂ E]
    [SMul M E] [SMulCommClass ℂ M E] : SMulCommClass ℝ M E where
  smul_comm r _ _ := smul_comm (r : ℂ) _ _

/-- The scalar action of `ℝ` on a `ℂ`-module `E` induced by `Module.complexToReal` associates with
another scalar action of `M` on `E` whenever the action of `ℂ` associates with the action of `M`. -/
instance IsScalarTower.complexToReal {M E : Type*} [AddCommGroup M] [Module ℂ M] [AddCommGroup E]
    [Module ℂ E] [SMul M E] [IsScalarTower ℂ M E] : IsScalarTower ℝ M E where
  smul_assoc r _ _ := smul_assoc (r : ℂ) _ _

-- check that the following instance is implied by the one above.
example (E : Type*) [AddCommGroup E] [Module ℂ E] : IsScalarTower ℝ ℂ E := inferInstance

instance (priority := 900) StarModule.complexToReal {E : Type*} [AddCommGroup E] [Star E]
    [Module ℂ E] [StarModule ℂ E] : StarModule ℝ E :=
  ⟨fun r a => by rw [← smul_one_smul ℂ r a, star_smul, star_smul, star_one, smul_one_smul]⟩

namespace Complex

open ComplexConjugate

/-- Linear map version of the real part function, from `ℂ` to `ℝ`. -/
def reLm : ℂ →ₗ[ℝ] ℝ where
  toFun x := x.re
  map_add' := add_re
  map_smul' := by simp

@[simp]
theorem reLm_coe : ⇑reLm = re :=
  rfl

/-- Linear map version of the imaginary part function, from `ℂ` to `ℝ`. -/
def imLm : ℂ →ₗ[ℝ] ℝ where
  toFun x := x.im
  map_add' := add_im
  map_smul' := by simp

@[simp]
theorem imLm_coe : ⇑imLm = im :=
  rfl

/-- `ℝ`-algebra morphism version of the canonical embedding of `ℝ` in `ℂ`. -/
def ofRealAm : ℝ →ₐ[ℝ] ℂ :=
  Algebra.ofId ℝ ℂ

@[simp]
theorem ofRealAm_coe : ⇑ofRealAm = ((↑) : ℝ → ℂ) :=
  rfl

/-- `ℝ`-algebra isomorphism version of the complex conjugation function from `ℂ` to `ℂ` -/
def conjAe : ℂ ≃ₐ[ℝ] ℂ :=
  { conj with
    invFun := conj
    left_inv := star_star
    right_inv := star_star
    commutes' := conj_ofReal }

@[simp]
theorem conjAe_coe : ⇑conjAe = conj :=
  rfl

/-- The matrix representation of `conjAe`. -/
@[simp]
theorem toMatrix_conjAe :
    LinearMap.toMatrix basisOneI basisOneI conjAe.toLinearMap = !![1, 0; 0, -1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [LinearMap.toMatrix_apply]

/-- The identity and the complex conjugation are the only two `ℝ`-algebra homomorphisms of `ℂ`. -/
theorem real_algHom_eq_id_or_conj (f : ℂ →ₐ[ℝ] ℂ) : f = AlgHom.id ℝ ℂ ∨ f = conjAe := by
  refine
      (eq_or_eq_neg_of_sq_eq_sq (f I) I <| by rw [← map_pow, I_sq, map_neg, map_one]).imp ?_ ?_ <;>
    refine fun h => algHom_ext ?_
  exacts [h, conj_I.symm ▸ h]

/-- The natural `LinearEquiv` from `ℂ` to `ℝ × ℝ`. -/
@[simps! +simpRhs apply symm_apply_re symm_apply_im]
def equivRealProdLm : ℂ ≃ₗ[ℝ] ℝ × ℝ :=
  { equivRealProdAddHom with
    map_smul' := fun r c => by simp }

theorem equivRealProdLm_symm_apply (p : ℝ × ℝ) :
    Complex.equivRealProdLm.symm p = p.1 + p.2 * Complex.I := Complex.equivRealProd_symm_apply p
section lift

variable {A : Type*} [Ring A] [Algebra ℝ A]

/-- There is an alg_hom from `ℂ` to any `ℝ`-algebra with an element that squares to `-1`.

See `Complex.lift` for this as an equiv. -/
def liftAux (I' : A) (hf : I' * I' = -1) : ℂ →ₐ[ℝ] A :=
  AlgHom.ofLinearMap
    ((Algebra.linearMap ℝ A).comp reLm + (LinearMap.toSpanSingleton _ _ I').comp imLm)
    (show algebraMap ℝ A 1 + (0 : ℝ) • I' = 1 by rw [RingHom.map_one, zero_smul, add_zero])
    fun ⟨x₁, y₁⟩ ⟨x₂, y₂⟩ =>
    show
      algebraMap ℝ A (x₁ * x₂ - y₁ * y₂) + (x₁ * y₂ + y₁ * x₂) • I' =
        (algebraMap ℝ A x₁ + y₁ • I') * (algebraMap ℝ A x₂ + y₂ • I') by
      rw [add_mul, mul_add, mul_add, add_comm _ (y₁ • I' * y₂ • I'), add_add_add_comm]
      congr 1
      -- equate "real" and "imaginary" parts
      · rw [smul_mul_smul_comm, hf, smul_neg, ← Algebra.algebraMap_eq_smul_one, ← sub_eq_add_neg,
          ← RingHom.map_mul, ← RingHom.map_sub]
      · rw [Algebra.smul_def, Algebra.smul_def, Algebra.smul_def, ← Algebra.right_comm _ x₂,
          ← mul_assoc, ← add_mul, ← RingHom.map_mul, ← RingHom.map_mul, ← RingHom.map_add]

@[simp]
theorem liftAux_apply (I' : A) (hI') (z : ℂ) : liftAux I' hI' z = algebraMap ℝ A z.re + z.im • I' :=
  rfl

theorem liftAux_apply_I (I' : A) (hI') : liftAux I' hI' I = I' := by simp

@[simp]
theorem adjoin_I : Algebra.adjoin ℝ {I} = ⊤ := by
  refine top_unique fun x hx => ?_; clear hx
  rw [← x.re_add_im, ← smul_eq_mul, ← Complex.coe_algebraMap]
  exact add_mem (algebraMap_mem _ _) (Subalgebra.smul_mem _ (Algebra.subset_adjoin <| by simp) _)

@[simp]
theorem range_liftAux (I' : A) (hI') : (liftAux I' hI').range = Algebra.adjoin ℝ {I'} := by
  simp_rw [← Algebra.map_top, ← adjoin_I, AlgHom.map_adjoin, Set.image_singleton, liftAux_apply_I]

/-- A universal property of the complex numbers, providing a unique `ℂ →ₐ[ℝ] A` for every element
of `A` which squares to `-1`.

This can be used to embed the complex numbers in the `Quaternion`s.

This isomorphism is named to match the very similar `Zsqrtd.lift`. -/
@[simps +simpRhs]
def lift : { I' : A // I' * I' = -1 } ≃ (ℂ →ₐ[ℝ] A) where
  toFun I' := liftAux I' I'.prop
  invFun F := ⟨F I, by rw [← map_mul, I_mul_I, map_neg, map_one]⟩
  left_inv I' := Subtype.ext <| liftAux_apply_I (I' : A) I'.prop
  right_inv _ := algHom_ext <| liftAux_apply_I _ _

-- When applied to `Complex.I` itself, `lift` is the identity.
@[simp]
theorem liftAux_I : liftAux I I_mul_I = AlgHom.id ℝ ℂ :=
  algHom_ext <| liftAux_apply_I _ _

-- When applied to `-Complex.I`, `lift` is conjugation, `conj`.
@[simp]
theorem liftAux_neg_I : liftAux (-I) ((neg_mul_neg _ _).trans I_mul_I) = conjAe :=
  algHom_ext <| (liftAux_apply_I _ _).trans conj_I.symm

end lift

end Complex

section RealImaginaryPart

open Complex

variable {A : Type*} [AddCommGroup A] [Module ℂ A] [StarAddMonoid A] [StarModule ℂ A]

/-- Create a `selfAdjoint` element from a `skewAdjoint` element by multiplying by the scalar
`-Complex.I`. -/
@[simps]
def skewAdjoint.negISMul : skewAdjoint A →ₗ[ℝ] selfAdjoint A where
  toFun a :=
    ⟨-I • ↑a, by
      simp only [neg_smul, neg_mem_iff, selfAdjoint.mem_iff, star_smul, star_def, conj_I,
        star_val_eq, smul_neg, neg_neg]⟩
  map_add' a b := by
    ext
    simp only [AddSubgroup.coe_add, smul_add, AddMemClass.mk_add_mk]
  map_smul' a b := by
    ext
    simp only [neg_smul, skewAdjoint.val_smul, AddSubgroup.coe_mk, RingHom.id_apply,
      selfAdjoint.val_smul, smul_neg, neg_inj]
    rw [smul_comm]

theorem skewAdjoint.I_smul_neg_I (a : skewAdjoint A) : I • (skewAdjoint.negISMul a : A) = a := by
  simp only [smul_smul, skewAdjoint.negISMul_apply_coe, neg_smul, smul_neg, I_mul_I, one_smul,
    neg_neg]

/-- The real part `ℜ a` of an element `a` of a star module over `ℂ`, as a linear map. This is just
`selfAdjointPart ℝ`, but we provide it as a separate definition in order to link it with lemmas
concerning the `imaginaryPart`, which doesn't exist in star modules over other rings. -/
noncomputable def realPart : A →ₗ[ℝ] selfAdjoint A :=
  selfAdjointPart ℝ

/-- The imaginary part `ℑ a` of an element `a` of a star module over `ℂ`, as a linear map into the
self adjoint elements. In a general star module, we have a decomposition into the `selfAdjoint`
and `skewAdjoint` parts, but in a star module over `ℂ` we have
`realPart_add_I_smul_imaginaryPart`, which allows us to decompose into a linear combination of
`selfAdjoint`s. -/
noncomputable def imaginaryPart : A →ₗ[ℝ] selfAdjoint A :=
  skewAdjoint.negISMul.comp (skewAdjointPart ℝ)

@[inherit_doc]
scoped[ComplexStarModule] notation "ℜ" => realPart
@[inherit_doc]
scoped[ComplexStarModule] notation "ℑ" => imaginaryPart

open ComplexStarModule

theorem realPart_apply_coe (a : A) : (ℜ a : A) = (2 : ℝ)⁻¹ • (a + star a) := by
  unfold realPart
  simp only [selfAdjointPart_apply_coe, invOf_eq_inv]

theorem imaginaryPart_apply_coe (a : A) : (ℑ a : A) = -I • (2 : ℝ)⁻¹ • (a - star a) := by
  unfold imaginaryPart
  simp only [LinearMap.coe_comp, Function.comp_apply, skewAdjoint.negISMul_apply_coe,
    skewAdjointPart_apply_coe, invOf_eq_inv, neg_smul]

/-- The standard decomposition of `ℜ a + Complex.I • ℑ a = a` of an element of a star module over
`ℂ` into a linear combination of self adjoint elements. -/
theorem realPart_add_I_smul_imaginaryPart (a : A) : (ℜ a : A) + I • (ℑ a : A) = a := by
  simpa only [smul_smul, realPart_apply_coe, imaginaryPart_apply_coe, neg_smul, I_mul_I, one_smul,
    neg_sub, add_add_sub_cancel, smul_sub, smul_add, neg_sub_neg, invOf_eq_inv] using
    invOf_two_smul_add_invOf_two_smul ℝ a

@[simp]
theorem realPart_I_smul (a : A) : ℜ (I • a) = -ℑ a := by
  ext
  simp [realPart_apply_coe, imaginaryPart_apply_coe, smul_comm I, sub_eq_add_neg, add_comm]

@[simp]
theorem imaginaryPart_I_smul (a : A) : ℑ (I • a) = ℜ a := by
  ext
  simp [realPart_apply_coe, imaginaryPart_apply_coe, smul_comm I (2⁻¹ : ℝ), smul_smul I]

theorem realPart_smul (z : ℂ) (a : A) : ℜ (z • a) = z.re • ℜ a - z.im • ℑ a := by
  have := by congrm (ℜ ($((re_add_im z).symm) • a))
  simpa [-re_add_im, add_smul, ← smul_smul, sub_eq_add_neg]

theorem imaginaryPart_smul (z : ℂ) (a : A) : ℑ (z • a) = z.re • ℑ a + z.im • ℜ a := by
  have := by congrm (ℑ ($((re_add_im z).symm) • a))
  simpa [-re_add_im, add_smul, ← smul_smul]

lemma skewAdjointPart_eq_I_smul_imaginaryPart (x : A) :
    (skewAdjointPart ℝ x : A) = I • (imaginaryPart x : A) := by
  simp [imaginaryPart_apply_coe, smul_smul]

lemma imaginaryPart_eq_neg_I_smul_skewAdjointPart (x : A) :
    (imaginaryPart x : A) = -I • (skewAdjointPart ℝ x : A) :=
  rfl

lemma IsSelfAdjoint.coe_realPart {x : A} (hx : IsSelfAdjoint x) :
    (ℜ x : A) = x :=
  hx.coe_selfAdjointPart_apply ℝ

nonrec lemma IsSelfAdjoint.imaginaryPart {x : A} (hx : IsSelfAdjoint x) :
    ℑ x = 0 := by
  rw [imaginaryPart, LinearMap.comp_apply, hx.skewAdjointPart_apply _, map_zero]

lemma realPart_comp_subtype_selfAdjoint :
    realPart.comp (selfAdjoint.submodule ℝ A).subtype = LinearMap.id :=
  selfAdjointPart_comp_subtype_selfAdjoint ℝ

lemma imaginaryPart_comp_subtype_selfAdjoint :
    imaginaryPart.comp (selfAdjoint.submodule ℝ A).subtype = 0 := by
  rw [imaginaryPart, LinearMap.comp_assoc, skewAdjointPart_comp_subtype_selfAdjoint,
    LinearMap.comp_zero]

@[simp]
lemma imaginaryPart_realPart {x : A} : ℑ (ℜ x : A) = 0 :=
  (ℜ x).property.imaginaryPart

@[simp]
lemma imaginaryPart_imaginaryPart {x : A} : ℑ (ℑ x : A) = 0 :=
  (ℑ x).property.imaginaryPart

@[simp]
lemma realPart_idem {x : A} : ℜ (ℜ x : A) = ℜ x :=
  Subtype.ext <| (ℜ x).property.coe_realPart

@[simp]
lemma realPart_imaginaryPart {x : A} : ℜ (ℑ x : A) = ℑ x :=
  Subtype.ext <| (ℑ x).property.coe_realPart

lemma realPart_surjective : Function.Surjective (realPart (A := A)) :=
  fun x ↦ ⟨(x : A), Subtype.ext x.property.coe_realPart⟩

lemma imaginaryPart_surjective : Function.Surjective (imaginaryPart (A := A)) :=
  fun x ↦
    ⟨I • (x : A), Subtype.ext <| by simp only [imaginaryPart_I_smul, x.property.coe_realPart]⟩

open Submodule

lemma span_selfAdjoint : span ℂ (selfAdjoint A : Set A) = ⊤ := by
  refine eq_top_iff'.mpr fun x ↦ ?_
  rw [← realPart_add_I_smul_imaginaryPart x]
  exact add_mem (subset_span (ℜ x).property) <|
    SMulMemClass.smul_mem _ <| subset_span (ℑ x).property

/-- The natural `ℝ`-linear equivalence between `selfAdjoint ℂ` and `ℝ`. -/
@[simps apply symm_apply]
def Complex.selfAdjointEquiv : selfAdjoint ℂ ≃ₗ[ℝ] ℝ where
  toFun := fun z ↦ (z : ℂ).re
  invFun := fun x ↦ ⟨x, conj_ofReal x⟩
  left_inv := fun z ↦ Subtype.ext <| conj_eq_iff_re.mp z.property.star_eq
  map_add' := by simp
  map_smul' := by simp

lemma Complex.coe_selfAdjointEquiv (z : selfAdjoint ℂ) :
    (selfAdjointEquiv z : ℂ) = z := by
  simpa [selfAdjointEquiv_symm_apply]
    using (congr_arg Subtype.val <| Complex.selfAdjointEquiv.left_inv z)

@[simp]
lemma realPart_ofReal (r : ℝ) : (ℜ (r : ℂ) : ℂ) = r := by
  rw [realPart_apply_coe, star_def, conj_ofReal, ← two_smul ℝ (r : ℂ)]
  simp

@[simp]
lemma imaginaryPart_ofReal (r : ℝ) : ℑ (r : ℂ) = 0 := by
  ext1; simp [imaginaryPart_apply_coe, conj_ofReal]

lemma Complex.coe_realPart (z : ℂ) : (ℜ z : ℂ) = z.re := calc
  (ℜ z : ℂ) = (↑(ℜ (↑z.re + ↑z.im * I))) := by congrm (ℜ $((re_add_im z).symm))
  _         = z.re                       := by
    rw [map_add, AddSubmonoid.coe_add, mul_comm, ← smul_eq_mul, realPart_I_smul]
    simp [conj_ofReal, ← two_mul]

lemma star_mul_self_add_self_mul_star {A : Type*} [NonUnitalNonAssocRing A] [StarRing A]
    [Module ℂ A] [IsScalarTower ℂ A A] [SMulCommClass ℂ A A] [StarModule ℂ A] (a : A) :
    star a * a + a * star a = 2 • (ℜ a * ℜ a + ℑ a * ℑ a) :=
  have a_eq := (realPart_add_I_smul_imaginaryPart a).symm
  calc
    star a * a + a * star a = _ :=
      congr((star $(a_eq)) * $(a_eq) + $(a_eq) * (star $(a_eq)))
    _ = 2 • (ℜ a * ℜ a + ℑ a * ℑ a) := by
      simp [mul_add, add_mul, smul_smul, two_smul, mul_smul_comm,
        smul_mul_assoc]
      abel

end RealImaginaryPart

```

Norm.lean:
```
/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Sqrt

/-!
  # Norm on the complex numbers
-/

noncomputable section

open ComplexConjugate Topology Filter Set

namespace Complex
variable {z : ℂ}

instance instNorm : Norm ℂ where
  norm z := √(normSq z)

theorem norm_def (z : ℂ) : ‖z‖ = √(normSq z) := rfl

theorem norm_mul_self_eq_normSq (z : ℂ) : ‖z‖ * ‖z‖ = normSq z :=
  Real.mul_self_sqrt (normSq_nonneg _)

@[deprecated (since := "2025-02-16")] alias mul_self_abs := norm_mul_self_eq_normSq

private theorem norm_nonneg (z : ℂ) : 0 ≤ ‖z‖ :=
  Real.sqrt_nonneg _

@[bound]
theorem abs_re_le_norm (z : ℂ) : |z.re| ≤ ‖z‖ := by
  rw [mul_self_le_mul_self_iff (abs_nonneg z.re) (norm_nonneg _), abs_mul_abs_self,
    norm_mul_self_eq_normSq]
  apply re_sq_le_normSq

theorem re_le_norm (z : ℂ) : z.re ≤ ‖z‖ :=
  (abs_le.1 (abs_re_le_norm _)).2

@[deprecated (since := "2025-02-16")] alias abs_re_le_abs := abs_re_le_norm
@[deprecated (since := "2025-02-16")] alias re_le_abs := re_le_norm

private theorem norm_add_le' (z w : ℂ) :  ‖z + w‖ ≤ ‖z‖ + ‖w‖ :=
  (mul_self_le_mul_self_iff (norm_nonneg (z + w)) (add_nonneg (norm_nonneg z)
    (norm_nonneg w))).2 <| by
    rw [norm_mul_self_eq_normSq, add_mul_self_eq, norm_mul_self_eq_normSq, norm_mul_self_eq_normSq,
      add_right_comm, normSq_add, add_le_add_iff_left, mul_assoc, mul_le_mul_left (zero_lt_two' ℝ),
      norm_def, norm_def, ← Real.sqrt_mul <| normSq_nonneg z, ← normSq_conj w, ← map_mul]
    exact re_le_norm (z * conj w)

private theorem norm_eq_zero_iff {z : ℂ} : ‖z‖ = 0 ↔ z = 0 :=
  (Real.sqrt_eq_zero <| normSq_nonneg _).trans normSq_eq_zero

private theorem norm_map_zero' : ‖(0 : ℂ)‖ = 0 :=
  norm_eq_zero_iff.mpr rfl

private theorem norm_neg' (z : ℂ) : ‖-z‖ = ‖z‖ := by
  rw [Complex.norm_def, norm_def, normSq_neg]

instance instNormedAddCommGroup : NormedAddCommGroup ℂ :=
  AddGroupNorm.toNormedAddCommGroup
  { toFun := norm
    map_zero' := norm_map_zero'
    add_le' := norm_add_le'
    neg' := norm_neg'
    eq_zero_of_map_eq_zero' := fun _ ↦ norm_eq_zero_iff.mp }

/-- The complex absolute value function, defined as the Complex norm. -/
@[deprecated "use the norm instead" (since := "2025-02-16")]
protected noncomputable abbrev abs (z : ℂ) : ℝ := ‖z‖

@[deprecated (since := "2025-02-16")] alias abs_apply := norm_def

@[simp 1100]
protected theorem norm_mul (z w : ℂ) : ‖z * w‖ = ‖z‖ * ‖w‖ := by
  rw [norm_def, norm_def, norm_def, normSq_mul, Real.sqrt_mul (normSq_nonneg _)]

@[simp 1100]
protected theorem norm_div (z w : ℂ) : ‖z / w‖ = ‖z‖ / ‖w‖ := by
  rw [norm_def, norm_def, norm_def, normSq_div, Real.sqrt_div (normSq_nonneg _)]

instance isAbsoluteValueNorm : IsAbsoluteValue (‖·‖ : ℂ → ℝ) where
  abv_nonneg' := norm_nonneg
  abv_eq_zero' := norm_eq_zero_iff
  abv_add' := norm_add_le
  abv_mul' := Complex.norm_mul

protected theorem norm_pow (z : ℂ) (n : ℕ) : ‖z ^ n‖ = ‖z‖ ^ n :=
  map_pow isAbsoluteValueNorm.abvHom _ _

protected theorem norm_zpow (z : ℂ) (n : ℤ) :  ‖z ^ n‖ = ‖z‖ ^ n :=
  map_zpow₀ isAbsoluteValueNorm.abvHom _ _

protected theorem norm_prod {ι : Type*} (s : Finset ι) (f : ι → ℂ) :
    ‖s.prod f‖ = s.prod fun i ↦ ‖f i‖ :=
  map_prod isAbsoluteValueNorm.abvHom _ _

theorem norm_conj (z : ℂ) : ‖conj z‖ = ‖z‖ := by simp [norm_def]

@[deprecated (since := "2025-02-16")] protected alias abs_pow := Complex.norm_pow
@[deprecated (since := "2025-02-16")] alias abs_zpow := Complex.norm_zpow
@[deprecated (since := "2025-02-16")] alias abs_prod := Complex.norm_prod
@[deprecated (since := "2025-02-16")] alias abs_conj := norm_conj
@[deprecated (since := "2025-02-16")] protected alias abs_abs := abs_norm

@[simp] lemma norm_I : ‖I‖ = 1 := by simp [norm]

@[deprecated (since := "2025-02-16")] alias abs_I := norm_I

@[simp] lemma nnnorm_I : ‖I‖₊ = 1 := by simp [nnnorm]

@[simp 1100, norm_cast]
lemma norm_real (r : ℝ) : ‖(r : ℂ)‖ = ‖r‖ := by
  simp [norm_def, Real.sqrt_mul_self_eq_abs]

protected theorem norm_of_nonneg {r : ℝ} (h : 0 ≤ r) : ‖(r : ℂ)‖ = r :=
  (norm_real _).trans (abs_of_nonneg h)

@[deprecated (since := "2025-02-16")] alias abs_ofReal := norm_real
@[deprecated (since := "2025-02-16")] protected alias abs_of_nonneg := Complex.norm_of_nonneg

@[simp, norm_cast]
lemma nnnorm_real (r : ℝ) : ‖(r : ℂ)‖₊ = ‖r‖₊ := by ext; exact norm_real _

@[simp 1100, norm_cast]
lemma norm_natCast (n : ℕ) : ‖(n : ℂ)‖ = n := Complex.norm_of_nonneg n.cast_nonneg

@[simp 1100]
lemma norm_ofNat (n : ℕ) [n.AtLeastTwo] :
    ‖(ofNat(n) : ℂ)‖ = OfNat.ofNat n := norm_natCast n

protected lemma norm_two : ‖(2 : ℂ)‖ = 2 := norm_ofNat 2

@[simp 1100, norm_cast]
lemma nnnorm_natCast (n : ℕ) : ‖(n : ℂ)‖₊ = n := Subtype.ext <| by simp

@[simp 1100]
lemma nnnorm_ofNat (n : ℕ) [n.AtLeastTwo] :
    ‖(ofNat(n) : ℂ)‖₊ = OfNat.ofNat n := nnnorm_natCast n

@[deprecated (since := "2025-02-16")] alias abs_natCast := norm_natCast
@[deprecated (since := "2025-02-16")] alias abs_ofNat := norm_ofNat
@[deprecated (since := "2025-02-16")] protected alias abs_two := Complex.norm_two

@[simp 1100, norm_cast]
lemma norm_intCast (n : ℤ) : ‖(n : ℂ)‖ = |(n : ℝ)| := by
  rw [← ofReal_intCast, norm_real, Real.norm_eq_abs]

theorem norm_int_of_nonneg {n : ℤ} (hn : 0 ≤ n) : ‖(n : ℂ)‖ = n := by
  rw [norm_intCast, ← Int.cast_abs, abs_of_nonneg hn]

@[simp 1100, norm_cast]
lemma norm_ratCast (q : ℚ) : ‖(q : ℂ)‖ = |(q : ℝ)| := norm_real _

@[simp 1100, norm_cast]
lemma norm_nnratCast (q : ℚ≥0) : ‖(q : ℂ)‖ = q := Complex.norm_of_nonneg q.cast_nonneg

@[simp 1100, norm_cast]
lemma nnnorm_ratCast (q : ℚ) : ‖(q : ℂ)‖₊ = ‖(q : ℝ)‖₊ := nnnorm_real q

@[simp 1100, norm_cast]
lemma nnnorm_nnratCast (q : ℚ≥0) : ‖(q : ℂ)‖₊ = q := by simp [nnnorm]

@[deprecated (since := "2025-02-16")] alias abs_intCast := norm_intCast

lemma normSq_eq_norm_sq (z : ℂ) : normSq z = ‖z‖ ^ 2 := by
  simp [norm_def, sq, Real.mul_self_sqrt (normSq_nonneg _)]

protected theorem sq_norm (z : ℂ) : ‖z‖ ^ 2 = normSq z := (normSq_eq_norm_sq z).symm

@[simp]
theorem sq_norm_sub_sq_re (z : ℂ) : ‖z‖ ^ 2 - z.re ^ 2 = z.im ^ 2 := by
  rw [Complex.sq_norm, normSq_apply, ← sq, ← sq, add_sub_cancel_left]

@[simp]
theorem sq_norm_sub_sq_im (z : ℂ) : ‖z‖ ^ 2 - z.im ^ 2 = z.re ^ 2 := by
  rw [← sq_norm_sub_sq_re, sub_sub_cancel]

lemma norm_add_mul_I (x y : ℝ) : ‖x + y * I‖ = √(x ^ 2 + y ^ 2) := by
  rw [← normSq_add_mul_I]; rfl

lemma norm_eq_sqrt_sq_add_sq (z : ℂ) : ‖z‖ = √(z.re ^ 2 + z.im ^ 2) := by
  rw [norm_def, normSq_apply, sq, sq]

@[deprecated (since := "2025-02-16")] alias normSq_eq_abs := normSq_eq_norm_sq
@[deprecated (since := "2025-02-16")] protected alias sq_abs := Complex.sq_norm
@[deprecated (since := "2025-02-16")] alias sq_abs_sub_sq_re := sq_norm_sub_sq_re
@[deprecated (since := "2025-02-16")] alias sq_abs_sub_sq_im := sq_norm_sub_sq_im
@[deprecated (since := "2025-02-16")] alias abs_add_mul_I := norm_add_mul_I
@[deprecated (since := "2025-02-16")] alias abs_eq_sqrt_sq_add_sq := norm_eq_sqrt_sq_add_sq

@[simp 1100]
protected theorem range_norm : range (‖·‖ : ℂ → ℝ) = Set.Ici 0 :=
  Subset.antisymm (range_subset_iff.2 norm_nonneg) fun x hx ↦ ⟨x, Complex.norm_of_nonneg hx⟩

@[deprecated (since := "2025-02-16")] alias range_abs := Complex.range_norm

@[simp]
theorem range_normSq : range normSq = Ici 0 :=
  Subset.antisymm (range_subset_iff.2 normSq_nonneg) fun x hx =>
    ⟨√x, by rw [normSq_ofReal, Real.mul_self_sqrt hx]⟩

theorem norm_le_abs_re_add_abs_im (z : ℂ) : ‖z‖ ≤ |z.re| + |z.im| := by
    simpa [re_add_im] using norm_add_le (z.re : ℂ) (z.im * I)

@[bound]
theorem abs_im_le_norm (z : ℂ) : |z.im| ≤ ‖z‖ :=
  Real.abs_le_sqrt <| by
    rw [normSq_apply, ← sq, ← sq]
    exact le_add_of_nonneg_left (sq_nonneg _)

theorem im_le_norm (z : ℂ) : z.im ≤ ‖z‖ :=
  (abs_le.1 (abs_im_le_norm _)).2

@[simp]
theorem abs_re_lt_norm {z : ℂ} : |z.re| < ‖z‖ ↔ z.im ≠ 0 := by
  rw [norm_def, Real.lt_sqrt (abs_nonneg _), normSq_apply, sq_abs, ← sq, lt_add_iff_pos_right,
    mul_self_pos]

@[simp]
theorem abs_im_lt_norm {z : ℂ} : |z.im| < ‖z‖ ↔ z.re ≠ 0 := by
  simpa using @abs_re_lt_norm (z * I)

@[simp]
lemma abs_re_eq_norm {z : ℂ} : |z.re| = ‖z‖ ↔ z.im = 0 :=
  not_iff_not.1 <| (abs_re_le_norm z).lt_iff_ne.symm.trans abs_re_lt_norm

@[simp]
lemma abs_im_eq_norm {z : ℂ} : |z.im| = ‖z‖ ↔ z.re = 0 :=
  not_iff_not.1 <| (abs_im_le_norm z).lt_iff_ne.symm.trans abs_im_lt_norm

@[deprecated (since := "2025-02-16")] alias abs_le_abs_re_add_abs_im := norm_le_abs_re_add_abs_im
@[deprecated (since := "2025-02-16")] alias abs_im_le_abs := abs_im_le_norm
@[deprecated (since := "2025-02-16")] alias im_le_abs := im_le_norm
@[deprecated (since := "2025-02-16")] alias abs_re_lt_abs := abs_re_lt_norm
@[deprecated (since := "2025-02-16")] alias abs_im_lt_abs := abs_im_lt_norm
@[deprecated (since := "2025-02-16")] alias abs_re_eq_abs := abs_re_eq_norm
@[deprecated (since := "2025-02-16")] alias abs_im_eq_abs := abs_im_eq_norm

theorem norm_le_sqrt_two_mul_max (z : ℂ) : ‖z‖ ≤ √2 * max |z.re| |z.im| := by
  obtain ⟨x, y⟩ := z
  simp only [norm_def, normSq_mk, norm_def, ← sq]
  set m := max |x| |y|
  have hm₀ : 0 ≤ m := by positivity
  calc
    √(x ^ 2 + y ^ 2) ≤ √(m ^ 2 + m ^ 2) := by
      gcongr √(?_ + ?_) <;> rw [sq_le_sq, abs_of_nonneg hm₀]
      exacts [le_max_left _ _, le_max_right _ _]
    _ = √2 * m := by
      rw [← two_mul, Real.sqrt_mul, Real.sqrt_sq] <;> positivity

theorem abs_re_div_norm_le_one (z : ℂ) : |z.re / ‖z‖| ≤ 1 :=
  if hz : z = 0 then by simp [hz, zero_le_one]
  else by
    simp_rw [abs_div, abs_norm, div_le_iff₀ (norm_pos_iff.mpr hz), one_mul, abs_re_le_norm]

theorem abs_im_div_norm_le_one (z : ℂ) : |z.im / ‖z‖| ≤ 1 :=
  if hz : z = 0 then by simp [hz, zero_le_one]
  else by
    simp_rw [_root_.abs_div, abs_norm, div_le_iff₀ (norm_pos_iff.mpr hz), one_mul, abs_im_le_norm]

@[deprecated (since := "2025-02-16")] alias abs_le_sqrt_two_mul_max := norm_le_sqrt_two_mul_max
@[deprecated (since := "2025-02-16")] alias abs_re_div_abs_le_one := abs_re_div_norm_le_one
@[deprecated (since := "2025-02-16")] alias abs_im_div_abs_le_one := abs_im_div_norm_le_one

theorem dist_eq (z w : ℂ) : dist z w = ‖z - w‖ := rfl

theorem dist_eq_re_im (z w : ℂ) : dist z w = √((z.re - w.re) ^ 2 + (z.im - w.im) ^ 2) := by
  rw [sq, sq]
  rfl

@[simp]
theorem dist_mk (x₁ y₁ x₂ y₂ : ℝ) :
    dist (mk x₁ y₁) (mk x₂ y₂) = √((x₁ - x₂) ^ 2 + (y₁ - y₂) ^ 2) :=
  dist_eq_re_im _ _

theorem dist_of_re_eq {z w : ℂ} (h : z.re = w.re) : dist z w = dist z.im w.im := by
  rw [dist_eq_re_im, h, sub_self, zero_pow two_ne_zero, zero_add, Real.sqrt_sq_eq_abs, Real.dist_eq]

theorem nndist_of_re_eq {z w : ℂ} (h : z.re = w.re) : nndist z w = nndist z.im w.im :=
  NNReal.eq <| dist_of_re_eq h

theorem edist_of_re_eq {z w : ℂ} (h : z.re = w.re) : edist z w = edist z.im w.im := by
  rw [edist_nndist, edist_nndist, nndist_of_re_eq h]

theorem dist_of_im_eq {z w : ℂ} (h : z.im = w.im) : dist z w = dist z.re w.re := by
  rw [dist_eq_re_im, h, sub_self, zero_pow two_ne_zero, add_zero, Real.sqrt_sq_eq_abs, Real.dist_eq]

theorem nndist_of_im_eq {z w : ℂ} (h : z.im = w.im) : nndist z w = nndist z.re w.re :=
  NNReal.eq <| dist_of_im_eq h

theorem edist_of_im_eq {z w : ℂ} (h : z.im = w.im) : edist z w = edist z.re w.re := by
  rw [edist_nndist, edist_nndist, nndist_of_im_eq h]

theorem dist_conj_self (z : ℂ) : dist (conj z) z = 2 * |z.im| := by
  rw [dist_of_re_eq (conj_re z), conj_im, dist_comm, Real.dist_eq, sub_neg_eq_add, ← two_mul,
    _root_.abs_mul, abs_of_pos (zero_lt_two' ℝ)]

theorem nndist_conj_self (z : ℂ) : nndist (conj z) z = 2 * Real.nnabs z.im :=
  NNReal.eq <| by rw [← dist_nndist, NNReal.coe_mul, NNReal.coe_two, Real.coe_nnabs, dist_conj_self]

theorem dist_self_conj (z : ℂ) : dist z (conj z) = 2 * |z.im| := by rw [dist_comm, dist_conj_self]

theorem nndist_self_conj (z : ℂ) : nndist z (conj z) = 2 * Real.nnabs z.im := by
  rw [nndist_comm, nndist_conj_self]

/-! ### Cauchy sequences -/

theorem isCauSeq_re (f : CauSeq ℂ (‖·‖)) : IsCauSeq abs fun n ↦ (f n).re := fun _ ε0 ↦
  (f.cauchy ε0).imp fun i H j ij ↦
    lt_of_le_of_lt (by simpa using abs_re_le_norm (f j - f i)) (H _ ij)

theorem isCauSeq_im (f : CauSeq ℂ (‖·‖)) : IsCauSeq abs fun n ↦ (f n).im := fun ε ε0 ↦
  (f.cauchy ε0).imp fun i H j ij ↦ by
    simpa only [← ofReal_sub, norm_real, sub_re] using (abs_im_le_norm _).trans_lt <| H _ ij

/-- The real part of a complex Cauchy sequence, as a real Cauchy sequence. -/
noncomputable def cauSeqRe (f : CauSeq ℂ (‖·‖)) : CauSeq ℝ abs :=
  ⟨_, isCauSeq_re f⟩

/-- The imaginary part of a complex Cauchy sequence, as a real Cauchy sequence. -/
noncomputable def cauSeqIm (f : CauSeq ℂ (‖·‖)) : CauSeq ℝ abs :=
  ⟨_, isCauSeq_im f⟩

theorem isCauSeq_norm {f : ℕ → ℂ} (hf : IsCauSeq (‖·‖) f) :
    IsCauSeq abs ((‖·‖) ∘ f) := fun ε ε0 ↦
  let ⟨i, hi⟩ := hf ε ε0
  ⟨i, fun j hj ↦  lt_of_le_of_lt (abs_norm_sub_norm_le _ _) (hi j hj)⟩

/-- The limit of a Cauchy sequence of complex numbers. -/
noncomputable def limAux (f : CauSeq ℂ (‖·‖)) : ℂ :=
  ⟨CauSeq.lim (cauSeqRe f), CauSeq.lim (cauSeqIm f)⟩

theorem equiv_limAux (f : CauSeq ℂ (‖·‖)) :
    f ≈ CauSeq.const (‖·‖) (limAux f) := fun ε ε0 ↦
  (exists_forall_ge_and
  (CauSeq.equiv_lim ⟨_, isCauSeq_re f⟩ _ (half_pos ε0))
        (CauSeq.equiv_lim ⟨_, isCauSeq_im f⟩ _ (half_pos ε0))).imp
    fun _ H j ij ↦ by
    obtain ⟨H₁, H₂⟩ := H _ ij
    apply lt_of_le_of_lt (norm_le_abs_re_add_abs_im _)
    dsimp [limAux] at *
    have := add_lt_add H₁ H₂
    rwa [add_halves] at this

instance instIsComplete : CauSeq.IsComplete ℂ (‖·‖) :=
  ⟨fun f ↦ ⟨limAux f, equiv_limAux f⟩⟩

open CauSeq

theorem lim_eq_lim_im_add_lim_re (f : CauSeq ℂ (‖·‖)) :
    lim f = ↑(lim (cauSeqRe f)) + ↑(lim (cauSeqIm f)) * I :=
  lim_eq_of_equiv_const <|
    letI : IsAbsoluteValue (‖·‖ : ℂ → ℝ) := inferInstance
    calc
      f ≈ _ := equiv_limAux f
      _ = CauSeq.const (‖·‖) (↑(lim (cauSeqRe f)) + ↑(lim (cauSeqIm f)) * I) :=
        CauSeq.ext fun _ ↦
          Complex.ext (by simp [limAux, cauSeqRe, ofReal]) (by simp [limAux, cauSeqIm, ofReal])

theorem lim_re (f : CauSeq ℂ (‖·‖)) : lim (cauSeqRe f) = (lim f).re := by
  rw [lim_eq_lim_im_add_lim_re]; simp [ofReal]

theorem lim_im (f : CauSeq ℂ (‖·‖)) : lim (cauSeqIm f) = (lim f).im := by
  rw [lim_eq_lim_im_add_lim_re]; simp [ofReal]

theorem isCauSeq_conj (f : CauSeq ℂ (‖·‖)) :
    IsCauSeq (‖·‖) fun n ↦ conj (f n) := fun ε ε0 ↦
  let ⟨i, hi⟩ := f.2 ε ε0
  ⟨i, fun j hj => by
    simp_rw [← RingHom.map_sub, norm_conj]; exact hi j hj⟩

/-- The complex conjugate of a complex Cauchy sequence, as a complex Cauchy sequence. -/
noncomputable def cauSeqConj (f : CauSeq ℂ (‖·‖)) : CauSeq ℂ (‖·‖) :=
  ⟨_, isCauSeq_conj f⟩

theorem lim_conj (f : CauSeq ℂ (‖·‖)) : lim (cauSeqConj f) = conj (lim f) :=
  Complex.ext (by simp [cauSeqConj, (lim_re _).symm, cauSeqRe])
    (by simp [cauSeqConj, (lim_im _).symm, cauSeqIm, (lim_neg _).symm]; rfl)

/-- The norm of a complex Cauchy sequence, as a real Cauchy sequence. -/
noncomputable def cauSeqNorm (f : CauSeq ℂ (‖·‖)) : CauSeq ℝ abs :=
  ⟨_, isCauSeq_norm f.2⟩

theorem lim_norm (f : CauSeq ℂ (‖·‖)) : lim (cauSeqNorm f) = ‖lim f‖ :=
  lim_eq_of_equiv_const fun ε ε0 ↦
    let ⟨i, hi⟩ := equiv_lim f ε ε0
    ⟨i, fun j hj => lt_of_le_of_lt (abs_norm_sub_norm_le _ _) (hi j hj)⟩

@[deprecated (since := "2025-02-16")] alias isCauSeq_abs := isCauSeq_norm
@[deprecated (since := "2025-02-16")] alias cauSeqAbs := cauSeqNorm
@[deprecated (since := "2025-02-16")] alias  lim_abs := lim_norm

lemma ne_zero_of_re_pos {s : ℂ} (hs : 0 < s.re) : s ≠ 0 :=
  fun h ↦ (zero_re ▸ h ▸ hs).false

lemma ne_zero_of_one_lt_re {s : ℂ} (hs : 1 < s.re) : s ≠ 0 :=
  ne_zero_of_re_pos <| zero_lt_one.trans hs

lemma re_neg_ne_zero_of_re_pos {s : ℂ} (hs : 0 < s.re) : (-s).re ≠ 0 :=
  ne_iff_lt_or_gt.mpr <| Or.inl <| neg_re s ▸ (neg_lt_zero.mpr hs)

lemma re_neg_ne_zero_of_one_lt_re {s : ℂ} (hs : 1 < s.re) : (-s).re ≠ 0 :=
  re_neg_ne_zero_of_re_pos <| zero_lt_one.trans hs

end Complex

```

Order.lean:
```
/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.Data.Complex.Norm

/-!
# The partial order on the complex numbers

This order is defined by `z ≤ w ↔ z.re ≤ w.re ∧ z.im = w.im`.

This is a natural order on `ℂ` because, as is well-known, there does not exist an order on `ℂ`
making it into a `LinearOrderedField`. However, the order described above is the canonical order
stemming from the structure of `ℂ` as a ⋆-ring (i.e., it becomes a `StarOrderedRing`). Moreover,
with this order `ℂ` is a `StrictOrderedCommRing` and the coercion `(↑) : ℝ → ℂ` is an order
embedding.

This file only provides `Complex.partialOrder` and lemmas about it. Further structural classes are
provided by `Mathlib/Data/RCLike/Basic.lean` as

* `RCLike.toStrictOrderedCommRing`
* `RCLike.toStarOrderedRing`
* `RCLike.toOrderedSMul`

These are all only available with `open scoped ComplexOrder`.
-/

namespace Complex

/-- We put a partial order on ℂ so that `z ≤ w` exactly if `w - z` is real and nonnegative.
Complex numbers with different imaginary parts are incomparable.
-/
protected def partialOrder : PartialOrder ℂ where
  le z w := z.re ≤ w.re ∧ z.im = w.im
  lt z w := z.re < w.re ∧ z.im = w.im
  lt_iff_le_not_ge z w := by
    rw [lt_iff_le_not_ge]
    tauto
  le_refl _ := ⟨le_rfl, rfl⟩
  le_trans _ _ _ h₁ h₂ := ⟨h₁.1.trans h₂.1, h₁.2.trans h₂.2⟩
  le_antisymm _ _ h₁ h₂ := ext (h₁.1.antisymm h₂.1) h₁.2

namespace _root_.ComplexOrder

scoped[ComplexOrder] attribute [instance] Complex.partialOrder

end _root_.ComplexOrder

open ComplexOrder

theorem le_def {z w : ℂ} : z ≤ w ↔ z.re ≤ w.re ∧ z.im = w.im :=
  Iff.rfl

theorem lt_def {z w : ℂ} : z < w ↔ z.re < w.re ∧ z.im = w.im :=
  Iff.rfl

theorem nonneg_iff {z : ℂ} : 0 ≤ z ↔ 0 ≤ z.re ∧ 0 = z.im :=
  le_def

theorem pos_iff {z : ℂ} : 0 < z ↔ 0 < z.re ∧ 0 = z.im :=
  lt_def

theorem nonpos_iff {z : ℂ} : z ≤ 0 ↔ z.re ≤ 0 ∧ z.im = 0 :=
  le_def

theorem neg_iff {z : ℂ} : z < 0 ↔ z.re < 0 ∧ z.im = 0 :=
  lt_def

@[simp, norm_cast]
theorem real_le_real {x y : ℝ} : (x : ℂ) ≤ (y : ℂ) ↔ x ≤ y := by simp [le_def, ofReal]

@[simp, norm_cast]
theorem real_lt_real {x y : ℝ} : (x : ℂ) < (y : ℂ) ↔ x < y := by simp [lt_def, ofReal]

@[simp, norm_cast]
theorem zero_le_real {x : ℝ} : (0 : ℂ) ≤ (x : ℂ) ↔ 0 ≤ x :=
  real_le_real

@[simp, norm_cast]
theorem zero_lt_real {x : ℝ} : (0 : ℂ) < (x : ℂ) ↔ 0 < x :=
  real_lt_real

theorem not_le_iff {z w : ℂ} : ¬z ≤ w ↔ w.re < z.re ∨ z.im ≠ w.im := by
  rw [le_def, not_and_or, not_le]

theorem not_lt_iff {z w : ℂ} : ¬z < w ↔ w.re ≤ z.re ∨ z.im ≠ w.im := by
  rw [lt_def, not_and_or, not_lt]

theorem not_le_zero_iff {z : ℂ} : ¬z ≤ 0 ↔ 0 < z.re ∨ z.im ≠ 0 :=
  not_le_iff

theorem not_lt_zero_iff {z : ℂ} : ¬z < 0 ↔ 0 ≤ z.re ∨ z.im ≠ 0 :=
  not_lt_iff

theorem eq_re_of_ofReal_le {r : ℝ} {z : ℂ} (hz : (r : ℂ) ≤ z) : z = z.re := by
  rw [eq_comm, ← conj_eq_iff_re, conj_eq_iff_im, ← (Complex.le_def.1 hz).2, Complex.ofReal_im]

@[simp]
lemma re_eq_norm {z : ℂ} : z.re = ‖z‖ ↔ 0 ≤ z :=
  have : 0 ≤ ‖z‖ := norm_nonneg z
  ⟨fun h ↦ ⟨h.symm ▸ this, (abs_re_eq_norm.1 <| h.symm ▸ abs_of_nonneg this).symm⟩,
    fun ⟨h₁, h₂⟩ ↦ by rw [← abs_re_eq_norm.2 h₂.symm, abs_of_nonneg h₁]⟩

@[simp]
lemma neg_re_eq_norm {z : ℂ} : -z.re = ‖z‖ ↔ z ≤ 0 := by
  rw [← neg_re, ← norm_neg z, re_eq_norm]
  exact neg_nonneg.and <| eq_comm.trans neg_eq_zero

@[simp]
lemma re_eq_neg_norm {z : ℂ} : z.re = -‖z‖ ↔ z ≤ 0 := by rw [← neg_eq_iff_eq_neg, neg_re_eq_norm]

@[deprecated (since := "2025-02-16")] alias re_eq_abs := re_eq_norm
@[deprecated (since := "2025-02-16")] alias neg_re_eq_abs := neg_re_eq_norm
@[deprecated (since := "2025-02-16")] alias re_eq_neg_abs := re_eq_neg_norm

lemma monotone_ofReal : Monotone ofReal := by
  intro x y hxy
  simp only [ofRealHom_eq_coe, real_le_real, hxy]

end Complex

namespace Mathlib.Meta.Positivity
open Lean Meta Qq Complex
open scoped ComplexOrder

private alias ⟨_, ofReal_pos⟩ := zero_lt_real
private alias ⟨_, ofReal_nonneg⟩ := zero_le_real
private alias ⟨_, ofReal_ne_zero_of_ne_zero⟩ := ofReal_ne_zero

/-- Extension for the `positivity` tactic: `Complex.ofReal` is positive/nonnegative/nonzero if its
input is. -/
@[positivity Complex.ofReal _, Complex.ofReal _]
def evalComplexOfReal : PositivityExt where eval {u α} _ _ e := do
  -- TODO: Can we avoid duplicating the code?
  match u, α, e with
  | 0, ~q(ℂ), ~q(Complex.ofReal $a) =>
    assumeInstancesCommute
    match ← core q(inferInstance) q(inferInstance) a with
    | .positive pa => return .positive q(ofReal_pos $pa)
    | .nonnegative pa => return .nonnegative q(ofReal_nonneg $pa)
    | .nonzero pa => return .nonzero q(ofReal_ne_zero_of_ne_zero $pa)
    | _ => return .none
  | 0, ~q(ℂ), ~q(Complex.ofReal $a) =>
    assumeInstancesCommute
    match ← core q(inferInstance) q(inferInstance) a with
    | .positive pa => return .positive q(ofReal_pos $pa)
    | .nonnegative pa => return .nonnegative q(ofReal_nonneg $pa)
    | .nonzero pa => return .nonzero q(ofReal_ne_zero_of_ne_zero $pa)
    | _ => return .none
  | _, _ => throwError "not Complex.ofReal"

example (x : ℝ) (hx : 0 < x) : 0 < (x : ℂ) := by positivity
example (x : ℝ) (hx : 0 ≤ x) : 0 ≤ (x : ℂ) := by positivity
example (x : ℝ) (hx : x ≠ 0) : (x : ℂ) ≠ 0 := by positivity

end Mathlib.Meta.Positivity

```

Orientation.lean:
```
/-
Copyright (c) 2021 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
import Mathlib.Data.Complex.Module
import Mathlib.LinearAlgebra.Orientation

/-!
# The standard orientation on `ℂ`.

This had previously been in `LinearAlgebra.Orientation`,
but keeping it separate results in a significant import reduction.
-/


namespace Complex

/-- The standard orientation on `ℂ`. -/
protected noncomputable def orientation : Orientation ℝ ℂ (Fin 2) :=
  Complex.basisOneI.orientation

end Complex

```

Trigonometric.lean:
```
/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Abhimanyu Pallavi Sudhir
-/
import Mathlib.Data.Complex.Exponential

/-!
# Trigonometric and hyperbolic trigonometric functions

This file contains the definitions of the sine, cosine, tangent,
hyperbolic sine, hyperbolic cosine, and hyperbolic tangent functions.

-/

open CauSeq Finset IsAbsoluteValue
open scoped ComplexConjugate

namespace Complex

noncomputable section

/-- The complex sine function, defined via `exp` -/
@[pp_nodot]
def sin (z : ℂ) : ℂ :=
  (exp (-z * I) - exp (z * I)) * I / 2

/-- The complex cosine function, defined via `exp` -/
@[pp_nodot]
def cos (z : ℂ) : ℂ :=
  (exp (z * I) + exp (-z * I)) / 2

/-- The complex tangent function, defined as `sin z / cos z` -/
@[pp_nodot]
def tan (z : ℂ) : ℂ :=
  sin z / cos z

/-- The complex cotangent function, defined as `cos z / sin z` -/
def cot (z : ℂ) : ℂ :=
  cos z / sin z

/-- The complex hyperbolic sine function, defined via `exp` -/
@[pp_nodot]
def sinh (z : ℂ) : ℂ :=
  (exp z - exp (-z)) / 2

/-- The complex hyperbolic cosine function, defined via `exp` -/
@[pp_nodot]
def cosh (z : ℂ) : ℂ :=
  (exp z + exp (-z)) / 2

/-- The complex hyperbolic tangent function, defined as `sinh z / cosh z` -/
@[pp_nodot]
def tanh (z : ℂ) : ℂ :=
  sinh z / cosh z

end

end Complex

namespace Real

open Complex

noncomputable section

/-- The real sine function, defined as the real part of the complex sine -/
@[pp_nodot]
nonrec def sin (x : ℝ) : ℝ :=
  (sin x).re

/-- The real cosine function, defined as the real part of the complex cosine -/
@[pp_nodot]
nonrec def cos (x : ℝ) : ℝ :=
  (cos x).re

/-- The real tangent function, defined as the real part of the complex tangent -/
@[pp_nodot]
nonrec def tan (x : ℝ) : ℝ :=
  (tan x).re

/-- The real cotangent function, defined as the real part of the complex cotangent -/
nonrec def cot (x : ℝ) : ℝ :=
  (cot x).re

/-- The real hypebolic sine function, defined as the real part of the complex hyperbolic sine -/
@[pp_nodot]
nonrec def sinh (x : ℝ) : ℝ :=
  (sinh x).re

/-- The real hypebolic cosine function, defined as the real part of the complex hyperbolic cosine -/
@[pp_nodot]
nonrec def cosh (x : ℝ) : ℝ :=
  (cosh x).re

/-- The real hypebolic tangent function, defined as the real part of
the complex hyperbolic tangent -/
@[pp_nodot]
nonrec def tanh (x : ℝ) : ℝ :=
  (tanh x).re

end

end Real

namespace Complex

variable (x y : ℂ)

theorem two_sinh : 2 * sinh x = exp x - exp (-x) :=
  mul_div_cancel₀ _ two_ne_zero

theorem two_cosh : 2 * cosh x = exp x + exp (-x) :=
  mul_div_cancel₀ _ two_ne_zero

@[simp]
theorem sinh_zero : sinh 0 = 0 := by simp [sinh]

@[simp]
theorem sinh_neg : sinh (-x) = -sinh x := by simp [sinh, exp_neg, (neg_div _ _).symm, add_mul]

private theorem sinh_add_aux {a b c d : ℂ} :
    (a - b) * (c + d) + (a + b) * (c - d) = 2 * (a * c - b * d) := by ring

theorem sinh_add : sinh (x + y) = sinh x * cosh y + cosh x * sinh y := by
  rw [← mul_right_inj' (two_ne_zero' ℂ), two_sinh, exp_add, neg_add, exp_add, eq_comm, mul_add, ←
    mul_assoc, two_sinh, mul_left_comm, two_sinh, ← mul_right_inj' (two_ne_zero' ℂ), mul_add,
    mul_left_comm, two_cosh, ← mul_assoc, two_cosh]
  exact sinh_add_aux

@[simp]
theorem cosh_zero : cosh 0 = 1 := by simp [cosh]

@[simp]
theorem cosh_neg : cosh (-x) = cosh x := by simp [add_comm, cosh, exp_neg]

private theorem cosh_add_aux {a b c d : ℂ} :
    (a + b) * (c + d) + (a - b) * (c - d) = 2 * (a * c + b * d) := by ring

theorem cosh_add : cosh (x + y) = cosh x * cosh y + sinh x * sinh y := by
  rw [← mul_right_inj' (two_ne_zero' ℂ), two_cosh, exp_add, neg_add, exp_add, eq_comm, mul_add, ←
    mul_assoc, two_cosh, ← mul_assoc, two_sinh, ← mul_right_inj' (two_ne_zero' ℂ), mul_add,
    mul_left_comm, two_cosh, mul_left_comm, two_sinh]
  exact cosh_add_aux

theorem sinh_sub : sinh (x - y) = sinh x * cosh y - cosh x * sinh y := by
  simp [sub_eq_add_neg, sinh_add, sinh_neg, cosh_neg]

theorem cosh_sub : cosh (x - y) = cosh x * cosh y - sinh x * sinh y := by
  simp [sub_eq_add_neg, cosh_add, sinh_neg, cosh_neg]

theorem sinh_conj : sinh (conj x) = conj (sinh x) := by
  rw [sinh, ← RingHom.map_neg, exp_conj, exp_conj, ← RingHom.map_sub, sinh, map_div₀, map_ofNat]

@[simp]
theorem ofReal_sinh_ofReal_re (x : ℝ) : ((sinh x).re : ℂ) = sinh x :=
  conj_eq_iff_re.1 <| by rw [← sinh_conj, conj_ofReal]

@[simp, norm_cast]
theorem ofReal_sinh (x : ℝ) : (Real.sinh x : ℂ) = sinh x :=
  ofReal_sinh_ofReal_re _

@[simp]
theorem sinh_ofReal_im (x : ℝ) : (sinh x).im = 0 := by rw [← ofReal_sinh_ofReal_re, ofReal_im]

theorem sinh_ofReal_re (x : ℝ) : (sinh x).re = Real.sinh x :=
  rfl

theorem cosh_conj : cosh (conj x) = conj (cosh x) := by
  rw [cosh, ← RingHom.map_neg, exp_conj, exp_conj, ← RingHom.map_add, cosh, map_div₀, map_ofNat]

theorem ofReal_cosh_ofReal_re (x : ℝ) : ((cosh x).re : ℂ) = cosh x :=
  conj_eq_iff_re.1 <| by rw [← cosh_conj, conj_ofReal]

@[simp, norm_cast]
theorem ofReal_cosh (x : ℝ) : (Real.cosh x : ℂ) = cosh x :=
  ofReal_cosh_ofReal_re _

@[simp]
theorem cosh_ofReal_im (x : ℝ) : (cosh x).im = 0 := by rw [← ofReal_cosh_ofReal_re, ofReal_im]

@[simp]
theorem cosh_ofReal_re (x : ℝ) : (cosh x).re = Real.cosh x :=
  rfl

theorem tanh_eq_sinh_div_cosh : tanh x = sinh x / cosh x :=
  rfl

@[simp]
theorem tanh_zero : tanh 0 = 0 := by simp [tanh]

@[simp]
theorem tanh_neg : tanh (-x) = -tanh x := by simp [tanh, neg_div]

theorem tanh_conj : tanh (conj x) = conj (tanh x) := by
  rw [tanh, sinh_conj, cosh_conj, ← map_div₀, tanh]

@[simp]
theorem ofReal_tanh_ofReal_re (x : ℝ) : ((tanh x).re : ℂ) = tanh x :=
  conj_eq_iff_re.1 <| by rw [← tanh_conj, conj_ofReal]

@[simp, norm_cast]
theorem ofReal_tanh (x : ℝ) : (Real.tanh x : ℂ) = tanh x :=
  ofReal_tanh_ofReal_re _

@[simp]
theorem tanh_ofReal_im (x : ℝ) : (tanh x).im = 0 := by rw [← ofReal_tanh_ofReal_re, ofReal_im]

theorem tanh_ofReal_re (x : ℝ) : (tanh x).re = Real.tanh x :=
  rfl

@[simp]
theorem cosh_add_sinh : cosh x + sinh x = exp x := by
  rw [← mul_right_inj' (two_ne_zero' ℂ), mul_add, two_cosh, two_sinh, add_add_sub_cancel, two_mul]

@[simp]
theorem sinh_add_cosh : sinh x + cosh x = exp x := by rw [add_comm, cosh_add_sinh]

@[simp]
theorem exp_sub_cosh : exp x - cosh x = sinh x :=
  sub_eq_iff_eq_add.2 (sinh_add_cosh x).symm

@[simp]
theorem exp_sub_sinh : exp x - sinh x = cosh x :=
  sub_eq_iff_eq_add.2 (cosh_add_sinh x).symm

@[simp]
theorem cosh_sub_sinh : cosh x - sinh x = exp (-x) := by
  rw [← mul_right_inj' (two_ne_zero' ℂ), mul_sub, two_cosh, two_sinh, add_sub_sub_cancel, two_mul]

@[simp]
theorem sinh_sub_cosh : sinh x - cosh x = -exp (-x) := by rw [← neg_sub, cosh_sub_sinh]

@[simp]
theorem cosh_sq_sub_sinh_sq : cosh x ^ 2 - sinh x ^ 2 = 1 := by
  rw [sq_sub_sq, cosh_add_sinh, cosh_sub_sinh, ← exp_add, add_neg_cancel, exp_zero]

theorem cosh_sq : cosh x ^ 2 = sinh x ^ 2 + 1 := by
  rw [← cosh_sq_sub_sinh_sq x]
  ring

theorem sinh_sq : sinh x ^ 2 = cosh x ^ 2 - 1 := by
  rw [← cosh_sq_sub_sinh_sq x]
  ring

theorem cosh_two_mul : cosh (2 * x) = cosh x ^ 2 + sinh x ^ 2 := by rw [two_mul, cosh_add, sq, sq]

theorem sinh_two_mul : sinh (2 * x) = 2 * sinh x * cosh x := by
  rw [two_mul, sinh_add]
  ring

theorem cosh_three_mul : cosh (3 * x) = 4 * cosh x ^ 3 - 3 * cosh x := by
  have h1 : x + 2 * x = 3 * x := by ring
  rw [← h1, cosh_add x (2 * x)]
  simp only [cosh_two_mul, sinh_two_mul]
  have h2 : sinh x * (2 * sinh x * cosh x) = 2 * cosh x * sinh x ^ 2 := by ring
  rw [h2, sinh_sq]
  ring

theorem sinh_three_mul : sinh (3 * x) = 4 * sinh x ^ 3 + 3 * sinh x := by
  have h1 : x + 2 * x = 3 * x := by ring
  rw [← h1, sinh_add x (2 * x)]
  simp only [cosh_two_mul, sinh_two_mul]
  have h2 : cosh x * (2 * sinh x * cosh x) = 2 * sinh x * cosh x ^ 2 := by ring
  rw [h2, cosh_sq]
  ring

@[simp]
theorem sin_zero : sin 0 = 0 := by simp [sin]

@[simp]
theorem sin_neg : sin (-x) = -sin x := by
  simp [sin, sub_eq_add_neg, exp_neg, (neg_div _ _).symm, add_mul]

theorem two_sin : 2 * sin x = (exp (-x * I) - exp (x * I)) * I :=
  mul_div_cancel₀ _ two_ne_zero

theorem two_cos : 2 * cos x = exp (x * I) + exp (-x * I) :=
  mul_div_cancel₀ _ two_ne_zero

theorem sinh_mul_I : sinh (x * I) = sin x * I := by
  rw [← mul_right_inj' (two_ne_zero' ℂ), two_sinh, ← mul_assoc, two_sin, mul_assoc, I_mul_I,
    mul_neg_one, neg_sub, neg_mul_eq_neg_mul]

theorem cosh_mul_I : cosh (x * I) = cos x := by
  rw [← mul_right_inj' (two_ne_zero' ℂ), two_cosh, two_cos, neg_mul_eq_neg_mul]

theorem tanh_mul_I : tanh (x * I) = tan x * I := by
  rw [tanh_eq_sinh_div_cosh, cosh_mul_I, sinh_mul_I, mul_div_right_comm, tan]

theorem cos_mul_I : cos (x * I) = cosh x := by rw [← cosh_mul_I]; ring_nf; simp

theorem sin_mul_I : sin (x * I) = sinh x * I := by
  have h : I * sin (x * I) = -sinh x := by
    rw [mul_comm, ← sinh_mul_I]
    ring_nf
    simp
  rw [← neg_neg (sinh x), ← h]
  apply Complex.ext <;> simp

theorem tan_mul_I : tan (x * I) = tanh x * I := by
  rw [tan, sin_mul_I, cos_mul_I, mul_div_right_comm, tanh_eq_sinh_div_cosh]

theorem sin_add : sin (x + y) = sin x * cos y + cos x * sin y := by
  rw [← mul_left_inj' I_ne_zero, ← sinh_mul_I, add_mul, add_mul, mul_right_comm, ← sinh_mul_I,
    mul_assoc, ← sinh_mul_I, ← cosh_mul_I, ← cosh_mul_I, sinh_add]

@[simp]
theorem cos_zero : cos 0 = 1 := by simp [cos]

@[simp]
theorem cos_neg : cos (-x) = cos x := by simp [cos, sub_eq_add_neg, exp_neg, add_comm]

theorem cos_add : cos (x + y) = cos x * cos y - sin x * sin y := by
  rw [← cosh_mul_I, add_mul, cosh_add, cosh_mul_I, cosh_mul_I, sinh_mul_I, sinh_mul_I,
    mul_mul_mul_comm, I_mul_I, mul_neg_one, sub_eq_add_neg]

theorem sin_sub : sin (x - y) = sin x * cos y - cos x * sin y := by
  simp [sub_eq_add_neg, sin_add, sin_neg, cos_neg]

theorem cos_sub : cos (x - y) = cos x * cos y + sin x * sin y := by
  simp [sub_eq_add_neg, cos_add, sin_neg, cos_neg]

theorem sin_add_mul_I (x y : ℂ) : sin (x + y * I) = sin x * cosh y + cos x * sinh y * I := by
  rw [sin_add, cos_mul_I, sin_mul_I, mul_assoc]

theorem sin_eq (z : ℂ) : sin z = sin z.re * cosh z.im + cos z.re * sinh z.im * I := by
  convert sin_add_mul_I z.re z.im; exact (re_add_im z).symm

theorem cos_add_mul_I (x y : ℂ) : cos (x + y * I) = cos x * cosh y - sin x * sinh y * I := by
  rw [cos_add, cos_mul_I, sin_mul_I, mul_assoc]

theorem cos_eq (z : ℂ) : cos z = cos z.re * cosh z.im - sin z.re * sinh z.im * I := by
  convert cos_add_mul_I z.re z.im; exact (re_add_im z).symm

theorem sin_sub_sin : sin x - sin y = 2 * sin ((x - y) / 2) * cos ((x + y) / 2) := by
  have s1 := sin_add ((x + y) / 2) ((x - y) / 2)
  have s2 := sin_sub ((x + y) / 2) ((x - y) / 2)
  rw [div_add_div_same, add_sub, add_right_comm, add_sub_cancel_right, add_self_div_two] at s1
  rw [div_sub_div_same, ← sub_add, add_sub_cancel_left, add_self_div_two] at s2
  rw [s1, s2]
  ring

theorem cos_sub_cos : cos x - cos y = -2 * sin ((x + y) / 2) * sin ((x - y) / 2) := by
  have s1 := cos_add ((x + y) / 2) ((x - y) / 2)
  have s2 := cos_sub ((x + y) / 2) ((x - y) / 2)
  rw [div_add_div_same, add_sub, add_right_comm, add_sub_cancel_right, add_self_div_two] at s1
  rw [div_sub_div_same, ← sub_add, add_sub_cancel_left, add_self_div_two] at s2
  rw [s1, s2]
  ring

theorem sin_add_sin : sin x + sin y = 2 * sin ((x + y) / 2) * cos ((x - y) / 2) := by
  simpa using sin_sub_sin x (-y)

theorem cos_add_cos : cos x + cos y = 2 * cos ((x + y) / 2) * cos ((x - y) / 2) := by
  calc
    cos x + cos y = cos ((x + y) / 2 + (x - y) / 2) + cos ((x + y) / 2 - (x - y) / 2) := ?_
    _ =
        cos ((x + y) / 2) * cos ((x - y) / 2) - sin ((x + y) / 2) * sin ((x - y) / 2) +
          (cos ((x + y) / 2) * cos ((x - y) / 2) + sin ((x + y) / 2) * sin ((x - y) / 2)) :=
      ?_
    _ = 2 * cos ((x + y) / 2) * cos ((x - y) / 2) := ?_
  · congr <;> field_simp
  · rw [cos_add, cos_sub]
  ring

theorem sin_conj : sin (conj x) = conj (sin x) := by
  rw [← mul_left_inj' I_ne_zero, ← sinh_mul_I, ← conj_neg_I, ← RingHom.map_mul, ← RingHom.map_mul,
    sinh_conj, mul_neg, sinh_neg, sinh_mul_I, mul_neg]

@[simp]
theorem ofReal_sin_ofReal_re (x : ℝ) : ((sin x).re : ℂ) = sin x :=
  conj_eq_iff_re.1 <| by rw [← sin_conj, conj_ofReal]

@[simp, norm_cast]
theorem ofReal_sin (x : ℝ) : (Real.sin x : ℂ) = sin x :=
  ofReal_sin_ofReal_re _

@[simp]
theorem sin_ofReal_im (x : ℝ) : (sin x).im = 0 := by rw [← ofReal_sin_ofReal_re, ofReal_im]

theorem sin_ofReal_re (x : ℝ) : (sin x).re = Real.sin x :=
  rfl

theorem cos_conj : cos (conj x) = conj (cos x) := by
  rw [← cosh_mul_I, ← conj_neg_I, ← RingHom.map_mul, ← cosh_mul_I, cosh_conj, mul_neg, cosh_neg]

@[simp]
theorem ofReal_cos_ofReal_re (x : ℝ) : ((cos x).re : ℂ) = cos x :=
  conj_eq_iff_re.1 <| by rw [← cos_conj, conj_ofReal]

@[simp, norm_cast]
theorem ofReal_cos (x : ℝ) : (Real.cos x : ℂ) = cos x :=
  ofReal_cos_ofReal_re _

@[simp]
theorem cos_ofReal_im (x : ℝ) : (cos x).im = 0 := by rw [← ofReal_cos_ofReal_re, ofReal_im]

theorem cos_ofReal_re (x : ℝ) : (cos x).re = Real.cos x :=
  rfl

@[simp]
theorem tan_zero : tan 0 = 0 := by simp [tan]

theorem tan_eq_sin_div_cos : tan x = sin x / cos x :=
  rfl

theorem cot_eq_cos_div_sin : cot x = cos x / sin x :=
  rfl

theorem tan_mul_cos {x : ℂ} (hx : cos x ≠ 0) : tan x * cos x = sin x := by
  rw [tan_eq_sin_div_cos, div_mul_cancel₀ _ hx]

@[simp]
theorem tan_neg : tan (-x) = -tan x := by simp [tan, neg_div]

theorem tan_conj : tan (conj x) = conj (tan x) := by rw [tan, sin_conj, cos_conj, ← map_div₀, tan]

theorem cot_conj : cot (conj x) = conj (cot x) := by rw [cot, sin_conj, cos_conj, ← map_div₀, cot]

@[simp]
theorem ofReal_tan_ofReal_re (x : ℝ) : ((tan x).re : ℂ) = tan x :=
  conj_eq_iff_re.1 <| by rw [← tan_conj, conj_ofReal]

@[simp]
theorem ofReal_cot_ofReal_re (x : ℝ) : ((cot x).re : ℂ) = cot x :=
  conj_eq_iff_re.1 <| by rw [← cot_conj, conj_ofReal]

@[simp, norm_cast]
theorem ofReal_tan (x : ℝ) : (Real.tan x : ℂ) = tan x :=
  ofReal_tan_ofReal_re _

@[simp, norm_cast]
theorem ofReal_cot (x : ℝ) : (Real.cot x : ℂ) = cot x :=
  ofReal_cot_ofReal_re _

@[simp]
theorem tan_ofReal_im (x : ℝ) : (tan x).im = 0 := by rw [← ofReal_tan_ofReal_re, ofReal_im]

theorem tan_ofReal_re (x : ℝ) : (tan x).re = Real.tan x :=
  rfl

theorem cos_add_sin_I : cos x + sin x * I = exp (x * I) := by
  rw [← cosh_add_sinh, sinh_mul_I, cosh_mul_I]

theorem cos_sub_sin_I : cos x - sin x * I = exp (-x * I) := by
  rw [neg_mul, ← cosh_sub_sinh, sinh_mul_I, cosh_mul_I]

@[simp]
theorem sin_sq_add_cos_sq : sin x ^ 2 + cos x ^ 2 = 1 :=
  Eq.trans (by rw [cosh_mul_I, sinh_mul_I, mul_pow, I_sq, mul_neg_one, sub_neg_eq_add, add_comm])
    (cosh_sq_sub_sinh_sq (x * I))

@[simp]
theorem cos_sq_add_sin_sq : cos x ^ 2 + sin x ^ 2 = 1 := by rw [add_comm, sin_sq_add_cos_sq]

theorem cos_two_mul' : cos (2 * x) = cos x ^ 2 - sin x ^ 2 := by rw [two_mul, cos_add, ← sq, ← sq]

theorem cos_two_mul : cos (2 * x) = 2 * cos x ^ 2 - 1 := by
  rw [cos_two_mul', eq_sub_iff_add_eq.2 (sin_sq_add_cos_sq x), ← sub_add, sub_add_eq_add_sub,
    two_mul]

theorem sin_two_mul : sin (2 * x) = 2 * sin x * cos x := by
  rw [two_mul, sin_add, two_mul, add_mul, mul_comm]

theorem cos_sq : cos x ^ 2 = 1 / 2 + cos (2 * x) / 2 := by
  simp [cos_two_mul, div_add_div_same, mul_div_cancel_left₀, two_ne_zero, -one_div]

theorem cos_sq' : cos x ^ 2 = 1 - sin x ^ 2 := by rw [← sin_sq_add_cos_sq x, add_sub_cancel_left]

theorem sin_sq : sin x ^ 2 = 1 - cos x ^ 2 := by rw [← sin_sq_add_cos_sq x, add_sub_cancel_right]

theorem inv_one_add_tan_sq {x : ℂ} (hx : cos x ≠ 0) : (1 + tan x ^ 2)⁻¹ = cos x ^ 2 := by
  rw [tan_eq_sin_div_cos, div_pow]
  field_simp

theorem tan_sq_div_one_add_tan_sq {x : ℂ} (hx : cos x ≠ 0) :
    tan x ^ 2 / (1 + tan x ^ 2) = sin x ^ 2 := by
  simp only [← tan_mul_cos hx, mul_pow, ← inv_one_add_tan_sq hx, div_eq_mul_inv, one_mul]

theorem cos_three_mul : cos (3 * x) = 4 * cos x ^ 3 - 3 * cos x := by
  have h1 : x + 2 * x = 3 * x := by ring
  rw [← h1, cos_add x (2 * x)]
  simp only [cos_two_mul, sin_two_mul, mul_add, mul_sub, mul_one, sq]
  have h2 : 4 * cos x ^ 3 = 2 * cos x * cos x * cos x + 2 * cos x * cos x ^ 2 := by ring
  rw [h2, cos_sq']
  ring

theorem sin_three_mul : sin (3 * x) = 3 * sin x - 4 * sin x ^ 3 := by
  have h1 : x + 2 * x = 3 * x := by ring
  rw [← h1, sin_add x (2 * x)]
  simp only [cos_two_mul, sin_two_mul, cos_sq']
  have h2 : cos x * (2 * sin x * cos x) = 2 * sin x * cos x ^ 2 := by ring
  rw [h2, cos_sq']
  ring

theorem exp_mul_I : exp (x * I) = cos x + sin x * I :=
  (cos_add_sin_I _).symm

theorem exp_add_mul_I : exp (x + y * I) = exp x * (cos y + sin y * I) := by rw [exp_add, exp_mul_I]

theorem exp_eq_exp_re_mul_sin_add_cos : exp x = exp x.re * (cos x.im + sin x.im * I) := by
  rw [← exp_add_mul_I, re_add_im]

theorem exp_re : (exp x).re = Real.exp x.re * Real.cos x.im := by
  rw [exp_eq_exp_re_mul_sin_add_cos]
  simp [exp_ofReal_re, cos_ofReal_re]

theorem exp_im : (exp x).im = Real.exp x.re * Real.sin x.im := by
  rw [exp_eq_exp_re_mul_sin_add_cos]
  simp [exp_ofReal_re, sin_ofReal_re]

@[simp]
theorem exp_ofReal_mul_I_re (x : ℝ) : (exp (x * I)).re = Real.cos x := by
  simp [exp_mul_I, cos_ofReal_re]

@[simp]
theorem exp_ofReal_mul_I_im (x : ℝ) : (exp (x * I)).im = Real.sin x := by
  simp [exp_mul_I, sin_ofReal_re]

/-- **De Moivre's formula** -/
theorem cos_add_sin_mul_I_pow (n : ℕ) (z : ℂ) :
    (cos z + sin z * I) ^ n = cos (↑n * z) + sin (↑n * z) * I := by
  rw [← exp_mul_I, ← exp_mul_I, ← exp_nat_mul, mul_assoc]

end Complex

namespace Real

open Complex

variable (x y : ℝ)

@[simp]
theorem sin_zero : sin 0 = 0 := by simp [sin]

@[simp]
theorem sin_neg : sin (-x) = -sin x := by simp [sin, exp_neg, (neg_div _ _).symm, add_mul]

nonrec theorem sin_add : sin (x + y) = sin x * cos y + cos x * sin y :=
  ofReal_injective <| by simp [sin_add]

@[simp]
theorem cos_zero : cos 0 = 1 := by simp [cos]

@[simp]
theorem cos_neg : cos (-x) = cos x := by simp [cos, exp_neg]

@[simp]
theorem cos_abs : cos |x| = cos x := by
  cases le_total x 0 <;> simp only [*, abs_of_nonneg, abs_of_nonpos, cos_neg]

nonrec theorem cos_add : cos (x + y) = cos x * cos y - sin x * sin y :=
  ofReal_injective <| by simp [cos_add]

theorem sin_sub : sin (x - y) = sin x * cos y - cos x * sin y := by
  simp [sub_eq_add_neg, sin_add, sin_neg, cos_neg]

theorem cos_sub : cos (x - y) = cos x * cos y + sin x * sin y := by
  simp [sub_eq_add_neg, cos_add, sin_neg, cos_neg]

nonrec theorem sin_sub_sin : sin x - sin y = 2 * sin ((x - y) / 2) * cos ((x + y) / 2) :=
  ofReal_injective <| by simp [sin_sub_sin]

nonrec theorem cos_sub_cos : cos x - cos y = -2 * sin ((x + y) / 2) * sin ((x - y) / 2) :=
  ofReal_injective <| by simp [cos_sub_cos]

nonrec theorem cos_add_cos : cos x + cos y = 2 * cos ((x + y) / 2) * cos ((x - y) / 2) :=
  ofReal_injective <| by simp [cos_add_cos]

theorem two_mul_sin_mul_sin (x y : ℝ) : 2 * sin x * sin y = cos (x - y) - cos (x + y) := by
  simp [cos_add, cos_sub]
  ring

theorem two_mul_cos_mul_cos (x y : ℝ) : 2 * cos x * cos y = cos (x - y) + cos (x + y) := by
  simp [cos_add, cos_sub]
  ring

theorem two_mul_sin_mul_cos (x y : ℝ) : 2 * sin x * cos y = sin (x - y) + sin (x + y) := by
  simp [sin_add, sin_sub]
  ring

nonrec theorem tan_eq_sin_div_cos : tan x = sin x / cos x :=
  ofReal_injective <| by simp only [ofReal_tan, tan_eq_sin_div_cos, ofReal_div, ofReal_sin,
    ofReal_cos]

nonrec theorem cot_eq_cos_div_sin : cot x = cos x / sin x :=
  ofReal_injective <| by simp [cot_eq_cos_div_sin]

theorem tan_mul_cos {x : ℝ} (hx : cos x ≠ 0) : tan x * cos x = sin x := by
  rw [tan_eq_sin_div_cos, div_mul_cancel₀ _ hx]

@[simp]
theorem tan_zero : tan 0 = 0 := by simp [tan]

@[simp]
theorem tan_neg : tan (-x) = -tan x := by simp [tan, neg_div]

@[simp]
nonrec theorem sin_sq_add_cos_sq : sin x ^ 2 + cos x ^ 2 = 1 :=
  ofReal_injective (by simp [sin_sq_add_cos_sq])

@[simp]
theorem cos_sq_add_sin_sq : cos x ^ 2 + sin x ^ 2 = 1 := by rw [add_comm, sin_sq_add_cos_sq]

theorem sin_sq_le_one : sin x ^ 2 ≤ 1 := by
  rw [← sin_sq_add_cos_sq x]; exact le_add_of_nonneg_right (sq_nonneg _)

theorem cos_sq_le_one : cos x ^ 2 ≤ 1 := by
  rw [← sin_sq_add_cos_sq x]; exact le_add_of_nonneg_left (sq_nonneg _)

theorem abs_sin_le_one : |sin x| ≤ 1 :=
  abs_le_one_iff_mul_self_le_one.2 <| by simp only [← sq, sin_sq_le_one]

theorem abs_cos_le_one : |cos x| ≤ 1 :=
  abs_le_one_iff_mul_self_le_one.2 <| by simp only [← sq, cos_sq_le_one]

theorem sin_le_one : sin x ≤ 1 :=
  (abs_le.1 (abs_sin_le_one _)).2

theorem cos_le_one : cos x ≤ 1 :=
  (abs_le.1 (abs_cos_le_one _)).2

theorem neg_one_le_sin : -1 ≤ sin x :=
  (abs_le.1 (abs_sin_le_one _)).1

theorem neg_one_le_cos : -1 ≤ cos x :=
  (abs_le.1 (abs_cos_le_one _)).1

nonrec theorem cos_two_mul : cos (2 * x) = 2 * cos x ^ 2 - 1 :=
  ofReal_injective <| by simp [cos_two_mul]

nonrec theorem cos_two_mul' : cos (2 * x) = cos x ^ 2 - sin x ^ 2 :=
  ofReal_injective <| by simp [cos_two_mul']

nonrec theorem sin_two_mul : sin (2 * x) = 2 * sin x * cos x :=
  ofReal_injective <| by simp [sin_two_mul]

nonrec theorem cos_sq : cos x ^ 2 = 1 / 2 + cos (2 * x) / 2 :=
  ofReal_injective <| by simp [cos_sq]

theorem cos_sq' : cos x ^ 2 = 1 - sin x ^ 2 := by rw [← sin_sq_add_cos_sq x, add_sub_cancel_left]

theorem sin_sq : sin x ^ 2 = 1 - cos x ^ 2 :=
  eq_sub_iff_add_eq.2 <| sin_sq_add_cos_sq _

lemma sin_sq_eq_half_sub : sin x ^ 2 = 1 / 2 - cos (2 * x) / 2 := by
  rw [sin_sq, cos_sq, ← sub_sub, sub_half]

theorem abs_sin_eq_sqrt_one_sub_cos_sq (x : ℝ) : |sin x| = √(1 - cos x ^ 2) := by
  rw [← sin_sq, sqrt_sq_eq_abs]

theorem abs_cos_eq_sqrt_one_sub_sin_sq (x : ℝ) : |cos x| = √(1 - sin x ^ 2) := by
  rw [← cos_sq', sqrt_sq_eq_abs]

theorem inv_one_add_tan_sq {x : ℝ} (hx : cos x ≠ 0) : (1 + tan x ^ 2)⁻¹ = cos x ^ 2 :=
  have : Complex.cos x ≠ 0 := mt (congr_arg re) hx
  ofReal_inj.1 <| by simpa using Complex.inv_one_add_tan_sq this

theorem tan_sq_div_one_add_tan_sq {x : ℝ} (hx : cos x ≠ 0) :
    tan x ^ 2 / (1 + tan x ^ 2) = sin x ^ 2 := by
  simp only [← tan_mul_cos hx, mul_pow, ← inv_one_add_tan_sq hx, div_eq_mul_inv, one_mul]

theorem inv_sqrt_one_add_tan_sq {x : ℝ} (hx : 0 < cos x) : (√(1 + tan x ^ 2))⁻¹ = cos x := by
  rw [← sqrt_sq hx.le, ← sqrt_inv, inv_one_add_tan_sq hx.ne']

theorem tan_div_sqrt_one_add_tan_sq {x : ℝ} (hx : 0 < cos x) :
    tan x / √(1 + tan x ^ 2) = sin x := by
  rw [← tan_mul_cos hx.ne', ← inv_sqrt_one_add_tan_sq hx, div_eq_mul_inv]

nonrec theorem cos_three_mul : cos (3 * x) = 4 * cos x ^ 3 - 3 * cos x := by
  rw [← ofReal_inj]; simp [cos_three_mul]

nonrec theorem sin_three_mul : sin (3 * x) = 3 * sin x - 4 * sin x ^ 3 := by
  rw [← ofReal_inj]; simp [sin_three_mul]

/-- The definition of `sinh` in terms of `exp`. -/
nonrec theorem sinh_eq (x : ℝ) : sinh x = (exp x - exp (-x)) / 2 :=
  ofReal_injective <| by simp [Complex.sinh]

@[simp]
theorem sinh_zero : sinh 0 = 0 := by simp [sinh]

@[simp]
theorem sinh_neg : sinh (-x) = -sinh x := by simp [sinh, exp_neg, (neg_div _ _).symm, add_mul]

nonrec theorem sinh_add : sinh (x + y) = sinh x * cosh y + cosh x * sinh y := by
  rw [← ofReal_inj]; simp [sinh_add]

/-- The definition of `cosh` in terms of `exp`. -/
theorem cosh_eq (x : ℝ) : cosh x = (exp x + exp (-x)) / 2 :=
  eq_div_of_mul_eq two_ne_zero <| by
    rw [cosh, exp, exp, Complex.ofReal_neg, Complex.cosh, mul_two, ← Complex.add_re, ← mul_two,
      div_mul_cancel₀ _ (two_ne_zero' ℂ), Complex.add_re]

@[simp]
theorem cosh_zero : cosh 0 = 1 := by simp [cosh]

@[simp]
theorem cosh_neg : cosh (-x) = cosh x :=
  ofReal_inj.1 <| by simp

@[simp]
theorem cosh_abs : cosh |x| = cosh x := by
  cases le_total x 0 <;> simp [*, abs_of_nonneg, abs_of_nonpos]

nonrec theorem cosh_add : cosh (x + y) = cosh x * cosh y + sinh x * sinh y := by
  rw [← ofReal_inj]; simp [cosh_add]

theorem sinh_sub : sinh (x - y) = sinh x * cosh y - cosh x * sinh y := by
  simp [sub_eq_add_neg, sinh_add, sinh_neg, cosh_neg]

theorem cosh_sub : cosh (x - y) = cosh x * cosh y - sinh x * sinh y := by
  simp [sub_eq_add_neg, cosh_add, sinh_neg, cosh_neg]

nonrec theorem tanh_eq_sinh_div_cosh : tanh x = sinh x / cosh x :=
  ofReal_inj.1 <| by simp [tanh_eq_sinh_div_cosh]

@[simp]
theorem tanh_zero : tanh 0 = 0 := by simp [tanh]

@[simp]
theorem tanh_neg : tanh (-x) = -tanh x := by simp [tanh, neg_div]

@[simp]
theorem cosh_add_sinh : cosh x + sinh x = exp x := by rw [← ofReal_inj]; simp

@[simp]
theorem sinh_add_cosh : sinh x + cosh x = exp x := by rw [add_comm, cosh_add_sinh]

@[simp]
theorem exp_sub_cosh : exp x - cosh x = sinh x :=
  sub_eq_iff_eq_add.2 (sinh_add_cosh x).symm

@[simp]
theorem exp_sub_sinh : exp x - sinh x = cosh x :=
  sub_eq_iff_eq_add.2 (cosh_add_sinh x).symm

@[simp]
theorem cosh_sub_sinh : cosh x - sinh x = exp (-x) := by
  rw [← ofReal_inj]
  simp

@[simp]
theorem sinh_sub_cosh : sinh x - cosh x = -exp (-x) := by rw [← neg_sub, cosh_sub_sinh]

@[simp]
theorem cosh_sq_sub_sinh_sq (x : ℝ) : cosh x ^ 2 - sinh x ^ 2 = 1 := by rw [← ofReal_inj]; simp

nonrec theorem cosh_sq : cosh x ^ 2 = sinh x ^ 2 + 1 := by rw [← ofReal_inj]; simp [cosh_sq]

theorem cosh_sq' : cosh x ^ 2 = 1 + sinh x ^ 2 :=
  (cosh_sq x).trans (add_comm _ _)

nonrec theorem sinh_sq : sinh x ^ 2 = cosh x ^ 2 - 1 := by rw [← ofReal_inj]; simp [sinh_sq]

nonrec theorem cosh_two_mul : cosh (2 * x) = cosh x ^ 2 + sinh x ^ 2 := by
  rw [← ofReal_inj]; simp [cosh_two_mul]

nonrec theorem sinh_two_mul : sinh (2 * x) = 2 * sinh x * cosh x := by
  rw [← ofReal_inj]; simp [sinh_two_mul]

nonrec theorem cosh_three_mul : cosh (3 * x) = 4 * cosh x ^ 3 - 3 * cosh x := by
  rw [← ofReal_inj]; simp [cosh_three_mul]

nonrec theorem sinh_three_mul : sinh (3 * x) = 4 * sinh x ^ 3 + 3 * sinh x := by
  rw [← ofReal_inj]; simp [sinh_three_mul]

open IsAbsoluteValue Nat

private theorem add_one_lt_exp_of_pos {x : ℝ} (hx : 0 < x) : x + 1 < exp x :=
  (by nlinarith : x + 1 < 1 + x + x ^ 2 / 2).trans_le (quadratic_le_exp_of_nonneg hx.le)

private theorem add_one_le_exp_of_nonneg {x : ℝ} (hx : 0 ≤ x) : x + 1 ≤ exp x := by
  rcases eq_or_lt_of_le hx with (rfl | h)
  · simp
  exact (add_one_lt_exp_of_pos h).le

/-- `Real.cosh` is always positive -/
theorem cosh_pos (x : ℝ) : 0 < Real.cosh x :=
  (cosh_eq x).symm ▸ half_pos (add_pos (exp_pos x) (exp_pos (-x)))

theorem sinh_lt_cosh : sinh x < cosh x :=
  lt_of_pow_lt_pow_left₀ 2 (cosh_pos _).le <| (cosh_sq x).symm ▸ lt_add_one _

end Real

namespace Real

open Complex Finset

theorem cos_bound {x : ℝ} (hx : |x| ≤ 1) : |cos x - (1 - x ^ 2 / 2)| ≤ |x| ^ 4 * (5 / 96) :=
  calc
    |cos x - (1 - x ^ 2 / 2)| = ‖Complex.cos x - (1 - (x : ℂ) ^ 2 / 2)‖ := by
      rw [← Real.norm_eq_abs, ← norm_real]; simp
    _ = ‖(Complex.exp (x * I) + Complex.exp (-x * I) - (2 - (x : ℂ) ^ 2)) / 2‖ := by
      simp [Complex.cos, sub_div, add_div, neg_div, div_self (two_ne_zero' ℂ)]
    _ = ‖((Complex.exp (x * I) - ∑ m ∈ range 4, (x * I) ^ m / m.factorial) +
              (Complex.exp (-x * I) - ∑ m ∈ range 4, (-x * I) ^ m / m.factorial)) / 2‖ :=
      (congr_arg (‖·‖ : ℂ → ℝ)
        (congr_arg (fun x : ℂ => x / 2) (by
          simp only [neg_mul, pow_succ, pow_zero, sum_range_succ, range_zero, sum_empty,
          Nat.factorial, Nat.cast_succ, zero_add, mul_one, Nat.mul_one, mul_neg, neg_neg]
          apply Complex.ext <;> simp [div_eq_mul_inv, normSq] <;> ring_nf)))
    _ ≤ ‖(Complex.exp (x * I) - ∑ m ∈ range 4, (x * I) ^ m / m.factorial) / 2‖ +
          ‖(Complex.exp (-x * I) - ∑ m ∈ range 4, (-x * I) ^ m / m.factorial) / 2‖ := by
      rw [add_div]; exact norm_add_le _ _
    _ = ‖Complex.exp (x * I) - ∑ m ∈ range 4, (x * I) ^ m / m.factorial‖ / 2 +
          ‖Complex.exp (-x * I) - ∑ m ∈ range 4, (-x * I) ^ m / m.factorial‖ / 2 := by
      simp [map_div₀]
    _ ≤ ‖x * I‖ ^ 4 * (Nat.succ 4 * ((Nat.factorial 4) * (4 : ℕ) : ℝ)⁻¹) / 2 +
          ‖-x * I‖ ^ 4 * (Nat.succ 4 * ((Nat.factorial 4) * (4 : ℕ) : ℝ)⁻¹) / 2 := by
      gcongr
      · exact Complex.exp_bound (by simpa) (by decide)
      · exact Complex.exp_bound (by simpa) (by decide)
    _ ≤ |x| ^ 4 * (5 / 96) := by norm_num [Nat.factorial]

theorem sin_bound {x : ℝ} (hx : |x| ≤ 1) : |sin x - (x - x ^ 3 / 6)| ≤ |x| ^ 4 * (5 / 96) :=
  calc
    |sin x - (x - x ^ 3 / 6)| = ‖Complex.sin x - (x - x ^ 3 / 6 : ℝ)‖ := by
      rw [← Real.norm_eq_abs, ← norm_real]; simp
    _ = ‖((Complex.exp (-x * I) - Complex.exp (x * I)) * I -
          (2 * x - x ^ 3 / 3 : ℝ)) / 2‖ := by
      simp [Complex.sin, sub_div, add_div, neg_div, mul_div_cancel_left₀ _ (two_ne_zero' ℂ),
        div_div, show (3 : ℂ) * 2 = 6 by norm_num]
    _ = ‖((Complex.exp (-x * I) - ∑ m ∈ range 4, (-x * I) ^ m / m.factorial) -
                (Complex.exp (x * I) - ∑ m ∈ range 4, (x * I) ^ m / m.factorial)) * I / 2‖ :=
      (congr_arg (‖·‖ : ℂ → ℝ)
        (congr_arg (fun x : ℂ => x / 2)
          (by
            simp only [neg_mul, pow_succ, pow_zero, ofReal_sub, ofReal_mul, ofReal_ofNat,
              ofReal_div, sum_range_succ, range_zero, sum_empty, Nat.factorial, Nat.cast_succ,
              zero_add, mul_neg, mul_one, neg_neg, Nat.mul_one]
            apply Complex.ext <;> simp [div_eq_mul_inv, normSq]; ring)))
    _ ≤ ‖(Complex.exp (-x * I) - ∑ m ∈ range 4, (-x * I) ^ m / m.factorial) * I / 2‖ +
          ‖-((Complex.exp (x * I) - ∑ m ∈ range 4, (x * I) ^ m / m.factorial) * I) / 2‖ := by
      rw [sub_mul, sub_eq_add_neg, add_div]; exact norm_add_le _ _
    _ = ‖Complex.exp (x * I) - ∑ m ∈ range 4, (x * I) ^ m / m.factorial‖ / 2 +
          ‖Complex.exp (-x * I) - ∑ m ∈ range 4, (-x * I) ^ m / m.factorial‖ / 2 := by
      simp [add_comm, map_div₀]
    _ ≤ ‖x * I‖ ^ 4 * (Nat.succ 4 * (Nat.factorial 4 * (4 : ℕ) : ℝ)⁻¹) / 2 +
          ‖-x * I‖ ^ 4 * (Nat.succ 4 * (Nat.factorial 4 * (4 : ℕ) : ℝ)⁻¹) / 2 := by
      gcongr
      · exact Complex.exp_bound (by simpa) (by decide)
      · exact Complex.exp_bound (by simpa) (by decide)
    _ ≤ |x| ^ 4 * (5 / 96) := by norm_num [Nat.factorial]

theorem cos_pos_of_le_one {x : ℝ} (hx : |x| ≤ 1) : 0 < cos x :=
  calc 0 < 1 - x ^ 2 / 2 - |x| ^ 4 * (5 / 96) :=
      sub_pos.2 <|
        lt_sub_iff_add_lt.2
          (calc
            |x| ^ 4 * (5 / 96) + x ^ 2 / 2 ≤ 1 * (5 / 96) + 1 / 2 := by
                  gcongr
                  · exact pow_le_one₀ (abs_nonneg _) hx
                  · rw [sq, ← abs_mul_self, abs_mul]
                    exact mul_le_one₀ hx (abs_nonneg _) hx
            _ < 1 := by norm_num)
    _ ≤ cos x := sub_le_comm.1 (abs_sub_le_iff.1 (cos_bound hx)).2

theorem sin_pos_of_pos_of_le_one {x : ℝ} (hx0 : 0 < x) (hx : x ≤ 1) : 0 < sin x :=
  calc 0 < x - x ^ 3 / 6 - |x| ^ 4 * (5 / 96) :=
      sub_pos.2 <| lt_sub_iff_add_lt.2
          (calc
            |x| ^ 4 * (5 / 96) + x ^ 3 / 6 ≤ x * (5 / 96) + x / 6 := by
                gcongr
                · calc
                    |x| ^ 4 ≤ |x| ^ 1 :=
                      pow_le_pow_of_le_one (abs_nonneg _)
                        (by rwa [abs_of_nonneg (le_of_lt hx0)]) (by decide)
                    _ = x := by simp [abs_of_nonneg (le_of_lt hx0)]
                · calc
                    x ^ 3 ≤ x ^ 1 := pow_le_pow_of_le_one (le_of_lt hx0) hx (by decide)
                    _ = x := pow_one _
            _ < x := by linarith)
    _ ≤ sin x :=
      sub_le_comm.1 (abs_sub_le_iff.1 (sin_bound (by rwa [abs_of_nonneg (le_of_lt hx0)]))).2

theorem sin_pos_of_pos_of_le_two {x : ℝ} (hx0 : 0 < x) (hx : x ≤ 2) : 0 < sin x :=
  have : x / 2 ≤ 1 := (div_le_iff₀ (by norm_num)).mpr (by simpa)
  calc
    0 < 2 * sin (x / 2) * cos (x / 2) :=
      mul_pos (mul_pos (by norm_num) (sin_pos_of_pos_of_le_one (half_pos hx0) this))
        (cos_pos_of_le_one (by rwa [abs_of_nonneg (le_of_lt (half_pos hx0))]))
    _ = sin x := by rw [← sin_two_mul, two_mul, add_halves]

theorem cos_one_le : cos 1 ≤ 5 / 9 :=
  calc
    cos 1 ≤ |(1 : ℝ)| ^ 4 * (5 / 96) + (1 - 1 ^ 2 / 2) :=
      sub_le_iff_le_add.1 (abs_sub_le_iff.1 (cos_bound (by simp))).1
    _ ≤ 5 / 9 := by norm_num

theorem cos_one_pos : 0 < cos 1 :=
  cos_pos_of_le_one (le_of_eq abs_one)

theorem cos_two_neg : cos 2 < 0 :=
  calc cos 2 = cos (2 * 1) := congr_arg cos (mul_one _).symm
    _ = _ := Real.cos_two_mul 1
    _ ≤ 2 * (5 / 9) ^ 2 - 1 := by
      gcongr
      · exact cos_one_pos.le
      · apply cos_one_le
    _ < 0 := by norm_num

end Real

namespace Mathlib.Meta.Positivity
open Lean.Meta Qq

/-- Extension for the `positivity` tactic: `Real.cosh` is always positive. -/
@[positivity Real.cosh _]
def evalCosh : PositivityExt where eval {u α} _ _ e := do
  match u, α, e with
  | 0, ~q(ℝ), ~q(Real.cosh $a) =>
    assertInstancesCommute
    return .positive q(Real.cosh_pos $a)
  | _, _, _ => throwError "not Real.cosh"

example (x : ℝ) : 0 < x.cosh := by positivity

end Mathlib.Meta.Positivity

namespace Complex

@[simp]
theorem norm_cos_add_sin_mul_I (x : ℝ) : ‖cos x + sin x * I‖ = 1 := by
  have := Real.sin_sq_add_cos_sq x
  simp_all [add_comm, norm_def, normSq, sq, sin_ofReal_re, cos_ofReal_re, mul_re]

@[simp]
theorem norm_exp_ofReal_mul_I (x : ℝ) : ‖exp (x * I)‖ = 1 := by
  rw [exp_mul_I, norm_cos_add_sin_mul_I]

theorem norm_exp (z : ℂ) : ‖exp z‖ = Real.exp z.re := by
  rw [exp_eq_exp_re_mul_sin_add_cos, Complex.norm_mul, norm_exp_ofReal, norm_cos_add_sin_mul_I,
    mul_one]

theorem norm_exp_eq_iff_re_eq {x y : ℂ} : ‖exp x‖ = ‖exp y‖ ↔ x.re = y.re := by
  rw [norm_exp, norm_exp, Real.exp_eq_exp]

@[deprecated (since := "2025-02-16")] alias abs_cos_add_sin_mul_I := norm_cos_add_sin_mul_I
@[deprecated (since := "2025-02-16")] alias abs_exp_ofReal_mul_I := norm_exp_ofReal_mul_I
@[deprecated (since := "2025-02-16")] alias abs_exp := norm_exp
@[deprecated (since := "2025-02-16")] alias abs_exp_eq_iff_re_eq := norm_exp_eq_iff_re_eq

end Complex

```

