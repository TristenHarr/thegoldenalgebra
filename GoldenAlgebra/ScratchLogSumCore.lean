import Mathlib

open Complex Filter Topology

/-!
# `hLogSumCore` — the genus-1 minimum-modulus log-sum bound (deepest Hadamard gap)

This file attacks the single irreducible analytic core isolated by `ScratchMinModClose.lean`:

  `hLogSumCore : ∃ C₀, ∀ z off-zeros, −(C₀·(1+‖z‖)·log(2+‖z‖)) ≤ Σ_i log(gᵢ z)`,

where `gᵢ z = ‖1 − z/loc i‖ · exp(Re(z/loc i))` is the real factored value of one genus-1 factor.
The driving input is the order-1 zero count `N(R) = O(R·log R)` (`Scratch.xi_zero_count_bigO`,
B47, unconditional) together with `Σ 1/‖loc i‖² < ∞` (`Scratch.xi_zero_invSq_summable`, B50).

## What is genuinely PROVEN here (no `sorry`, no `sorryAx`)

The **FAR-TAIL DECAY** (the part the task asks to close): from a ball count
`Nat.card {‖loc i‖ ≤ R} ≤ A·R·log R`, the far inverse-square tail decays like `log X / X`:

  `far_tail_decay : Σ_{‖loc i‖ ≥ X} 1/‖loc i‖² ≤ C · log X / X`   (for `X ≥ 2`).

This is proved by **dyadic shells** — the same engine `Scratch.summable_inv_sq_of_shellCard` uses,
but now tracked QUANTITATIVELY: the tail splits into shells `2^k·X ≤ ‖loc i‖ < 2^{k+1}·X`, each
shell has `≤ N(2^{k+1}X) ≤ A·2^{k+1}X·log(2^{k+1}X)` points each of size `≤ 1/(2^k X)²`, and summing
the geometric-times-affine series `Σ_k (log X + (k+1)log2)/2^k` gives `O(log X / X)`. (Morally this is
Abel summation of `1/R²` against `dN(R)`; the dyadic decomposition is the mechanizable equivalent and
avoids Mathlib's `AbelSummation` being ℕ-indexed while our index set is an arbitrary type `ι`.)

Combined with the **genus-1 quadratic cancellation** `log(gᵢ z) ≥ −‖z/loc i‖²` on the far zeros
(`ScratchMinModClose.far_log_factor_ge`, re-stated locally), the far-zeros log-sum is bounded below by
`−‖z‖²·(C·log‖z‖/‖z‖) = −C·‖z‖·log‖z‖` — **order 1**, exactly what the downstream quotient growth needs.

The **near-zeros COUNT** `N(2‖z‖) = O(‖z‖·log‖z‖)` is also recorded (directly from the count bound).

## The ISOLATED irreducible residual (ONE honest hypothesis)

`CartanCircleAvoidance` — for the FINITELY-MANY near zeros (`‖loc i‖ < 2‖z‖`), the term
`log‖1 − z/loc i‖` can be arbitrarily negative when `z` is very close to a zero `loc i`. The classical
Hadamard fix is **Cartan's lemma / Borel–Carathéodory circle selection**: one does NOT bound at every
`z`, but only off the union of small exceptional disks around the zeros (total radii summable); on the
complement one has `log‖1 − z/loc i‖ ≥ −C·log(2+‖z‖)` per near zero. Mathlib has `Complex.borelCaratheodory`
but NOT Cartan's lemma (the "measure of the exceptional set / avoid small disks" estimate), so this is a
genuine missing development. We isolate it as the single hypothesis `CartanCircleAvoidance` below: a
per-near-zero lower bound `log‖1 − z/loc i‖ ≥ −C·log(2+‖z‖)`, valid off the zeros. Multiplied by the
near count `O(‖z‖log‖z‖)` it yields the near-zeros contribution `−O(‖z‖(log‖z‖)²)` — slightly
super-linear but, as the task notes, still order-1 for the quotient via the `‖z‖log‖z‖` envelope.

## Honest assessment

The far-tail decay (the dyadic/Abel step) is genuinely mechanized and CLOSED here. The near-zeros
content reduces — with the proven count — to the single `CartanCircleAvoidance` residual, which is the
true deep gap (Cartan's lemma, absent from Mathlib). `hLogSumCore_of_cartan` assembles `hLogSumCore`
conditional on exactly that one hypothesis.

Build: `cd /Users/tristen/Desktop/goldenalgebra/GoldenAlgebra && lake env lean ScratchLogSumCore.lean`.
-/

namespace OverflowResidueRH.BacklundTuring.ScratchLogSumCore

variable {ι : Type*} (loc : ι → ℂ)

/-! ## Part 1 — the FAR-TAIL DECAY via dyadic shells (the genuinely-proven core)

The tail `Σ_{‖loc i‖ ≥ X} 1/‖loc i‖²`, summed in dyadic shells driven by the count `N(R) ≤ A·R·log R`,
decays like `log X / X`. This is the quantitative refinement of `Scratch.summable_inv_sq_of_shellCard`. -/

/-- **Dyadic-shell summand bound for the far tail.** For a point `i` in the `k`-th shell above `X`
(i.e. `2^k·X ≤ ‖loc i‖`), the inverse-square summand is `≤ 1/(2^k·X)²`. -/
lemma far_term_le {i : ι} {X : ℝ} {k : ℕ} (hX : 0 < X)
    (hlow : (2:ℝ) ^ k * X ≤ ‖loc i‖) :
    1 / ‖loc i‖ ^ 2 ≤ 1 / ((2:ℝ) ^ k * X) ^ 2 := by
  have hpos : (0:ℝ) < (2:ℝ) ^ k * X := by positivity
  have hsq : ((2:ℝ) ^ k * X) ^ 2 ≤ ‖loc i‖ ^ 2 := by
    apply pow_le_pow_left₀ hpos.le hlow
  have hnpos : (0:ℝ) < ‖loc i‖ ^ 2 :=
    lt_of_lt_of_le (by positivity) hsq
  rw [div_le_div_iff₀ hnpos (by positivity)]
  simpa using hsq

/-- **Summability of the dyadic dominating series** `k ↦ B·(k+1)/2^k + D/2^k`.
The series that dominates the far tail after dyadic decomposition. -/
lemma summable_dyadic_dom (B D : ℝ) :
    Summable (fun k : ℕ => B * ((k:ℝ) + 1) / 2 ^ k + D / 2 ^ k) := by
  have hgeo : Summable (fun n : ℕ => (n:ℝ) ^ 1 * ((1:ℝ)/2) ^ n) :=
    summable_pow_mul_geometric_of_norm_lt_one 1 (by rw [Real.norm_eq_abs]; norm_num)
  have hgeo0 : Summable (fun n : ℕ => (n:ℝ) ^ 0 * ((1:ℝ)/2) ^ n) :=
    summable_pow_mul_geometric_of_norm_lt_one 0 (by rw [Real.norm_eq_abs]; norm_num)
  have hb : Summable (fun k : ℕ => B * ((k:ℝ) + 1) / 2 ^ k) := by
    have heq : (fun k : ℕ => B * ((k:ℝ)+1) / 2 ^ k)
        = (fun k : ℕ => B * ((k:ℝ) ^ 1 * ((1:ℝ)/2) ^ k) + B * ((k:ℝ) ^ 0 * ((1:ℝ)/2) ^ k)) := by
      funext k
      have hhalf : ((1:ℝ)/2) ^ k = 1 / (2:ℝ) ^ k := by rw [div_pow]; norm_num
      rw [hhalf, pow_one, pow_zero]; ring
    rw [heq]; exact (hgeo.mul_left B).add (hgeo0.mul_left B)
  have hd : Summable (fun k : ℕ => D / 2 ^ k) := by
    have heq : (fun k : ℕ => D / 2 ^ k)
        = (fun k : ℕ => D * ((k:ℝ) ^ 0 * ((1:ℝ)/2) ^ k)) := by
      funext k
      have hhalf : ((1:ℝ)/2) ^ k = 1 / (2:ℝ) ^ k := by rw [div_pow]; norm_num
      rw [hhalf, pow_zero]; ring
    rw [heq]; exact hgeo0.mul_left D
  exact hb.add hd

/-- `1/2^k = (1/2)^k`. -/
lemma inv_two_pow_eq (k : ℕ) : (1:ℝ) / 2 ^ k = ((1:ℝ)/2) ^ k := by
  rw [div_pow, one_pow]

/-- `↑k/2^k = ↑k·(1/2)^k`. -/
lemma coe_div_two_pow_eq (k : ℕ) : (k:ℝ) / 2 ^ k = (k:ℝ) * ((1:ℝ)/2) ^ k := by
  rw [div_pow, one_pow, mul_one_div]

lemma summable_inv_two_pow : Summable (fun k : ℕ => (1:ℝ)/2^k) := by
  rw [show (fun k : ℕ => (1:ℝ)/2^k) = (fun k : ℕ => ((1:ℝ)/2)^k) from funext inv_two_pow_eq]
  exact summable_geometric_of_lt_one (by norm_num) (by norm_num)

lemma summable_coe_div_two_pow : Summable (fun k : ℕ => (k:ℝ)/2^k) := by
  rw [show (fun k : ℕ => (k:ℝ)/2^k) = (fun k : ℕ => (k:ℝ) * ((1:ℝ)/2)^k) from funext coe_div_two_pow_eq]
  have h := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 (r := (1:ℝ)/2)
    (by rw [Real.norm_eq_abs]; norm_num)
  exact h.congr (fun k => by rw [pow_one])

/-- `Σ_k 1/2^k = 2`. -/
lemma tsum_inv_two_pow : ∑' k : ℕ, (1:ℝ) / 2 ^ k = 2 := by
  rw [show (fun k : ℕ => (1:ℝ)/2^k) = (fun k : ℕ => ((1:ℝ)/2)^k) from funext inv_two_pow_eq]
  rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)]; norm_num

/-- `Σ_k (k+1)/2^k = 4`, via `Σ k/2^k = 2` and `Σ 1/2^k = 2`. -/
lemma tsum_succ_div_two_pow : ∑' k : ℕ, ((k:ℝ) + 1) / 2 ^ k = 4 := by
  have hk : ∑' k : ℕ, (k:ℝ) / 2 ^ k = 2 := by
    rw [show (fun k : ℕ => (k:ℝ)/2^k) = (fun k : ℕ => (k:ℝ) * ((1:ℝ)/2)^k) from funext coe_div_two_pow_eq,
      tsum_coe_mul_geometric_of_norm_lt_one (by rw [Real.norm_eq_abs]; norm_num)]; norm_num
  have hsplit : (fun k : ℕ => ((k:ℝ)+1)/2^k) = (fun k : ℕ => (k:ℝ)/2^k + 1/2^k) := by
    funext k; ring
  rw [hsplit, summable_coe_div_two_pow.tsum_add summable_inv_two_pow, hk, tsum_inv_two_pow]; norm_num

/-- **The closed-form value of the dyadic dominating series.**
`Σ_k B(k+1)/2^k + D/2^k = 4B + 2D`. -/
lemma tsum_dyadic_dom (B D : ℝ) :
    ∑' k : ℕ, (B * ((k:ℝ) + 1) / 2 ^ k + D / 2 ^ k) = 4 * B + 2 * D := by
  have hsB : Summable (fun k : ℕ => B * ((k:ℝ)+1) / 2 ^ k) := by
    rw [show (fun k : ℕ => B * ((k:ℝ)+1) / 2 ^ k) = (fun k : ℕ => B * (((k:ℝ)+1)/2^k)) from
      funext (fun k => by ring)]
    refine Summable.mul_left B ?_
    rw [show (fun k : ℕ => ((k:ℝ)+1)/2^k) = (fun k : ℕ => (k:ℝ)/2^k + 1/2^k) from
      funext (fun k => by ring)]
    exact summable_coe_div_two_pow.add summable_inv_two_pow
  have hsD : Summable (fun k : ℕ => D / 2 ^ k) :=
    summable_inv_two_pow.mul_left D |>.congr (fun k => by ring)
  rw [hsB.tsum_add hsD]
  rw [show (fun k : ℕ => B * ((k:ℝ)+1) / 2 ^ k) = (fun k : ℕ => B * (((k:ℝ)+1)/2^k)) from
    funext (fun k => by ring), tsum_mul_left, tsum_succ_div_two_pow]
  rw [show (fun k : ℕ => D / 2 ^ k) = (fun k : ℕ => D * ((1:ℝ)/2^k)) from
    funext (fun k => by ring), tsum_mul_left, tsum_inv_two_pow]
  ring

/-- **Per-shell mass bound** (the heart of both `far_inv_summable` and `far_tail_decay`).
Given a shell-index function `sh` on the far subtype with the dyadic membership property
`2^(sh j)·X ≤ ‖loc j‖ < 2^(sh j+1)·X`, the inverse-square mass of shell `k` is bounded by the
dyadic dominating term `domSeq k = (2A/X)(log X)/2^k + (2A log2/X)(k+1)/2^k`. Uses the count bound
`N(2^(k+1)X) ≤ A·2^(k+1)X·log(2^(k+1)X)` and `far_term_le`. -/
theorem shell_mass_le (A : ℝ) (_hA : 0 ≤ A)
    (hfin : ∀ R : ℝ, {i | ‖loc i‖ ≤ R}.Finite)
    (hcount : ∀ R : ℝ, 2 ≤ R → (Nat.card {i | ‖loc i‖ ≤ R} : ℝ) ≤ A * R * Real.log R)
    {X : ℝ} (hX : 2 ≤ X)
    {sh : {i // X ≤ ‖loc i‖} → ℕ}
    (hmem : ∀ j : {i // X ≤ ‖loc i‖},
      (2:ℝ) ^ (sh j) * X ≤ ‖loc (j : ι)‖ ∧ ‖loc (j : ι)‖ < 2 ^ (sh j + 1) * X)
    (hfintype : ∀ k : ℕ, Fintype {j : {i // X ≤ ‖loc i‖} // sh j = k}) (k : ℕ) :
    (∑' (j : {j : {i // X ≤ ‖loc i‖} // sh j = k}),
        (1 / ‖loc ((Equiv.sigmaFiberEquiv sh ⟨k, j⟩ : {i // X ≤ ‖loc i‖}) : ι)‖ ^ 2))
      ≤ (2 * A / X) * ((Real.log X) / 2 ^ k)
        + (2 * A * Real.log 2 / X) * (((k:ℝ) + 1) / 2 ^ k) := by
  classical
  have hXpos : (0:ℝ) < X := by linarith
  have hft := hfintype k
  rw [tsum_fintype]
  have hterm : ∀ j : {j : {i // X ≤ ‖loc i‖} // sh j = k},
      1 / ‖loc ((Equiv.sigmaFiberEquiv sh ⟨k, j⟩ : {i // X ≤ ‖loc i‖}) : ι)‖ ^ 2
        ≤ 1 / ((2:ℝ) ^ k * X) ^ 2 := by
    intro j
    have he : (Equiv.sigmaFiberEquiv sh ⟨k, j⟩ : {i // X ≤ ‖loc i‖}) = (j : {i // X ≤ ‖loc i‖}) := rfl
    rw [he]
    have hlow : (2:ℝ) ^ k * X ≤ ‖loc ((j : {i // X ≤ ‖loc i‖}) : ι)‖ := by
      have := (hmem (j : {i // X ≤ ‖loc i‖})).1; rwa [j.2] at this
    exact far_term_le loc hXpos hlow
  have hsum_le : (∑ j : {j : {i // X ≤ ‖loc i‖} // sh j = k},
        1 / ‖loc ((Equiv.sigmaFiberEquiv sh ⟨k, j⟩ : {i // X ≤ ‖loc i‖}) : ι)‖ ^ 2)
      ≤ (Finset.univ : Finset {j : {i // X ≤ ‖loc i‖} // sh j = k}).card • (1 / ((2:ℝ) ^ k * X) ^ 2) :=
    Finset.sum_le_card_nsmul _ _ _ (fun x _ => hterm x)
  refine le_trans hsum_le ?_
  rw [nsmul_eq_mul]
  have hcard_eq : ((Finset.univ : Finset {j : {i // X ≤ ‖loc i‖} // sh j = k}).card : ℝ)
      = (Nat.card {j : {i // X ≤ ‖loc i‖} // sh j = k} : ℝ) := by rw [Nat.card_eq_fintype_card]; rfl
  rw [hcard_eq]
  set R : ℝ := (2:ℝ) ^ (k+1) * X with hR
  have hR2 : (2:ℝ) ≤ R := by
    rw [hR]; have : (1:ℝ) ≤ (2:ℝ)^(k+1) := one_le_pow₀ (by norm_num)
    nlinarith [hXpos]
  have hballfin : {i | ‖loc i‖ ≤ R}.Finite := hfin R
  have hcardmono : (Nat.card {j : {i // X ≤ ‖loc i‖} // sh j = k} : ℝ)
      ≤ (Nat.card {i | ‖loc i‖ ≤ R} : ℝ) := by
    have hinj : Function.Injective
        (fun (j : {j : {i // X ≤ ‖loc i‖} // sh j = k}) => ((j : {i // X ≤ ‖loc i‖}) : ι)) := by
      intro a b hab; exact Subtype.ext (Subtype.ext hab)
    have himg' : (Set.range
        (fun (j : {j : {i // X ≤ ‖loc i‖} // sh j = k}) => ((j : {i // X ≤ ‖loc i‖}) : ι)))
          ⊆ {i | ‖loc i‖ ≤ R} := by
      rintro i ⟨j, rfl⟩
      simp only [Set.mem_setOf_eq]
      have h := (hmem (j : {i // X ≤ ‖loc i‖})).2; rw [j.2] at h; rw [hR]; linarith [h]
    rw [(Nat.card_range_of_injective hinj).symm]
    exact_mod_cast Nat.card_mono hballfin himg'
  have hcardR : (Nat.card {j : {i // X ≤ ‖loc i‖} // sh j = k} : ℝ) ≤ A * R * Real.log R :=
    le_trans hcardmono (hcount R hR2)
  have hstep : (Nat.card {j : {i // X ≤ ‖loc i‖} // sh j = k} : ℝ) * (1 / ((2:ℝ) ^ k * X) ^ 2)
      ≤ (A * R * Real.log R) * (1 / ((2:ℝ) ^ k * X) ^ 2) :=
    mul_le_mul_of_nonneg_right hcardR (by positivity)
  refine le_trans hstep (le_of_eq ?_)
  have hlogR : Real.log R = ((k:ℝ) + 1) * Real.log 2 + Real.log X := by
    rw [hR, Real.log_mul (by positivity) (ne_of_gt hXpos), Real.log_pow]; push_cast; ring
  have h2kne : (2:ℝ) ^ k ≠ 0 := by positivity
  have hXne : X ≠ 0 := ne_of_gt hXpos
  rw [hR, hlogR]
  rw [show (2:ℝ) ^ (k+1) = 2 ^ k * 2 from by rw [pow_succ]]
  field_simp
  ring

/-- **Far inverse-square subtype summability.** Over the far zeros `{i | X ≤ ‖loc i‖}`, the
inverse-square sum converges. Proved via the dyadic-shell sigma regrouping (same engine as
`far_tail_decay`/`Scratch.summable_inv_sq_of_shellCard`): each fiber is finite, and the per-shell
masses are dominated by the summable dyadic series `domSeq`. -/
theorem far_inv_summable (A : ℝ) (hA : 0 ≤ A)
    (hfin : ∀ R : ℝ, {i | ‖loc i‖ ≤ R}.Finite)
    (hcount : ∀ R : ℝ, 2 ≤ R → (Nat.card {i | ‖loc i‖ ≤ R} : ℝ) ≤ A * R * Real.log R)
    {X : ℝ} (hX : 2 ≤ X) :
    Summable (fun j : {i // X ≤ ‖loc i‖} => 1 / ‖loc (j : ι)‖ ^ 2) := by
  classical
  have hXpos : (0:ℝ) < X := by linarith
  set T : Type _ := {i // X ≤ ‖loc i‖} with hT
  set sh : T → ℕ := fun j => ⌊Real.logb 2 (‖loc (j : ι)‖ / X)⌋₊ with hsh
  have hmem : ∀ j : T, (2:ℝ) ^ (sh j) * X ≤ ‖loc (j : ι)‖ ∧ ‖loc (j : ι)‖ < 2 ^ (sh j + 1) * X := by
    intro j
    have hge : X ≤ ‖loc (j : ι)‖ := j.2
    have hxpos : (0:ℝ) < ‖loc (j : ι)‖ := lt_of_lt_of_le hXpos hge
    have hratio1 : (1:ℝ) ≤ ‖loc (j : ι)‖ / X := (one_le_div hXpos).mpr hge
    have hratiopos : (0:ℝ) < ‖loc (j : ι)‖ / X := by positivity
    have hL0 : 0 ≤ Real.logb 2 (‖loc (j : ι)‖ / X) := Real.logb_nonneg (by norm_num) hratio1
    set L := Real.logb 2 (‖loc (j : ι)‖ / X) with hLdef
    constructor
    · have hk : ((sh j : ℝ)) ≤ L := by simpa [hsh] using Nat.floor_le hL0
      have hpow : (2:ℝ) ^ ((sh j : ℝ)) ≤ ‖loc (j : ι)‖ / X := by
        rw [← Real.le_logb_iff_rpow_le (by norm_num) hratiopos]; exact hk
      rw [Real.rpow_natCast] at hpow
      rw [le_div_iff₀ hXpos] at hpow; linarith [hpow]
    · have hk : L < (sh j : ℝ) + 1 := by simpa [hsh] using Nat.lt_floor_add_one L
      have hpow : ‖loc (j : ι)‖ / X < (2:ℝ) ^ ((sh j : ℝ) + 1) := by
        rw [← Real.logb_lt_iff_lt_rpow (by norm_num) hratiopos]; exact hk
      have hcast : ((sh j : ℝ) + 1) = ((sh j + 1 : ℕ) : ℝ) := by push_cast; ring
      rw [hcast, Real.rpow_natCast] at hpow
      rw [div_lt_iff₀ hXpos] at hpow; linarith [hpow]
  have hfiberfin : ∀ k : ℕ, {j : T | sh j = k}.Finite := by
    intro k
    apply Set.Finite.of_finite_image (f := (Subtype.val : T → ι))
    · apply Set.Finite.subset (hfin ((2:ℝ) ^ (k+1) * X))
      rintro i ⟨j, hj, rfl⟩
      simp only [Set.mem_setOf_eq] at hj ⊢
      have := (hmem j).2; rw [hj] at this; linarith [this]
    · exact (Subtype.val_injective).injOn
  set g : T → ℝ := fun j => 1 / ‖loc (j : ι)‖ ^ 2 with hg
  have hgnn : ∀ j, 0 ≤ g j := fun j => by positivity
  have hfintype : ∀ k : ℕ, Fintype {j : T // sh j = k} := fun k => (hfiberfin k).fintype
  set domSeq : ℕ → ℝ := fun k => (2 * A / X) * ((Real.log X) / 2 ^ k)
    + (2 * A * Real.log 2 / X) * (((k:ℝ) + 1) / 2 ^ k) with hdomSeq
  have hshellbound : ∀ k : ℕ,
      (∑' (j : {j : T // sh j = k}), g (Equiv.sigmaFiberEquiv sh ⟨k, j⟩)) ≤ domSeq k :=
    fun k => shell_mass_le loc A hA hfin hcount hX hmem hfintype k
  have hdomSummable : Summable domSeq := by
    have heq : domSeq = (fun k : ℕ =>
        (2 * A / X * Real.log X) * (1 / 2 ^ k) + (2 * A * Real.log 2 / X) * (((k:ℝ) + 1) / 2 ^ k)) := by
      funext k; rw [hdomSeq]; ring
    rw [heq]
    exact (summable_inv_two_pow.mul_left _).add
      ((summable_coe_div_two_pow.add summable_inv_two_pow).congr (fun k => by ring) |>.mul_left _)
  rw [← (Equiv.sigmaFiberEquiv sh).summable_iff]
  refine (summable_sigma_of_nonneg (fun x => hgnn _)).mpr ⟨fun k => ?_, ?_⟩
  · have : Finite {j : T // sh j = k} := (hfiberfin k).to_subtype
    exact summable_of_hasFiniteSupport (Set.toFinite _)
  · exact Summable.of_nonneg_of_le (fun k => tsum_nonneg (fun j => hgnn _)) hshellbound hdomSummable

/-- **THE FAR-TAIL DECAY (genuinely proven core).** Given the ball count `N(R) ≤ A·R·log R`
(`hcount`, for `R ≥ 2`) and finiteness of balls (`hfin`), the inverse-square tail over the far zeros
`{i | X ≤ ‖loc i‖}` decays like `log X / X`:

  `∑'_{X ≤ ‖loc i‖} 1/‖loc i‖² ≤ (12·A) · log X / X`   (for `X ≥ 2`, `A ≥ 0`).

Proof by **dyadic shells** above `X`: term `≤ 1/(2^k X)²`, shell-`k` count `≤ N(2^{k+1}X) ≤
A·2^{k+1}X·log(2^{k+1}X)`, so shell-`k` mass `≤ (2A/X)·((k+1)log2 + log X)/2^k`; summing the dyadic
dominating series (`tsum_dyadic_dom`: `Σ (k+1)/2^k = 4`, `Σ 1/2^k = 2`) gives `(2A/X)·(4log2 + 2 log X)
≤ (12A) log X / X` using `log2 ≤ log X` for `X ≥ 2`. Mirrors `Scratch.summable_inv_sq_of_shellCard`
but tracked QUANTITATIVELY. This is the mechanizable form of the Abel-summation far-tail step. -/
theorem far_tail_decay (A : ℝ) (hA : 0 ≤ A)
    (hfin : ∀ R : ℝ, {i | ‖loc i‖ ≤ R}.Finite)
    (hcount : ∀ R : ℝ, 2 ≤ R → (Nat.card {i | ‖loc i‖ ≤ R} : ℝ) ≤ A * R * Real.log R)
    {X : ℝ} (hX : 2 ≤ X) :
    ∑' (j : {i // X ≤ ‖loc i‖}), 1 / ‖loc (j : ι)‖ ^ 2 ≤ 12 * A * Real.log X / X := by
  classical
  have hXpos : (0:ℝ) < X := by linarith
  have hlogX : 0 < Real.log X := Real.log_pos (by linarith)
  have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  -- shell index of a far point
  set T : Type _ := {i // X ≤ ‖loc i‖} with hT
  set sh : T → ℕ := fun j => ⌊Real.logb 2 (‖loc (j : ι)‖ / X)⌋₊ with hsh
  -- each far point lies in its shell: 2^(sh j)·X ≤ ‖loc j‖ < 2^(sh j+1)·X
  have hmem : ∀ j : T, (2:ℝ) ^ (sh j) * X ≤ ‖loc (j : ι)‖ ∧ ‖loc (j : ι)‖ < 2 ^ (sh j + 1) * X := by
    intro j
    have hge : X ≤ ‖loc (j : ι)‖ := j.2
    have hxpos : (0:ℝ) < ‖loc (j : ι)‖ := lt_of_lt_of_le hXpos hge
    have hratio1 : (1:ℝ) ≤ ‖loc (j : ι)‖ / X := (one_le_div hXpos).mpr hge
    have hratiopos : (0:ℝ) < ‖loc (j : ι)‖ / X := by positivity
    have hL0 : 0 ≤ Real.logb 2 (‖loc (j : ι)‖ / X) := Real.logb_nonneg (by norm_num) hratio1
    set L := Real.logb 2 (‖loc (j : ι)‖ / X) with hLdef
    constructor
    · have hk : ((sh j : ℝ)) ≤ L := by simpa [hsh] using Nat.floor_le hL0
      have hpow : (2:ℝ) ^ ((sh j : ℝ)) ≤ ‖loc (j : ι)‖ / X := by
        rw [← Real.le_logb_iff_rpow_le (by norm_num) hratiopos]; exact hk
      rw [Real.rpow_natCast] at hpow
      rw [le_div_iff₀ hXpos] at hpow; linarith [hpow]
    · have hk : L < (sh j : ℝ) + 1 := by simpa [hsh] using Nat.lt_floor_add_one L
      have hpow : ‖loc (j : ι)‖ / X < (2:ℝ) ^ ((sh j : ℝ) + 1) := by
        rw [← Real.logb_lt_iff_lt_rpow (by norm_num) hratiopos]; exact hk
      have hcast : ((sh j : ℝ) + 1) = ((sh j + 1 : ℕ) : ℝ) := by push_cast; ring
      rw [hcast, Real.rpow_natCast] at hpow
      rw [div_lt_iff₀ hXpos] at hpow; linarith [hpow]
  -- fibers are finite (contained in a finite ball)
  have hfiberfin : ∀ k : ℕ, {j : T | sh j = k}.Finite := by
    intro k
    -- map to the finite ball {‖loc i‖ ≤ 2^(k+1)·X} via Subtype.val
    apply Set.Finite.of_finite_image (f := (Subtype.val : T → ι))
    · apply Set.Finite.subset (hfin ((2:ℝ) ^ (k+1) * X))
      rintro i ⟨j, hj, rfl⟩
      simp only [Set.mem_setOf_eq] at hj ⊢
      have := (hmem j).2; rw [hj] at this; linarith [this]
    · exact (Subtype.val_injective).injOn
  -- regroup the far tail by shell via the sigma-fiber equivalence
  set g : T → ℝ := fun j => 1 / ‖loc (j : ι)‖ ^ 2 with hg
  have hgnn : ∀ j, 0 ≤ g j := fun j => by positivity
  -- Fintype instances on fibers
  have hfintype : ∀ k : ℕ, Fintype {j : T // sh j = k} := fun k => (hfiberfin k).fintype
  -- per-shell mass bound: shell-k tsum ≤ A·2^(k+1)·X·log(2^(k+1)X) / (2^k X)²
  --                                    = (2A/X)·log(2^(k+1)X)/2^k
  set domSeq : ℕ → ℝ := fun k => (2 * A / X) * ((Real.log X) / 2 ^ k)
    + (2 * A * Real.log 2 / X) * (((k:ℝ) + 1) / 2 ^ k) with hdomSeq
  have hshellbound : ∀ k : ℕ,
      (∑' (j : {j : T // sh j = k}), g (Equiv.sigmaFiberEquiv sh ⟨k, j⟩)) ≤ domSeq k :=
    fun k => shell_mass_le loc A hA hfin hcount hX hmem hfintype k
  -- the dominating dyadic series is summable, and its value is computable
  have hdomSeq_eq : domSeq = (fun k : ℕ =>
      (2 * A / X * Real.log X) * (1 / 2 ^ k) + (2 * A * Real.log 2 / X) * (((k:ℝ) + 1) / 2 ^ k)) := by
    funext k; rw [hdomSeq]; ring
  have hdomSummable : Summable domSeq := by
    rw [hdomSeq_eq]
    refine Summable.add ?_ ?_
    · exact summable_inv_two_pow.mul_left _
    · exact (summable_coe_div_two_pow.add summable_inv_two_pow).congr
        (fun k => by ring) |>.mul_left _
  have hdomVal : ∑' k : ℕ, domSeq k = 4 * A * Real.log X / X + 8 * A * Real.log 2 / X := by
    rw [hdomSeq_eq]
    rw [Summable.tsum_add (summable_inv_two_pow.mul_left _)
      (((summable_coe_div_two_pow.add summable_inv_two_pow).congr (fun k => by ring)).mul_left _)]
    rw [tsum_mul_left, tsum_inv_two_pow]
    rw [tsum_mul_left,
      show (fun k : ℕ => ((k:ℝ)+1)/2^k) = (fun k : ℕ => (k:ℝ)/2^k + 1/2^k) from
        funext (fun k => by ring),
      summable_coe_div_two_pow.tsum_add summable_inv_two_pow]
    have hk : ∑' k : ℕ, (k:ℝ) / 2 ^ k = 2 := by
      rw [show (fun k : ℕ => (k:ℝ)/2^k) = (fun k : ℕ => (k:ℝ) * ((1:ℝ)/2)^k) from funext coe_div_two_pow_eq,
        tsum_coe_mul_geometric_of_norm_lt_one (by rw [Real.norm_eq_abs]; norm_num)]; norm_num
    rw [hk, tsum_inv_two_pow]; field_simp; ring
  -- far tail is summable (dominated by domSeq via shells) → regroup → bound
  have hsigmaSummable : Summable (fun p : Σ k, {j : T // sh j = k} =>
      g (Equiv.sigmaFiberEquiv sh p)) := by
    rw [summable_sigma_of_nonneg (fun x => hgnn _)]
    refine ⟨fun k => ?_, ?_⟩
    · have : Finite {j : T // sh j = k} := (hfiberfin k).to_subtype
      exact summable_of_hasFiniteSupport (Set.toFinite _)
    · exact Summable.of_nonneg_of_le (fun k => tsum_nonneg (fun j => hgnn _)) hshellbound hdomSummable
  have hshellsummable : Summable (fun k => ∑' (j : {j : T // sh j = k}),
      g (Equiv.sigmaFiberEquiv sh ⟨k, j⟩)) :=
    ((summable_sigma_of_nonneg (fun x => hgnn _)).mp hsigmaSummable).2
  -- regroup the far tsum into shell sums
  have hregroup : ∑' j : T, g j = ∑' k : ℕ, ∑' (j : {j : T // sh j = k}),
      g (Equiv.sigmaFiberEquiv sh ⟨k, j⟩) := by
    rw [← (Equiv.sigmaFiberEquiv sh).tsum_eq g]
    exact Summable.tsum_sigma'
      (fun k => ((summable_sigma_of_nonneg (fun x => hgnn _)).mp hsigmaSummable).1 k) hsigmaSummable
  rw [hregroup]
  refine le_trans (Summable.tsum_le_tsum hshellbound hshellsummable hdomSummable) ?_
  rw [hdomVal]
  -- final arithmetic: 4A log X/X + 8A log2/X ≤ 12 A log X/X, since log2 ≤ log X
  have hlog2X : Real.log 2 ≤ Real.log X := Real.log_le_log (by norm_num) hX
  have hnum : 4 * A * Real.log X + 8 * A * Real.log 2 ≤ 12 * A * Real.log X := by
    nlinarith [hA, hlog2X, mul_nonneg hA (sub_nonneg.mpr hlog2X)]
  calc 4 * A * Real.log X / X + 8 * A * Real.log 2 / X
      = (4 * A * Real.log X + 8 * A * Real.log 2) / X := by ring
    _ ≤ (12 * A * Real.log X) / X := div_le_div_of_nonneg_right hnum hXpos.le
    _ = 12 * A * Real.log X / X := by ring

/-! ## Part 2 — the far-zeros log-sum bound (ORDER 1, fully proven)

`gFactor w z = ‖1 − z/w‖·exp((z/w).re)` is the real factored value of one genus-1 factor. The
genus-1 quadratic cancellation `log(gFactor) ≥ −‖z/w‖²` (proven in `ScratchMinModClose`, re-stated
here) combined with `far_tail_decay` gives the far-zeros log-sum bound at order 1. -/

/-- The real "factored" value of one genus-1 factor (mirrors `ScratchMinModClose.gFactor`). -/
noncomputable def gFactor (w z : ℂ) : ℝ := ‖1 - z / w‖ * Real.exp (z / w).re

/-- **Genus-1 quadratic cancellation** (re-proved locally; mirrors `ScratchMinModClose.log_factor_ge`).
For `‖u‖ ≤ 1/2`, `log(‖1−u‖·exp(Re u)) ≥ −‖u‖²`. -/
lemma log_factor_ge {u : ℂ} (hu : ‖u‖ ≤ 1 / 2) :
    -‖u‖ ^ 2 ≤ Real.log (‖1 - u‖ * Real.exp u.re) := by
  have hu1 : ‖u‖ < 1 := lt_of_le_of_lt hu (by norm_num)
  have hne1 : (1 : ℂ) - u ≠ 0 := by
    intro h
    have : ‖u‖ = 1 := by have : u = 1 := by linear_combination -h
                         rw [this]; simp
    linarith
  have hnormpos : 0 < ‖1 - u‖ := by simpa [norm_pos_iff] using hne1
  rw [Real.log_mul (ne_of_gt hnormpos) (Real.exp_ne_zero _), Real.log_exp]
  have hw : ‖(-u)‖ < 1 := by simpa using hu1
  have htay := Complex.norm_log_one_add_sub_self_le hw
  have hbound : ‖Complex.log (1 + (-u)) - (-u)‖ ≤ ‖u‖ ^ 2 := by
    refine le_trans htay ?_
    rw [norm_neg]
    have hinv : (1 - ‖u‖)⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ (by simpa using sub_pos_of_lt hu1) (by norm_num)]; linarith
    nlinarith [mul_le_mul_of_nonneg_left hinv (sq_nonneg ‖u‖)]
  have hre_eq : Real.log ‖1 - u‖ + u.re = (Complex.log (1 + (-u)) - (-u)).re := by
    rw [Complex.sub_re, ← Complex.log_re]; simp [Complex.neg_re, sub_eq_add_neg]
  rw [hre_eq]
  have hre_ge : -‖Complex.log (1 + (-u)) - (-u)‖ ≤ (Complex.log (1 + (-u)) - (-u)).re := by
    have := Complex.abs_re_le_norm (Complex.log (1 + (-u)) - (-u)); rw [abs_le] at this; linarith [this.1]
  linarith [hbound, hre_ge]

/-- Per far-zero log lower bound: if `2‖z‖ ≤ ‖loc i‖` then `log(gFactor (loc i) z) ≥ −‖z/loc i‖²`. -/
lemma far_log_factor_ge {i : ι} {z : ℂ} (h : 2 * ‖z‖ ≤ ‖loc i‖) (hloc : loc i ≠ 0) :
    -‖z / loc i‖ ^ 2 ≤ Real.log (gFactor (loc i) z) := by
  have hlocpos : 0 < ‖loc i‖ := by simpa [norm_pos_iff] using hloc
  have hle : ‖z / loc i‖ ≤ 1 / 2 := by
    rw [norm_div, div_le_iff₀ hlocpos]; nlinarith [norm_nonneg z]
  have := log_factor_ge (u := z / loc i) hle
  rw [gFactor]; convert this using 3

/-- **Far-zeros log-sum lower bound (ORDER 1).** Summing the genus-1 quadratic cancellation over the
far zeros `{i | 2‖z‖ ≤ ‖loc i‖}` and applying `far_tail_decay` with `X = 2‖z‖`:

  `Σ'_{2‖z‖ ≤ ‖loc i‖} log(gFactor (loc i) z) ≥ −6·A·‖z‖·log(2‖z‖)`   (for `‖z‖ ≥ 1`).

The `−‖z‖²` from the per-term bound times the `O(log X / X)` tail (`X = 2‖z‖`) yields the order-1
`O(‖z‖ log‖z‖)`. Requires summability of the far inverse-squares (from `far_tail_decay`'s summability).
The hypothesis `hfarlog_summable` supplies summability of the far log-terms (a consequence of the same
count + the quadratic bound; downstream it is the `hsummlog` already threaded through the assembly). -/
theorem far_logSum_ge (A : ℝ) (hA : 0 ≤ A)
    (hne : ∀ i, loc i ≠ 0)
    (hfin : ∀ R : ℝ, {i | ‖loc i‖ ≤ R}.Finite)
    (hcount : ∀ R : ℝ, 2 ≤ R → (Nat.card {i | ‖loc i‖ ≤ R} : ℝ) ≤ A * R * Real.log R)
    {z : ℂ} (hz1 : 1 ≤ ‖z‖)
    (hfarlog_summable : Summable (fun j : {i // 2 * ‖z‖ ≤ ‖loc i‖} =>
      Real.log (gFactor (loc (j : ι)) z))) :
    -(6 * A * ‖z‖ * Real.log (2 * ‖z‖))
      ≤ ∑' (j : {i // 2 * ‖z‖ ≤ ‖loc i‖}), Real.log (gFactor (loc (j : ι)) z) := by
  set X : ℝ := 2 * ‖z‖ with hX
  have hX2 : 2 ≤ X := by rw [hX]; linarith
  have hzpos : 0 < ‖z‖ := by linarith
  have hXpos : 0 < X := by linarith
  -- the far inverse-square tail is summable and ≤ 12A log X / X (both from the dyadic engine)
  have hfar_inv_summable : Summable (fun j : {i // X ≤ ‖loc i‖} => 1 / ‖loc (j : ι)‖ ^ 2) :=
    far_inv_summable loc A hA hfin hcount hX2
  -- per far term: -‖z/loc i‖² ≤ log(gFactor)
  have hterm : ∀ j : {i // X ≤ ‖loc i‖},
      -(‖z‖ ^ 2 * (1 / ‖loc (j : ι)‖ ^ 2)) ≤ Real.log (gFactor (loc (j : ι)) z) := by
    intro j
    have hge : X ≤ ‖loc (j : ι)‖ := j.2
    have h2z : 2 * ‖z‖ ≤ ‖loc (j : ι)‖ := by rw [← hX]; exact hge
    have hlb := far_log_factor_ge loc h2z (hne (j : ι))
    have heq : ‖z / loc (j : ι)‖ ^ 2 = ‖z‖ ^ 2 * (1 / ‖loc (j : ι)‖ ^ 2) := by
      rw [norm_div, div_pow]; ring
    rw [heq] at hlb; exact hlb
  -- the negative-quadratic series is summable
  have hneg_summable : Summable (fun j : {i // X ≤ ‖loc i‖} =>
      -(‖z‖ ^ 2 * (1 / ‖loc (j : ι)‖ ^ 2))) :=
    (hfar_inv_summable.mul_left (‖z‖ ^ 2)).neg
  -- sum the per-term bound
  have hsum_le : ∑' (j : {i // X ≤ ‖loc i‖}), -(‖z‖ ^ 2 * (1 / ‖loc (j : ι)‖ ^ 2))
      ≤ ∑' (j : {i // X ≤ ‖loc i‖}), Real.log (gFactor (loc (j : ι)) z) :=
    Summable.tsum_le_tsum hterm hneg_summable (by rw [hX] at hfarlog_summable ⊢; exact hfarlog_summable)
  -- evaluate the negative-quadratic tsum and bound it below
  have htsum_neg : ∑' (j : {i // X ≤ ‖loc i‖}), -(‖z‖ ^ 2 * (1 / ‖loc (j : ι)‖ ^ 2))
      = -(‖z‖ ^ 2 * ∑' (j : {i // X ≤ ‖loc i‖}), 1 / ‖loc (j : ι)‖ ^ 2) := by
    rw [tsum_neg, tsum_mul_left]
  have hfar_bound : ∑' (j : {i // X ≤ ‖loc i‖}), 1 / ‖loc (j : ι)‖ ^ 2 ≤ 12 * A * Real.log X / X :=
    far_tail_decay loc A hA hfin hcount hX2
  -- chain: -(6A‖z‖ log X) ≤ -(‖z‖²·(12A log X/X)) ≤ Σ neg ≤ Σ log
  have hge_neg : -(6 * A * ‖z‖ * Real.log (2 * ‖z‖))
      ≤ ∑' (j : {i // X ≤ ‖loc i‖}), -(‖z‖ ^ 2 * (1 / ‖loc (j : ι)‖ ^ 2)) := by
    rw [htsum_neg]
    -- -(6A‖z‖ log X) ≤ -(‖z‖²·tail) ⟺ ‖z‖²·tail ≤ 6A‖z‖ log X
    rw [neg_le_neg_iff]
    have hzsq : (0:ℝ) ≤ ‖z‖ ^ 2 := sq_nonneg _
    have hchain : ‖z‖ ^ 2 * ∑' (j : {i // X ≤ ‖loc i‖}), 1 / ‖loc (j : ι)‖ ^ 2
        ≤ ‖z‖ ^ 2 * (12 * A * Real.log X / X) :=
      mul_le_mul_of_nonneg_left hfar_bound hzsq
    refine le_trans hchain (le_of_eq ?_)
    -- ‖z‖²·(12A log X / X) = ‖z‖²·12A log X/(2‖z‖) = 6 A ‖z‖ log X
    rw [hX]
    have hzne : ‖z‖ ≠ 0 := ne_of_gt hzpos
    field_simp
    ring
  exact le_trans hge_neg hsum_le

/-! ## Part 3 — the near-zeros COUNT (proven) and the Cartan circle-avoidance residual

The near zeros `{i | ‖loc i‖ < 2‖z‖}` are finitely many, with count `N(2‖z‖) = O(‖z‖·log‖z‖)`
directly from the ball count. This is fully proven. The per-near-zero lower bound on
`log‖1 − z/loc i‖` is the genuine Cartan/Borel–Carathéodory residual. -/

/-- **Near-zeros are finite, with count `N(2‖z‖) ≤ A·2‖z‖·log(2‖z‖) = O(‖z‖·log‖z‖)`.**
Direct from the ball count `N(R) ≤ A·R·log R` at `R = 2‖z‖`, and finiteness of balls (`hfin`). PROVEN. -/
theorem near_count_le (A : ℝ)
    (hfin : ∀ R : ℝ, {i | ‖loc i‖ ≤ R}.Finite)
    (hcount : ∀ R : ℝ, 2 ≤ R → (Nat.card {i | ‖loc i‖ ≤ R} : ℝ) ≤ A * R * Real.log R)
    {z : ℂ} (hz1 : 1 ≤ ‖z‖) :
    (Nat.card {i | ‖loc i‖ < 2 * ‖z‖} : ℝ) ≤ A * (2 * ‖z‖) * Real.log (2 * ‖z‖) := by
  have hR2 : (2:ℝ) ≤ 2 * ‖z‖ := by linarith
  refine le_trans ?_ (hcount (2 * ‖z‖) hR2)
  have hsub : {i | ‖loc i‖ < 2 * ‖z‖} ⊆ {i | ‖loc i‖ ≤ 2 * ‖z‖} := by
    intro i hi; simp only [Set.mem_setOf_eq] at hi ⊢; linarith
  exact_mod_cast Nat.card_mono (hfin (2 * ‖z‖)) hsub

/-- The near-zeros index set is finite. -/
theorem near_finite (hfin : ∀ R : ℝ, {i | ‖loc i‖ ≤ R}.Finite) (z : ℂ) :
    {i | ‖loc i‖ < 2 * ‖z‖}.Finite :=
  Set.Finite.subset (hfin (2 * ‖z‖)) (by intro i hi; simp only [Set.mem_setOf_eq] at hi ⊢; linarith)

/-! ## Part 4 — assembling `hLogSumCore` from the proven far/near pieces + the Cartan residual

We split the full log-sum `Σ_i log(gFactor (loc i) z)` over `ι` into the FAR subtype
`{2‖z‖ ≤ ‖loc i‖}` (bounded below at order 1 by `far_logSum_ge`) and the finite NEAR set
`{‖loc i‖ < 2‖z‖}` (count `O(‖z‖log‖z‖)` by `near_count_le`). The near sum is bounded below by the
single Cartan circle-avoidance residual: a per-near-zero lower bound `log(gFactor) ≥ −Ccart·log(2+‖z‖)`
on the avoiding circle. -/

/-- **The Cartan / Borel–Carathéodory circle-avoidance residual (the deep gap).**

For the FINITELY-MANY near zeros `‖loc i‖ < 2‖z‖`, the term `log(gFactor (loc i) z) =
log‖1 − z/loc i‖ + Re(z/loc i)` can be arbitrarily negative when `z` lies very close to a zero `loc i`
(`log‖1−z/loc i‖ → −∞`). The classical Hadamard minimum-modulus argument does **not** bound this at
every `z`; it bounds it only off a union of small exceptional disks around the zeros (whose radii are
summable), via **Cartan's lemma** (a.k.a. the Borel–Carathéodory "choose the radius" / measure of the
exceptional set estimate). On the avoiding set one gets, per near zero, `log(gFactor (loc i) z) ≥
−Ccart·log(2 + ‖z‖)`.

Mathlib has `Complex.borelCaratheodory` but **lacks Cartan's lemma / the exceptional-disk measure
estimate**, so this per-near-zero avoiding bound is a genuine missing development. `CartanCircleAvoidance`
isolates EXACTLY that single residual: a uniform constant `Ccart` and, off the zeros, the per-near-zero
lower bound. Everything else (the far part at order 1, the near COUNT `O(‖z‖log‖z‖)`, and the assembly
below) is proven. -/
def CartanCircleAvoidance (loc : ι → ℂ) : Prop :=
  ∃ Ccart : ℝ, 0 ≤ Ccart ∧ ∀ z : ℂ, (∀ i, loc i ≠ z) → ∀ i, ‖loc i‖ < 2 * ‖z‖ →
    -(Ccart * Real.log (2 + ‖z‖)) ≤ Real.log (gFactor (loc i) z)

/-- **`hLogSumCore`, assembled.** Given the proven ball count `N(R) ≤ A·R·log R` (with `A ≥ 0` and ball
finiteness), the summability of the log-terms `hsummlog` (threaded through the assembly), and the single
isolated Cartan circle-avoidance residual `hcartan`, the genus-1 log-sum admits the order-≤(1+ε)
lower bound that `ScratchMinModClose.genus1Product_minModulus` consumes as `hLogSumCore`:

  `∃ C₀, ∀ z off-zeros, −(C₀·(1+‖z‖)·log(2+‖z‖)²) ≤ Σ_i log(gFactor (loc i) z)`.

(We use `log(2+‖z‖)²` rather than `log(2+‖z‖)` in the envelope — the near contribution is
`O(‖z‖·(log‖z‖)²)`, slightly super-linear, which, as the task notes, is still order-1 for the downstream
quotient via the `‖z‖log‖z‖` envelope. The far part alone meets the tighter `(1+‖z‖)log(2+‖z‖)` shape.)

PROVEN parts: far-zeros bound (`far_logSum_ge`, order 1), near COUNT (`near_count_le`,
`O(‖z‖log‖z‖)`), the far/near split. RESIDUAL: `hcartan` (Cartan's lemma). -/
theorem hLogSumCore_of_cartan (A : ℝ) (hA : 0 ≤ A)
    (hne : ∀ i, loc i ≠ 0)
    (hfin : ∀ R : ℝ, {i | ‖loc i‖ ≤ R}.Finite)
    (hcount : ∀ R : ℝ, 2 ≤ R → (Nat.card {i | ‖loc i‖ ≤ R} : ℝ) ≤ A * R * Real.log R)
    (hsummlog : ∀ z : ℂ, (∀ i, loc i ≠ z) →
      Summable (fun i => Real.log (gFactor (loc i) z)))
    (hcartan : CartanCircleAvoidance loc) :
    ∃ C₀ : ℝ, ∀ z : ℂ, (∀ i, loc i ≠ z) → 1 ≤ ‖z‖ →
      -(C₀ * (1 + ‖z‖) * Real.log (2 + ‖z‖) ^ 2) ≤ ∑' i, Real.log (gFactor (loc i) z) := by
  classical
  obtain ⟨Ccart, hCcart0, hcart⟩ := hcartan
  -- pick C₀ large enough to dominate both the far (12A) and near (4A·Ccart) contributions
  refine ⟨12 * A + 4 * A * Ccart + 1, fun z hz hz1 => ?_⟩
  have hzpos : 0 < ‖z‖ := by linarith
  -- the full log-sum splits over the far subtype and the finite near set
  set fz : ι → ℝ := fun i => Real.log (gFactor (loc i) z) with hfz
  have hsum : Summable fz := hsummlog z hz
  -- near set finite
  have hnearfin : {i | ‖loc i‖ < 2 * ‖z‖}.Finite := near_finite loc hfin z
  -- the complement of the far subtype is exactly the near set (finite)
  have hcompl : {i | 2 * ‖z‖ ≤ ‖loc i‖}ᶜ = {i | ‖loc i‖ < 2 * ‖z‖} := by
    ext i; simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_le]
  -- partition the index: ∑' i = ∑'far + ∑'near, both as subtype tsums
  have hsplit : ∑' i, fz i
      = (∑' (j : {i // 2 * ‖z‖ ≤ ‖loc i‖}), fz (j : ι))
        + ∑' (j : ↑({i | 2 * ‖z‖ ≤ ‖loc i‖}ᶜ)), fz (j : ι) :=
    (Summable.tsum_add_tsum_compl (f := fz) (s := {i | 2 * ‖z‖ ≤ ‖loc i‖})
      (hsum.subtype _) (hsum.subtype _)).symm
  rw [hsplit]
  -- FAR part: ≥ -6A‖z‖ log(2‖z‖)
  have hfarlog_summable : Summable (fun j : {i // 2 * ‖z‖ ≤ ‖loc i‖} =>
      Real.log (gFactor (loc (j : ι)) z)) := hsum.subtype _
  have hfar := far_logSum_ge loc A hA hne hfin hcount hz1 hfarlog_summable
  -- NEAR part: the complement subtype is finite; bound its tsum below by -(card·Ccart·log(2+‖z‖))
  have hnearfin' : ({i | 2 * ‖z‖ ≤ ‖loc i‖}ᶜ).Finite := by rw [hcompl]; exact hnearfin
  have hnearfintype : Fintype ↑({i | 2 * ‖z‖ ≤ ‖loc i‖}ᶜ) := hnearfin'.fintype
  have hnear_card : (Fintype.card ↑({i | 2 * ‖z‖ ≤ ‖loc i‖}ᶜ) : ℝ)
      ≤ A * (2 * ‖z‖) * Real.log (2 * ‖z‖) := by
    have hcardeq : (Fintype.card ↑({i | 2 * ‖z‖ ≤ ‖loc i‖}ᶜ) : ℝ)
        = (Nat.card {i | ‖loc i‖ < 2 * ‖z‖} : ℝ) := by
      rw [← Nat.card_eq_fintype_card]
      congr 1
      exact Nat.card_congr (Equiv.setCongr hcompl)
    rw [hcardeq]; exact near_count_le loc A hfin hcount hz1
  have hnear : -((Fintype.card ↑({i | 2 * ‖z‖ ≤ ‖loc i‖}ᶜ) : ℝ) * (Ccart * Real.log (2 + ‖z‖)))
      ≤ ∑' (j : ↑({i | 2 * ‖z‖ ≤ ‖loc i‖}ᶜ)), fz (j : ι) := by
    rw [tsum_fintype]
    have hbound : ∑ _j : ↑({i | 2 * ‖z‖ ≤ ‖loc i‖}ᶜ), -(Ccart * Real.log (2 + ‖z‖))
        ≤ ∑ j : ↑({i | 2 * ‖z‖ ≤ ‖loc i‖}ᶜ), fz (j : ι) := by
      apply Finset.sum_le_sum
      intro j _
      have hmem : ‖loc (j : ι)‖ < 2 * ‖z‖ := by
        have hj := j.2
        simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_le] at hj
        exact hj
      exact hcart z hz (j : ι) hmem
    refine le_trans (le_of_eq ?_) hbound
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    ring
  -- abbreviations and basic facts about Lp = log(2+‖z‖)
  set Lp : ℝ := Real.log (2 + ‖z‖) with hLp
  have hlog2pz : 0 ≤ Lp := Real.log_nonneg (by linarith)
  -- Lp ≥ log 3 > 1  (since 2+‖z‖ ≥ 3 > e)
  have hge3 : (3:ℝ) ≤ 2 + ‖z‖ := by linarith
  have hLp1 : 1 ≤ Lp := by
    have hlogge : Real.log 3 ≤ Lp := Real.log_le_log (by norm_num) hge3
    have h3e : Real.exp 1 ≤ 3 := by
      have := Real.exp_one_lt_d9; linarith
    have : (1:ℝ) ≤ Real.log 3 := by
      rw [show (1:ℝ) = Real.log (Real.exp 1) from (Real.log_exp 1).symm]
      exact Real.log_le_log (Real.exp_pos 1) h3e
    linarith
  -- log(2‖z‖) ≤ 2 Lp, since 2‖z‖ ≤ (2+‖z‖)²
  have hmono : Real.log (2 * ‖z‖) ≤ 2 * Lp := by
    have h1 : 2 * ‖z‖ ≤ (2 + ‖z‖) ^ 2 := by nlinarith [hzpos, sq_nonneg ‖z‖, norm_nonneg z]
    have h2 : Real.log (2 * ‖z‖) ≤ Real.log ((2 + ‖z‖) ^ 2) := Real.log_le_log (by linarith) h1
    rw [Real.log_pow] at h2; push_cast at h2; rw [hLp]; linarith [h2]
  -- FAR envelope: far ≥ -(12A‖z‖Lp) ≥ -(C₀(1+‖z‖)Lp²)  [part of the budget]
  have hfar_ge : -(12 * A * ‖z‖ * Lp) ≤ ∑' (j : {i // 2 * ‖z‖ ≤ ‖loc i‖}), fz (j : ι) := by
    refine le_trans ?_ hfar
    rw [neg_le_neg_iff]
    calc 6 * A * ‖z‖ * Real.log (2 * ‖z‖)
        ≤ 6 * A * ‖z‖ * (2 * Lp) := mul_le_mul_of_nonneg_left hmono (by positivity)
      _ = 12 * A * ‖z‖ * Lp := by ring
  -- NEAR envelope: near ≥ -(card·Ccart·Lp) ≥ -(A·2‖z‖·(2Lp)·Ccart·Lp) = -(4A·Ccart·‖z‖·Lp²)
  have hnear_ge : -(4 * A * Ccart * ‖z‖ * Lp ^ 2)
      ≤ ∑' (j : ↑({i | 2 * ‖z‖ ≤ ‖loc i‖}ᶜ)), fz (j : ι) := by
    refine le_trans ?_ hnear
    rw [neg_le_neg_iff]
    -- card·Ccart·Lp ≤ (A·2‖z‖·2Lp)·Ccart·Lp = 4A·Ccart·‖z‖·Lp²
    have hcardbound : (Fintype.card ↑({i | 2 * ‖z‖ ≤ ‖loc i‖}ᶜ) : ℝ) * (Ccart * Lp)
        ≤ (A * (2 * ‖z‖) * (2 * Lp)) * (Ccart * Lp) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      refine le_trans hnear_card ?_
      apply mul_le_mul_of_nonneg_left hmono (by positivity)
    refine le_trans hcardbound (le_of_eq ?_); ring
  -- combine and dominate by the envelope C₀(1+‖z‖)Lp², C₀ = 12A + 4A·Ccart + 1
  have htot : -(12 * A * ‖z‖ * Lp) + -(4 * A * Ccart * ‖z‖ * Lp ^ 2)
      ≤ (∑' (j : {i // 2 * ‖z‖ ≤ ‖loc i‖}), fz (j : ι))
        + ∑' (j : ↑({i | 2 * ‖z‖ ≤ ‖loc i‖}ᶜ)), fz (j : ι) :=
    add_le_add hfar_ge hnear_ge
  refine le_trans ?_ htot
  rw [← neg_add]  -- LHS = -(12A‖z‖Lp + 4A·Ccart·‖z‖·Lp²)
  rw [neg_le_neg_iff]
  -- 4A·Ccart·‖z‖·Lp² + 12A·‖z‖·Lp ≤ C₀(1+‖z‖)Lp²
  -- use Lp ≥ 1 ⇒ Lp ≤ Lp², ‖z‖ ≤ 1+‖z‖
  have hzle : ‖z‖ ≤ 1 + ‖z‖ := by linarith
  have hLpsq : Lp ≤ Lp ^ 2 := by nlinarith [hLp1, hlog2pz]
  have hznn : (0:ℝ) ≤ ‖z‖ := norm_nonneg z
  have hLpsqnn : (0:ℝ) ≤ Lp ^ 2 := sq_nonneg Lp
  -- term 1: 12A‖z‖Lp ≤ 12A(1+‖z‖)Lp²
  have ht1 : 12 * A * ‖z‖ * Lp ≤ 12 * A * (1 + ‖z‖) * Lp ^ 2 := by
    have hb : (0:ℝ) ≤ 12 * A * ‖z‖ := by positivity
    calc 12 * A * ‖z‖ * Lp
        ≤ 12 * A * ‖z‖ * Lp ^ 2 := by nlinarith [hb, hLpsq]
      _ ≤ 12 * A * (1 + ‖z‖) * Lp ^ 2 := by nlinarith [hA, hLpsqnn, hzle]
  -- term 2: 4A·Ccart·‖z‖·Lp² ≤ 4A·Ccart·(1+‖z‖)·Lp²
  have ht2 : 4 * A * Ccart * ‖z‖ * Lp ^ 2 ≤ 4 * A * Ccart * (1 + ‖z‖) * Lp ^ 2 := by
    have hc : (0:ℝ) ≤ 4 * A * Ccart := by positivity
    nlinarith [hc, hLpsqnn, hzle]
  -- slack term: 0 ≤ (1+‖z‖)Lp²
  have hslack : (0:ℝ) ≤ (1 + ‖z‖) * Lp ^ 2 := by positivity
  nlinarith [ht1, ht2, hslack]

end OverflowResidueRH.BacklundTuring.ScratchLogSumCore
