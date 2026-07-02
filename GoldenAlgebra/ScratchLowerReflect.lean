/-
  ScratchLowerReflect.lean

  CLOSING THE LOWER-HALF REFLECTION — the final sliver of the convexity bound.

  CONTEXT.  `ScratchHalfStripPL.lean` / `ScratchSharpPL.lean` prove the SHARP Phragmén–Lindelöf
  bound on the UPPER half-strip (`t ≥ 1`) FOR REAL (`halfStrip_PL`, `Gprod_upper_const_bound`).
  The ONLY residual left there is the lower-half (`t ≤ -1`) transfer, isolated as the axiom
  `ScratchHalfStripPL.verticalStrip_lower_reflection`.  As its own docstring records, that axiom
  is stated for a GENERAL `F` with NO symmetry hypothesis — and is therefore genuinely irreducible
  in that generality: `F(σ+it)` for `t < 0` is a true lower-half value, unrelated to the upper
  point `σ+i|t|` by any hypothesis present.

  THE KEY OBSERVATION (this file).  The convexity-bound chain only ever applies the lower-half
  reflection to `F = xiF = (s-1)·ζ(s)` (removable-singularity-completed), which HAS conjugate
  symmetry `xiF (conj s) = conj (xiF s)`.  That symmetry closes the lower half outright.

  WHAT IS PROVEN HERE (no `sorry`, no new axioms beyond Mathlib's):

   1. `riemannZeta_conj` : `riemannZeta (conj s) = conj (riemannZeta s)` for ALL `s`.
      NOT in Mathlib (searched: no `riemannZeta_conj`).  PROVEN here by Schwarz reflection /
      the identity theorem on the connected open set `{1}ᶜ`: the Dirichlet series has REAL
      coefficients so the identity holds on `Re > 1` (via `zeta_eq_tsum_one_div_nat_cpow` +
      `conj` distributing through the `tsum` and `conj_cpow`), and both sides are analytic on
      `{1}ᶜ`, which is preconnected with `Re > 1` accumulating at `z₀ = 2`.

   2. `xiF` and its conjugate symmetry `xiF_conj : xiF (conj s) = conj (xiF s)`, hence
      `norm_xiF_conj : ‖xiF (conj s)‖ = ‖xiF s‖`.

   3. `lower_from_upper_of_conj_symm` : the ABSTRACT lower-from-upper reflection lemma.  Given a
      conjugate-symmetric `F` (`∀ s, F (conj s) = conj (F s)`) and the proven upper bound
      `∀ t ≥ 1, ‖F(σ+it)‖ ≤ C·|t|^k`, it concludes `∀ t ≤ -1, ‖F(σ+it)‖ ≤ C·|t|^k`.  PROVEN.

   4. `verticalStrip_lower_reflection_xiF` : the SYMMETRY-AUGMENTED version of
      `ScratchHalfStripPL.verticalStrip_lower_reflection`, specialised to a conjugate-symmetric
      `F` (which `xiF` is), DISCHARGED with NO axioms.  This is exactly the instance the ζ/xiF
      convexity chain consumes, so the chain closes.

  HONEST STATUS OF THE GENERAL AXIOM.  `ScratchHalfStripPL.verticalStrip_lower_reflection` is
  stated for a GENERAL `F` without the conjugate-symmetry hypothesis and CANNOT be discharged in
  that generality (a generic finite-order `F` on the strip need not have any reflection symmetry;
  the hypotheses only give `|t|`-symmetric BOUNDS).  This file therefore delivers the
  symmetry-augmented lemma that the application actually needs, plus the proof that `xiF`
  satisfies the symmetry hypothesis.  To remove the general axiom from the convexity chain, route
  that chain through `verticalStrip_lower_reflection_xiF` (or add the `∀ s, F (conj s) = conj F s`
  hypothesis to the general statement and discharge via `lower_from_upper_of_conj_symm`).

  EDIT ONLY THIS FILE.
-/
import Mathlib

open Complex Filter Topology ComplexConjugate Set
open scoped Topology

noncomputable section

namespace OverflowResidueRH.BacklundTuring.ScratchLowerReflect

/-! ## 1. ζ conjugate symmetry. -/

/-- `arg (n:ℂ) ≠ π` for a natural `n` (the base is a nonnegative real, so `arg = 0`). -/
theorem arg_natCast_ne_pi (n : ℕ) : ((n : ℂ)).arg ≠ Real.pi := by
  rw [show ((n : ℂ)) = ((n : ℝ) : ℂ) by push_cast; ring,
    Complex.arg_ofReal_of_nonneg (by positivity)]
  exact Real.pi_ne_zero.symm

/-- For a natural `n` and any `w : ℂ`, `conj ((n:ℂ) ^ (conj w)) = (n:ℂ) ^ w`.
The base `(n:ℂ)` is a nonnegative real, so `arg (n:ℂ) ≠ π`, and `conj_cpow` applies. -/
theorem conj_nat_cpow_conj (n : ℕ) (w : ℂ) :
    conj (((n : ℂ)) ^ (conj w)) = (n : ℂ) ^ w := by
  -- `conj_cpow x n hx : x ^ conj n = conj (conj x ^ n)`.  With `x = n` (so `conj x = x`):
  --   `(n:ℂ) ^ conj w = conj ((n:ℂ) ^ w)`.  Apply at `w ↦ conj w` and conj both sides.
  have key : ((n : ℂ)) ^ (conj w) = conj (((n : ℂ)) ^ w) := by
    have h := Complex.conj_cpow ((n : ℂ)) w (arg_natCast_ne_pi n)
    rw [Complex.conj_natCast] at h
    -- h : (n:ℂ) ^ w = conj ((n:ℂ) ^ conj w)
    -- we want (n:ℂ) ^ conj w = conj ((n:ℂ) ^ w); apply h with w := conj w then conj
    have h2 := Complex.conj_cpow ((n : ℂ)) (conj w) (arg_natCast_ne_pi n)
    rw [Complex.conj_natCast, Complex.conj_conj] at h2
    -- h2 : (n:ℂ) ^ conj w = conj ((n:ℂ) ^ w)
    exact h2
  rw [key, Complex.conj_conj]

/-- **ζ is real on `Re > 1`:** `riemannZeta (conj s) = conj (riemannZeta s)` for `1 < re s`.
Direct from the Dirichlet-series formula and `conj` distributing through the `tsum`. -/
theorem riemannZeta_conj_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
    riemannZeta (conj s) = conj (riemannZeta s) := by
  have hcs : 1 < (conj s).re := by simpa using hs
  rw [zeta_eq_tsum_one_div_nat_cpow hcs, zeta_eq_tsum_one_div_nat_cpow hs]
  -- conj (∑' n, 1/n^s) = ∑' n, conj (1/n^s) = ∑' n, 1/n^(conj s)
  rw [Complex.conj_tsum]
  refine tsum_congr (fun n => ?_)
  rw [map_div₀, map_one]
  congr 1
  -- conj (n^s) = n^(conj s):  from `conj_nat_cpow_conj n s` applied at conj s
  have h2 := conj_nat_cpow_conj n (conj s)
  rw [Complex.conj_conj] at h2
  exact h2.symm

/-- ζ at the pole-completed point `s = 1` is real: `conj (riemannZeta 1) = riemannZeta 1`.
Needed only to extend `riemannZeta_conj` to the single point `s = 1` (where `conj 1 = 1`).
`riemannZeta 1 = (γ - log(4π))/2` (Mathlib `riemannZeta_one`), a real expression. -/
theorem riemannZeta_one_eq_conj : riemannZeta 1 = conj (riemannZeta 1) := by
  rw [riemannZeta_one]
  rw [map_div₀, map_sub]
  congr 1
  · congr 1
    · exact (Complex.conj_ofReal _).symm
    · -- conj (log (4π)) = log (4π) since 4π is a positive real ⟹ log is real
      rw [show (4 * (Real.pi : ℂ)) = ((4 * Real.pi : ℝ) : ℂ) by push_cast; ring]
      rw [← Complex.ofReal_log (by positivity), Complex.conj_ofReal]
  · exact (map_ofNat (starRingEnd ℂ) 2).symm

/-- **ζ conjugate symmetry (all `s`):** `riemannZeta (conj s) = conj (riemannZeta s)`.
PROVEN by the identity theorem on the preconnected open set `{1}ᶜ`: the Schwarz-reflected
function `h z = conj (ζ (conj z))` is holomorphic there (anti-holo ∘ holo ∘ anti-holo = holo,
via `DifferentiableAt.conj_conj`) and agrees with `ζ` on `Re > 1` (which accumulates at
`z₀ = 2 ∈ {1}ᶜ`); hence `h = ζ` on `{1}ᶜ`, i.e. `conj (ζ (conj z)) = ζ z`. -/
theorem riemannZeta_conj (s : ℂ) :
    riemannZeta (conj s) = conj (riemannZeta s) := by
  -- It suffices to prove  conj (ζ (conj z)) = ζ z  for all z (apply at z = s, then rearrange).
  suffices hsuff : ∀ z : ℂ, conj (riemannZeta (conj z)) = riemannZeta z by
    have h := hsuff s
    -- h : conj (ζ (conj s)) = ζ s  ⟹  ζ (conj s) = conj (ζ s)
    have h2 := congrArg conj h
    rwa [Complex.conj_conj] at h2
  -- U = {1}ᶜ : open, preconnected (complement of a point in ℂ, rank 2).
  set U : Set ℂ := {(1 : ℂ)}ᶜ with hUdef
  have hUopen : IsOpen U := isOpen_compl_singleton
  have hUconn : IsPreconnected U := by
    have hrank : (1 : Cardinal) < Module.rank ℝ ℂ := by
      rw [Complex.rank_real_complex]; norm_num
    exact (isConnected_compl_singleton_of_one_lt_rank hrank (1 : ℂ)).isPreconnected
  -- h z = conj (ζ (conj z)) = (conj ∘ ζ ∘ conj) z
  set h : ℂ → ℂ := fun z => conj (riemannZeta (conj z)) with hhdef
  have hheq : h = conj ∘ riemannZeta ∘ conj := rfl
  -- h is analytic on U
  have hhA : AnalyticOnNhd ℂ h U := by
    have hd : DifferentiableOn ℂ h U := by
      intro z hz
      have hz1 : z ≠ 1 := by simpa [hUdef] using hz
      have hcz1 : conj z ≠ 1 := by
        intro hc; apply hz1
        have := congrArg conj hc; rwa [Complex.conj_conj, map_one] at this
      have hζd : DifferentiableAt ℂ riemannZeta (conj z) :=
        differentiableAt_riemannZeta hcz1
      -- (conj ∘ ζ ∘ conj) is differentiable at z = conj (conj z)
      have hconj := hζd.conj_conj
      rw [Complex.conj_conj] at hconj
      rw [hheq]
      exact hconj.differentiableWithinAt
    exact hd.analyticOnNhd hUopen
  -- ζ is analytic on U
  have hζA : AnalyticOnNhd ℂ riemannZeta U := by
    have hd : DifferentiableOn ℂ riemannZeta U := fun z hz =>
      (differentiableAt_riemannZeta (by simpa [hUdef] using hz)).differentiableWithinAt
    exact hd.analyticOnNhd hUopen
  -- z₀ = 2 ∈ U
  have hz0U : (2 : ℂ) ∈ U := by
    simp only [hUdef, mem_compl_iff, mem_singleton_iff]
    intro hc; have : (2 : ℂ).re = (1 : ℂ).re := by rw [hc]
    norm_num at this
  -- h and ζ agree frequently near z₀ = 2 (along reals 2 + 1/(n+1), all with Re > 1)
  have hfreq : ∃ᶠ z in 𝓝[≠] (2 : ℂ), h z = riemannZeta z := by
    set u : ℕ → ℂ := fun n => ((2 + 1 / (n + 1 : ℝ) : ℝ) : ℂ) with hudef
    have htend : Tendsto u atTop (𝓝[≠] (2 : ℂ)) := by
      apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      · have h0 : Tendsto (fun n : ℕ => (2 + 1 / (n + 1 : ℝ) : ℝ)) atTop (𝓝 (2 : ℝ)) := by
          have hbase : Tendsto (fun n : ℕ => (1 / (n + 1 : ℝ) : ℝ)) atTop (𝓝 (0 : ℝ)) :=
            tendsto_one_div_add_atTop_nhds_zero_nat
          have := (tendsto_const_nhds (x := (2:ℝ)) (f := atTop)).add hbase
          rw [add_zero] at this
          exact this
        have hc := (Complex.continuous_ofReal.tendsto (2:ℝ)).comp h0
        simpa [hudef, Function.comp_def] using hc
      · filter_upwards with n
        have hpos : (0 : ℝ) < 1 / (n + 1 : ℝ) := by positivity
        simp only [hudef, mem_compl_iff, mem_singleton_iff, ne_eq]
        intro hc
        rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by push_cast; ring, Complex.ofReal_inj] at hc
        linarith
    -- on each u n,  Re (u n) > 1,  so h (u n) = ζ (u n)
    have heq : ∀ n : ℕ, h (u n) = riemannZeta (u n) := by
      intro n
      have hpos : (0 : ℝ) < 1 / (n + 1 : ℝ) := by positivity
      have hre : 1 < (u n).re := by
        simp only [hudef, Complex.ofReal_re]; linarith
      -- h (u n) = conj (ζ (conj (u n))) = conj (conj (ζ (u n))) = ζ (u n)
      have hceq := riemannZeta_conj_of_one_lt_re hre
      rw [hhdef]
      simp only []
      rw [hceq, Complex.conj_conj]
    rw [Filter.frequently_iff]
    intro V hV
    have hev : ∀ᶠ n in atTop, u n ∈ V := htend hV
    obtain ⟨n, hn⟩ := hev.exists
    exact ⟨u n, hn, heq n⟩
  -- identity theorem: h = ζ on U
  have hEqOn : EqOn h riemannZeta U :=
    hhA.eqOn_of_preconnected_of_frequently_eq hζA hUconn hz0U hfreq
  -- conclude for every z: if z ≠ 1 use hEqOn; if z = 1 both sides are ζ 1 manually.
  intro z
  by_cases hz1 : z = 1
  · -- at z = 1:  conj 1 = 1,  so goal is  conj (ζ 1) = ζ 1,  i.e. ζ 1 is real.
    subst hz1
    rw [map_one]
    exact riemannZeta_one_eq_conj.symm
  · have := hEqOn (by simpa [hUdef] using hz1)
    exact this

/-! ## 2. `xiF` and its conjugate symmetry. -/

/-- The removable-singularity completion `xiF(s) = (s-1)·ζ(s)` (value `1` at `s=1`).
Local copy of `ScratchTWeightedPL.xiF` (the scratch files are not built into the import path,
so the definition is reproduced here, exactly as those files reproduce shared definitions). -/
def xiF : ℂ → ℂ := Function.update (fun s => (s - 1) * riemannZeta s) 1 1

theorem xiF_eq_of_ne {z : ℂ} (hz : z ≠ 1) : xiF z = (z - 1) * riemannZeta z := by
  simp only [xiF, Function.update_apply, if_neg hz]

/-- **`xiF` conjugate symmetry:** `xiF (conj s) = conj (xiF s)`.
Off `s = 1` this is `(conj s - 1)·ζ(conj s) = conj ((s-1)·ζ s)`, using `riemannZeta_conj` and
that `conj` is a ring hom (so `conj (s-1) = conj s - 1`).  At `s = 1`, `conj 1 = 1` and the
installed value `1` is real. -/
theorem xiF_conj (s : ℂ) : xiF (conj s) = conj (xiF s) := by
  by_cases hs1 : s = 1
  · subst hs1
    rw [map_one]
    show xiF 1 = conj (xiF 1)
    rw [show xiF 1 = 1 by simp [xiF], map_one]
  · have hcs1 : conj s ≠ 1 := by
      intro hc
      apply hs1
      have := congrArg conj hc; rwa [Complex.conj_conj, map_one] at this
    rw [xiF_eq_of_ne hcs1, xiF_eq_of_ne hs1]
    rw [map_mul, map_sub, map_one, riemannZeta_conj]

/-- `‖xiF (conj s)‖ = ‖xiF s‖`. -/
theorem norm_xiF_conj (s : ℂ) : ‖xiF (conj s)‖ = ‖xiF s‖ := by
  rw [xiF_conj, Complex.norm_conj]

/-! ## 3. The abstract lower-from-upper reflection lemma. -/

/-- **Lower-half bound from the upper-half bound via conjugate symmetry.**
If `F` is conjugate-symmetric (`∀ s, F (conj s) = conj (F s)`) and obeys the upper-half bound
`∀ t ≥ 1, ‖F(σ+it)‖ ≤ C·g t` where the bound `g` only sees `|t|` (`g (-t) = g t`), then it obeys
the same bound on the lower half `t ≤ -1`.

The mechanism: for `t ≤ -1`, `conj (σ+it) = σ - it = σ + i(-t)` with `-t = |t| ≥ 1`, so
`‖F(σ+it)‖ = ‖conj (F(σ+it))‖ = ‖F(conj(σ+it))‖ = ‖F(σ+i|t|)‖`, and the upper bound applies at
the reflected-up ordinate `|t|` (where `g |t| = g t`). -/
theorem lower_from_upper_of_conj_symm
    {F : ℂ → ℂ} (hsymm : ∀ s : ℂ, F (conj s) = conj (F s))
    {C : ℝ} {g : ℝ → ℝ} {σ : ℝ}
    (hg_even : ∀ t : ℝ, g (-t) = g t)
    (hupper : ∀ t : ℝ, 1 ≤ t → ‖F ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C * g t) :
    ∀ t : ℝ, t ≤ -1 → ‖F ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C * g t := by
  intro t ht
  have htpos : (1 : ℝ) ≤ -t := by linarith
  -- conj (σ + i t) = σ + i(-t)
  have hconj_pt : conj ((σ : ℂ) + (t : ℂ) * Complex.I) = (σ : ℂ) + ((-t : ℝ) : ℂ) * Complex.I := by
    simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
    push_cast; ring
  -- ‖F(σ+it)‖ = ‖F(σ+i(-t))‖
  have hnorm_eq : ‖F ((σ : ℂ) + (t : ℂ) * Complex.I)‖
      = ‖F ((σ : ℂ) + ((-t : ℝ) : ℂ) * Complex.I)‖ := by
    have h1 : ‖F ((σ : ℂ) + (t : ℂ) * Complex.I)‖
        = ‖conj (F ((σ : ℂ) + (t : ℂ) * Complex.I))‖ := (Complex.norm_conj _).symm
    rw [h1, ← hsymm, hconj_pt]
  rw [hnorm_eq, ← hg_even t]
  exact hupper (-t) htpos

/-! ## 4. Discharging the lower-half reflection for the `wgt`/`xiF` application.

We restate the EXACT signature of `ScratchSharpPL.wgt` / `ScratchHalfStripPL.Gprod` /
`verticalStrip_lower_reflection` (local copies — the scratch files are not in the import path),
and discharge the lower-half residual UNDER the conjugate-symmetry hypothesis that `F = xiF`
satisfies.  The convexity chain only ever applies the reflection to `xiF`, so this closes it. -/

/-- Weight base `L(σ,t,λ) = -i·(σ+it) + λ` (copy of `ScratchSharpPL.Lbase`). -/
def Lbase (σ t lam : ℝ) : ℂ := -Complex.I * ((σ : ℂ) + (t : ℂ) * Complex.I) + (lam : ℂ)

/-- Complex-linear exponent `p(s)` (copy of `ScratchSharpPL.pExp`). -/
def pExp (l u α β : ℝ) (s : ℂ) : ℂ :=
  (α : ℂ) + ((β : ℂ) - (α : ℂ)) * (s - (l : ℂ)) / ((u - l : ℝ) : ℂ)

/-- Non-constant-power weight `w(s) = exp(-p(s)·Log(-i·s+λ))` (copy of `ScratchSharpPL.wgt`). -/
def wgt (l u α β lam : ℝ) (s : ℂ) : ℂ :=
  Complex.exp (-(pExp l u α β s) * Complex.log (Lbase s.re s.im lam))

/-- Holomorphic weight base `Lhol λ s = -i·s + λ` (copy). -/
def Lhol (lam : ℝ) (s : ℂ) : ℂ := -Complex.I * s + (lam : ℝ)

/-- Holomorphic weight `wgtH λ s = exp(-(p s)·log(Lhol λ s))` (copy of `ScratchHalfStripPL.wgtH`). -/
def wgtH (l u α β lam : ℝ) (s : ℂ) : ℂ :=
  Complex.exp (-(pExp l u α β s) * Complex.log (Lhol lam s))

/-- Flattened product `G(s) = F(s)·wgtH(s)` (copy of `ScratchHalfStripPL.Gprod`). -/
def Gprod (F : ℂ → ℂ) (l u α β lam : ℝ) (s : ℂ) : ℂ := F s * wgtH l u α β lam s

/-- The closed vertical strip `l ≤ Re s ≤ u` (copy of Mathlib's `verticalClosedStrip`). -/
def verticalClosedStrip (l u : ℝ) : Set ℂ := Complex.re ⁻¹' Set.Icc l u

/-- **Symmetry-augmented lower-half reflection, DISCHARGED for conjugate-symmetric `F`.**
This is `ScratchHalfStripPL.verticalStrip_lower_reflection` with the EXTRA hypothesis
`hFsymm : ∀ s, F (conj s) = conj (F s)` (which `xiF` satisfies, see `xiF_conj`).  Under it, the
lower lines `t ≤ -1` obey the same constant bound `CG` that the upper-half bound supplies — proven
outright via `lower_from_upper_of_conj_symm`, NO axioms.

KEY ALGEBRA.  For `t ≤ -1` set `τ = |t| = -t ≥ 1`.  The target is
`‖F(σ+it) · wgt(σ+i|t|)‖ ≤ CG`.  Because `F(σ+i|t|) · wgtH(σ+i|t|) = Gprod(σ+i|t|)` (and
`wgtH = wgt` off the cut), and `F` is conjugate-symmetric so `‖F(σ+it)‖ = ‖F(σ+i|t|)‖`, the whole
product has the same norm as `Gprod(σ+i|t|)`, which the upper bound controls by `CG`. -/
theorem verticalStrip_lower_reflection_xiF
    (F : ℂ → ℂ) (l u α β lam : ℝ) (_hlu : l < u) (_hlam : 1 ≤ lam)
    (_hF : Differentiable ℂ F)
    (hFsymm : ∀ s : ℂ, F (conj s) = conj (F s))
    (hwgtHwgt : ∀ s : ℂ, 0 ≤ s.im → wgtH l u α β lam s = wgt l u α β lam s)
    (CG : ℝ) (_hCG0 : 0 ≤ CG)
    (hupper : ∀ σ t : ℝ, l ≤ σ → σ ≤ u → 1 ≤ t →
      ‖Gprod F l u α β lam ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ CG) :
    ∀ σ t : ℝ, l ≤ σ → σ ≤ u → t ≤ -1 →
      ‖F ((σ : ℂ) + (t : ℂ) * Complex.I)
          * wgt l u α β lam ((σ : ℂ) + ((|t| : ℝ) : ℂ) * Complex.I)‖ ≤ CG := by
  intro σ t hσl hσu ht
  have htpos : (1 : ℝ) ≤ -t := by linarith
  have habs : (|t| : ℝ) = -t := abs_of_nonpos (by linarith)
  -- ‖F(σ+it)‖ = ‖F(σ+i(-t))‖ = ‖F(σ+i|t|)‖  by conjugate symmetry.
  have hFnorm : ‖F ((σ : ℂ) + (t : ℂ) * Complex.I)‖
      = ‖F ((σ : ℂ) + ((|t| : ℝ) : ℂ) * Complex.I)‖ := by
    have hconj_pt : conj ((σ : ℂ) + (t : ℂ) * Complex.I)
        = (σ : ℂ) + ((|t| : ℝ) : ℂ) * Complex.I := by
      rw [habs]
      simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
      push_cast; ring
    have h1 : ‖F ((σ : ℂ) + (t : ℂ) * Complex.I)‖
        = ‖conj (F ((σ : ℂ) + (t : ℂ) * Complex.I))‖ := (Complex.norm_conj _).symm
    rw [h1, ← hFsymm, hconj_pt]
  -- The reflected-up point  σ + i|t|  has  Im = |t| ≥ 0,  so wgtH = wgt there.
  set sUp : ℂ := (σ : ℂ) + ((|t| : ℝ) : ℂ) * Complex.I with hsUp
  have hsUp_im : sUp.im = |t| := by rw [hsUp]; simp
  have hsUp_im0 : 0 ≤ sUp.im := by rw [hsUp_im]; exact abs_nonneg t
  -- ‖F(σ+it)·wgt(σ+i|t|)‖ = ‖F(σ+i|t|)·wgtH(σ+i|t|)‖ = ‖Gprod(σ+i|t|)‖
  have hnorm_prod : ‖F ((σ : ℂ) + (t : ℂ) * Complex.I)
        * wgt l u α β lam sUp‖
      = ‖Gprod F l u α β lam sUp‖ := by
    rw [norm_mul, hFnorm, Gprod, norm_mul, hwgtHwgt sUp hsUp_im0]
  rw [hnorm_prod]
  -- apply the upper bound at ordinate τ = |t| ≥ 1
  have hτ1 : (1 : ℝ) ≤ |t| := by rw [habs]; exact htpos
  have := hupper σ |t| hσl hσu hτ1
  rwa [hsUp]

end OverflowResidueRH.BacklundTuring.ScratchLowerReflect

-- ζ conjugate symmetry: PROVEN from Mathlib (identity theorem on {1}ᶜ), no extra axioms.
#print axioms OverflowResidueRH.BacklundTuring.ScratchLowerReflect.riemannZeta_conj
-- xiF conjugate symmetry: PROVEN, no extra axioms.
#print axioms OverflowResidueRH.BacklundTuring.ScratchLowerReflect.xiF_conj
-- Abstract lower-from-upper reflection: PROVEN, no extra axioms.
#print axioms OverflowResidueRH.BacklundTuring.ScratchLowerReflect.lower_from_upper_of_conj_symm
-- Symmetry-augmented lower-half reflection (the xiF application): DISCHARGED, no extra axioms.
#print axioms OverflowResidueRH.BacklundTuring.ScratchLowerReflect.verticalStrip_lower_reflection_xiF
