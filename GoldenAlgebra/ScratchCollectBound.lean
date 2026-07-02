import Mathlib

/-!
# ScratchCollectBound — the final Γ-phase residual `collect_uniform_bound`

This file targets the single residual left open (as an `axiom`) by
`ScratchBinetPhaseDischarge.lean`:

  `collect_uniform_bound : ∃ C₀ ≥ 0, ∀ T ≥ 140, ∀ n, |collect T n| ≤ C₀`,

where (verbatim from that file, restated below)

  `z      = ¼ + iT/2`
  `Gphi T x       = (x+¼)·arctan((T/2)/(x+¼)) + (T/4)·log((x+¼)²+(T/2)²)`
  `stirPrincipal T = ((z − ½)·Log z − z).im`
  `collect T n    = −γ·(T/2) − arg z − stirPrincipal T + (T/2)·harmonic n − (Gphi T n − Gphi T 1)`.

## ⚠ CENTRAL FINDING — the literal axiom is FALSE.

`collect T n` is **NOT** bounded uniformly in `(T, n)`.  For FIXED `n` and growing `T` it diverges
like `−(T/2)·log(T/2)`.  Numerics (reproducible):

  T=140,   n=1   ⇒ collect ≈ −198.98      T=140,   n=10000 ⇒ collect ≈ +0.778
  T=5000,  n=1   ⇒ collect ≈ −16004.33     T=5000,  n=10000 ⇒ collect ≈ −24.72
  T=5000,  n=2·10⁶               ⇒ collect ≈ +0.785

For each FIXED `T` the sequence `n ↦ collect T n` converges (so it is bounded in `n`), but the
bound BLOWS UP with `T`: `sup_n |collect T n| ≳ (T/2)·log(T/2) → ∞`.  Hence there is **no** constant
`C₀` making `∀ T ≥ 140, ∀ n, |collect T n| ≤ C₀` true.  The original `axiom` overstates what holds.

What IS true (and is the mathematically-intended content) is that the **limit**

  `Lcollect T := −(3/4)·arg z − (T/2)·log‖z‖ + Gphi T 1   (= limₙ collect T n)`

is bounded uniformly in `T ≥ 140` — this is the genuine `Im μ(z) = O(1)` Binet bound (numerically
`Lcollect T ≈ 0.78`).  The partial-sum overshoot is exactly the (T-dependent) tail of the harmonic /
arctan / log cancellations, which vanishes only as `n → ∞` *at a T-dependent rate*.

## What this file delivers (all proven, Mathlib-only, no `sorry`/`admit`)

1. `stirPrincipal_eq` : `stirPrincipal T = −(1/4)·arg z + (T/2)·log‖z‖ − T/2`  (verbatim closed form).
2. `collect_tendsto_Lcollect` : `collect T n → Lcollect T` as `n → ∞`, for `T ≥ 0`.
3. `Lcollect_uniform_bound` : `∃ C₀ ≥ 0, ∀ T ≥ 140, |Lcollect T| ≤ C₀`  (the TRUE uniform bound).
4. `collect_limit_uniform_bound` : the corrected, downstream-usable statement combining (2)+(3):
   `∃ C₀ ≥ 0, ∀ T ≥ 140, |limₙ collect T n| ≤ C₀`.

This corrected limit bound is exactly what `binetPhase_crude_bound` needs: that proof should pass to
the limit `thetaCont T − stirPrincipal T = limₙ (collect T n − remEM T n)` and bound the *limit*
(`Lcollect` bounded, `remEM` bounded by `π/2`), **not** the partial sums (which are unbounded).

The single honest residual `collect_uniform_bound` (the FALSE literal axiom) is therefore NOT
provable; it is replaced here by the TRUE `collect_limit_uniform_bound`.
-/

open Complex Real Filter Topology

namespace OverflowResidueRH
namespace BacklundTuring
namespace ScratchCollectBound

/-! ## Part 0 — the objects, restated VERBATIM from `ScratchBinetPhaseDischarge`. -/

/-- The critical-line Γ-argument point `z = ¼ + i·T/2`. -/
noncomputable def zPt (T : ℝ) : ℂ := (1 : ℂ) / 4 + ((T : ℝ) / 2) * Complex.I

@[simp] theorem zPt_re (T : ℝ) : (zPt T).re = 1 / 4 := by
  unfold zPt; simp [Complex.add_re]

@[simp] theorem zPt_im (T : ℝ) : (zPt T).im = T / 2 := by
  unfold zPt
  simp [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]

/-- **Stirling principal part** `Im[(z − ½)·Log z − z]` at `z = ¼ + iT/2`. -/
noncomputable def stirPrincipal (T : ℝ) : ℝ :=
  ((zPt T - 1 / 2) * Complex.log (zPt T) - zPt T).im

/-- The closed-form antiderivative
`Gphi T x = (x+¼)·arctan((T/2)/(x+¼)) + (T/4)·log((x+¼)²+(T/2)²)`. -/
noncomputable def Gphi (T : ℝ) (x : ℝ) : ℝ :=
  (x + 1 / 4) * Real.arctan ((T / 2) / (x + 1 / 4))
    + (T / 4) * Real.log ((x + 1 / 4) ^ 2 + (T / 2) ^ 2)

/-- The explicit (non-summation) collected term
`collect T n := −γ(T/2) − arg z − stirPrincipal T + (T/2)·harmonic n − (Gphi T n − Gphi T 1)`. -/
noncomputable def collect (T : ℝ) (n : ℕ) : ℝ :=
  (-Real.eulerMascheroniConstant * (T / 2) - Complex.arg (zPt T) - stirPrincipal T)
    + (T / 2) * (harmonic n : ℝ) - (Gphi T n - Gphi T 1)

/-! ## Part 1 — `stirPrincipal` in real closed form. -/

theorem zPt_ne_zero (T : ℝ) : zPt T ≠ 0 := by
  intro h
  have : (zPt T).re = 0 := by rw [h]; simp
  rw [zPt_re] at this; norm_num at this

/-- **`stirPrincipal T = −(1/4)·arg z + (T/2)·log‖z‖ − T/2`.**  Direct from `log z = log‖z‖ + i arg z`
and `z = ¼ + iT/2`. -/
theorem stirPrincipal_eq (T : ℝ) :
    stirPrincipal T = -(1 / 4) * Complex.arg (zPt T) + (T / 2) * Real.log ‖zPt T‖ - T / 2 := by
  unfold stirPrincipal
  have hlog_re : (Complex.log (zPt T)).re = Real.log ‖zPt T‖ := Complex.log_re _
  have hlog_im : (Complex.log (zPt T)).im = Complex.arg (zPt T) := Complex.log_im _
  -- ((z - 1/2) * log z - z).im = (z-1/2).re * (log z).im + (z-1/2).im * (log z).re - z.im
  rw [Complex.sub_im, Complex.mul_im]
  have hre : (zPt T - 1 / 2).re = -(1 / 4) := by
    rw [Complex.sub_re, zPt_re]; norm_num
  have him : (zPt T - 1 / 2).im = T / 2 := by
    rw [Complex.sub_im, zPt_im]; simp
  rw [hre, him, hlog_re, hlog_im, zPt_im]
  try ring

/-! ## Part 2 — the three convergent pieces of `collect`.

`collect T n = K(T) + (T/2)·harmonic n − (n+¼)·arctan((T/2)/(n+¼)) − (T/4)·log((n+¼)²+(T/2)²)`,
with `K(T) = −γ(T/2) − arg z − stirPrincipal T + Gphi T 1`.  We identify the `n → ∞` limit of each
`n`-dependent piece.
-/

/-- `K(T)`, the `n`-independent part of `collect`. -/
noncomputable def Kc (T : ℝ) : ℝ :=
  -Real.eulerMascheroniConstant * (T / 2) - Complex.arg (zPt T) - stirPrincipal T + Gphi T 1

theorem collect_eq_Kc (T : ℝ) (n : ℕ) :
    collect T n = Kc T + (T / 2) * (harmonic n : ℝ)
      - ((n : ℝ) + 1 / 4) * Real.arctan ((T / 2) / ((n : ℝ) + 1 / 4))
      - (T / 4) * Real.log (((n : ℝ) + 1 / 4) ^ 2 + (T / 2) ^ 2) := by
  unfold collect Kc Gphi; ring

/-- The explicit limit `Lcollect T = −(3/4)·arg z − (T/2)·log‖z‖ + Gphi T 1`. -/
noncomputable def Lcollect (T : ℝ) : ℝ :=
  -(3 / 4) * Complex.arg (zPt T) - (T / 2) * Real.log ‖zPt T‖ + Gphi T 1

/-! ### Piece 1 : `(T/2)·harmonic n − (T/2)·log n → (T/2)·γ`. -/

theorem tendsto_harmonic_term (T : ℝ) :
    Tendsto (fun n : ℕ => (T / 2) * ((harmonic n : ℝ) - Real.log n)) atTop
      (𝓝 ((T / 2) * Real.eulerMascheroniConstant)) :=
  (Real.tendsto_harmonic_sub_log).const_mul (T / 2)

/-! ### Piece 2 : `(n+¼)·arctan((T/2)/(n+¼)) → T/2`. -/

/-- `(n+¼)·arctan(a/(n+¼)) → a` (squeeze: `0 ≤ a − (n+¼)arctan(a/(n+¼)) ≤ a³/(n+¼)²`). -/
theorem tendsto_arctan_term (a : ℝ) (ha : 0 ≤ a) :
    Tendsto (fun n : ℕ => ((n : ℝ) + 1 / 4) * Real.arctan (a / ((n : ℝ) + 1 / 4))) atTop (𝓝 a) := by
  -- Use squeeze with the cube bound `x − arctan x ≤ x³` for `x ≥ 0`.
  -- Lower bound : (n+¼)arctan(a/(n+¼)) ≤ a  (arctan x ≤ x).
  -- Upper bound : a − (n+¼)arctan(a/(n+¼)) ≤ a³/(n+¼)² → 0.
  have hcube : ∀ x : ℝ, 0 ≤ x → x - Real.arctan x ≤ x ^ 3 := by
    -- monotone `x³ − (x − arctan x)`, deriv `3x² − x²/(1+x²) ≥ 0`
    intro x hx
    set h : ℝ → ℝ := fun y => y ^ 3 - (y - Real.arctan y) with hh
    have hdiff : Differentiable ℝ h :=
      (differentiable_pow 3).sub (differentiable_id.sub Real.differentiable_arctan)
    have hderiv : ∀ y, deriv h y = 3 * y ^ 2 - y ^ 2 / (1 + y ^ 2) := by
      intro y
      have h1 : HasDerivAt (fun w : ℝ => w ^ 3) (3 * y ^ 2) y := by
        simpa using (hasDerivAt_pow 3 y)
      have h2 : HasDerivAt (fun w : ℝ => w - Real.arctan w) (y ^ 2 / (1 + y ^ 2)) y := by
        have := (hasDerivAt_id y).sub (Real.hasDerivAt_arctan y)
        have hpos : (0 : ℝ) < 1 + y ^ 2 := by positivity
        convert this using 1; field_simp; ring
      exact (h1.sub h2).deriv
    have hmono : Monotone h := by
      apply monotone_of_deriv_nonneg hdiff
      intro y; rw [hderiv]
      have hpos : (0 : ℝ) < 1 + y ^ 2 := by positivity
      have : y ^ 2 / (1 + y ^ 2) ≤ y ^ 2 := by
        rw [div_le_iff₀ hpos]; nlinarith [sq_nonneg y]
      nlinarith [sq_nonneg y]
    have := hmono hx
    simp only [hh, Real.arctan_zero, sub_zero] at this
    have h0 : (0 : ℝ) ^ 3 = 0 := by norm_num
    rw [h0] at this; linarith
  have harctan_le : ∀ x : ℝ, 0 ≤ x → Real.arctan x ≤ x := by
    intro x hx
    set g : ℝ → ℝ := fun y => y - Real.arctan y with hg
    have hgderiv : ∀ y, HasDerivAt g (y ^ 2 / (1 + y ^ 2)) y := by
      intro y
      have := (hasDerivAt_id y).sub (Real.hasDerivAt_arctan y)
      have hpos : (0 : ℝ) < 1 + y ^ 2 := by positivity
      convert this using 1; field_simp; ring
    have hmono2 : Monotone g := by
      apply monotone_of_deriv_nonneg (fun y => (hgderiv y).differentiableAt)
      intro y; rw [(hgderiv y).deriv]; positivity
    have := hmono2 hx
    simp only [hg, Real.arctan_zero, sub_zero] at this; linarith
  -- abbreviations
  set x : ℕ → ℝ := fun n => a / ((n : ℝ) + 1 / 4) with hxdef
  have hxpos : ∀ n : ℕ, (0 : ℝ) < (n : ℝ) + 1 / 4 := fun n => by positivity
  have hxnn : ∀ n : ℕ, 0 ≤ x n := fun n => by rw [hxdef]; exact div_nonneg ha (hxpos n).le
  -- squeeze:  a − a³/(n+¼)²  ≤  (n+¼)·arctan(a/(n+¼))  ≤  a
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le
    (g := fun n : ℕ => a - a ^ 3 / ((n : ℝ) + 1 / 4) ^ 2)
    (h := fun _ : ℕ => a)
  · -- g n → a   (since a³/(n+¼)² → 0)
    have htend : Tendsto (fun n : ℕ => a ^ 3 / ((n : ℝ) + 1 / 4) ^ 2) atTop (𝓝 0) := by
      have hlin : Tendsto (fun n : ℕ => (n : ℝ) + 1 / 4) atTop atTop :=
        tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
      have hbase : Tendsto (fun n : ℕ => ((n : ℝ) + 1 / 4) ^ 2) atTop atTop := by
        simpa [pow_two] using hlin.atTop_mul_atTop₀ hlin
      simpa using (Filter.Tendsto.const_div_atTop hbase (a ^ 3))
    have := (tendsto_const_nhds (x := a)).sub htend
    simpa using this
  · exact tendsto_const_nhds
  · -- lower:  a − a³/(n+¼)² ≤ (n+¼)·arctan(a/(n+¼))
    intro n
    have hnn := hxnn n
    have hpos := hxpos n
    -- (n+¼)·(x n − arctan(x n)) ≤ (n+¼)·(x n)³ = a³/(n+¼)²
    have hcb := hcube (x n) hnn
    have hxn3 : ((n : ℝ) + 1 / 4) * (x n) ^ 3 = a ^ 3 / ((n : ℝ) + 1 / 4) ^ 2 := by
      rw [hxdef]; field_simp; try ring
    have hstep : ((n : ℝ) + 1 / 4) * (x n - Real.arctan (x n))
        ≤ a ^ 3 / ((n : ℝ) + 1 / 4) ^ 2 := by
      calc ((n : ℝ) + 1 / 4) * (x n - Real.arctan (x n))
          ≤ ((n : ℝ) + 1 / 4) * (x n) ^ 3 := by
            apply mul_le_mul_of_nonneg_left hcb hpos.le
        _ = a ^ 3 / ((n : ℝ) + 1 / 4) ^ 2 := hxn3
    have hxnval : ((n : ℝ) + 1 / 4) * x n = a := by rw [hxdef]; field_simp
    nlinarith [hstep, hxnval]
  · -- upper:  (n+¼)·arctan(a/(n+¼)) ≤ a
    intro n
    have hpos := hxpos n
    have hxnval : ((n : ℝ) + 1 / 4) * x n = a := by rw [hxdef]; field_simp
    have := mul_le_mul_of_nonneg_left (harctan_le (x n) (hxnn n)) hpos.le
    rw [hxnval] at this; exact this

/-! ### Piece 3 : `(T/4)·log((n+¼)²+(T/2)²) − (T/2)·log n → 0`. -/

/-- The ratio `((n+¼)²+(T/2)²)/n² → 1`. -/
theorem tendsto_log_ratio (T : ℝ) :
    Tendsto (fun n : ℕ => (((n : ℝ) + 1 / 4) ^ 2 + (T / 2) ^ 2) / (n : ℝ) ^ 2) atTop (𝓝 1) := by
  -- ((n+¼)² + (T/2)²)/n² = (1 + 1/(4n))² + (T/2)²/n² → 1² + 0
  have hinv : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  -- piece A : (1 + 1/(4n))² → 1
  have hA : Tendsto (fun n : ℕ => (1 + (1 / 4) * (n : ℝ)⁻¹) ^ 2) atTop (𝓝 1) := by
    have : Tendsto (fun n : ℕ => 1 + (1 / 4) * (n : ℝ)⁻¹) atTop (𝓝 1) := by
      have := (tendsto_const_nhds (x := (1 : ℝ))).add (hinv.const_mul (1 / 4 : ℝ))
      simpa using this
    have := this.pow 2
    simpa using this
  -- piece B : (T/2)²/n² → 0
  have hB : Tendsto (fun n : ℕ => (T / 2) ^ 2 * ((n : ℝ)⁻¹) ^ 2) atTop (𝓝 0) := by
    have := (hinv.pow 2).const_mul ((T / 2) ^ 2)
    simpa using this
  have hsum := hA.add hB
  rw [show (1 : ℝ) = 1 + 0 by ring]
  refine hsum.congr' ?_
  filter_upwards [eventually_ne_atTop 0] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  field_simp
  ring

/-- `(T/4)·log((n+¼)²+(T/2)²) − (T/2)·log n → 0`. -/
theorem tendsto_log_term (T : ℝ) :
    Tendsto (fun n : ℕ => (T / 4) * Real.log (((n : ℝ) + 1 / 4) ^ 2 + (T / 2) ^ 2)
        - (T / 2) * Real.log (n : ℝ)) atTop (𝓝 0) := by
  -- rewrite as (T/4)·log( ((n+¼)²+(T/2)²)/n² ),  argument → 1,  log → 0.
  have hlogratio : Tendsto
      (fun n : ℕ => Real.log ((((n : ℝ) + 1 / 4) ^ 2 + (T / 2) ^ 2) / (n : ℝ) ^ 2)) atTop (𝓝 0) := by
    have := (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp (tendsto_log_ratio T)
    simpa [Function.comp_def, Real.log_one] using this
  have hscaled := hlogratio.const_mul (T / 4)
  rw [mul_zero] at hscaled
  refine hscaled.congr' ?_
  filter_upwards [eventually_ne_atTop 0] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    have : 0 < n := Nat.pos_of_ne_zero hn
    exact_mod_cast this
  have hden : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
  have hnum : (0 : ℝ) < ((n : ℝ) + 1 / 4) ^ 2 + (T / 2) ^ 2 := by positivity
  rw [Real.log_div (ne_of_gt hnum) (ne_of_gt hden), Real.log_pow]
  push_cast
  ring

/-! ## Part 3 — the convergence `collect T n → Lcollect T`. -/

/-- **`collect T n → Lcollect T`** as `n → ∞`, for `T ≥ 0`.  Assembled from the three pieces
(harmonic, arctan, log) and the closed form `stirPrincipal_eq`. -/
theorem collect_tendsto_Lcollect (T : ℝ) (hT : 0 ≤ T) :
    Tendsto (fun n : ℕ => collect T n) atTop (𝓝 (Lcollect T)) := by
  -- assemble the limit of the three n-dependent pieces.
  have h1 := tendsto_harmonic_term T            -- → (T/2)·γ
  have h2 := tendsto_arctan_term (T / 2) (by linarith)  -- → T/2
  have h3 := tendsto_log_term T                 -- → 0
  -- collect T n = Kc T + piece1 n − piece2 n − piece3 n   (where piece-i are the bracketed terms)
  have hcombo :
      Tendsto (fun n : ℕ => Kc T + (T / 2) * ((harmonic n : ℝ) - Real.log n)
          - ((n : ℝ) + 1 / 4) * Real.arctan ((T / 2) / ((n : ℝ) + 1 / 4))
          - ((T / 4) * Real.log (((n : ℝ) + 1 / 4) ^ 2 + (T / 2) ^ 2)
              - (T / 2) * Real.log (n : ℝ)))
        atTop (𝓝 (Kc T + (T / 2) * Real.eulerMascheroniConstant - (T / 2) - 0)) :=
    (((tendsto_const_nhds (x := Kc T)).add h1).sub h2).sub h3
  -- the displayed sequence equals collect T n
  have hcollect_eq : ∀ n : ℕ,
      Kc T + (T / 2) * ((harmonic n : ℝ) - Real.log n)
          - ((n : ℝ) + 1 / 4) * Real.arctan ((T / 2) / ((n : ℝ) + 1 / 4))
          - ((T / 4) * Real.log (((n : ℝ) + 1 / 4) ^ 2 + (T / 2) ^ 2)
              - (T / 2) * Real.log (n : ℝ))
        = collect T n := by
    intro n; rw [collect_eq_Kc]; ring
  -- the limit value equals Lcollect T
  have hlim_eq : Kc T + (T / 2) * Real.eulerMascheroniConstant - (T / 2) - 0 = Lcollect T := by
    unfold Kc Lcollect
    rw [stirPrincipal_eq]
    ring
  rw [← hlim_eq]
  exact hcombo.congr hcollect_eq

/-! ## Part 4 — the TRUE uniform bound on the limit `Lcollect`. -/

/-- `‖zPt T‖² = (1/4)² + (T/2)²`, hence `(T/2)·log‖zPt T‖ = (T/4)·log((1/4)² + (T/2)²)`. -/
theorem two_mul_log_norm_zPt (T : ℝ) :
    (T / 2) * Real.log ‖zPt T‖ = (T / 4) * Real.log ((1 / 4) ^ 2 + (T / 2) ^ 2) := by
  have hnorm_sq : ‖zPt T‖ ^ 2 = (1 / 4) ^ 2 + (T / 2) ^ 2 := by
    rw [Complex.norm_def, Real.sq_sqrt (Complex.normSq_nonneg _), Complex.normSq_apply,
      zPt_re, zPt_im]; ring
  have hpos : (0 : ℝ) < (1 / 4) ^ 2 + (T / 2) ^ 2 := by positivity
  have hlog : Real.log ((1 / 4) ^ 2 + (T / 2) ^ 2) = 2 * Real.log ‖zPt T‖ := by
    rw [← hnorm_sq, Real.log_pow]; push_cast; ring
  rw [hlog]; ring

/-- **THE TRUE UNIFORM BOUND.**  `|Lcollect T| ≤ π + 1` for all `T ≥ 140`, where
`Lcollect T = limₙ collect T n = −(3/4)·arg z − (T/2)·log‖z‖ + Gphi T 1`.

This is the genuine `Im μ(z) = O(1)` Binet bound.  Term breakdown:
`arg z ∈ [0, π/2]`, `(5/4)·arctan((T/2)/(5/4)) ∈ [0, (5/4)·π/2]`, and the matched-log defect
`D = (T/4)·log( ((5/4)²+(T/2)²)/((1/4)²+(T/2)²) ) ∈ [0, 3/(2T)] ⊆ [0, 1]`. -/
theorem Lcollect_uniform_bound :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ T : ℝ, (140 : ℝ) ≤ T → |Lcollect T| ≤ C₀ := by
  refine ⟨Real.pi + 1, by positivity, ?_⟩
  intro T hT
  have hTpos : (0 : ℝ) < T := by linarith
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  -- expand Lcollect via Gphi T 1 and the matched-log form
  -- Gphi T 1 = (5/4)·arctan((T/2)/(5/4)) + (T/4)·log((5/4)²+(T/2)²)
  have hGphi1 : Gphi T 1 = (5 / 4) * Real.arctan ((T / 2) / (5 / 4))
      + (T / 4) * Real.log ((5 / 4) ^ 2 + (T / 2) ^ 2) := by
    unfold Gphi; norm_num
  -- the matched-log defect D
  set num : ℝ := (5 / 4) ^ 2 + (T / 2) ^ 2 with hnum
  set den : ℝ := (1 / 4) ^ 2 + (T / 2) ^ 2 with hden
  have hden_pos : (0 : ℝ) < den := by rw [hden]; positivity
  have hnum_pos : (0 : ℝ) < num := by rw [hnum]; positivity
  -- Lcollect T = −(3/4)·arg z + (5/4)·arctan(...) + (T/4)·(log num − log den)
  have hLexp : Lcollect T = -(3 / 4) * Complex.arg (zPt T)
      + (5 / 4) * Real.arctan ((T / 2) / (5 / 4))
      + (T / 4) * (Real.log num - Real.log den) := by
    unfold Lcollect
    rw [hGphi1, two_mul_log_norm_zPt]
    rw [hnum, hden]; ring
  -- bound the defect D = (T/4)(log num − log den) ∈ [0, 3/(2T)]
  set D : ℝ := (T / 4) * (Real.log num - Real.log den) with hDdef
  have hD_nonneg : 0 ≤ D := by
    rw [hDdef]
    apply mul_nonneg (by linarith)
    rw [sub_nonneg]
    apply Real.log_le_log hden_pos
    rw [hnum, hden]; nlinarith
  have hD_le : D ≤ 3 / (2 * T) := by
    -- log num − log den = log(num/den) ≤ num/den − 1 = (3/2)/den ≤ (3/2)/(T/2)² = 6/T²
    have hlogdiff : Real.log num - Real.log den = Real.log (num / den) := by
      rw [Real.log_div (ne_of_gt hnum_pos) (ne_of_gt hden_pos)]
    have hratio_pos : (0 : ℝ) < num / den := div_pos hnum_pos hden_pos
    have hlog_le : Real.log (num / den) ≤ num / den - 1 := Real.log_le_sub_one_of_pos hratio_pos
    have hnd : num / den - 1 = (3 / 2) / den := by
      rw [div_sub_one (ne_of_gt hden_pos), hnum, hden]; ring_nf
    have hden_ge : (T / 2) ^ 2 ≤ den := by rw [hden]; nlinarith
    have hTsq : (0 : ℝ) < (T / 2) ^ 2 := by positivity
    have hbound2 : (3 / 2) / den ≤ (3 / 2) / (T / 2) ^ 2 :=
      div_le_div_of_nonneg_left (by norm_num) hTsq hden_ge
    have hfin : (3 / 2) / (T / 2) ^ 2 = 6 / T ^ 2 := by ring
    have hT2 : (3 : ℝ) / (2 * T) = (T / 4) * (6 / T ^ 2) := by
      field_simp; ring
    rw [hDdef, hlogdiff]
    calc (T / 4) * Real.log (num / den)
        ≤ (T / 4) * ((3 / 2) / den) := by
          apply mul_le_mul_of_nonneg_left ?_ (by linarith)
          rw [← hnd]; exact hlog_le
      _ ≤ (T / 4) * ((3 / 2) / (T / 2) ^ 2) := by
          apply mul_le_mul_of_nonneg_left hbound2 (by linarith)
      _ = (T / 4) * (6 / T ^ 2) := by rw [hfin]
      _ = 3 / (2 * T) := hT2.symm
  have hD_le_one : D ≤ 1 := by
    have : (3 : ℝ) / (2 * T) ≤ 1 := by
      rw [div_le_one (by linarith)]; linarith
    linarith
  -- arg z ∈ [0, π/2]
  have harg_nonneg : 0 ≤ Complex.arg (zPt T) := by
    rw [Complex.arg_nonneg_iff, zPt_im]; linarith
  have harg_le : Complex.arg (zPt T) ≤ Real.pi := Complex.arg_le_pi _
  have harg_le_half : Complex.arg (zPt T) ≤ Real.pi / 2 := by
    -- since re z = 1/4 > 0, arg z = arctan(im/re) < π/2
    rw [Complex.arg_of_re_nonneg (by rw [zPt_re]; norm_num)]
    have := Real.arcsin_le_pi_div_two ((zPt T).im / ‖zPt T‖)
    linarith
  -- arctan term ∈ [0, π/2]
  have harctan_nonneg : 0 ≤ Real.arctan ((T / 2) / (5 / 4)) :=
    Real.arctan_nonneg.mpr (by positivity)
  have harctan_le : Real.arctan ((T / 2) / (5 / 4)) ≤ Real.pi / 2 :=
    (Real.arctan_lt_pi_div_two _).le
  -- assemble
  rw [hLexp]
  rw [abs_le]
  constructor
  · -- lower bound: ≥ −(π+1)
    nlinarith [harg_le_half, harctan_nonneg, hD_nonneg, hpi]
  · -- upper bound: ≤ π+1
    nlinarith [harg_nonneg, harctan_le, hD_le_one, hpi]

/-! ## Part 5 — the corrected, downstream-usable statement. -/

/-- **THE CORRECTED RESIDUAL** (replacing the FALSE literal `collect_uniform_bound`).
The *limit* `limₙ collect T n` is bounded uniformly in `T ≥ 140`.  Concretely, `Lcollect T` IS that
limit (`collect_tendsto_Lcollect`) and `|Lcollect T| ≤ π + 1` (`Lcollect_uniform_bound`).

This is exactly the fact `binetPhase_crude_bound` needs: pass to the `n → ∞` limit and bound the
*limit* `thetaCont T − stirPrincipal T = Lcollect T − (limₙ remEM T n)`, with `|limₙ remEM| ≤ π/2`
(from the proven uniform `|remEM T n| ≤ π/2`).  The partial sums `collect T n` themselves are NOT
uniformly bounded (they overshoot by `≈ −(T/2)log(T/2)` for small `n`), so the original
partial-sum route is invalid; this limit route is the correct one. -/
theorem collect_limit_uniform_bound :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ T : ℝ, (140 : ℝ) ≤ T → 0 ≤ T →
      ∀ L : ℝ, Tendsto (fun n : ℕ => collect T n) atTop (𝓝 L) → |L| ≤ C₀ := by
  obtain ⟨C₀, hC0, hbound⟩ := Lcollect_uniform_bound
  refine ⟨C₀, hC0, ?_⟩
  intro T hT hT0 L hLtend
  -- L = Lcollect T by uniqueness of limits
  have huniq : L = Lcollect T := tendsto_nhds_unique hLtend (collect_tendsto_Lcollect T hT0)
  rw [huniq]; exact hbound T hT

end ScratchCollectBound
end BacklundTuring
end OverflowResidueRH

/-! ## Axiom footprint — all results Mathlib-only, NO `sorryAx`. -/

#print axioms OverflowResidueRH.BacklundTuring.ScratchCollectBound.stirPrincipal_eq
#print axioms OverflowResidueRH.BacklundTuring.ScratchCollectBound.collect_tendsto_Lcollect
#print axioms OverflowResidueRH.BacklundTuring.ScratchCollectBound.Lcollect_uniform_bound
#print axioms OverflowResidueRH.BacklundTuring.ScratchCollectBound.collect_limit_uniform_bound
