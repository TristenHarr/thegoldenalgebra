import rh

open Filter Topology
open OverflowResidueRH

-- ============================================================
-- Probe 1: discrete primitive is bounded by total multiplicity (finite!)
-- ============================================================
example (D : FluctuationMeasureData) (T X : ℝ) :
    Phase1IBP.discreteCountingPrimitive D T X
      ≤ ∑ j ∈ Finset.range D.n, (D.mult j : ℝ) := by
  unfold Phase1IBP.discreteCountingPrimitive
  apply Finset.sum_le_sum
  intro j _
  by_cases h : T ≤ D.Z j ∧ D.Z j ≤ X
  · simp [h]
  · simp only [h, if_false]; positivity

#check @smoothCountingPrimitive_eq_N0_diff
#check @smoothZeroCountingN0

-- ============================================================
-- Probe 3: N0 tends to +∞.
-- N0(u) = (u/2π)·log(u/2π) − u/2π + 7/8.
-- Let t = u/(2π). N0 = t·log t − t + 7/8 = t(log t − 1) + 7/8.
-- ============================================================
example : Tendsto smoothZeroCountingN0 atTop atTop := by
  have h2pi : (0:ℝ) < 2 * Real.pi := by positivity
  -- rewrite via t = u/(2π)
  have hrw : smoothZeroCountingN0 =
      (fun u => (u / (2*Real.pi)) * (Real.log (u/(2*Real.pi)) - 1) + 7/8) := by
    funext u; unfold smoothZeroCountingN0; ring
  rw [hrw]
  -- The map u ↦ u/(2π) tends to atTop
  have htmap : Tendsto (fun u:ℝ => u/(2*Real.pi)) atTop atTop :=
    Tendsto.atTop_div_const h2pi tendsto_id
  -- t(log t − 1) tends to atTop ; compose
  have hbase : Tendsto (fun t:ℝ => t * (Real.log t - 1)) atTop atTop := by
    apply tendsto_atTop_mono' atTop _ tendsto_id
    -- eventually: t ≤ t*(log t − 1), i.e. for t ≥ e^2, log t − 1 ≥ 1
    filter_upwards [eventually_ge_atTop (Real.exp 2)] with t ht
    have ht0 : (0:ℝ) < t := lt_of_lt_of_le (Real.exp_pos 2) ht
    have hlog : 2 ≤ Real.log t := by
      have := Real.log_le_log (Real.exp_pos 2) ht
      rwa [Real.log_exp] at this
    show id t ≤ t * (Real.log t - 1)
    simp only [id]
    nlinarith [hlog, ht0]
  have := (hbase.comp htmap)
  simpa using this.atTop_add (tendsto_const_nhds (x := (7/8:ℝ)))

-- ============================================================
-- N0 tends to +∞, named.
-- ============================================================
theorem N0_tendsto_atTop : Tendsto smoothZeroCountingN0 atTop atTop := by
  have h2pi : (0:ℝ) < 2 * Real.pi := by positivity
  have hrw : smoothZeroCountingN0 =
      (fun u => (u / (2*Real.pi)) * (Real.log (u/(2*Real.pi)) - 1) + 7/8) := by
    funext u; unfold smoothZeroCountingN0; ring
  rw [hrw]
  have htmap : Tendsto (fun u:ℝ => u/(2*Real.pi)) atTop atTop :=
    Tendsto.atTop_div_const h2pi tendsto_id
  have hbase : Tendsto (fun t:ℝ => t * (Real.log t - 1)) atTop atTop := by
    apply tendsto_atTop_mono' atTop _ tendsto_id
    filter_upwards [eventually_ge_atTop (Real.exp 2)] with t ht
    have ht0 : (0:ℝ) < t := lt_of_lt_of_le (Real.exp_pos 2) ht
    have hlog : 2 ≤ Real.log t := by
      have := Real.log_le_log (Real.exp_pos 2) ht
      rwa [Real.log_exp] at this
    show id t ≤ t * (Real.log t - 1)
    simp only [id]; nlinarith [hlog, ht0]
  have := (hbase.comp htmap)
  simpa using this.atTop_add (tendsto_const_nhds (x := (7/8:ℝ)))

-- ============================================================
-- log u ≤ N0(u) eventually  (N0 ~ u log u beats log u).
-- ============================================================
theorem log_le_N0_eventually :
    ∀ᶠ u in atTop, Real.log u ≤ smoothZeroCountingN0 u := by
  -- For u ≥ 2π·e³: t = u/2π ≥ e³, log t ≥ 3, so N0 = t(log t -1)+7/8 ≥ 2t.
  -- And log u = log(2π) + log t ≤ log(2π) + t ≤ t + t = 2t  (since t ≥ e³ ≥ log(2π) and t ≥ log t).
  have h2pi : (0:ℝ) < 2 * Real.pi := by positivity
  have he3_gt7 : (7:ℝ) < Real.exp 3 := by
    have heq : Real.exp 3 = Real.exp 1 ^ 3 := by
      rw [← Real.exp_nat_mul]; norm_num
    rw [heq]
    have hge : (2:ℝ) < Real.exp 1 := Real.exp_one_gt_two
    have hpos : (0:ℝ) < Real.exp 1 := Real.exp_pos 1
    nlinarith [hge, hpos, mul_pos hpos hpos]
  have h2pi_lt7 : 2*Real.pi < 7 := by
    have := Real.pi_lt_d2; linarith
  have hlog2pi : Real.log (2*Real.pi) ≤ Real.exp 3 := by
    have h1 : 2*Real.pi ≤ Real.exp 3 := le_of_lt (lt_trans h2pi_lt7 he3_gt7)
    calc Real.log (2*Real.pi) ≤ Real.log (Real.exp 3) :=
            Real.log_le_log h2pi h1
      _ = 3 := Real.log_exp 3
      _ ≤ Real.exp 3 := le_of_lt (lt_trans (by norm_num) he3_gt7)
  filter_upwards [eventually_ge_atTop (2*Real.pi*Real.exp 3)] with u hu
  set t := u / (2*Real.pi) with ht_def
  have hupos : 0 < u := lt_of_lt_of_le (by positivity) hu
  have hue : Real.exp 3 ≤ t := by
    rw [ht_def, le_div_iff₀ h2pi]; nlinarith [hu]
  have htpos : 0 < t := lt_of_lt_of_le (Real.exp_pos 3) hue
  -- log t ≥ 3
  have hlogt : 3 ≤ Real.log t := by
    have := Real.log_le_log (Real.exp_pos 3) hue
    rwa [Real.log_exp] at this
  -- t ≥ log t
  have ht_ge_logt : Real.log t ≤ t := Real.log_le_sub_one_of_pos htpos |>.trans (by linarith)
  -- u = 2π * t  ⇒ log u = log(2π) + log t
  have hu_eq : u = (2*Real.pi) * t := by
    rw [ht_def]; field_simp
  have hlogu : Real.log u = Real.log (2*Real.pi) + Real.log t := by
    rw [hu_eq, Real.log_mul (by positivity) (ne_of_gt htpos)]
  -- N0(u) = t*(log t - 1) + 7/8 ≥ 2t  (since log t -1 ≥ 2)
  have hN0 : smoothZeroCountingN0 u = t*(Real.log t - 1) + 7/8 := by
    unfold smoothZeroCountingN0; rw [← ht_def]; ring
  have hN0ge : (2:ℝ)*t ≤ smoothZeroCountingN0 u := by
    rw [hN0]; nlinarith [hlogt, htpos]
  -- log u = log(2π) + log t ≤ t + t = 2t  (log(2π) ≤ e³ ≤ t, and log t ≤ t)
  have hlog2pi_le_t : Real.log (2*Real.pi) ≤ t := le_trans hlog2pi hue
  rw [hlogu]
  linarith [hN0ge, ht_ge_logt, hlog2pi_le_t]

-- ============================================================
-- N0(u) − ½ log u → +∞.  (½ log u ≤ ½ N0 u eventually ⇒ ≥ ½ N0 u → ∞.)
-- ============================================================
theorem N0_sub_halfLog_tendsto_atTop :
    Tendsto (fun u => smoothZeroCountingN0 u - (1/2) * Real.log u) atTop atTop := by
  -- ½ N0 u → ∞, and ½ N0 u ≤ N0 u − ½ log u eventually (⇔ ½ log u ≤ ½ N0 u ⇔ log u ≤ N0 u).
  have hhalfN0 : Tendsto (fun u => (1/2 : ℝ) * smoothZeroCountingN0 u) atTop atTop :=
    Tendsto.const_mul_atTop (by norm_num) N0_tendsto_atTop
  apply tendsto_atTop_mono' atTop _ hhalfN0
  filter_upwards [log_le_N0_eventually] with u hu
  -- ½ N0 u ≤ N0 u − ½ log u  ⇔  ½ log u ≤ ½ N0 u  ⇔  log u ≤ N0 u
  linarith [hu]

-- ============================================================
-- smoothCountingPrimitive 10 u − ½ log u → +∞.
-- (smoothCountingPrimitive 10 u = N0 u − N0 10 for u ≥ 10.)
-- ============================================================
theorem smoothPrim10_sub_halfLog_tendsto_atTop :
    Tendsto (fun u => Phase1IBP.smoothCountingPrimitive 10 u - (1/2) * Real.log u)
      atTop atTop := by
  have hbase := N0_sub_halfLog_tendsto_atTop
  -- subtract constant N0 10
  have : Tendsto
      (fun u => (smoothZeroCountingN0 u - (1/2) * Real.log u) - smoothZeroCountingN0 10)
      atTop atTop := hbase.atTop_add (tendsto_const_nhds (x := (-smoothZeroCountingN0 10)))
      |>.congr (fun u => by ring)
  refine this.congr' ?_
  filter_upwards [eventually_ge_atTop (10:ℝ)] with u hu
  rw [smoothCountingPrimitive_eq_N0_diff (by norm_num) hu]
  ring

-- ============================================================
-- finiteFluctuationPrimitive bound:  for any finite Dzero,
--   smoothCountingPrimitive 10 u − ½ log u ≤ M + 49/20   for all u ≥ 140
-- would follow from hHighLog.  But the LHS → +∞.  CONTRADICTION.
--
-- MAIN THEOREM:  hHighLog is UNSATISFIABLE for every finite Dzero.
-- ============================================================
theorem hHighLog_unsatisfiable
    (Dzero : Phase1IBP.OrderedFluctuationMeasureData) :
    ¬ (∀ {z : ℂ} {T u : ℝ},
        140 ≤ T → 0 < z.im →
        2 * (1 + |z.re| + z.im) ≤ T →
        T ≤ u →
        |Phase1IBP.finiteFluctuationPrimitive Dzero 10 u|
          ≤ (1 / 2 : ℝ) * Real.log u + (49 / 20 : ℝ)) := by
  intro hHighLog
  -- Total (finite!) multiplicity mass.
  set M : ℝ := ∑ j ∈ Finset.range Dzero.n,
      (Dzero.toFluctuationMeasureData.mult j : ℝ) with hM_def
  -- Witness z = I  (re = 0, im = 1),  T = 140.
  have hzim : (0:ℝ) < Complex.I.im := by simp
  have hregime : 2 * (1 + |Complex.I.re| + Complex.I.im) ≤ 140 := by
    simp; norm_num
  -- For all u ≥ 140:  smooth 10 u − ½ log u ≤ M + 49/20.
  have hUpperBdd : ∀ u : ℝ, 140 ≤ u →
      Phase1IBP.smoothCountingPrimitive 10 u - (1/2) * Real.log u ≤ M + 49/20 := by
    intro u hu140
    have hbound := hHighLog (z := Complex.I) (T := 140) (u := u)
      (by norm_num) hzim hregime hu140
    -- |fFP| ≤ ½ log u + 49/20  ⇒  −(½ log u + 49/20) ≤ fFP = discrete − smooth
    have hlow : -((1/2) * Real.log u + 49/20)
        ≤ Phase1IBP.finiteFluctuationPrimitive Dzero 10 u :=
      neg_le_of_abs_le hbound |>.trans_eq (by ring) |>.trans (le_of_eq rfl)
    -- fFP = discrete − smooth
    have hfFP : Phase1IBP.finiteFluctuationPrimitive Dzero 10 u
        = Phase1IBP.discreteCountingPrimitive Dzero.toFluctuationMeasureData 10 u
          - Phase1IBP.smoothCountingPrimitive 10 u := rfl
    -- discrete ≤ M
    have hdisc : Phase1IBP.discreteCountingPrimitive Dzero.toFluctuationMeasureData 10 u ≤ M := by
      rw [hM_def]
      unfold Phase1IBP.discreteCountingPrimitive
      apply Finset.sum_le_sum
      intro j _
      by_cases h : (10:ℝ) ≤ Dzero.toFluctuationMeasureData.Z j
          ∧ Dzero.toFluctuationMeasureData.Z j ≤ u
      · simp [h]
      · simp only [h, if_false]; positivity
    rw [hfFP] at hlow
    -- −(½logu+49/20) ≤ discrete − smooth ≤ M − smooth
    -- ⇒ smooth − ½ log u ≤ M + 49/20
    linarith [hlow, hdisc]
  -- But smooth 10 u − ½ log u → +∞, so it eventually exceeds M + 49/20.
  have htend := smoothPrim10_sub_halfLog_tendsto_atTop
  have hev := (htend.eventually_gt_atTop (M + 49/20))
  -- Combine with u ≥ 140 to get a u where bound holds and is exceeded.
  obtain ⟨u, hu_gt, hu140⟩ :=
    ((hev.and (eventually_ge_atTop (140:ℝ))).exists)
  exact absurd (hUpperBdd u hu140) (not_le.mpr hu_gt)

#print axioms hHighLog_unsatisfiable
#print axioms N0_tendsto_atTop
#print axioms smoothPrim10_sub_halfLog_tendsto_atTop
