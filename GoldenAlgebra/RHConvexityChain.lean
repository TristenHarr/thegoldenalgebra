/-
  RHConvexityChain.lean — the convexity tower, fully wired across module boundaries.

  Module graph (each arrow = an `import`; each seam = a transplant axiom in the original
  Scratch consumer, here DELETED and replaced by the imported producer THEOREM):

      RHConvexityTower            -- proves `phragmenLindelof_flatten`   (HalfStripPL ⊕ Flatten)
          │  (seam 1, already discharged by the prior agent)
          ▼
      RHSharpPL                   -- proves `tWeightedPL_linear_sharp`   (seam 2)
          │  imports RHConvexityTower; reuses its `wgt`/`Lbase`/`pExp`/`ellInterp`
          ▼
      RHConvexityWire             -- proves `tWeightedPL_zeta_convexity` + `zeta_convexity_bound`
          │  imports RHSharpPL; pure-ζ seam, no def clash                (seam 3)
          ▼
      RHCountWiring               -- proves `backlund_subconvex_sign_count_proven`   (seam 4)
             imports RHConvexityWire; pure-ζ seam

  This aggregator imports the FINAL consumer and re-audits the endpoint across ALL four
  boundaries.  The `#print axioms` below must show NO transplant axioms
  (`phragmenLindelof_flatten`, `tWeightedPL_linear_sharp`, `tWeightedPL_zeta_convexity`,
  on-the-line `zeta_convexity_bound`) — only the GENUINE residuals.
-/
import RHCountWiring

open OverflowResidueRH.BacklundTuring

-- The fully-wired endpoints are imported THEOREMS, not axioms.
#check @RHConvexityWire.zeta_convexity_bound
#check @RHConvexityWire.tWeightedPL_zeta_convexity
#check @RHSharpPL.tWeightedPL_linear_sharp
#check @RHCountWiring.backlund_subconvex_sign_count_proven

/-- The sharp Backlund convexity count, re-exported through the full chain. -/
theorem backlund_subconvex_sign_count_chain :
    ∃ α β₀ : ℝ, 0 ≤ α ∧ α ≤ 0.111 ∧ α < 0.399 ∧
      ∀ T : ℝ, (140 : ℝ) ≤ T →
        ((∑ᶠ u : ℂ, (MeromorphicOn.divisor (RHCountWiring.backlundF T)
            (Metric.closedBall ((1/2 : ℝ) : ℂ) (1/256 : ℝ))) u : ℝ))
          ≤ α * Real.log T + β₀ :=
  RHCountWiring.backlund_subconvex_sign_count_proven

-- FINAL CROSS-BOUNDARY AXIOM AUDIT.
#print axioms RHSharpPL.tWeightedPL_linear_sharp
#print axioms RHConvexityWire.tWeightedPL_zeta_convexity
#print axioms RHConvexityWire.zeta_convexity_bound
#print axioms backlund_subconvex_sign_count_chain
