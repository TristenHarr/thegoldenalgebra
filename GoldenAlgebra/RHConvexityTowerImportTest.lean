/-
  RHConvexityTowerImportTest.lean — proves the consolidated module COMPOSES.

  This file IMPORTS the consolidated `RHConvexityTower` module (rather than re-axiomatizing
  anything) and references `phragmenLindelof_flatten` as a genuine, already-PROVEN theorem.
  If this compiles, the lakefile `lean_lib RHConvexityTower` is a real importable module and the
  HalfStripPL→Flatten seam is composed with NO transplant axiom across the file boundary.
-/
import RHConvexityTower

open OverflowResidueRH.BacklundTuring.ScratchHalfStripPL

-- `phragmenLindelof_flatten` is now an imported THEOREM, not an axiom in this file.
#check @phragmenLindelof_flatten
#check @verticalStrip_PL_upper_const_bound

-- Axiom audit across the import boundary: only Mathlib axioms + the single genuine residual
-- `verticalStrip_lower_reflection`.  No transplant axiom for the PL upper-const-bound seam.
#print axioms phragmenLindelof_flatten
