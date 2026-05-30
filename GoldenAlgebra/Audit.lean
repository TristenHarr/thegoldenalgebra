import GoldenAlgebra

/-!
  DependencyAudit — machine-checked axiom dependency report.

  Run with:  lake env lean Audit.lean

  `#print axioms name` lists the axioms a declaration actually depends on.
  The three Lean built-ins (`propext`, `Classical.choice`, `Quot.sound`)
  are standard classical foundations. Anything else — `sorryAx` or a
  GoldenAlgebra-specific `axiom` — is real load-bearing debt.

  IMPORTANT: a clean `#print axioms` is necessary but NOT sufficient for
  "real progress". A theorem `(h : RH-strength-hypothesis) → RH` also
  prints clean, because the hard content sits in a *hypothesis*, not an
  axiom. See STATUS.md for the two-axis classification.
-/

open GoldenAlgebra

-- === Baseline: a genuinely unconditional theorem (expect GREEN) ===
#print axioms T_add_J_eq_one_half

-- === Remaining file-level axioms (expect each to depend on itself) ===
#print axioms centralBinomSeries_closed_form_lambdaG1
#print axioms harmonic_cotangent_zeta_identity

-- === C077: formerly an axiom, now discharged to a theorem ===
#print axioms council_C077_functional_equation
#print axioms council_C077_functional_equation_axiom
#print axioms council_C078_critical_symmetry

-- === Flagship RH-conditional theorems ===
#print axioms GoldenHPConjecture_implies_critical_line
#print axioms GoldenHPConjecture_for_zeta_implies_critical_line
#print axioms LocalGlobalZetaSource_implies_zeta_critical_line
#print axioms BoundedHPBridge_implies_zeta_critical_line
#print axioms WeilPositivityPackage_implies_zeta_critical_line
#print axioms FinalRHProofPackage_implies_zeta_critical_line
#print axioms GOLDENALGEBRA_FINAL_RH_CONDITIONAL
#print axioms GoldenAlgebra_RH_conditional
#print axioms one_shot_RH_from_explicit_formula_and_weil_positivity
#print axioms diamond_RH_from_Xi_HP_approximation
