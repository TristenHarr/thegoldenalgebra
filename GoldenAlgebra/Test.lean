-- Test.lean
import Mathlib.Tactic

example (x y : ℝ) : (x + y)^2 = x^2 + 2*x*y + y^2 := by
  ring

example : (123 * 456) / 3 = 18696 := by
  norm_num
