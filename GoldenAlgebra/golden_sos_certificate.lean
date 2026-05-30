/-
  Auto-generated SOS certificate (SDP status: closed_form_scalar22_15)
  Domain: T >= 140.0, x >= 0, y >= 0.1, 2(1 + x + y) <= T

  Inequality (cleared of denominators, multiplied by T^2):
    0.663789125619395*T - 77.4039605921791  >=  0

  Schmüdgen decomposition:
    target = sum_S  sigma_S * prod(g_i in S)
  where each sigma_S is a sum of squares and each g_i >= 0 on the slab.
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace GoldenAlgebra.SOSCertificate

def T0 : ℝ := 140.0
def yMin : ℝ := 0.1

-- constraint g_T >= 0:  T - 140.0
-- constraint g_x >= 0:  x
-- constraint g_y >= 0:  y
-- constraint g_B >= 0:  T - 2*x - 2*y - 2

-- sigma_g_T
--   product : T - 140.0
--   sigma   : 0.663789125619395

-- sigma_empty
--   product : 1
--   sigma   : 15.5265169945363

end GoldenAlgebra.SOSCertificate