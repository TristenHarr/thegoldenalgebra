"""
SECMOM_gate.py — does squaring SHIFT the δT~1 detection gate?  η⁴ vs η².

First-moment readout per zero:  Δ_ρ ≈ 4·(cosh(ηT)-1)·∫|g|  in worst case, and the
visibility floor (ScratchResolutionTheory cosh_minus_one_resolution) is governed by
the EDGE value cosh(ηT)-1: invisible (O((ηT)²)) for ηT<1, O(1) for ηT>1.  Gate: ηT~1.

Second moment per zero: |Δ_ρ|² ≈ 16 (cosh(ηT)-1)² (∫|g|)².  Its two-regime law:
   cosh(ηT)-1 ≤ (ηT)²cosh(ηT)   ⟹  (cosh(ηT)-1)² ≤ (ηT)⁴ cosh²(ηT)   [INVISIBLE O((ηT)⁴)]
   ηT≥1 ⟹ cosh(ηT)-1 ≥ ½(ηT)²  ⟹  (cosh(ηT)-1)² ≥ ¼(ηT)⁴            [VISIBLE  O(1) above]
So the GATE is the SAME ηT~1; only the INVISIBILITY EXPONENT changes p=2 → p=4.
Squaring does NOT move the wall — it makes the sub-gate decay STEEPER (η⁴ not η²), i.e.
the second moment is EVEN BLINDER below the gate.  This is the central negative finding.
"""
import mpmath as mp
mp.mp.dps = 30

print("Comparison of detector decay below the gate ηT<1 (T=1, sweep η):")
print(f"{'eta=ηT':>8} {'cosh-1 (p=2)':>16} {'(cosh-1)² (p=4)':>18} {'ratio sq/lin²':>14}")
for x in [mp.mpf('0.5'),mp.mpf('0.3'),mp.mpf('0.1'),mp.mpf('0.05'),mp.mpf('0.01')]:
    lin = mp.cosh(x)-1
    sq = lin**2
    print(f"{float(x):>8} {float(lin):>16.4e} {float(sq):>18.4e} {float(sq/lin**2):>14.4f}")
print()
print("Below the gate: first moment ~ (ηT)²/2, second moment ~ (ηT)⁴/4.")
print("So to reach a FIXED detectable floor ε, the gates are:")
print("   first  moment: (ηT)² ≳ ε   ⟹  ηT ≳ √ε")
print("   second moment: (ηT)⁴ ≳ ε   ⟹  ηT ≳ ε^{1/4}  (LARGER ⟹ needs MORE T for same η)")
print("⟹ for small displacement the second moment needs LARGER support to detect: it is a")
print("  STRICTLY WORSE displacement detector below the gate.  Same wall, steeper blindness.")
print()
# verify the two-regime law numerically (the squared cosh kernel)
print("Squared-kernel two-regime law check  R2(x)=(cosh x - 1)²:")
print(f"{'x':>6} {'R2':>14} {'x⁴cosh²x (UB)':>16} {'¼x⁴ (LB if x≥1)':>16}")
for x in [mp.mpf('0.2'),mp.mpf('0.5'),mp.mpf('1.0'),mp.mpf('2.0'),mp.mpf('3.0')]:
    R2=(mp.cosh(x)-1)**2; UB=x**4*mp.cosh(x)**2; LB=x**4/4
    flag = "  (UB ok, LB ok)" if (R2<=UB and (x<1 or LB<=R2)) else "  CHECK"
    print(f"{float(x):>6} {float(R2):>14.4e} {float(UB):>16.4e} {float(LB):>16.4e}{flag}")
