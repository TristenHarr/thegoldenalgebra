"""
route_c_values.py — the ACTUAL averaged-defect-density VALUES (Route C + Conrey),
not just the crossover. Plus honesty check on the count bound and what 'nonvacuous'
means. The clean statement:
   (1/T) int_0^T (G(x+iY))_-  dx   <=   2pi * T^{-2 theta Y} * log T   =: D(Y,T,theta)
This is the averaged SIGN-DEFECT DENSITY. D<1 = nonvacuous; D small = strong.
"""
import math
def D(Y,T,theta): return 2*math.pi*T**(-2*theta*Y)*math.log(T)

thetaC=4/7
print("Averaged sign-defect density  (1/T)int(G)_- <= 2pi T^{-8Y/7} logT  (Conrey):")
print(" Y \\ T   1e6        1e9        1e12       1e15       1e30")
for Y in [0.49,0.45,0.40,0.35,0.30,0.25,0.20,0.15,0.10]:
    row=f" {Y:.2f}  "
    for T in [1e6,1e9,1e12,1e15,1e30]:
        row+=f" {D(Y,T,thetaC):.2e}"
    print(row)
print()
print("Interpretation: D(Y,T) is an unconditional bound on the AVERAGE negative")
print("part of G(.+iY) per unit abscissa. D<1 means 'G is positive on average to")
print("within defect <1 per unit length' -- a genuine averaged anti-Herglotz law.")
print()
print("HUMAN-HEIGHT NONVACUOUS ZONE (D<1), Conrey:")
for T in [1e6,1e9,1e12]:
    Ystar=None
    for Y in [x/100 for x in range(49,4,-1)]:
        if D(Y,T,thetaC)<1: Ystar=Y
        else: break
    print(f"  T={T:.0e} (~{'verified zeros' if T<=3e12 else 'beyond'}): D<1 for all Y >= {Ystar}")
print()
print(">>> So at T=10^12 (within verified-zero range!), Conrey Route C gives a")
print(">>> NONVACUOUS averaged sign-defect bound for all Y down to ~0.18.")
print(">>> THIS IS THE PRIZE: a reasonable-constant averaged anti-Herglotz statement")
print(">>> nonvacuous at human/verified heights for Y in [~0.18, 1/2).")
print()
print("Honesty: the FULL hard region needs Y->0, where the crossover still -> inf")
print("(exp(O(1)/(theta Y))). The constant/route is fixed; the Y->0 blowup is intrinsic.")

# Cross-check the count bound numerically: count of (fake) zeros with eta>Y feasible
# under Selberg/Conrey at moderate T, vs T itself.
print()
print("Sanity: Conrey count bound N_off(Y,T) <= 2 T^{1-8Y/7} logT vs T:")
print(" Y     T=1e12   N_off bound      N_off/T")
for Y in [0.49,0.30,0.18]:
    T=1e12
    Nb=2*T**(1-2*thetaC*Y)*math.log(T)
    print(f"  {Y:.2f}  {T:.0e}   {Nb:.3e}      {Nb/T:.3e}")
