#!/usr/bin/env python3
"""
signed_kernel_exact_net.py — the EXACT per-mirror net as one rational, and the
true (tight) sign condition. Goal: a clean polynomial certificate provable by
nlinarith in Lean for the region R = {y >= 1/2}.

per-mirror net  m(y,e,a) = 2y/(y^2+a^2) + k(e,a),
   k(e,a) = 2 e^2 y (y^2-3a^2-e^2)/[(a^2+y^2)((y-e)^2+a^2)((y+e)^2+a^2)].
Combine over the common denominator and factor the numerator. Find: numerator >= 0
on  y>=1/2, |e|<=1/2, all a  ?  (then per-mirror net >= 0, summing gives G>=0.)
"""
import sympy as sp

y,e,a = sp.symbols('y e a', real=True)

k = 2*e**2*y*(y**2-3*a**2-e**2)/((a**2+y**2)*((y-e)**2+a**2)*((y+e)**2+a**2))
ref = 2*y/(y**2+a**2)
m = sp.together(ref + k)
num, den = sp.fraction(m)
num = sp.expand(num); den = sp.factor(den)
print("per-mirror net m = N/D")
print("D =", den)
print()
# D = (a^2+y^2)((y-e)^2+a^2)((y+e)^2+a^2) > 0 for y>0. So sign(m)=sign(N).
N = sp.factor(num)
print("N (factored) =", N)
print()
Nexp = sp.expand(num)
print("N (expanded) =", Nexp)
print()
# Pull out the obvious 2y factor:
N_over_2y = sp.simplify(Nexp/(2*y))
print("N/(2y) =", sp.expand(N_over_2y))
print()
# So m = 2y * P / D with P = N/(2y). Need P>=0 on y>=1/2,|e|<=1/2, all a.
P = sp.expand(N_over_2y)
print("Need P >= 0.  P =", sp.collect(P, a))
print()
# Treat P as polynomial in a^2 =: A. Substitute.
A = sp.symbols('A', nonnegative=True)
P_A = P.subs(a**2, A)
# Make sure only even powers of a appear:
print("P only even in a?", sp.simplify(P.subs(a,-a)-P)==0)
P_A = sp.expand(P.subs(a, sp.sqrt(A)))
P_A = sp.simplify(P_A)
print("P as polynomial in A=a^2:", sp.collect(sp.expand(P_A), A))
print()
# Coeffs in A:
PA_poly = sp.Poly(sp.expand(P_A), A)
print("Coeffs of P in A (highest->lowest):")
for i,c in enumerate(PA_poly.all_coeffs()):
    print(f"   A^{PA_poly.degree()-i}: {sp.factor(c)}")
print()
# For P>=0 for ALL A>=0, since it's (we'll check) degree<=2 in A with positive
# leading coeff, need: leading>=0, and either no positive real roots or discriminant<=0,
# OR just check the constant term and min.  Evaluate worst-case bounds.
print("=== Establish P>=0 on y>=1/2, |e|<=1/2, A>=0 ===")
print("Check the three A-coefficients' signs under the constraints:")
deg = PA_poly.degree()
coeffs = PA_poly.all_coeffs()
for i,c in enumerate(coeffs):
    cc = sp.factor(c)
    # min over y>=1/2,|e|<=1/2
    print(f"  coeff A^{deg-i} = {cc}")
print()
# Constant term (A=0): this is P at a=0 (the pole-touch column). Must be >=0.
P0 = sp.simplify(P_A.subs(A,0))
print("P at a=0 (constant term):", sp.factor(P0))
print("  = (y^2-... )? evaluate sign on y>=1/2,|e|<=1/2:")
# numeric min of P0
import mpmath as mp
mp.mp.dps=30
f0 = sp.lambdify((y,e), P0, 'mpmath')
mn=None
import random; random.seed(3)
for _ in range(200000):
    yy=random.uniform(0.5,50); ee=random.uniform(-0.5,0.5)
    v=f0(yy,ee)
    if mn is None or v<mn[0]: mn=(float(v),yy,ee)
print(f"  min P(a=0) over y>=1/2,|e|<=1/2: {mn[0]:.6g} at y={mn[1]:.3f},e={mn[2]:.3f}  >=0? {mn[0]>=0}")
print()
# full P numeric min over all a
fP = sp.lambdify((y,e,a), P, 'mpmath')
mn=None
for _ in range(600000):
    yy=random.uniform(0.5,200); ee=random.uniform(-0.5,0.5); aa=random.uniform(-400,400)
    v=fP(yy,ee,aa)
    if mn is None or v<mn[0]: mn=(float(v),yy,ee,aa)
print(f"  min P over y>=1/2,|e|<=1/2,all a: {mn[0]:.6g} at y={mn[1]:.3f},e={mn[2]:.3f},a={mn[3]:.2f}  >=0? {mn[0]>=0}")
