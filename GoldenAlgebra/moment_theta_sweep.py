"""
Displacement second-moment recomputation under the general near-line density
   N(1/2+u, T) << T^{1 - 2*theta*u} * log T      (Conrey: any theta < 4/7)
The layer-cake identity:
   Sigma_{gamma<=T} eta^2 = 2 * int_0^{1/2} u * N_off(u,T) du,
   N_off(u,T) <= 2 * N(1/2+u,T) <= 2 * T^{1-2*theta*u} log T.
So
   M2(T) <= 4 log T * int_0^{1/2} u * T^{1-2*theta*u} du
          = 4 T log T * int_0^{1/2} u * e^{-(2*theta*log T) u} du.
Let c = 2*theta*log T. Then int_0^{1/2} u e^{-c u} du = [1 - e^{-c/2}(1+c/2)]/c^2 <= 1/c^2.
=> M2(T) <= 4 T log T / c^2 = 4 T log T / (4 theta^2 log^2 T) = T/(theta^2 log T).
So the ENVELOPE constant is 1/theta^2 (times T/log T), NOT a change of exponent.
"""
import sympy as sp

u, T, c, theta = sp.symbols('u T c theta', positive=True)

# exact inner integral
I = sp.integrate(u*sp.exp(-c*u), (u, 0, sp.Rational(1,2)))
I = sp.simplify(I)
print("int_0^{1/2} u e^{-c u} du =", I)
print("  <= 1/c^2 envelope; ratio at large c ->", sp.limit(I*c**2, c, sp.oo))

# Full envelope: M2 <= 4 T logT * I, with c = 2 theta logT
L = sp.symbols('L', positive=True)  # L = log T
c_val = 2*theta*L
env = 4*T*L*(1 - sp.exp(-c_val/2)*(1+c_val/2))/c_val**2
env = sp.simplify(env)
print("\nExact envelope M2(T) <=", env)
# leading term as L -> oo
lead = sp.limit(env*L/T, L, sp.oo)
print("Leading coefficient of T/log T:", lead, "= 1/theta^2")

print("\n--- Constant 1/theta^2 for each theta ---")
for th in [sp.Rational(1,8), sp.Rational(1,2), sp.Rational(4,7), sp.Rational(4,7)-sp.Rational(1,1000)]:
    print(f"  theta={th} ({float(th):.4f}):  1/theta^2 = {float(1/th**2):.4f}")
print("\nSelberg theta=1/8 -> constant 64 (matches Lean file's 64 T/log T).")
print("Conrey theta->4/7 -> constant (7/4)^2 = 49/16 =", float(sp.Rational(49,16)))
