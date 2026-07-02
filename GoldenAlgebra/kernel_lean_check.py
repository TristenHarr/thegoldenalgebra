import sympy as sp
g,e,y = sp.symbols('g e y', real=True)
# kernel K0(g,e,y) = -Im D_quad at x=0:
K0 = -4*y/(g**2+y**2) - 2*(e-y)/(g**2+(e-y)**2) + 2*(e+y)/(g**2+(e+y)**2)
# This is the Lean kernel def K_axis g e y.  Verify against the small-eta leading and decay.
print("K0 simplified together:", sp.simplify(sp.together(K0)))
# check the EXACT identity to be used in Lean:  K0 * (g^2+y^2)^2  is a polynomial-bounded expr.
# We'll bank the inequality  K0 <= 12 y e^2/(g^2+y^2)^2  and  -K0 <= 12 y e^2/(g^2+y^2)^2,
# i.e. (g^2+y^2)^2 * |K0| <= 12 y e^2.  Verify the polynomial certificate for y>=1, |e|<=1/2.
num = sp.together(K0); N,D = sp.fraction(num); N=sp.expand(N); D=sp.factor(D)
print("N=",N); print("D=",D)
# (g^2+y^2)^2 K0 = (g^2+y^2)^2 N / D.  D=(g^2+y^2)((e-y)^2+g^2)((e+y)^2+g^2).
# So (g^2+y^2)^2 K0 = (g^2+y^2) N / [((e-y)^2+g^2)((e+y)^2+g^2)].
expr = sp.simplify((g**2+y**2)**2 * K0)
print("\n(g^2+y^2)^2 * K0 =", expr)
