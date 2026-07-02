"""
kernel_density.py  —  exact anti-Herglotz kernel K_z(eta,gamma) and the
kernel-weighted layer-cake bound from modern (Guth-Maynard) zero density.

Coordinate convention (inherited from ScratchPositionEnvelope / ScratchDisplacementObstruction):
  XiPullback z = xi(1/2 + i z).  A zeta-zero s = beta + i*gamma pulls back to an atom
  (gamma, eta) with eta = beta - 1/2.  The four functional-equation pullback points are
  {±gamma ± i eta}.  The anti-Herglotz field is
        G(z) = -Im (Xi'/Xi)(z) = -Im sum_rho [ 1/(z - w_rho) + 1/(z + w_rho) ]
  with w_rho the pullback.  We probe at z = x + i y on the UHP (y>0).

  The EXACT contribution of ONE off-line zero (its FE-paired quadruple, minus the
  two on-line reference atoms) to G(z) is the displacement field of
  ScratchDisplacementObstruction:
        G_atom(z) = -Im D_quad(z, gamma, eta),  D_quad = K_{g+ie}+K_{g-ie}-2 K_g.
  We DEFINE the exact anti-Herglotz kernel as
        K_z(eta,gamma) := -Im D_quad(z,gamma,eta)        (signed contribution to G)
  and its magnitude weight  |K_z(eta,gamma)|.

  This script:
   (1) confirms the closed form ImDquad symbolically (matches the Lean theorem),
   (2) derives the exact kernel decay in (eta, gamma, y),
   (3) builds the kernel-weighted layer-cake and compares to the crude count bound
       using the Guth-Maynard exponent A(sigma) = 15/(3+5 sigma).
"""
import sympy as sp

x, y, g, e, eta, gamma = sp.symbols('x y g e eta gamma', real=True)

# --- (1) Symbolic ImDquad (the Lean closed form) and the kernel -------------
def Im_recip(zx, zy, ax, ay):
    # Im 1/((zx+i zy) - (ax+i ay)) = -(zy-ay)/((zx-ax)^2+(zy-ay)^2)
    return -(zy-ay)/((zx-ax)**2 + (zy-ay)**2)

def Im_Kpair(zx, zy, ux, uy):
    # K_u(z) = 1/(z-u)+1/(z+u);  Im = Im 1/(z-u) + Im 1/(z+u)
    return Im_recip(zx,zy,ux,uy) + Im_recip(zx,zy,-ux,-uy)

# D_quad = K_{g+ie} + K_{g-ie} - 2 K_{g}
ImD = Im_Kpair(x,y, g, e) + Im_Kpair(x,y, g, -e) - 2*Im_Kpair(x,y, g, 0)
ImD = sp.simplify(ImD)

# The Lean closed form ImDquad x y gamma eta  (with g->gamma, e->eta):
ImDquad_lean = ( 2*y/(y**2+(g+x)**2) + 2*y/(y**2+(g-x)**2)
   + (e-y)/((e-y)**2+(g+x)**2) + (e-y)/((e-y)**2+(g-x)**2)
   - (e+y)/((e+y)**2+(g+x)**2) - (e+y)/((e+y)**2+(g-x)**2) )

print("ImDquad matches Lean closed form:",
      sp.simplify(ImD - ImDquad_lean) == 0)

# Exact anti-Herglotz kernel K_z(eta,gamma) := -Im D_quad
K = -ImD

# --- (2) On-axis probe x=0, decay analysis ----------------------------------
# Put x=0 (probe on the imaginary axis through the zero abscissa is the relevant
# worst case; the offline obstruction lives directly below the zero, x=Re w).
K0 = sp.simplify(K.subs(x,0))
print("\nK on axis (x=0):")
print(sp.nsimplify(K0))

# Small-eta expansion: leading order in eta (eta -> 0), fixed gamma,y>0.
ser = sp.series(K0, e, 0, 3).removeO()
print("\nSmall-eta expansion of K0 (to O(eta^2)):")
print(sp.simplify(ser))

# Large-gamma decay at fixed eta,y:  K0 ~ C(eta,y)/gamma^? 
# expand in 1/gamma
gam = sp.symbols('gam', positive=True)
K0g = K0.subs(g, gam)
big = sp.series(K0g, gam, sp.oo, 4)
print("\nLarge-gamma asymptotics of K0:")
print(big)

# --- (2b) Exact large-gamma decay rate -------------------------------------
print("\n=== Exact kernel decay ===")
# K0 = -4y/(g^2+y^2) - 2(e-y)/(g^2+(e-y)^2) + 2(e+y)/(g^2+(e+y)^2)
# Combine over common structure; expand numerator in 1/g properly.
K0c = sp.together(K0)
num, den = sp.fraction(K0c)
num = sp.expand(num); den = sp.expand(den)
print("K0 = N/D with")
print("  N =", sp.collect(num, g))
print("  D =", sp.factor(den))
# leading behavior as g->oo: degree of N vs D
pn = sp.Poly(num, g); pd = sp.Poly(den, g)
print("deg_g N =", pn.degree(), " deg_g D =", pd.degree(),
      " => K0 ~ gamma^{", pn.degree()-pd.degree(), "}")
# leading coefficient ratio
lc = sp.simplify(pn.LC()/pd.LC())
print("leading coeff (coeff of gamma^{deg}):", sp.simplify(lc))
# So K0 ~ lc * gamma^{deg_N-deg_D}.  Extract the gamma^{-4} coefficient:
c4 = sp.limit(K0*gamma**4, gamma, sp.oo) if False else None
gg = sp.symbols('gg', positive=True)
coeff_m4 = sp.limit(K0.subs(g,gg)*gg**4, gg, sp.oo)
print("lim gamma->oo  gamma^4 * K0  =", sp.simplify(coeff_m4))
