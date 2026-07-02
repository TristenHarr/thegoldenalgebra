#!/usr/bin/env python3
"""
signed_kernel_offaxis.py — THE OFF-AXIS SIGNED KERNEL  K_z(eta,gamma) with x != 0.

Mission: prove (or sharply locate the failure of) an UNCONDITIONAL anti-Herglotz
region OFF the imaginary axis using the EXACT displacement kernel's SIGN.

Conventions (inherited from ScratchDisplacementObstruction / ScratchKernelDensity):
  XiPullback z = xi(1/2 + i z).  zeta-zero  s = beta + i*gamma  pulls back to atom
  (gamma, eta), eta = beta - 1/2.  FE quadruple {±gamma ± i eta}.
  Anti-Herglotz sign field  G(z) = -Im (Xi'/Xi)(z) = -Im sum_rho[1/(z-w)+1/(z+w)].
  ONE off-line zero contributes  K_z(eta,gamma) := -Im D_quad(z,gamma,eta)  to G,
  with D_quad = K_{g+ie}+K_{g-ie}-2 K_g  (the two on-line reference atoms removed).
  Probe z = x + i y, y>0.  The on-axis prior agent used x=0 (the FAR ray); we open x.

  STEP 1: closed form of K_z(eta,gamma) for general x, and its SIGN map.
  STEP 2: HELP vs HURT region in (x,y) relative to a zero (gamma,eta).
  STEP 3: the on-line reference reservoir at general x, and the per-zero net.
  STEP 4: honest triviality test — does a net-positive region reach NEAR the zeros?
"""
import sympy as sp

x, y, g, e = sp.symbols('x y g e', real=True)

def Im_recip(zx, zy, ax, ay):
    return -(zy-ay)/((zx-ax)**2 + (zy-ay)**2)

def Im_Kpair(zx, zy, ux, uy):
    return Im_recip(zx,zy,ux,uy) + Im_recip(zx,zy,-ux,-uy)

# D_quad = K_{g+ie} + K_{g-ie} - 2 K_{g}  ;  ImD = Im D_quad
ImD = Im_Kpair(x,y, g, e) + Im_Kpair(x,y, g, -e) - 2*Im_Kpair(x,y, g, 0)
ImD = sp.simplify(ImD)

# Lean closed form (ScratchDisplacementObstruction.ImDquad), variables (x,y,g,e):
ImDquad_lean = ( 2*y/(y**2+(g+x)**2) + 2*y/(y**2+(g-x)**2)
   + (e-y)/((e-y)**2+(g+x)**2) + (e-y)/((e-y)**2+(g-x)**2)
   - (e+y)/((e+y)**2+(g+x)**2) - (e+y)/((e+y)**2+(g-x)**2) )
print("ImDquad matches Lean closed form (general x):",
      sp.simplify(ImD - ImDquad_lean) == 0)

# The signed kernel K = -Im D_quad  (contribution to G):
K = sp.simplify(-ImD)

# ---------------------------------------------------------------------------
# STEP 1.  K is even in x (x -> -x) and even in eta. Combine the two abscissa
#          mirror images.  Write K = K(+ side) + K(- side) where the two sides
#          use (g+x) and (g-x).  Factor out the eta^2 (must vanish at e=0).
# ---------------------------------------------------------------------------
print("\n=== STEP 1: structure of the off-axis signed kernel ===")
print("K even in x? ", sp.simplify(K.subs(x,-x) - K) == 0)
print("K even in eta?", sp.simplify(K.subs(e,-e) - K) == 0)
print("K = 0 at eta=0 (on-line)?", sp.simplify(K.subs(e,0)) == 0)

# Split the single-abscissa kernel:  for ONE mirror with offset a := g±x,
# the contribution of {atom at height +e} and {-e} minus reference is
#   k(e, a) := -[ 2y/(y^2+a^2) + (e-y)/((e-y)^2+a^2) - (e+y)/((e+y)^2+a^2) ]
# Wait: D_quad has, per mirror, the two true atoms (e-y),(−(e+y)) AND the −2 ref.
# Group by mirror a in {g+x, g-x}. Each mirror carries:
#    +2y/(y^2+a^2)   (the -2*K_g reference, with Im sign already in)
#    +(e-y)/((e-y)^2+a^2) - (e+y)/((e+y)^2+a^2)
# So K_mirror(a) = -[ 2y/(y^2+a^2) + (e-y)/((e-y)^2+a^2) - (e+y)/((e+y)^2+a^2) ].
a = sp.symbols('a', real=True)
Kmirror = -( 2*y/(y**2+a**2) + (e-y)/((e-y)**2+a**2) - (e+y)/((e+y)**2+a**2) )
Kmirror = sp.simplify(Kmirror)
print("\nSingle-mirror kernel k(e,a) (offset a = g±x):")
Km = sp.together(Kmirror); num,den = sp.fraction(Km)
print("  numerator:", sp.factor(sp.expand(num)))
print("  denominator:", sp.factor(den))

# verify K = Kmirror(g+x) + Kmirror(g-x)
Ksum = Kmirror.subs(a, g+x) + Kmirror.subs(a, g-x)
print("\nK == k(e,g+x)+k(e,g-x)?", sp.simplify(K - Ksum) == 0)

# Factor eta^2 out of the single-mirror kernel.
Km_over_e2 = sp.simplify(Kmirror/e**2)
print("\nk(e,a)/eta^2 (the per-mirror weight):")
print("  =", sp.simplify(sp.together(Km_over_e2)))

# numerator of k(e,a):  what is its SIGN?
num_factored = sp.factor(sp.expand(num))
print("\n--- SIGN of single mirror ---")
print("k(e,a) numerator (factored):", num_factored)
# expand to read off the leading sign-determining factor
num_exp = sp.expand(num)
print("k(e,a) numerator (expanded):", num_exp)
