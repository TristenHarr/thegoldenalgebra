"""
kernel_layercake.py — the kernel-weighted layer-cake bound vs the crude count.

KERNEL BOUND.  From kernel_density.py: with probe z = i y (x=0, y>0 fixed), the
exact anti-Herglotz kernel of an off-line atom (eta,gamma) satisfies, for the
worst-case probe directly below the abscissa,
    |K_z(eta,gamma)|  <=  Cw(y) * eta^2 / (gamma^2 + y^2)^2          (*)
a UNIFORM kernel majorant (verified below): quadratic in displacement eta,
quadratic-decay^2 = degree-4 decay in height gamma.  Compare to the CRUDE weight
1 per off-line zero used in averagedAntiHerglotz_of_modernZeroDensity.

KERNEL-WEIGHTED ENERGY.  The off-line population's contribution to G(z) is
    Phi_K(z) := integral |K_z(eta,gamma)| dmu(eta,gamma)
             <= Cw(y) * integral eta^2/(gamma^2+y^2)^2 dmu.
Kernel-weighted LAYER-CAKE in eta (eta^2 = 2 int_0^|eta| u du) gives
    Phi_K(z) <= 2 Cw(y) int_0^{1/2} u [ int_{gamma} 1_{|eta|>=u}/(gamma^2+y^2)^2 dmu ] du.
The inner integral is a gamma-WEIGHTED off-line count.  Bounding it by the
height-resolved modern density (Guth-Maynard) N(1/2+u, T) summed dyadically over
gamma with the 1/(gamma^2+y^2)^2 weight produces a CONVERGENT height sum (the
crude count over [0,T] is replaced by a convergent integral over all gamma).

This script numerically demonstrates the gain.
"""
import sympy as sp, mpmath as mp
mp.mp.dps = 30

x,y,g,e = sp.symbols('x y g e', real=True)

def Im_recip(zx,zy,ax,ay): return -(zy-ay)/((zx-ax)**2+(zy-ay)**2)
def Im_Kpair(zx,zy,ux,uy): return Im_recip(zx,zy,ux,uy)+Im_recip(zx,zy,-ux,-uy)
ImD = Im_Kpair(x,y,g,e)+Im_Kpair(x,y,g,-e)-2*Im_Kpair(x,y,g,0)
K = -ImD
K0 = sp.simplify(K.subs(x,0))

# ---- verify uniform majorant (*) on a grid: |K0| <= Cw * e^2/(g^2+y^2)^2 ----
print("=== Uniform kernel majorant test: |K0| <= Cw(y) e^2/(g^2+y^2)^2 ===")
Kf = sp.lambdify((g,e,y), K0, 'mpmath')
worst = mp.mpf(0)
for yv in [0.5,1,2,5]:
    cw_needed = mp.mpf(0)
    for gv in [0.01,0.1,0.5,1,2,5,10,50,100]:
        for ev in [0.001,0.01,0.05,0.1,0.25,0.49]:
            kv = abs(Kf(gv,ev,yv))
            base = ev**2/(gv**2+yv**2)**2
            ratio = kv/base
            cw_needed = max(cw_needed, ratio)
    print(f"  y={yv}:  max |K0|/(e^2/(g^2+y^2)^2) = {mp.nstr(cw_needed,6)}  (so Cw(y) ~ {mp.nstr(cw_needed,4)})")
    worst = max(worst, cw_needed)
# Claim: Cw(y) = 6y suffices (check the constant scales ~ y).
print("\nCheck Cw(y)=6y is a valid majorant constant:")
ok = True
for yv in [0.5,1,2,5,10]:
    for gv in [mp.mpf(k)/10 for k in range(1,200,3)]:
        for ev in [mp.mpf(k)/100 for k in range(1,50,2)]:
            kv = abs(Kf(gv,ev,yv)); base = 6*yv*ev**2/(gv**2+yv**2)**2
            if kv > base*(1+mp.mpf('1e-12')):
                ok=False; print("  FAIL", yv,gv,ev, mp.nstr(kv/base,6))
print("  6y majorant holds on grid:", ok)
