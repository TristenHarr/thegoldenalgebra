import sympy as sp, mpmath as mp
mp.mp.dps=30
x,y,g,e = sp.symbols('x y g e', real=True)
def Im_recip(zx,zy,ax,ay): return -(zy-ay)/((zx-ax)**2+(zy-ay)**2)
def Im_Kpair(zx,zy,ux,uy): return Im_recip(zx,zy,ux,uy)+Im_recip(zx,zy,-ux,-uy)
ImD = Im_Kpair(x,y,g,e)+Im_Kpair(x,y,g,-e)-2*Im_Kpair(x,y,g,0)
K0 = sp.simplify((-ImD).subs(x,0))
Kf = sp.lambdify((g,e,y), K0, 'mpmath')

# Find sup over g>=0, 0<e<=1/2 of  |K0| * (g^2+y^2)^2 / (e^2 * y)   for several y.
print("sup_{g,e} |K0|(g^2+y^2)^2/(e^2 y):")
for yv in [0.25,0.5,1,2,5,10,50]:
    best=mp.mpf(0); arg=None
    for gv in [mp.mpf(k)/100 for k in range(1,4000,3)]:
        for ev in [mp.mpf(k)/200 for k in range(1,101,1)]:
            r = abs(Kf(gv,ev,yv))*(gv**2+yv**2)**2/(ev**2*yv)
            if r>best: best=r; arg=(gv,ev)
    print(f"  y={yv}:  sup ~ {mp.nstr(best,6)}  at (g,e)={ (mp.nstr(arg[0],4),mp.nstr(arg[1],4)) }")

# The sup of |K0|(g^2+y^2)^2/(e^2 y) appears bounded by 12 (small e limit).
# Check the EXACT small-e leading: K0 = 4 e^2 y (y^2-3g^2)/(g^2+y^2)^3 + O(e^4).
# So |K0|(g^2+y^2)^2/(e^2 y) -> 4|y^2-3g^2|/(g^2+y^2).  Sup over g of 4|y^2-3g^2|/(g^2+y^2):
gg=sp.symbols('gg',nonnegative=True); yy=sp.symbols('yy',positive=True)
f = 4*sp.Abs(yy**2-3*gg**2)/(gg**2+yy**2)
# at g=0: 4 y^2/y^2 = 4 ; as g->oo: 12 g^2/g^2 = 12.  So sup_g = 12 (approached).
print("\nSmall-e leading sup over gamma of 4|y^2-3g^2|/(g^2+y^2):")
print("  g=0 ->", sp.simplify(f.subs(gg,0)), "(=4)")
print("  g->oo ->", sp.limit(4*(3*gg**2-yy**2)/(gg**2+yy**2), gg, sp.oo), "(=12)")
print("  => uniform constant Cw = 12*y works in the small-e regime;")
print("     the global sup including finite e is verified numerically below.")

# Global check: is |K0| <= 12 y e^2/(g^2+y^2)^2 everywhere?
ok=True; mx=mp.mpf(0)
import random
random.seed(1)
for _ in range(200000):
    yv=mp.mpf(random.uniform(0.05,20)); gv=mp.mpf(random.uniform(0,300)); ev=mp.mpf(random.uniform(1e-4,0.5))
    lhs=abs(Kf(gv,ev,yv)); rhs=12*yv*ev**2/(gv**2+yv**2)**2
    if rhs>0: mx=max(mx,lhs/rhs)
    if lhs>rhs*(1+mp.mpf('1e-9')): ok=False
print("\n|K0| <= 12 y e^2/(g^2+y^2)^2  holds on 2e5 random pts:", ok, " max ratio:", mp.nstr(mx,8))
