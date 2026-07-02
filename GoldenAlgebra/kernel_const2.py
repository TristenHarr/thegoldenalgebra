import sympy as sp, mpmath as mp, random
mp.mp.dps=30
x,y,g,e = sp.symbols('x y g e', real=True)
def Im_recip(zx,zy,ax,ay): return -(zy-ay)/((zx-ax)**2+(zy-ay)**2)
def Im_Kpair(zx,zy,ux,uy): return Im_recip(zx,zy,ux,uy)+Im_recip(zx,zy,-ux,-uy)
ImD = Im_Kpair(x,y,g,e)+Im_Kpair(x,y,g,-e)-2*Im_Kpair(x,y,g,0)
K0 = sp.simplify((-ImD).subs(x,0))
Kf = sp.lambdify((g,e,y), K0, 'mpmath')

# The blow-up regions are small y with small g, large e.  There |K0| can be O(1/(g+...)).
# But note for the anti-Herglotz program y is FIXED (probe height) and we care about
# the family over the off-line population (g,e).  Restrict e<=1/2 (always true: |eta|<=1/2).
# Seek a UNIFORM-in-(g,e) majorant for a FIXED y>0:  |K0| <= Cw(y) * e^2/(g^2+y^2)^2.
# Compute Cw(y) := sup_{g>0, 0<e<=1/2} |K0|(g,e,y) (g^2+y^2)^2 / e^2  for a grid of y.
print("Cw(y) := sup_{g,0<e<=1/2} |K0|(g^2+y^2)^2/e^2  (FIXED y):")
data=[]
for yv in [0.1,0.25,0.5,1,2,5,10,20]:
    best=mp.mpf(0)
    for gv in [mp.mpf(k)/200 for k in range(1,8000,2)]:
        for ev in [mp.mpf(k)/200 for k in range(1,101,1)]:
            r=abs(Kf(gv,ev,yv))*(gv**2+yv**2)**2/ev**2
            if r>best: best=r
    data.append((yv,best)); print(f"  y={yv}: Cw={mp.nstr(best,6)},  Cw/y={mp.nstr(best/yv,6)}")
# fit: does Cw(y) ~ const * max(y, 1/y)?  print Cw*y and Cw/y
print("\nCw(y)*y and Cw(y)/y:")
for yv,c in data:
    print(f"  y={yv}: Cw*y={mp.nstr(c*yv,5)}  Cw/y={mp.nstr(c/yv,5)}")
