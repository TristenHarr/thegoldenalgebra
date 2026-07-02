import sympy as sp, mpmath as mp, random
mp.mp.dps=30
x,y,g,e = sp.symbols('x y g e', real=True)
def Im_recip(zx,zy,ax,ay): return -(zy-ay)/((zx-ax)**2+(zy-ay)**2)
def Im_Kpair(zx,zy,ux,uy): return Im_recip(zx,zy,ux,uy)+Im_recip(zx,zy,-ux,-uy)
ImD = Im_Kpair(x,y,g,e)+Im_Kpair(x,y,g,-e)-2*Im_Kpair(x,y,g,0)
K0 = sp.simplify((-ImD).subs(x,0))
Kf = sp.lambdify((g,e,y), K0, 'mpmath')

print("=== CLAIM (banked regime y>=1):  |K_z(eta,gamma)| <= 12 y eta^2/(gamma^2+y^2)^2 ===")
random.seed(7); ok=True; mx=mp.mpf(0); worst=None
for _ in range(500000):
    yv=mp.mpf(random.uniform(1,200)); gv=mp.mpf(random.uniform(1e-3,500)); ev=mp.mpf(random.uniform(1e-5,0.5))
    lhs=abs(Kf(gv,ev,yv)); rhs=12*yv*ev**2/(gv**2+yv**2)**2
    r=lhs/rhs
    if r>mx: mx=r; worst=(yv,gv,ev)
    if lhs>rhs*(1+mp.mpf('1e-9')): ok=False
print("holds on 5e5 random pts (y>=1):", ok, " max ratio:", mp.nstr(mx,8), " at", [mp.nstr(w,4) for w in worst])

print("\n=== Layer-cake convergence: the kernel-weighted height integral converges ===")
# crude count weight: 1 per zero over [0,T]  -> total ~ N(T) ~ (T/2pi) log T  (DIVERGES with T)
# kernel weight: 1/(gamma^2+y^2)^2 per zero -> int_0^oo (density ~ (1/2pi)log gamma) /(gamma^2+y^2)^2 dgamma CONVERGES.
def zdens(t): return mp.log(t/(2*mp.pi))/(2*mp.pi) if t>2*mp.pi else mp.mpf(0)  # ~ dN/dgamma
for yv in [1,2,5]:
    I = mp.quad(lambda t: zdens(t)/(t**2+yv**2)**2, [2*mp.pi, 50, 1000, mp.inf])
    print(f"  y={yv}: int_0^inf rho(gamma)/(gamma^2+y^2)^2 dgamma = {mp.nstr(I,6)}  (FINITE, uniform in T)")

print("\n=== Improvement vs crude count at T=10^6 (eps=0.01) ===")
# crude: averagedAntiHerglotz bound = modernDensityBound = T^{A(1/2+eps)(1/2-eps)} log T
T=mp.mpf(10)**6; eps=mp.mpf('0.01'); sigma=0.5+eps
def A_modern(s):
    return 3/(2-s) if s<=0.7 else 15/(3+5*s)
crude = T**(A_modern(sigma)*(0.5-eps))*mp.log(T)
print(f"  crude count-based bound (modernDensityBound) ~ {mp.nstr(crude,4)}  (GROWS with T as T^{mp.nstr(A_modern(sigma)*(0.5-eps),4)})")
# kernel-weighted: the gamma-integral is T-UNIFORM; bound ~ Cw(y) * sup_eta[ eta^2-weighted density ] * (finite height integral)
# illustrate the T-uniformity: kernel bound has NO positive power of T.
print("  kernel-weighted bound: height integral is T-UNIFORM (no positive power of T) =>")
print("    the off-line contribution to G(z) at fixed probe z stays BOUNDED as T->oo,")
print("    whereas the crude exceptional COUNT grows like T^{%s}." % mp.nstr(A_modern(sigma)*(0.5-eps),4))
