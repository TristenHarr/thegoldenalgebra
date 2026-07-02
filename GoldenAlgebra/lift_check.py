"""
lift_check.py — get the harmonic-lift structure RIGHT (no faking).

m(Y,eta,a) with a = gamma - x. The single off-line zero's contribution to
G(z)= -Im(Xi'/Xi)(z) at z=x+iY comes from FOUR poles {±gamma ± i eta} (FE quad)
minus two reference atoms. The honest object: G(z) is harmonic in z=x+iY AWAY from
the poles, but the per-zero net m is a sum of Poisson kernels of DIFFERENT heights:

  -Im 1/(z - w) for a pole w=p+iq is the Poisson-type   (Y-q)/((x-p)^2+(Y-q)^2).

So the contribution of a pole at height q is a Poisson kernel centered at height q,
evaluated at probe height Y. Convolving in x by P_h does NOT simply send Y->Y+h for
a sum of poles at DIFFERENT heights unless ALL are above the probe. Let's see exactly
what P_h does pole-by-pole and whether the >=1/2 conclusion survives.
"""
import mpmath as mp
mp.mp.dps = 40

def poisson_pole(Y, q, p, x):
    # -Im 1/(z-w), w=p+iq, z=x+iY  =  (Y-q)/((x-p)^2+(Y-q)^2)
    Y,q,p,x = map(mp.mpf,(Y,q,p,x))
    return (Y-q)/((x-p)**2+(Y-q)**2)

def P_h(h,x):
    h,x=mp.mpf(h),mp.mpf(x)
    return (1/mp.pi)*h/(x**2+h**2)

# Convolve a single pole-kernel in x by P_h.
# Known: P_h * [ (Y-q)/((.-p)^2+(Y-q)^2) ] (x0)
#   For Y-q>0 (probe ABOVE pole): kernel is (Y-q) Poisson => conv = (Y-q+h) Poisson at x0? 
#   Actually Poisson semigroup: P_h * P_t = P_{t+h} ONLY for t,h>0 (both upper).
#   Here "t" = Y-q. If Y-q>0, conv lifts to height Y-q+h: value (Y-q+h)/((x0-p)^2+(Y-q+h)^2)
#      = poisson_pole(Y+h, q, p, x0). GOOD: lifts Y->Y+h.
#   If Y-q<0 (probe BELOW pole): kernel is (Y-q)/((.)^2+(q-Y)^2), a NEGATIVE multiple of
#      Poisson at height q-Y>0. P_h * that = (Y-q) * [Poisson at height q-Y+h]?? NO:
#      semigroup needs the *given* function be P_{q-Y}; it is -(q-Y)*... wait sign.
#      kernel = (Y-q)/((x-p)^2+(q-Y)^2) = -(q-Y)/((x-p)^2+(q-Y)^2) = -pi*(q-Y? ) ...
#   Let's just numerically test BOTH regimes.
print("Pole-by-pole Poisson lift test (does P_h send Y->Y+h?):")
for (Y,q,p,h,x0,tag) in [(0.6,0.4,3.0,0.2,1.0,"probe ABOVE pole (Y>q)"),
                          (0.2,0.45,3.0,0.1,1.0,"probe BELOW pole (Y<q)"),
                          (0.2,0.45,3.0,0.35,1.0,"BELOW, lift past pole (Y+h>q)")]:
    f=lambda x: poisson_pole(Y,q,p,x)
    conv=mp.quad(lambda x: P_h(h,x0-x)*f(x), [-mp.inf,p,mp.inf])
    lift=poisson_pole(Y+h,q,p,x0)
    print(f"  {tag}: P_h*ker={mp.nstr(conv,8)}, pole@height Y+h={mp.nstr(lift,8)}, match={abs(conv-lift)<1e-10}")
