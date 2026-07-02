"""
Resonating Weil test function, ANALYTIC transforms (fast & exact).
h(r)=phi(r)^2, phi(r)=e^{-b(r-g0)^2}+e^{-b(r+g0)^2}.
Expand: h(r)= e^{-2b(r-g0)^2} + e^{-2b(r+g0)^2} + 2 e^{-b((r-g0)^2+(r+g0)^2)}.
 (r-g0)^2+(r+g0)^2 = 2r^2+2g0^2 => last term = 2 e^{-2b g0^2} e^{-2b r^2}.
So h(r)= sum of three Gaussians:
   G(r;c,A) := A e^{-2b (r-c)^2}, with centers c in {+g0, -g0, 0} and amps {1,1,2e^{-2bg0^2}}.
For a Gaussian gauss_r(r)=A e^{-beta (r-c)^2} (beta=2b), its inverse FT (g) is
   g(u)= (1/2pi) int A e^{-beta(r-c)^2} e^{i r u} dr = A/(2 sqrt(pi beta)) e^{-u^2/(4 beta)} e^{i c u}.
Since centers come in +/-c pairs with equal amp, sum is real: cos(c u).
"""
import mpmath as mp
from sympy import isprime as _isprime
mp.mp.dps=25
def dig(z): return mp.digamma(z)
PRIMES=[p for p in range(2,200000) if _isprime(p)]
g0=mp.mpf('14.134725'); b=mp.mpf('1.5'); beta=2*b
# three gaussian components: (center, amp)
comps=[(g0,mp.mpf(1)),(-g0,mp.mpf(1)),(mp.mpf(0),2*mp.e**(-2*b*g0*g0))]
def h(z):
    return sum(A*mp.e**(-beta*(z-c)**2) for c,A in comps)
def g(u):  # inverse FT, real
    tot=mp.mpf(0)
    for c,A in comps:
        tot+= A/(2*mp.sqrt(mp.pi*beta))*mp.e**(-(u*u)/(4*beta))*mp.cos(c*u)
    return tot
W=lambda r: mp.re(dig(mp.mpf(1)/4+1j*r/2))-mp.log(mp.pi)
# ARCH per gaussian component analytically-ish via quad (fast, 1D, smooth)
A_arch=mp.mpf(0)
for c,Amp in comps:
    val=mp.quad(lambda r:Amp*mp.e**(-beta*(r-c)**2)*W(r),[-mp.inf,c-8,c,c+8,mp.inf])
    A_arch+=val
A_arch/= (2*mp.pi)
P=mp.re(h(1j/2)+h(-1j/2))
s=mp.mpf(0)
for p in PRIMES:
    lp=mp.log(p)
    for k in range(1,80):
        u=k*lp;t=lp*p**(-mp.mpf(k)/2)*g(u);s+=t
        if abs(t)<mp.mpf(10)**(-22) and u>40:break
PR=2*s
Q=mp.re(A_arch+P-PR)
print("ARCH=",mp.nstr(A_arch,12),"POLE=",mp.nstr(P,12),"PRIME=",mp.nstr(PR,12))
print("Q=",mp.nstr(Q,12))
ZS=mp.mpf(0)
for n in range(1,1500):
    gm=mp.im(mp.zetazero(n));t=2*h(gm);ZS+=t
    if t<mp.mpf(10)**(-22) and gm>3*g0:break
print("true ZS=",mp.nstr(ZS,12)," diff=",mp.nstr(Q-ZS,6))
print("h(g0)=",mp.nstr(h(g0),8))
for d in [mp.mpf('0.1'),mp.mpf('0.2'),mp.mpf('0.3'),mp.mpf('0.4')]:
    args=[g0-1j*d,g0+1j*d,-g0-1j*d,-g0+1j*d]
    print(f" off-line delta={float(d)}: contrib={mp.nstr(mp.re(sum(h(z) for z in args)),8)}")
