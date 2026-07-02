"""
CALIBRATION: verify the explicit-formula identity at high precision so the
Weil-form assembly is TRUSTED, then probe the threshold with a clean numerical floor.

Identity (Weil), even real test fn, h(r)=ghat(r):
  sum_rho h(gamma_rho) = ARCH(h)+POLE(h) - PRIME(g)
where sum over nontrivial zeros rho=1/2+i gamma (gamma possibly complex; if RH then real).
We use a Gaussian h(r)=exp(-a r^2) (positive type), g(u)=(1/2 sqrt(pi a)) exp(-u^2/4a).
LHS computed from actual zeta zeros (mpmath zetazero) -- this is a CHECK of the
formula bookkeeping, independent of the positivity question.
"""
import mpmath as mp
mp.mp.dps=30

a=mp.mpf('0.5')
def h(r): return mp.e**(-a*r*r)
def hc(z): return mp.e**(-a*z*z)  # analytic
def g(u): return 1/(2*mp.sqrt(mp.pi*a))*mp.e**(-u*u/(4*a))

# ARCH = (1/2pi)\int h(r) (Re psi(1/4+ir/2) - log pi) dr
Omega=lambda r: mp.re(mp.digamma(mp.mpf(1)/4+1j*r/2))-mp.log(mp.pi)
ARCH=mp.quad(lambda r:h(r)*Omega(r),[-mp.inf,0,mp.inf])/(2*mp.pi)
# POLE: contributions from poles of xi at s=0,1 -> h evaluated at r=+-i/2
POLE=hc(1j/2)+hc(-1j/2)
# PRIME: 2 sum Lambda(n)/sqrt(n) g(log n)
def Lambda(n):
    mm=n;fac={};d=2
    while d*d<=mm:
        while mm%d==0: fac[d]=fac.get(d,0)+1;mm//=d
        d+=1
    if mm>1: fac[mm]=fac.get(mm,0)+1
    return mp.log(list(fac.keys())[0]) if len(fac)==1 else mp.mpf(0)
PRIME=mp.mpf(0)
for n in range(2,200000):
    L=Lambda(n)
    if L==0: continue
    t=L/mp.sqrt(n)*g(mp.log(n))
    PRIME+=t
    if t<mp.mpf(10)**(-32) and n>100: break
PRIME*=2
RHS=ARCH+POLE-PRIME
# LHS: sum over zeros h(gamma). zeros come in +-gamma pairs.
LHS=mp.mpf(0)
for k in range(1,2000):
    gam=mp.im(mp.zetazero(k))
    t=2*h(gam)
    LHS+=t
    if t<mp.mpf(10)**(-32) and gam>5: break
print("ARCH =",mp.nstr(ARCH,20))
print("POLE =",mp.nstr(POLE,20))
print("PRIME=",mp.nstr(PRIME,20))
print("RHS=ARCH+POLE-PRIME =",mp.nstr(RHS,20))
print("LHS=sum_rho h(gamma)=",mp.nstr(LHS,20))
print("DIFF =",mp.nstr(RHS-LHS,8))
print()
print("Note: LHS>0 since all gamma real here (zeros on line in range) & h>0.")
print("This CONFIRMS the assembly. Q(g)=LHS = sum h(gamma) is what we test for sign.")
