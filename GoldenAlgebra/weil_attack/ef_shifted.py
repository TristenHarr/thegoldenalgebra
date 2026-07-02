"""
Test explicit formula for an EVEN test function with structure at u!=0:
psi symmetric pair: bumps at +u0 and -u0 with equal coeff => psi even => 
hatpsi(r)=2 cos(r u0)* gauss => h(r)=4 cos^2(r u0) gauss^2 >=0, even, real.
This is a clean Weil test function. Check ZS == ARCH+POLE-PRIME.
"""
import mpmath as mp
from sympy import isprime as _isprime
mp.mp.dps=30
def dig(z): return mp.digamma(z)
PRIMES=[p for p in range(2,30000) if _isprime(p)]
sig=mp.mpf('0.3')  # wider in freq so zeros contribute
C=2*mp.pi*sig*sig
u0=mp.mpf('1.0')
# psi(x)= gauss(x-u0)+gauss(x+u0). hatpsi(r)=sqrt(2pi)sig e^{-sig^2 r^2/2} *2cos(r u0)
# h(r)=|hatpsi|^2 = C * e^{-sig^2 r^2} * 4 cos^2(r u0)
def h(r): return C*mp.e**(-(sig*sig)*r*r)*4*mp.cos(r*u0)**2
def hh(z): # analytic continuation: cos^2 stays cos^2
    return C*mp.e**(-(sig*sig)*z*z)*4*mp.cos(z*u0)**2
# g = autocorrelation. psi corr psi at u: bumps at u in {-2u0,0,2u0} (and 0 twice)
def g(uu):
    tot=mp.mpf(0)
    for uj in [u0,-u0]:
        for uk in [u0,-u0]:
            d=uu-(uj-uk);tot+=mp.sqrt(mp.pi)*sig*mp.e**(-(d*d)/(4*sig*sig))
    return tot
W=lambda r: mp.re(dig(mp.mpf(1)/4+1j*r/2))-mp.log(mp.pi)
A=mp.quad(lambda r:h(r)*W(r),[-mp.inf,0,mp.inf])/(2*mp.pi)
P=mp.re(hh(1j/2)+hh(-1j/2))
s=mp.mpf(0)
for p in PRIMES:
    lp=mp.log(p)
    for k in range(1,50):
        u=k*lp;t=lp*p**(-mp.mpf(k)/2)*g(u);s+=t
        if t<mp.mpf(10)**(-28) and u>2*u0+3:break
PR=2*s
ZS=mp.mpf(0)
for n in range(1,3000):
    gm=mp.im(mp.zetazero(n));t=2*h(gm);ZS+=t
    if t<mp.mpf(10)**(-28) and gm>10:break
print("ZS   =",mp.nstr(ZS,15))
print("ARCH =",mp.nstr(A,15))
print("POLE =",mp.nstr(P,15))
print("PRIME=",mp.nstr(PR,15))
print("A+P-PR=",mp.nstr(mp.re(A+P-PR),15))
print("diff =",mp.nstr(ZS-mp.re(A+P-PR),8))
