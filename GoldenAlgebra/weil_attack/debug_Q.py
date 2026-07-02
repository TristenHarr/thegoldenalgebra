import mpmath as mp
from sympy import isprime as _isprime
mp.mp.dps=25
def dig(z): return mp.digamma(z)
PRIMES=[p for p in range(2,20000) if _isprime(p)]
LOGP={p:mp.log(p) for p in PRIMES}
sig=mp.mpf('1.0');C=2*mp.pi*sig*sig
vec=[mp.mpf(x) for x in ['-0.69254','-0.17057','-0.1291','-0.21003','-0.33588','-0.37533','0.42051']]
us=[mp.mpf(n) for n in range(7)]
def h(r):
    S=sum(c*mp.e**(-1j*r*u) for c,u in zip(vec,us))
    return C*mp.e**(-(sig*sig)*r*r)*abs(S)**2
def g(uu):
    tot=mp.mpf(0)
    for cj,uj in zip(vec,us):
        for ck,uk in zip(vec,us):
            d=uu-(uj-uk);tot+=cj*ck*mp.sqrt(mp.pi)*sig*mp.e**(-(d*d)/(4*sig*sig))
    return tot
A=mp.quad(lambda r:h(r)*(mp.re(dig(mp.mpf(1)/4+1j*r/2))-mp.log(mp.pi)),[-mp.inf,0,mp.inf])/(2*mp.pi)
P=mp.re(h(1j/2)+h(-1j/2))
# prime sum: note g samples at u up to ~ 6 (=u_j-u_k max) + few -> need k log p near up to ~6-8
s=mp.mpf(0)
for p in PRIMES:
    lp=LOGP[p]
    for k in range(1,40):
        u=k*lp;t=lp*p**(-mp.mpf(k)/2)*g(u);s+=t
PR=2*s
print("ARCH=",mp.nstr(A,12))
print("POLE=",mp.nstr(P,12))
print("PRIME=",mp.nstr(PR,12))
print("Q=A+P-PR=",mp.nstr(mp.re(A+P-PR),12))
print("(should be ~0, the zero sum)")
# check: is POLE = h(i/2)+h(-i/2) finite? h at complex arg uses abs(S)**2 -> |.|^2 of complex is wrong analytic continuation!
print("\nh(1j/2) via abs:",mp.nstr(h(1j/2),10))
# correct analytic h(z)=C e^{-sig^2 z^2} S(z) Sbar(z) where Sbar is conj-analytic
def hh(z):
    S=sum(c*mp.e**(-1j*z*u) for c,u in zip(vec,us))
    Sb=sum(c*mp.e**(1j*z*u) for c,u in zip(vec,us))  # conj of S for real z, analytic cont
    return C*mp.e**(-(sig*sig)*z*z)*S*Sb
print("hh(1j/2) analytic:",mp.nstr(hh(1j/2),10))
P2=mp.re(hh(1j/2)+hh(-1j/2))
print("POLE corrected=",mp.nstr(P2,12))
print("Q corrected=",mp.nstr(mp.re(A+P2-PR),12))
