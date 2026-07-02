import mpmath as mp
from sympy import isprime as _isprime
mp.mp.dps=25
def dig(z): return mp.digamma(z)
PRIMES=[p for p in range(2,5000) if _isprime(p)]
LOGP={p:mp.log(p) for p in PRIMES}
def arch_term(h):
    integ=lambda r:h(r)*(mp.re(dig(mp.mpf(1)/4+1j*r/2))-mp.log(mp.pi))
    return mp.quad(integ,[-mp.inf,0,mp.inf])/(2*mp.pi)
def pole_term(h): return mp.re(h(1j/2)+h(-1j/2))
def prime_term(g):
    s=mp.mpf(0)
    for p in PRIMES:
        lp=LOGP[p]
        for k in range(1,30):
            u=k*lp;t=lp*p**(-mp.mpf(k)/2)*g(u);s+=t
            if abs(t)<mp.mpf(10)**(-24):break
    return 2*s
sig=mp.mpf('1.0');C=2*mp.pi*sig*sig
# direct Q for psi = a0 bump@0 + a1 bump@1
def Qdirect(a0,a1):
    cs=[a0,a1];us=[mp.mpf(0),mp.mpf(1)]
    def h(r):
        S=sum(c*mp.e**(-1j*r*u) for c,u in zip(cs,us))
        return C*mp.e**(-(sig*sig)*r*r)*abs(S)**2
    def g(uu):
        tot=mp.mpf(0)
        for cj,uj in zip(cs,us):
            for ck,uk in zip(cs,us):
                d=uu-(uj-uk);tot+=cj*ck*mp.sqrt(mp.pi)*sig*mp.e**(-(d*d)/(4*sig*sig))
        return tot
    return arch_term(h)+pole_term(h)-prime_term(g)
# bilinear B
def Bmn(um,un):
    def h(r):return C*mp.e**(-(sig*sig)*r*r)*mp.e**(-1j*r*(um-un))
    def g(uu):
        d=uu-(um-un);return mp.sqrt(mp.pi)*sig*mp.e**(-(d*d)/(4*sig*sig))
    return arch_term(h)+pole_term(h)-prime_term(g)
B00=Bmn(0,0);B11=Bmn(1,1);B01=Bmn(0,1);B10=Bmn(1,0)
a0,a1=mp.mpf('1.0'),mp.mpf('0.7')
quad=a0*a0*B00+a1*a1*B11+a0*a1*(B01+B10)
print("Qdirect(1,0.7) =",mp.nstr(Qdirect(a0,a1),12))
print("a^T B a        =",mp.nstr(mp.re(quad),12))
print("B00,B11=",mp.nstr(mp.re(B00),8),mp.nstr(mp.re(B11),8))
print("B01,B10=",mp.nstr(B01,8),mp.nstr(B10,8))
print("Qdirect(1,0)=",mp.nstr(Qdirect(1,0),10)," B00=",mp.nstr(mp.re(B00),10))
