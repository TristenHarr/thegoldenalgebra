import mpmath as mp
from sympy import isprime as _isprime
mp.mp.dps = 30

def psi(z): return mp.digamma(z)

def make_gaussian(a):
    def h(r): return mp.e**(-a*r*r)
    def g(u): return (1/(2*mp.sqrt(mp.pi*a)))*mp.e**(-(u*u)/(4*a))
    return h,g

def arch_term(h):
    integ = lambda r: h(r)*(mp.re(psi(mp.mpf(1)/4 + 1j*r/2)) - mp.log(mp.pi))
    return mp.quad(integ, [-mp.inf, 0, mp.inf])/(2*mp.pi)

def pole_term(h):
    return mp.re(h(1j/2) + h(-1j/2))

def prime_term(g, maxp=5000, maxk=30):
    s = mp.mpf(0); p = 2
    while p <= maxp:
        if _isprime(p):
            lp = mp.log(p)
            for k in range(1, maxk+1):
                u = k*lp
                term = lp * p**(-mp.mpf(k)/2) * g(u)
                s += term
                if term < mp.mpf(10)**(-28): break
        p += 1
    return 2*s

def zero_sum(h, N=3000):
    s = mp.mpf(0)
    for n in range(1, N+1):
        gm = mp.im(mp.zetazero(n))
        t = 2*h(gm)
        s += t
        if t < mp.mpf(10)**(-28) and gm>20: break
    return s

for a in [mp.mpf('0.05'), mp.mpf('0.02'), mp.mpf('0.1')]:
    h,g = make_gaussian(a)
    ZS = zero_sum(h, N=3000)
    A = arch_term(h); P = pole_term(h); PR = prime_term(g)
    RHS = A + P - PR
    print(f"a={float(a):.3f}  ZS={mp.nstr(ZS,12)}  RHS={mp.nstr(RHS,12)}  diff={mp.nstr(ZS-RHS,6)}")
