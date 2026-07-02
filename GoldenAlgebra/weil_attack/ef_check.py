"""
Verify the Weil/Guinand explicit formula numerically with a Gaussian test function,
then assemble the Weil quadratic form Q(g) and probe its sign structure.

Convention (Guinand-Weil): for even h(r), g(u) = (1/2pi) int h(r) e^{-i r u} dr.
   sum_rho h(gamma) = ARCH(h) + POLE(h) - PRIME(g)
where gamma runs over imaginary parts of nontrivial zeros (both signs),
   ARCH(h) = (1/2pi) int h(r) * [ Re psi(1/4 + i r/2) - log pi ] dr
   POLE(h) = h(i/2) + h(-i/2)      (from the pole of zeta at s=1 and trivial structure)
   PRIME(g) = 2 sum_{p,k} (log p) p^{-k/2} g(k log p)
"""
import mpmath as mp
from sympy import isprime as _isprime
mp.mp.dps = 30

def psi(z): return mp.digamma(z)

# Test function h(r) = exp(-a r^2). Then g(u) = (1/(2 sqrt(pi a))) exp(-u^2/(4a)).
def make_gaussian(a):
    def h(r): return mp.e**(-a*r*r)
    def g(u): return (1/(2*mp.sqrt(mp.pi*a)))*mp.e**(-(u*u)/(4*a))
    return h,g

def arch_term(h, a):
    # (1/2pi) int_{-inf}^{inf} h(r)*(Re psi(1/4 + i r/2) - log pi) dr
    integ = lambda r: h(r)*(mp.re(psi(mp.mpf(1)/4 + 1j*r/2)) - mp.log(mp.pi))
    val = mp.quad(integ, [-mp.inf, 0, mp.inf])
    return val/(2*mp.pi)

def pole_term(h):
    return h(1j/2) + h(-1j/2)

def prime_term(g, maxp=2000, maxk=20):
    s = mp.mpf(0)
    p = 2
    while p <= maxp:
        if _isprime(p):
            lp = mp.log(p)
            for k in range(1, maxk+1):
                u = k*lp
                term = lp * p**(-mp.mpf(k)/2) * g(u)
                s += term
                if term < mp.mpf(10)**(-25): break
        p += 1
    return 2*s

def zero_sum(h, N=2000):
    # sum over nontrivial zeros, both signs: 2*sum_{n} h(gamma_n) for h even real
    s = mp.mpf(0)
    for n in range(1, N+1):
        g = mp.im(mp.zetazero(n))
        s += 2*h(g)   # both +gamma and -gamma
    return s

a = mp.mpf('2.0')
h,g = make_gaussian(a)
ZS = zero_sum(h, N=500)
A = arch_term(h,a)
P = pole_term(h)
PR = prime_term(g)
RHS = A + P - PR
print("a =", a)
print("zero sum      =", mp.nstr(ZS, 15))
print("arch          =", mp.nstr(A, 15))
print("pole          =", mp.nstr(P, 15))
print("prime         =", mp.nstr(PR, 15))
print("RHS=A+P-PR    =", mp.nstr(RHS, 15))
print("diff (ZS-RHS) =", mp.nstr(ZS-RHS, 8))
