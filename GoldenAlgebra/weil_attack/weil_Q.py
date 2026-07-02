"""
The Weil quadratic form, expressed purely on the (arch+pole-prime) side so it
is computable WITHOUT zeros. For test data psi (even, real), set g = psi * psi~
(autocorrelation) so that h = |hat psi|^2 >= 0 on R.

Q(psi) = ARCH(h) + POLE(h) - PRIME(g),  with h = |hat psi|^2, g = psi corr psi.

We want: is Q(psi) >= 0 for ALL psi?  (RH <=> yes).

Strategy probe 1: take psi = real Gaussian bump family, build h = |hatpsi|^2
which is itself a Gaussian => reuse machinery. Compute Q and watch its sign
as we vary parameters. Look for the most-negative direction (the Bombieri
negative eigenvalue is invisible if RH true, but the *near-zero* structure
shows where positivity is fragile).
"""
import mpmath as mp
from sympy import isprime as _isprime
mp.mp.dps = 30

def psi_dig(z): return mp.digamma(z)

def arch_term(h):
    integ = lambda r: h(r)*(mp.re(psi_dig(mp.mpf(1)/4 + 1j*r/2)) - mp.log(mp.pi))
    return mp.quad(integ, [-mp.inf, 0, mp.inf])/(2*mp.pi)
def pole_term(h):
    return mp.re(h(1j/2) + h(-1j/2))
def prime_term(g, maxp=5000, maxk=30):
    s = mp.mpf(0); p = 2
    while p <= maxp:
        if _isprime(p):
            lp = mp.log(p)
            for k in range(1, maxk+1):
                u = k*lp; term = lp*p**(-mp.mpf(k)/2)*g(u); s += term
                if term < mp.mpf(10)**(-28): break
        p += 1
    return 2*s

# Family: psi(x) = sum_j c_j delta-like Gaussians at shift t_j? Instead use
# h(r) = (sum_j c_j cos(t_j r)) * env(r)? Simpler: h = |F|^2 where
# F(r) = sum_j c_j exp(-b (r - m_j)^2)... but h must be even & of positive type.
# Cleanest positive-type family: h(r) = |sum_j c_j e^{-a r^2} e^{i r u_j}|^2 form.
# Equivalent g(u) = autocorrelation of sum_j c_j (gaussian centered at u_j).
# Let psi(x) = sum_j c_j gauss(x-u_j; sig). Then g = psi corr psi (real, even if symmetric set).

def build(cs, us, sig):
    a = sig
    # h(r) = |hatpsi(r)|^2 ; hat of gauss(x-u;sig)= exp(-sig^2 r^2/2) e^{-i r u} * const
    # Use psi(x)=sum c_j exp(-(x-u_j)^2/(2 sig^2)). hatpsi(r)= sqrt(2pi)sig exp(-sig^2 r^2/2) sum c_j e^{-i r u_j}
    C = 2*mp.pi*sig*sig
    def h(r):
        S = sum(c*mp.e**(-1j*r*u) for c,u in zip(cs,us))
        return C*mp.e**(-sig*sig*r*r)*(S*mp.conj(S)).real if False else C*mp.e**(-(sig*sig)*r*r)*abs(S)**2
    # g(u)=autocorrelation: (psi corr psi)(u)= sum_{j,k} c_j c_k gauss(u-(u_j-u_k); sqrt2 sig)... 
    def g(uu):
        tot = mp.mpf(0)
        for cj,uj in zip(cs,us):
            for ck,uk in zip(cs,us):
                d = uu-(uj-uk)
                tot += cj*ck*mp.sqrt(mp.pi)*sig*mp.e**(-(d*d)/(4*sig*sig))
        return tot
    return h,g

def Q(cs,us,sig):
    h,g = build(cs,us,sig)
    return arch_term(h)+pole_term(h)-prime_term(g)

# single bump
print("single bump sig=1:", mp.nstr(Q([1],[0],1),12))
print("single bump sig=0.5:", mp.nstr(Q([1],[0],mp.mpf('0.5')),12))
print("two bumps:", mp.nstr(Q([1,1],[0,2],1),12))
print("two bumps opp sign:", mp.nstr(Q([1,-1],[0,2],1),12))
