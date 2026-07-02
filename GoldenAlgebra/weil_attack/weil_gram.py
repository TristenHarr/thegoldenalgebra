"""
Build the Weil quadratic form as a Gram matrix Q[i,j] in a basis of test functions,
then look at its eigenvalues. This is the real object: RH <=> Q is PSD on every
finite-dim subspace of admissible test functions.

Basis: psi_n(x) = Gaussian bump centered at u_n = n*step (n=0..N), fixed width sig.
Q(sum a_n psi_n) = sum_{m,n} a_m a_n B[m,n],   B[m,n] = bilinear Weil form.

Bilinear form from polarization: B[m,n] uses
  h_{mn}(r) = hatpsi_m(r) conj(hatpsi_n(r))  (Hermitian; for real symmetric basis -> real)
  g_{mn}(u) = (psi_m corr psi_n)(u)
Q_bilinear = ARCH(h_mn)+POLE(h_mn) - PRIME(g_mn).
"""
import mpmath as mp
from sympy import isprime as _isprime
mp.mp.dps = 25

def dig(z): return mp.digamma(z)
PRIMES=[p for p in range(2,4000) if _isprime(p)]
LOGP={p:mp.log(p) for p in PRIMES}

def arch_term(h):
    integ = lambda r: h(r)*(mp.re(dig(mp.mpf(1)/4+1j*r/2))-mp.log(mp.pi))
    return mp.quad(integ,[-mp.inf,0,mp.inf])/(2*mp.pi)
def pole_term(h): return mp.re(h(1j/2)+h(-1j/2))
def prime_term(g):
    s=mp.mpf(0)
    for p in PRIMES:
        lp=LOGP[p]
        for k in range(1,30):
            u=k*lp; t=lp*p**(-mp.mpf(k)/2)*g(u); s+=t
            if abs(t)<mp.mpf(10)**(-24): break
    return 2*s

sig=mp.mpf('1.0')
C=2*mp.pi*sig*sig
def Bmn(um,un):
    # h_mn(r)=C e^{-sig^2 r^2} e^{-i r um} conj(e^{-i r un}) = C e^{-sig^2 r^2} e^{-i r(um-un)}
    def h(r): return C*mp.e**(-(sig*sig)*r*r)*mp.e**(-1j*r*(um-un))
    def g(uu):
        d=uu-(um-un)
        return mp.sqrt(mp.pi)*sig*mp.e**(-(d*d)/(4*sig*sig))
    return arch_term(h)+pole_term(h)-prime_term(g)

N=7
us=[mp.mpf(n) for n in range(N)]
B=mp.matrix(N,N)
for i in range(N):
    for j in range(N):
        B[i,j]=mp.re(Bmn(us[i],us[j]))
# symmetrize numerically
for i in range(N):
    for j in range(N):
        B[i,j]=(B[i,j]+B[j,i])/2
E=mp.eigsy(B, eigvals_only=True)
print("step=1, sig=1, N=",N)
print("eigenvalues:")
for e in E: print("  ",mp.nstr(e,10))
print("min eig:", mp.nstr(min(E),10))
