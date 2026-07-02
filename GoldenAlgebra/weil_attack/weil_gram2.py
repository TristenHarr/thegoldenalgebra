"""
Correct Weil Gram matrix via POLARIZATION of the genuine real quadratic form Q.
Q(psi) for real psi = sum a_n bump_n is a real quadratic form a^T B a.
Recover B by  B[m,n] = (1/2)(Q(e_m+e_n) - Q(e_m) - Q(e_n)),  B[m,m]=Q(e_m).
This is guaranteed self-consistent with Q. Then eigenvalues of B test PSD-ness.
"""
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
def Qof(cs,us):
    def h(r):
        S=sum(c*mp.e**(-1j*r*u) for c,u in zip(cs,us))
        return C*mp.e**(-(sig*sig)*r*r)*abs(S)**2
    def g(uu):
        tot=mp.mpf(0)
        for cj,uj in zip(cs,us):
            for ck,uk in zip(cs,us):
                d=uu-(uj-uk);tot+=cj*ck*mp.sqrt(mp.pi)*sig*mp.e**(-(d*d)/(4*sig*sig))
        return tot
    return mp.re(arch_term(h)+pole_term(h)-prime_term(g))

N=7
us=[mp.mpf(n) for n in range(N)]
def Qvec(a): return Qof(a,us)
diag=[]
for i in range(N):
    e=[mp.mpf(0)]*N;e[i]=mp.mpf(1);diag.append(Qvec(e))
B=mp.matrix(N,N)
for i in range(N): B[i,i]=diag[i]
for i in range(N):
    for j in range(i+1,N):
        e=[mp.mpf(0)]*N;e[i]=mp.mpf(1);e[j]=mp.mpf(1)
        Qij=Qvec(e)
        b=(Qij-diag[i]-diag[j])/2
        B[i,j]=b;B[j,i]=b
E=mp.eigsy(B,eigvals_only=True)
print("Polarized Weil Gram, sig=1, step=1, N=",N)
for e in E: print("  ",mp.nstr(e,12))
print("MIN EIG:",mp.nstr(min(E),12))

# Get eigenvector for min eigenvalue and evaluate Q directly on it
Eall,V=mp.eigsy(B)
idx=min(range(N),key=lambda i:Eall[i])
vec=[V[i,idx] for i in range(N)]
print("\nmin eigenvalue:",mp.nstr(Eall[idx],12))
print("eigenvector:",[mp.nstr(v,5) for v in vec])
print("Q(eigenvector) DIRECT:",mp.nstr(Qvec(vec),12))
print("v^T B v:",mp.nstr(sum(vec[i]*B[i,j]*vec[j] for i in range(N) for j in range(N)),12))
