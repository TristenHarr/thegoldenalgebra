"""
DECISIVE EXPERIMENT. Build the Weil quadratic form Q as a genuine real-symmetric
matrix in a basis of EVEN cosine-Gaussian wave packets

   phi_m(r) = e^{-b(r-c_m)^2} + e^{-b(r+c_m)^2}      (even, real)

with centers c_m sweeping a frequency band [c0, c0+...]. The test function is
psi = sum a_m phi_m, h=|psi_freq|^2... here psi_freq:=sum a_m phi_m is REAL EVEN,
and the Weil functional's "h" is h=(sum a_m phi_m)^2? NO -- to keep h of positive
type we set h = F^2 with F=sum a_m phi_m real even => h>=0 automatically. Then
Q(a) = ARCH(h)+POLE(h)-PRIME(g), h=F^2, polarize to get matrix B s.t. a^T B a = Q.

B[m,n] obtained by polarization of the genuine Q (consistent by construction).
Eigenvalues of B test PSD. For TRUE zeta we expect min eig >= 0 (RH true here).
"""
import mpmath as mp
from sympy import isprime as _isprime
mp.mp.dps=22
def dig(z): return mp.digamma(z)
PRIMES=[p for p in range(2,5000) if _isprime(p)]
b=mp.mpf('0.6')
W=lambda r: mp.re(dig(mp.mpf(1)/4+1j*r/2))-mp.log(mp.pi)
def phi(c,z): return mp.e**(-b*(z-c)**2)+mp.e**(-b*(z+c)**2)
def Qof(coeffs,centers):
    # F(z)=sum a phi_c(z); h=F^2
    def F(z): return sum(a*phi(c,z) for a,c in zip(coeffs,centers))
    def h(z): return F(z)**2
    # ARCH
    pts=[-mp.inf]+sorted(set([-mc for mc in centers]+[0]+list(centers)))+[mp.inf]
    pts=[-mp.inf]+[mp.mpf(t) for t in range(-40,41,2)]+[mp.inf]
    A=mp.quad(lambda r:h(r)*W(r),pts)/(2*mp.pi)
    P=mp.re(h(1j/2)+h(-1j/2))
    # g(u): h=F^2 = sum over pairs of phi products. phi(c,r)=g_+ + g_-, gaussian.
    # Build h as explicit sum of gaussians A_i e^{-b_i(r-d_i)^2}? product of two gaussians
    # e^{-b(r-c1)^2}e^{-b(r-c2)^2}=e^{-2b(r-(c1+c2)/2)^2} e^{-b(c1-c2)^2/2}. 
    glist=[]  # (amp, center, beta) for each gaussian in h
    terms=[]
    for a,c in zip(coeffs,centers):
        terms.append((a,c)); terms.append((a,-c))
    for (a1,c1) in terms:
        for (a2,c2) in terms:
            amp=a1*a2*mp.e**(-b*(c1-c2)**2/2)
            cen=(c1+c2)/2
            glist.append((amp,cen,2*b))
    def g(u):
        tot=mp.mpf(0)
        for amp,cen,bb in glist:
            tot+=amp/(2*mp.sqrt(mp.pi*bb))*mp.e**(-(u*u)/(4*bb))*mp.cos(cen*u)
        return tot
    s=mp.mpf(0)
    for p in PRIMES:
        lp=mp.log(p)
        for k in range(1,50):
            u=k*lp;t=lp*p**(-mp.mpf(k)/2)*g(u);s+=t
            if abs(t)<mp.mpf(10)**(-20) and u>30:break
    PR=2*s
    return mp.re(A+P-PR)
N=6
centers=[mp.mpf(10)+mp.mpf(2)*m for m in range(N)]  # band 10..20
diag=[Qof([1 if i==j else 0 for j in range(N)],centers) for i in range(N)]
B=mp.matrix(N,N)
for i in range(N): B[i,i]=diag[i]
for i in range(N):
    for j in range(i+1,N):
        e=[0]*N;e[i]=1;e[j]=1
        Qij=Qof(e,centers)
        bb=(Qij-diag[i]-diag[j])/2;B[i,j]=bb;B[j,i]=bb
E=mp.eigsy(B,eigvals_only=True)
print("Weil matrix, resonating band centers",[float(c) for c in centers])
for e in E: print("  ",mp.nstr(e,10))
print("MIN EIG:",mp.nstr(min(E),10))
