"""
Refined cone threshold: RICH basis (dense centers, moderate width with overlap),
find smallest T where min-eig of Weil matrix M(T) goes negative UNCONDITIONALLY.
Key fix vs v1: width s ~ spacing so the basis actually spans L^2([-T/2,T/2]) and
can form resonant combinations. Also report the n of primes actually in support.
"""
import numpy as np
import mpmath as mp
mp.mp.dps = 18

def vonMangoldt_list(Nmax):
    out={}
    for n in range(2,Nmax+1):
        mm=n;fac={};d=2
        while d*d<=mm:
            while mm%d==0: fac[d]=fac.get(d,0)+1;mm//=d
            d+=1
        if mm>1: fac[mm]=fac.get(mm,0)+1
        if len(fac)==1:
            out[n]=np.log(list(fac.keys())[0])
    return out

def Omega(r):
    return float(mp.re(mp.digamma(mp.mpf(1)/4+1j*mp.mpf(r)/2))-mp.log(mp.pi))

RGRID=np.linspace(-300,300,60001)
OMEGA=np.array([Omega(r) for r in RGRID])

vm=vonMangoldt_list(200000)
PL={n:(lam,np.sqrt(n)) for n,lam in vm.items()}

def assemble(T, centers, s):
    n=len(centers); s2=s*s
    C=np.array(centers)
    D=C[:,None]-C[None,:]   # x_i - x_j
    # ARCH A_{ij}= s^2 \int exp(-s^2 r^2) cos(r D) Omega dr
    A=np.zeros((n,n))
    base=s2*np.exp(-s2*RGRID**2)*OMEGA
    for i in range(n):
        for j in range(i,n):
            val=np.trapezoid(base*np.cos(RGRID*D[i,j]),RGRID)
            A[i,j]=val;A[j,i]=val
    # POLE_{ij}= 2 pi s^2 (e^{D/2}+e^{-D/2}) e^{s^2/4}
    POLE=2*np.pi*s2*(np.exp(D/2)+np.exp(-D/2))*np.exp(s2/4)
    # PRIME_{ij}=2 sum_n Lambda/sqrt(n) * sqrt(pi) s exp(-(log n - D)^2/(4 s^2))
    PRIME=np.zeros((n,n))
    emax=np.exp(T+6*s)  # primes within support+tail
    for nn,(lam,sq) in PL.items():
        if nn>emax: break
        u=np.log(nn)
        g=np.sqrt(np.pi)*s*np.exp(-(u-D)**2/(4*s2))
        PRIME+=2*lam/sq*g
    return A+POLE-PRIME, A, POLE, PRIME

print(f"{'T':>6} {'s':>6} {'#basis':>6} {'#primes':>7} {'mineig':>14}")
for T in [1.0,2.0,3.0,4.0,5.0,6.0,7.0,8.0,9.0,10.0,12.0]:
    s=0.20
    spacing=0.5*s
    nb=int(T/spacing)+1
    centers=np.linspace(-T/2,T/2,nb)
    M,A,POLE,PRIME=assemble(T,centers,s)
    ev=np.linalg.eigvalsh((M+M.T)/2)
    nprimes=sum(1 for nn in PL if nn<=np.exp(T))
    print(f"{T:6.1f} {s:6.2f} {nb:6d} {nprimes:7d} {ev.min():14.6e}")
