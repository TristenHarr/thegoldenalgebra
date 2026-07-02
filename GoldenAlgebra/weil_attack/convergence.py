"""
Is the small negative eigenvalue at moderate T a NUMERICAL artifact or REAL?
Fix T=6, vary (a) basis density, (b) trapezoid grid resolution, (c) width s.
If mineig -> 0+ as we refine, it's an artifact (true cone includes T=6).
If it stabilizes at a fixed negative, the cone boundary is BELOW T=6.
"""
import numpy as np
import mpmath as mp
mp.mp.dps=18
def vm_list(N):
    out={}
    for n in range(2,N+1):
        mm=n;fac={};d=2
        while d*d<=mm:
            while mm%d==0: fac[d]=fac.get(d,0)+1;mm//=d
            d+=1
        if mm>1: fac[mm]=fac.get(mm,0)+1
        if len(fac)==1: out[n]=np.log(list(fac.keys())[0])
    return out
PL=vm_list(200000)
def Omega(r): return float(mp.re(mp.digamma(mp.mpf(1)/4+1j*mp.mpf(r)/2))-mp.log(mp.pi))

def run(T,s,spacing_frac,rmax,rn):
    RG=np.linspace(-rmax,rmax,rn); OM=np.array([Omega(r) for r in RG])
    s2=s*s
    nb=int(T/(spacing_frac*s))+1
    C=np.linspace(-T/2,T/2,nb); D=C[:,None]-C[None,:]
    A=np.zeros((nb,nb)); base=s2*np.exp(-s2*RG**2)*OM
    for i in range(nb):
        for j in range(i,nb):
            v=np.trapezoid(base*np.cos(RG*D[i,j]),RG); A[i,j]=v;A[j,i]=v
    POLE=2*np.pi*s2*(np.exp(D/2)+np.exp(-D/2))*np.exp(s2/4)
    PRIME=np.zeros((nb,nb)); emax=np.exp(T+6*s)
    for nn,lam in PL.items():
        if nn>emax: break
        u=np.log(nn); PRIME+=2*lam/np.sqrt(nn)*np.sqrt(np.pi)*s*np.exp(-(u-D)**2/(4*s2))
    M=A+POLE-PRIME
    ev=np.linalg.eigvalsh((M+M.T)/2)
    return ev.min(), nb, np.linalg.cond((M+M.T)/2)

T=6.0
print(f"T={T}. Refining grid & basis; watch mineig & condition number.")
print(f"{'s':>5} {'spc':>5} {'rmax':>5} {'rn':>7} {'nb':>4} {'mineig':>13} {'cond':>11}")
for s in [0.30,0.20,0.15]:
    for spacing_frac in [0.6,0.4]:
        for (rmax,rn) in [(200,40001),(400,120001)]:
            mn,nb,cond=run(T,s,spacing_frac,rmax,rn)
            print(f"{s:5.2f} {spacing_frac:5.2f} {rmax:5d} {rn:7d} {nb:4d} {mn:13.4e} {cond:11.3e}")
