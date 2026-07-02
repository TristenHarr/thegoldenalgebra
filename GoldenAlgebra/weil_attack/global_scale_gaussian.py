"""
Cross-check the knife-edge with the ACCURATE Gaussian engine (matches zero-sum to 1e-16).
Scale ALL prime coefficients by a factor alpha: PRIME_alpha = alpha * (true prime sum).
alpha=1 is zeta. Compute min generalized eig of Q_alpha=ARCH+POLE-alpha*PRIME vs alpha.
If min-eig peaks at alpha=1 (the true arithmetic) and dips negative on both sides, that is
the global knife-edge: zeta's prime data sits exactly at the positivity edge. This uses the
1e-16-accurate Gaussian assembly (cosh POLE), so the negative dips are REAL, not 8% error.
Support past log2 (T=1.0,1.5) so multiple primes are active.
"""
import numpy as np, mpmath as mp
def Omega(r): return float(mp.re(mp.digamma(0.25+1j*r/2))-mp.log(mp.pi))
RG=np.linspace(-400,400,200001); OM=np.array([Omega(r) for r in RG])
def vm(N):
    out={}
    for n in range(2,N+1):
        mm=n;fac={};d=2
        while d*d<=mm:
            while mm%d==0:fac[d]=fac.get(d,0)+1;mm//=d
            d+=1
        if mm>1:fac[mm]=fac.get(mm,0)+1
        if len(fac)==1:out[n]=np.log(list(fac.keys())[0])
    return out
PL=vm(200000)
def build(centers,s):
    n=len(centers);s2=s*s;C=np.array(centers);D=C[:,None]-C[None,:]
    A=np.zeros((n,n));base=s2*np.exp(-s2*RG**2)*OM
    for i in range(n):
        for j in range(i,n):
            v=np.trapezoid(base*np.cos(RG*D[i,j]),RG);A[i,j]=v;A[j,i]=v
    POLE=2*np.pi*s2*np.exp(s2/4)*(np.exp(D/2)+np.exp(-D/2))
    PRIME=np.zeros((n,n));Tsup=C.max()-C.min();emax=np.exp(Tsup+12*s)
    for nn,lam in PL.items():
        if nn>emax: break
        u=np.log(nn)
        gkl=s2*(np.sqrt(np.pi)/(2*s))*(np.exp(-(D-u)**2/(4*s2))+np.exp(-(D+u)**2/(4*s2)))
        PRIME+=2*lam/np.sqrt(nn)*gkl
    G=np.sqrt(np.pi)*s*np.exp(-D**2/(4*s2))
    return (A+POLE+(A+POLE).T)/2*0+(A+POLE), PRIME, (G+G.T)/2
def mineig(M,G):
    Ms=(M+M.T)/2;w,V=np.linalg.eigh(G);keep=w>w.max()*1e-9
    U=V[:,keep]/np.sqrt(w[keep]);B=U.T@Ms@U
    return np.linalg.eigvalsh((B+B.T)/2).min()
if __name__=="__main__":
    print("Gaussian engine (1e-16 accurate). min-eig of ARCH+POLE-alpha*PRIME vs alpha (zeta=alpha=1).")
    for T in [1.0,1.5]:
        s=0.22; nb=max(8,int(T/(0.6*s))+1); centers=np.linspace(-T/2,T/2,nb)
        AP,PR,G=build(centers,s)
        print(f"  T={T}, s={s}, n={nb}:")
        print(f"    {'alpha':>7} {'mineig':>14}")
        for alpha in [0.0,0.5,0.8,0.9,1.0,1.1,1.2,1.5,2.0]:
            me=mineig(AP-alpha*PR,G)
            tag=' <-- ZETA' if alpha==1.0 else ''
            print(f"    {alpha:7.2f} {me:14.5e}{tag}")
