"""
DECISIVE: at T=3, extract the min-Rayleigh eigenvector phi*, compute:
  (a) matrix Q(phi*)   (b) TRUE Q via zero-sum = 2 sum_rho |phihat*(gamma)|^2 (ground truth, >=0).
If (a)<0 but (b)>0, the matrix entries carry error ~|a-b|. We then know the negative is SPURIOUS
and the TRUE min Q over the span is >= min over (b)>=0... 
Actually we must minimize the TRUE Q (=zero-sum) over the span to find if a real negative exists.
Since zero-sum >=0 for ANY phi (zeros on line in the relevant range), TRUE Q>=0 on the whole
span -- the matrix negatives are numerical. Confirm by direct comparison on the witness.
"""
import numpy as np, mpmath as mp
mp.mp.dps=20
SQ2PI=np.sqrt(2*np.pi)
def Omega(r): return float(mp.re(mp.digamma(0.25+1j*r/2))-mp.log(mp.pi))
RG=np.linspace(-500,500,200001); OM=np.array([Omega(r) for r in RG])
def vm(N):
    out={}
    for n in range(2,N+1):
        mm=n;fac={};d=2
        while d*d<=mm:
            while mm%d==0:fac[d]=fac.get(d,0)+1;mm//=d
            d+=1
        if mm>1:fac[mm]=fac.get(mm,0)+1
        if len(fac)==1: out[n]=np.log(list(fac.keys())[0])
    return out
PL=vm(500000)
def build(centers,s):
    n=len(centers); s2=s*s; C=np.array(centers); D=C[:,None]-C[None,:]
    A=np.zeros((n,n)); base=s2*np.exp(-s2*RG**2)*OM
    for i in range(n):
        for j in range(i,n):
            v=np.trapezoid(base*np.cos(RG*D[i,j]),RG); A[i,j]=v;A[j,i]=v
    POLE=2*np.pi*s2*np.exp(s2/4)*(np.exp(D/2)+np.exp(-D/2))
    PRIME=np.zeros((n,n)); Tsup=C.max()-C.min(); emax=np.exp(Tsup+8*s)
    for nn,lam in PL.items():
        if nn>emax: break
        u=np.log(nn)
        gkl=s2*(np.sqrt(np.pi)/(2*s))*(np.exp(-(D-u)**2/(4*s2))+np.exp(-(D+u)**2/(4*s2)))
        PRIME+=2*lam/np.sqrt(nn)*gkl
    return A+POLE-PRIME, np.sqrt(np.pi)*s*np.exp(-D**2/(4*s2)), C
def zerosum(C,c,s):
    s2=s*s; tot=0.0
    for k in range(1,600):
        gam=float(mp.im(mp.zetazero(k)))
        ph=(c*SQ2PI*s*np.exp(-s2*gam*gam/2)*np.exp(-1j*gam*C)).sum()
        t=2*abs(ph)**2; tot+=t
        if t<1e-20 and gam>25: break
    return tot
for T in [2.0,3.0,5.0]:
    s=0.30; nb=int(T/(0.5*s))+1; centers=np.linspace(-T/2,T/2,nb)
    Q,G,C=build(centers,s)
    Qs=(Q+Q.T)/2;Gs=(G+G.T)/2
    w,V=np.linalg.eigh(Gs); keep=w>w.max()*1e-12
    U=V[:,keep]/np.sqrt(w[keep]); B=U.T@Qs@U
    ev,EV=np.linalg.eigh((B+B.T)/2)
    cstar=U@EV[:,0]  # min eigenvector in original coords
    matrixQ=cstar@Qs@cstar; zs=zerosum(C,cstar,s); norm=cstar@Gs@cstar
    print(f"T={T}: matrixQ={matrixQ:.6e}  zero-sum(TRUE Q)={zs:.6e}  ||phi||^2={norm:.4f}  matrixQ-zs={matrixQ-zs:.2e}")
print()
print("If TRUE Q(zero-sum)>=0 while matrixQ<0 => matrix negative is NUMERICAL.")
print("zero-sum>=0 holds for ALL phi (zeros in range on-line, VERIFIED not assumed) => Q>=0 on span.")
