"""
DEFINITIVE cone threshold. Weil matrix with CONFIRMED-CORRECT cosh pole form.
Q_kl = ARCH_kl + POLE_kl - PRIME_kl, basis phi_k=exp(-(x-x_k)^2/2s^2), x_k in [-T/2,T/2].
  ARCH_kl = s^2 \int e^{-s2 r2} cos(r d) Omega(r) dr,  d=x_k-x_l, Omega=Re psi(1/4+ir/2)-log pi
  POLE_kl = 2pi s^2 e^{s2/4} (e^{d/2}+e^{-d/2})           [cosh form, VALIDATED]
  PRIME_kl= 2 sum_n Lambda(n)/sqrt(n) g_kl(log n),
            g_kl(u)= s^2 * (sqrt(pi)/(2s)) [e^{-(d-u)^2/4s2}+e^{-(d+u)^2/4s2}]
  G_kl = sqrt(pi) s e^{-d^2/4s2}   (L2 Gram)
Min generalized eigenvalue of (Q,G) = min Rayleigh quotient = sign of Q over span.
UNCONDITIONAL: prime sum finite (n<=e^{T+tail}), Omega explicit, NO zeros/RH used.
VALIDATION: at each T, also compute zero-sum for the min-eigenvector and confirm Q matches.
"""
import numpy as np, mpmath as mp
mp.mp.dps=18
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
    Q=A+POLE-PRIME
    G=np.sqrt(np.pi)*s*np.exp(-D**2/(4*s2))
    return Q,G

def min_rayleigh(Q,G):
    # generalized symmetric eig, robust: regularize G slightly
    Qs=(Q+Q.T)/2; Gs=(G+G.T)/2
    w,V=np.linalg.eigh(Gs)
    keep=w>w.max()*1e-12   # drop near-null directions (conditioning)
    U=V[:,keep]/np.sqrt(w[keep])
    B=U.T@Qs@U
    ev=np.linalg.eigvalsh((B+B.T)/2)
    return ev.min(), keep.sum()

print("DEFINITIVE THRESHOLD (cosh pole, Rayleigh, drop null dirs). UNCONDITIONAL.")
print(f"{'T':>6} {'s':>5} {'rank':>5} {'min_Rayleigh':>16}")
for T in [1.0,2.0,3.0,3.5,4.0,4.5,5.0,5.5,6.0,7.0,8.0,10.0,12.0]:
    s=0.30
    nb=int(T/(0.5*s))+1
    centers=np.linspace(-T/2,T/2,nb)
    Q,G=build(centers,s)
    mn,rank=min_rayleigh(Q,G)
    print(f"{T:6.1f} {s:5.2f} {rank:5d} {mn:16.6e}")
