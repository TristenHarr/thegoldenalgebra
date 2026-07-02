"""
Validated float threshold scan with CORRECT calibrated normalization + generalized eig.
Basis phi_k = exp(-(x-x_k)^2/(2 s^2)). All entries in closed form except ARCH integral.
Q(phi)=sum_{kl} c_k c_l M_kl,  G_kl = L2 inner product (for Rayleigh normalization).
We validate M against zero-sum for one vector, THEN scan min generalized eig vs T.
"""
import numpy as np, mpmath as mp
mp.mp.dps=20
def Omega(r): return float(mp.re(mp.digamma(0.25+1j*r/2))-mp.log(mp.pi))
RG=np.linspace(-400,400,160001); OM=np.array([Omega(r) for r in RG]); 
SQ2PI=np.sqrt(2*np.pi)
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
PL=vm(300000)

def build(centers,s):
    n=len(centers); s2=s*s; C=np.array(centers); D=C[:,None]-C[None,:]
    # h_kl(r)=phihat_k conj(phihat_l)=2pi s^2 e^{-s2 r2} e^{-i r(x_k-x_l)} ; Re part for matrix:
    # ARCH_kl=(1/2pi)\int Re(h_kl)Omega dr = s^2 \int e^{-s2 r2} cos(r D)Omega dr
    A=np.zeros((n,n)); base=s2*np.exp(-s2*RG**2)*OM
    for i in range(n):
        for j in range(i,n):
            v=np.trapezoid(base*np.cos(RG*D[i,j]),RG); A[i,j]=v;A[j,i]=v
    # POLE_kl=h_kl(i/2)+h_kl(-i/2); phihat_k(i/2)=SQ2PI s e^{s2/8} e^{x_k/2}
    pe=SQ2PI*s*np.exp(s2/8)*np.exp(C/2)   # phihat_k(i/2)
    pem=SQ2PI*s*np.exp(s2/8)*np.exp(-C/2) # phihat_k(-i/2)
    POLE=np.outer(pe,pe)+np.outer(pem,pem)
    # PRIME_kl=2 sum Lambda/sqrt(n) g_kl(log n); g_kl(u)=(1/2pi)\int Re h_kl e^{iru}dr
    #  =(1/2pi)\int 2pi s^2 e^{-s2 r2}cos(r D)cos(r u)dr = s^2 \int e^{-s2 r2}cos(rD)cos(ru)dr
    #  = (s^2)(sqrt(pi)/(2 s)) [e^{-(u-D)^2/4s2}+e^{-(u+D)^2/4s2}]/... do closed form:
    #  \int_{-inf}^{inf} e^{-s2 r2}cos(rD)cos(ru)dr = (1/2)sqrt(pi)/s [e^{-(D-u)^2/(4s2)}+e^{-(D+u)^2/(4s2)}]
    PRIME=np.zeros((n,n)); emax=np.exp(np.log(max(np.exp(np.abs(C).max()),2))+ s*8 + (centers[-1]-centers[0]))
    Tsup=C.max()-C.min()
    emax=np.exp(Tsup+8*s)
    for nn,lam in PL.items():
        if nn>emax: break
        u=np.log(nn)
        gkl=s2*0.5*np.sqrt(np.pi)/s*(np.exp(-(D-u)**2/(4*s2))+np.exp(-(D+u)**2/(4*s2)))
        PRIME+=2*lam/np.sqrt(nn)*gkl
    M=A+POLE-PRIME
    # Gram G_kl=<phi_k,phi_l>=sqrt(pi) s e^{-D^2/(4 s2)}
    G=np.sqrt(np.pi)*s*np.exp(-D**2/(4*s2))
    return M,G,A,POLE,PRIME

# VALIDATE: single bump, compare Q to zero-sum
def zerosum_for(centers,coeffs,s):
    C=np.array(centers); c=np.array(coeffs); s2=s*s
    tot=0.0
    for k in range(1,400):
        gam=float(mp.im(mp.zetazero(k)))
        ph=(c*SQ2PI*s*np.exp(-s2*gam*gam/2)*np.exp(-1j*gam*C)).sum()
        t=2*abs(ph)**2; tot+=t
        if t<1e-22 and gam>20: break
    return tot
for (cn,cf,s) in [([0.0],[1.0],0.4),([0.5,-0.5],[1.0,1.0],0.4),([0.5,-0.5],[1.0,-1.0],0.4)]:
    M,G,A,POLE,PRIME=build(cn,s)
    c=np.array(cf); Q=c@M@c; ZS=zerosum_for(cn,cf,s)
    print(f"validate centers={cn} coeffs={cf}: Q={Q:.8e}  zero-sum={ZS:.8e}  diff={Q-ZS:.2e}")
