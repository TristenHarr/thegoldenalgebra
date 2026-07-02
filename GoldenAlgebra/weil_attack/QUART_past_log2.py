"""
PAST log2: add the prime sum (n=2,3,...) with genuinely-supported g, find where the
true Weil form Q=ARCH+POLE-PRIME first goes indefinite (min eig < 0). This is the
UNCONDITIONAL boundary of forced positivity. Builds on QUART_yoshida_honest.py basis.
"""
import numpy as np, mpmath as mp
mp.mp.dps=18
def Omega(r): return float(mp.re(mp.digamma(0.25+1j*r/2))-mp.log(mp.pi))
RG=np.linspace(-300,300,120001); OM=np.array([Omega(r) for r in RG])

def vonmangoldt(N):
    out={}
    for n in range(2,N+1):
        m=n;fac={};d=2
        while d*d<=m:
            while m%d==0:fac[d]=fac.get(d,0)+1;m//=d
            d+=1
        if m>1:fac[m]=fac.get(m,0)+1
        if len(fac)==1:out[n]=np.log(list(fac.keys())[0])
    return out
PL=vonmangoldt(100000)

def phihat(c,hw,r):
    if abs(r)<1e-12: return hw
    a=np.pi/hw; I1=2*np.sin(r*hw)/r
    t1=hw if abs(a-r)<1e-9 else np.sin((a-r)*hw)/(a-r)
    t2=hw if abs(a+r)<1e-9 else np.sin((a+r)*hw)/(a+r)
    return 0.5*(I1+t1+t2)

def phi_real(c,hw,x):
    # phi(x)=cos^2(pi(x-c)/(2hw)) on [c-hw,c+hw]
    t=x-c
    return np.where(np.abs(t)<=hw, np.cos(np.pi*t/(2*hw))**2, 0.0)

def gkl_real(ci,cj,hw,u):
    # g_kl(u) = (phi_i * phi_j~)(u) = \int phi_i(x) phi_j(x-u) dx. Numeric convolution.
    xs=np.linspace(min(ci,cj)-hw-1,max(ci,cj)+hw+1,4000); dx=xs[1]-xs[0]
    return np.array([np.sum(phi_real(ci,hw,xs)*phi_real(cj,hw,xs-uu))*dx for uu in u])

def build(H,n):
    centers=np.linspace(-H*0.7,H*0.7,n); hw=H*0.3
    Tsup=2*(centers.max()-centers.min()+2*hw)
    Fh=np.array([[phihat(c,hw,r) for r in RG] for c in centers])
    A=np.zeros((n,n));POLE=np.zeros((n,n));G=np.zeros((n,n));PRIME=np.zeros((n,n))
    # prime nodes within support
    logs=[np.log(nn) for nn in PL if np.log(nn)<=2*hw+ (centers.max()-centers.min())+0.01]
    for i in range(n):
        for j in range(n):
            d=centers[i]-centers[j]
            ghat=Fh[i]*Fh[j]*np.cos(RG*d)
            A[i,j]=np.trapezoid(ghat*OM,RG)/(2*np.pi)
            Fki=phihat(centers[i],hw,1j/2);Fkj=phihat(centers[j],hw,1j/2)
            POLE[i,j]=float(np.real(Fki*Fkj*(np.exp(d/2)+np.exp(-d/2))))
            G[i,j]=np.trapezoid(Fh[i]*Fh[j]*np.cos(RG*d),RG)/(2*np.pi)
    # prime term: 2 sum Lambda(n)/sqrt(n) g_kl(log n)
    relevant=[(nn,lam) for nn,lam in PL.items() if np.log(nn)<= (centers.max()-centers.min())+2*hw+0.01]
    for i in range(n):
        for j in range(n):
            us=np.array([np.log(nn) for nn,_ in relevant])
            if len(us)==0: continue
            gv=gkl_real(centers[i],centers[j],hw,us)
            PRIME[i,j]=2*np.sum([lam/np.sqrt(nn)*gv[k] for k,(nn,lam) in enumerate(relevant)])
    return A+POLE-PRIME,G,len(relevant)

def min_ray(M,G):
    Ms=(M+M.T)/2;Gs=(G+G.T)/2
    w,V=np.linalg.eigh(Gs);keep=w>w.max()*1e-10
    U=V[:,keep]/np.sqrt(w[keep]);B=U.T@Ms@U
    return np.linalg.eigvalsh((B+B.T)/2).min(),keep.sum()

log2=np.log(2)
print("TRUE Weil form Q=ARCH+POLE-PRIME, genuinely-supported g. Boundary of forced positivity.")
print(f"log2={log2:.4f}, log3={np.log(3):.4f}, log4={np.log(4):.4f}")
print(f"{'T':>7} {'n':>3} {'#primes':>8} {'min_eig':>15}")
for T in [0.6,0.69,0.8,1.0,1.2,1.39,1.6,2.0]:
    H=T/2; n=7
    M,G,npr=build(H,n)
    mn,rk=min_ray(M,G)
    flag=" <-- INDEFINITE" if mn<-1e-6 else ""
    print(f"{T:7.3f} {n:3d} {npr:8d} {mn:15.5e}{flag}")
