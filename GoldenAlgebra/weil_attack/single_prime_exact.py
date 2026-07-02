"""
TASK 1 + 3, DONE HONESTLY with COMPACT support so the prime cutoff is EXACT.

For supp(g) subset (-T,T) with log2 < T < log3, the explicit formula's prime sum is
EXACTLY the single n=2 term (no Gaussian tail leakage). We use compactly supported phi on
(-T/2, T/2) so g=phi*phi~ has supp in (-T,T). Then:

  Q(g) = ARCH(g) + POLE(g) - 2*(log2/sqrt2)*g(log2)

is EXACT and unconditional. g(log2) = <phi, S_{log2} phi> with S the shift, sign-indefinite.

We discretize phi on a grid of compact bumps b_k(x)=hat-function (linear B-spline) at nodes
in (-T/2,T/2). Then:
  ARCH_ij = (1/2pi) int Omega(r) bhat_i(r) conj(bhat_j(r)) dr
  POLE_ij = bhat_i(i/2) conj(bhat_j)(i/2) + bhat_i(-i/2) conj(bhat_j)(-i/2)
  PRIME_ij= 2 (log2/sqrt2) * (b_i * b_j~)(log2)        [single prime, EXACT]
  G_ij    = (b_i*b_j~)(0) = int b_i b_j dx

where bhat_k(r)=int b_k(x) e^{-i r x} dx (compact -> entire, analytic continuation trivial).

We compute min generalized eigenvalue of Q rel G, unconstrained and under each constraint,
sweeping T in (log2,log3). The Yoshida floor: at T just below log2 (PRIME=0) min-eig MUST be
>=0; that calibrates trust. Past log2 the single n=2 term is the ONLY new ingredient.
"""
import numpy as np, mpmath as mp
mp.mp.dps=25

def Omega(r): return float(mp.re(mp.digamma(0.25+1j*r/2))-mp.log(mp.pi))
RG=np.linspace(-200,200,80001); OM=np.array([Omega(r) for r in RG])
l2=float(np.log(2)); l3=float(np.log(3))
W2=l2/np.sqrt(2.0)

def hat_basis(nodes, hh):
    """linear B-spline (triangle) bump at each node, half-width hh.
       b_k(x)=max(0,1-|x-node_k|/hh). Returns funcs via their support params."""
    return [(c,hh) for c in nodes]

# bhat(r) for triangle of half-width h centered at c:
#   triangle = (1/h)*(box_h * box_h)  where box_h indicator on (-h/2.. ) -> actually
#   triangle_h(x)=max(0,1-|x|/h) has Fourier transform h * sinc^2(r h /2)/ ... let's just compute:
#   int_{-h}^{h}(1-|x|/h) e^{-irx}dx = (2/h)*(1-cos(rh))/r^2 = h * (sin(rh/2)/(rh/2))^2
def bhat(r, c, h):
    # real-shifted: e^{-i r c} * H(r), H(r)= h*(sinc(rh/2))^2
    rh=r*h/2
    if abs(rh)<1e-9: H=h
    else: H=h*(np.sin(rh)/rh)**2  # note: int triangle width h on each side -> base 2h
    return np.exp(-1j*r*c)*H

def bhat_imag(c,h,half):
    # bhat at r=i*half (real result): e^{-i (i half) c} = e^{half c}; H(i half)= h*(sinh(half h/2)/(half h/2))^2
    rh=half*h/2
    if abs(rh)<1e-9: H=h
    else: H=h*(np.sinh(rh)/rh)**2
    return np.exp(half*c)*H

def triangle_corr(c1,c2,h,u):
    """(b1 * b2~)(u) = int b1(x) b2(x-u) dx for two triangles half-width h at c1,c2.
       = autocorr of triangle evaluated at (c1-c2-u)? Cross-corr: int b1(x)b2(x-u)dx.
       b1(x)=tri(x-c1), b2(x-u)=tri(x-u-c2). Overlap = T(t) with t=c1-(c2+u)... define
       cross-correlation R(tau)=int tri(x) tri(x-tau) dx, tau = (c2+u)-c1. R is the
       triangle-autocorrelation: piecewise cubic, support |tau|<2h."""
    tau=(c2+u)-c1
    a=abs(tau)
    if a>=2*h: return 0.0
    # R(tau) for tri half-width h (base 2h). Known: autocorr of triangle.
    t=a/h  # in [0,2]
    if t<=1:
        # integral formula
        return h*( (2.0/3.0) - t*t + 0.5*t**3 )
    else:
        return h*( (1.0/6.0)*(2-t)**3 )

def _H(r,h):
    rh=r*h/2
    out=np.where(np.abs(rh)<1e-9, h, h*(np.sin(rh)/np.where(rh==0,1,rh))**2)
    return out

def build(nodes, h, include_prime=True):
    n=len(nodes); C=np.array(nodes,float)
    A=np.zeros((n,n)); POLE=np.zeros((n,n)); PR=np.zeros((n,n)); G=np.zeros((n,n))
    # vectorized bhat on grid: BH[k,m] = e^{-i RG[m] C[k]} * H(RG[m])
    Hr=_H(RG,h)                                  # len(RG)
    EXP=np.exp(-1j*np.outer(C,RG))               # n x len(RG)
    BH=EXP*Hr[None,:]                            # n x len(RG)
    OMr=OM
    for i in range(n):
        for j in range(n):
            integ=OMr*np.real(BH[i]*np.conj(BH[j]))
            A[i,j]=np.trapz(integ,RG)/(2*np.pi)
            phi=bhat_imag(C[i],h,0.5); phj=bhat_imag(C[j],h,0.5)
            phim=bhat_imag(C[i],h,-0.5); phjm=bhat_imag(C[j],h,-0.5)
            POLE[i,j]=phi*phj+phim*phjm
            G[i,j]=triangle_corr(C[i],C[j],h,0.0)
            if include_prime:
                PR[i,j]=2*W2*triangle_corr(C[i],C[j],h,l2)
    Q=A+POLE-PR
    return (Q+Q.T)/2,(G+G.T)/2

def mineig(Q,G,constraints=None):
    n=Q.shape[0]
    if constraints:
        Ac=np.array(constraints); u,sv,vt=np.linalg.svd(Ac)
        rank=int((sv>1e-10*sv.max()).sum()); K=vt[rank:].T
        if K.shape[1]==0: return None
        Q=K.T@Q@K; G=K.T@G@K
    w,V=np.linalg.eigh(G); keep=w>w.max()*1e-9
    U=V[:,keep]/np.sqrt(w[keep]); B=U.T@Q@U
    return np.linalg.eigvalsh((B+B.T)/2).min()

if __name__=="__main__":
    print("EXACT single-prime regime (compact triangle basis). Prime cutoff EXACT for T<log3.")
    print(f"log2={l2:.4f} log3={l3:.4f}")
    print(f"{'T':>6} {'h':>5} {'n':>3} {'mineig_noPRIME':>15} {'mineig_withn2':>15}")
    for T in [0.60,0.69,0.75,0.85,0.95,1.05]:
        half=T/2; n=9; h=half/3   # triangle half-width; nodes spaced so total support ~ (-half,half)
        nodes=np.linspace(-half+h, half-h, n)
        Q0,G=build(nodes,h,include_prime=False)
        Q1,_=build(nodes,h,include_prime=True)
        m0=mineig(Q0,G); m1=mineig(Q1,G)
        print(f"{T:6.3f} {h:5.3f} {n:3d} {m0:15.5e} {m1:15.5e}")
