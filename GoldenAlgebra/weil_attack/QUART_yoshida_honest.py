"""
HONEST Yoshida check with GENUINELY compactly-supported g (the prior Gaussian-basis scripts
LEAK outside [-T,T], so their 'prime sum empty' premise is false and their negative min-eigs
were wrongly excused as 'conditioning'). Here phi is supported in [-T/2,T/2] EXACTLY, so
g=phi*phi~ is supported in [-T,T] EXACTLY. For T<log2 the prime sum is then TRULY empty.

We use a B-spline / bump basis phi_k = compactly supported bumps on [-T/2,T/2], build
g_kl = phi_k * phi_l~ (supported in [-T,T]), and compute Q(g_kl)=ARCH+POLE-PRIME via the
EXACT real-axis formula:
  ARCH(g) = (1/2pi) \int ghat(r) Omega(r) dr,  ghat(r)=phihat_k(r) conj(phihat_l(r))
  POLE(g) = ghat(i/2)+ghat(-i/2)   (cosh bilinear)
  PRIME(g)= 2 sum_n Lambda(n)/sqrt(n) g(log n)   [EMPTY for T<log2]
Then min generalized eigenvalue of (Q,Gram). If Yoshida holds it is >= 0 (no conditioning
excuse: we use a well-conditioned orthonormalized bump basis and report the condition number).
"""
import numpy as np, mpmath as mp
mp.mp.dps=18

def Omega(r): return float(mp.re(mp.digamma(0.25+1j*r/2))-mp.log(mp.pi))

# Compactly supported phi on [-H,H]: use raised-cosine bumps (smooth, exact support).
# phi_k(x) = w(x) * cos/sin Fourier modes? Simpler: tent-product B-splines. We use
# phi_k(x) = bump centered at c_k with half-width hw, supported [c_k-hw,c_k+hw] inside [-H,H].
def make_basis(H, n):
    centers=np.linspace(-H*0.7,H*0.7,n)
    hw=H*0.3
    return centers,hw

def phihat(c,hw,r):
    # phi(x)=cos^2(pi(x-c)/(2hw)) on [c-hw,c+hw] (Hann bump), 0 else. Real, even about c.
    # Its FT: phihat(r)=\int phi(x) e^{-i r x} dx = e^{-i r c} * Fhat(r) where Fhat real (even bump)
    # Fhat(r)=\int_{-hw}^{hw} cos^2(pi t/(2hw)) e^{-i r t} dt
    #        = \int (1+cos(pi t/hw))/2 e^{-i r t} dt
    # = sin(r hw)/r  + (1/2)[ sinc-shifted terms ]. Compute closed form:
    if abs(r)<1e-12:
        Fhat=hw  # \int cos^2 = hw
    else:
        a=np.pi/hw
        # \int_{-hw}^{hw} (1+cos(a t))/2 cos(r t) dt  (sin part 0 by evenness)
        I1=2*np.sin(r*hw)/r
        # \int cos(a t) cos(r t) dt over [-hw,hw] = sin((a-r)hw)/(a-r)+sin((a+r)hw)/(a+r)
        if abs(a-r)<1e-9: t1=hw
        else: t1=np.sin((a-r)*hw)/(a-r)
        if abs(a+r)<1e-9: t2=hw
        else: t2=np.sin((a+r)*hw)/(a+r)
        I2=t1+t2
        Fhat=0.5*(I1+I2)
    return Fhat  # times e^{-i r c}, phase tracked separately

RG=np.linspace(-300,300,120001); OM=np.array([Omega(r) for r in RG])

def build(H,n):
    centers,hw=make_basis(H,n)
    # phihat_k(r)=Fhat_k(r) e^{-i r c_k}, Fhat real. ghat_kl(r)=phihat_k conj(phihat_l)
    #   = Fhat_k Fhat_l e^{-i r (c_k-c_l)}
    Fh=np.array([[phihat(c,hw,r) for r in RG] for c in centers])  # n x len(RG)
    A=np.zeros((n,n)); POLE=np.zeros((n,n)); G=np.zeros((n,n))
    for i in range(n):
        for j in range(n):
            d=centers[i]-centers[j]
            ghat=Fh[i]*Fh[j]*np.cos(RG*d)  # Re part (Im integrates to 0 with Omega even)
            A[i,j]=np.trapezoid(ghat*OM,RG)/(2*np.pi)
            # POLE: ghat(i/2)+ghat(-i/2). phihat_k(i/2)=Fhat_k(i/2) e^{c_k/2}
            Fk=phihat(centers[i],hw,1j/2); Fl=phihat(centers[j],hw,1j/2)
            # ghat(i/2)=phihat_k(i/2) conj(phihat_l)(i/2-> -i/2)... use cosh bilinear form:
            # ghat(i/2)+ghat(-i/2) with phihat_k(i/2)=Fk e^{ c_k/2}(Fk real since arg imaginary->real)
            Fki=phihat(centers[i],hw,1j/2); Fkj=phihat(centers[j],hw,1j/2)
            POLE[i,j]=float(np.real(Fki*Fkj*(np.exp(d/2)+np.exp(-d/2))))
            G[i,j]=np.trapezoid(Fh[i]*Fh[j]*np.cos(RG*d),RG)/(2*np.pi)
    return A+POLE,G

def min_ray(M,G):
    Ms=(M+M.T)/2;Gs=(G+G.T)/2
    w,V=np.linalg.eigh(Gs);keep=w>w.max()*1e-10
    U=V[:,keep]/np.sqrt(w[keep]);B=U.T@Ms@U
    return np.linalg.eigvalsh((B+B.T)/2).min(),keep.sum(),w.max()/w[keep].min()

log2=np.log(2)
print("HONEST Yoshida: GENUINELY supported phi (Hann bumps), g supported [-T,T] EXACTLY.")
print(f"T<log2={log2:.4f} => prime sum truly empty. Q=ARCH+POLE. Expect min eig >= 0.")
print(f"{'T':>7} {'n':>3} {'rank':>5} {'min_eig':>15} {'cond':>10}")
for T in [0.3,0.5,0.69,0.693]:
    H=T/2
    for n in [4,6,8]:
        M,G=build(H,n)
        mn,rk,cond=min_ray(M,G)
        print(f"{T:7.3f} {n:3d} {rk:5d} {mn:15.5e} {cond:10.2e}")
