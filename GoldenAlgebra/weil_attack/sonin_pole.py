"""
Clarify the POLE term (the positivity ENGINE at low frequency) and the Sonin space.

Weil's POLE term = ghat(1/2)+ghat(-1/2) where ghat(s)=\int g(u) e^{(s-1/2)u}... 
Standard normalization (Iwaniec-Kowalski): the s=0,1 poles of completed zeta contribute
  + [ ghat(i/2)+ghat(-i/2) ]  to the LHS-side... For g=phi*phi~ POSITIVE TYPE:
  ghat(i/2) = \int g(u) e^{u/2} du = (phi*phi~)^(at imaginary freq) = |phihat(i/2)|^2-ish >=0.
Actually ghat(i/2)= \int\int phi(x)phi(x-u)e^{u/2}dx du = |\int phi(x) e^{x/2}dx|^2 >= 0. YES >=0.
So POLE >= 0 always for positive-type g. It is the LARGE positive term seen in short_support.py
(P=0.41 vs A=-0.40). 

SONIN SPACE (Connes): the archimedean form ARCH becomes >=0 precisely on the subspace
where the "negative" low-frequency directions of Omega are killed -- Connes shows ARCH+(pole)
>= 0 on the range complement of the cutoff projections (prolate). The Sonin space S_e is
{ f in L^2 : f and its Fourier transform both vanish on (-e,e) } scaled appropriately;
for e=1 it's the cokernel that makes the scaling-action trace positive.
We confirm: ARCH(phi)+POLE(phi) >=0 for ALL positive-type phi? Test a few phi that try to
exploit Omega<0 at low r.
"""
import mpmath as mp
mp.mp.dps=30
Omega=lambda r: mp.re(mp.digamma(mp.mpf(1)/4+1j*r/2))-mp.log(mp.pi)
def AP(centers,coeffs,s):
    s2=s*s
    A=mp.mpf(0);POLE=mp.mpf(0)
    pe=mp.mpf(0)  # \int phi e^{x/2}: phi=sum c_k exp(-(x-x_k)^2/2s^2); \int = c_k sqrt(2pi)s e^{x_k/2+s^2/8}
    for ck,xk in zip(coeffs,centers):
        pe+=ck*mp.sqrt(2*mp.pi)*s*mp.e**(xk/2+s2/8)
    POLE=pe**2  # = ghat(i/2); plus ghat(-i/2) by symmetry if phi real even... include both:
    pem=mp.mpf(0)
    for ck,xk in zip(coeffs,centers):
        pem+=ck*mp.sqrt(2*mp.pi)*s*mp.e**(-xk/2+s2/8)
    POLE=pe*pe*0+ (pe**2+pem**2)/ (2*mp.pi*s2) *0  # normalization messy; use direct quad below
    # DIRECT: ghat(i/2)=\int g(u)e^{u/2}du, g=phi*phi~. Just compute |\int phi e^{x/2}|^2 / norm
    # Use consistent normalization with ARCH via phihat. ARCH=(1/2pi)\int|phihat|^2 Omega,
    # phihat(r)=\int phi(x)e^{-irx}dx = sum c_k sqrt(2pi)s e^{-s^2r^2/2 -i r x_k}.
    def phihat2(r):
        re=sum(ck*mp.sqrt(2*mp.pi)*s*mp.e**(-s2*r*r/2)*mp.cos(r*xk) for ck,xk in zip(coeffs,centers))
        im=sum(-ck*mp.sqrt(2*mp.pi)*s*mp.e**(-s2*r*r/2)*mp.sin(r*xk) for ck,xk in zip(coeffs,centers))
        return re*re+im*im
    A=mp.quad(lambda r: phihat2(r)*Omega(r),[-mp.inf,0,mp.inf])/(2*mp.pi)
    # POLE = ghat(i/2)+ghat(-i/2); ghat(i/2)=|phihat(i/2)|^2 with phihat(i/2)=\int phi e^{x/2}
    pe2=pe*pe; pem2=pem*pem
    POLE=pe2+pem2
    return A,POLE
print("ARCH+POLE on positive-type phi (try to exploit Omega<0 at low r):")
for desc,centers,coeffs,s in [
    ("single bump at 0",[mp.mpf(0)],[mp.mpf(1)],mp.mpf('0.5')),
    ("wide low-freq",[mp.mpf(0)],[mp.mpf(1)],mp.mpf('2.0')),
    ("pair +-1",[mp.mpf(1),mp.mpf(-1)],[mp.mpf(1),mp.mpf(1)],mp.mpf('0.4')),
    ("antisym-ish",[mp.mpf('0.5'),mp.mpf('-0.5')],[mp.mpf(1),mp.mpf('-1')],mp.mpf('0.4')),
]:
    A,POLE=AP(centers,coeffs,s)
    print(f" {desc:18}: ARCH={mp.nstr(A,8):>12} POLE={mp.nstr(POLE,8):>12} sum={mp.nstr(A+POLE,8):>12} {'OK>=0' if A+POLE>=0 else 'NEG!'}")
