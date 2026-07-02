"""
FIX normalization by anchoring to the VALIDATED calibrate.py identity (matched 28 digits):
   sum_rho h(gamma) = (1/2pi)\int h(r)Omega(r)dr + [h(i/2)+h(-i/2)] - 2 sum_n Lambda/sqrt(n) g(log n)
with h(r)=ghat(r) (=|phihat(r)|^2 for positive type), g(u)=(1/2pi)\int h(r)e^{iru}dr.
So POLE = h(i/2)+h(-i/2) = |phihat(i/2)|^2+|phihat(-i/2)|^2 where phihat(i/2)=\int phi(x)e^{x/2}dx.
The ERROR before: I had POLE=pe^2+pem^2 with pe=\int phi e^{x/2} -- that IS h(i/2)+h(-i/2)
ONLY IF phihat(i/2)=\int phi(x)e^{(1/2)x}dx. Check: phihat(r)=\int phi e^{-irx}, so
phihat(i/2)=\int phi e^{-i(i/2)x}=\int phi e^{x/2}=pe. GOOD. h(i/2)=|phihat(i/2)|^2=pe^2. OK.
So POLE term correct. The ARCH/g normalization must be the culprit: g(u)=(1/2pi)\int h cos(ru)dr,
I used g(u)=(1/pi)\int_0^inf -- same thing. Let me re-derive h consistently and re-test the
SYMMETRIC single-bump (should give Q≈ tiny positive = zero-sum, like calibrate).
"""
import mpmath as mp
mp.mp.dps=30
Omega=lambda r: mp.re(mp.digamma(mp.mpf(1)/4+1j*r/2))-mp.log(mp.pi)
def Lambda(n):
    mm=n;fac={};d=2
    while d*d<=mm:
        while mm%d==0:fac[d]=fac.get(d,0)+1;mm//=d
        d+=1
    if mm>1:fac[mm]=fac.get(mm,0)+1
    return mp.log(list(fac.keys())[0]) if len(fac)==1 else mp.mpf(0)

def run(centers,coeffs,s,label):
    s2=s*s
    def phihat_c(r):  # complex phihat(r)=sum c_k sqrt(2pi)s e^{-s2 r2/2} e^{-i r x_k}
        return sum(ck*mp.sqrt(2*mp.pi)*s*mp.e**(-s2*r*r/2)*mp.e**(-1j*r*xk) for ck,xk in zip(coeffs,centers))
    def h(r): return abs(phihat_c(r))**2
    def hc_imag(half):  # h at r=i*half : phihat(i*half)=sum c_k sqrt(2pi)s e^{s2 half^2/2} e^{half x_k}
        ph=sum(ck*mp.sqrt(2*mp.pi)*s*mp.e**(s2*half*half/2)*mp.e**(half*xk) for ck,xk in zip(coeffs,centers))
        phm=sum(ck*mp.sqrt(2*mp.pi)*s*mp.e**(s2*half*half/2)*mp.e**(-half*xk) for ck,xk in zip(coeffs,centers))
        return ph,phm
    A=mp.quad(lambda r: h(r)*Omega(r),[-mp.inf,0,mp.inf])/(2*mp.pi)
    ph,phm=hc_imag(mp.mpf(1)/2)
    POLE=ph*mp.conj(ph)+phm*mp.conj(phm)  # h(i/2)+h(-i/2); for real coeffs ph,phm real
    POLE=mp.re(POLE)
    def g(u): return mp.quad(lambda r: h(r)*mp.cos(r*u),[0,mp.inf])/mp.pi
    PRIME=mp.mpf(0)
    for n in range(2,3000):
        L=Lambda(n)
        if L==0: continue
        PRIME+=L/mp.sqrt(n)*g(mp.log(n))
    PRIME*=2
    Q=A+POLE-PRIME
    LHS=mp.mpf(0)
    for k in range(1,400):
        gam=mp.im(mp.zetazero(k)); t=2*h(gam); LHS+=t
        if t<mp.mpf(10)**(-25) and gam>20: break
    print(f"[{label}] A={mp.nstr(A,8)} POLE={mp.nstr(POLE,8)} PRIME={mp.nstr(PRIME,8)} Q={mp.nstr(Q,10)} LHS={mp.nstr(LHS,10)} Q-LHS={mp.nstr(Q-LHS,6)}")

run([mp.mpf(0)],[mp.mpf(1)],mp.mpf('0.4'),"single sym bump")
run([mp.mpf('0.5'),mp.mpf('-0.5')],[mp.mpf(1),mp.mpf(1)],mp.mpf('0.4'),"sym pair")
run([mp.mpf('0.5'),mp.mpf('-0.5')],[mp.mpf(1),mp.mpf('-1')],mp.mpf('0.4'),"antisym pair")
