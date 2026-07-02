"""
Is the 'antisym' phi (ARCH+POLE<0) actually a Q<0 witness, or does PRIME rescue?
Compute FULL Q=ARCH+POLE-PRIME with the SAME normalization, and cross-check via the
zero-sum LHS = 2 sum_rho |phihat(gamma)|^2 ... wait LHS = sum_rho ghat(gamma) and
ghat(r)=|phihat(r)|^2>=0, so LHS = sum over zeros |phihat(gamma_rho)|^2 >= 0 IF zeros on line.
That's the consistency check (not an assumption: zeros in range ARE on line, verified).
If FULL Q >=0 while ARCH+POLE<0, then PRIME is NEGATIVE (i.e. -PRIME>0) here, meaning
the prime term HELPS -- the sign of PRIME flips by direction. Let's see the decomposition.
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

centers=[mp.mpf('0.5'),mp.mpf('-0.5')]; coeffs=[mp.mpf(1),mp.mpf('-1')]; s=mp.mpf('0.4'); s2=s*s
def phihat_re_im(r):
    re=sum(ck*mp.sqrt(2*mp.pi)*s*mp.e**(-s2*r*r/2)*mp.cos(r*xk) for ck,xk in zip(coeffs,centers))
    im=sum(-ck*mp.sqrt(2*mp.pi)*s*mp.e**(-s2*r*r/2)*mp.sin(r*xk) for ck,xk in zip(coeffs,centers))
    return re,im
def phihat2(r):
    re,im=phihat_re_im(r); return re*re+im*im
A=mp.quad(lambda r: phihat2(r)*Omega(r),[-mp.inf,0,mp.inf])/(2*mp.pi)
# POLE = |int phi e^{x/2}|^2 + |int phi e^{-x/2}|^2
pe=sum(ck*mp.sqrt(2*mp.pi)*s*mp.e**(xk/2+s2/8) for ck,xk in zip(coeffs,centers))
pem=sum(ck*mp.sqrt(2*mp.pi)*s*mp.e**(-xk/2+s2/8) for ck,xk in zip(coeffs,centers))
POLE=pe*pe+pem*pem
# g(u)=(phi*phi~)(u). phihat2(r)=ghat(r). g(u)=(1/2pi)\int ghat(r)e^{i r u}dr.
# PRIME=2 sum Lambda(n)/sqrt(n) g(log n). Compute g via inverse transform of phihat2.
def g(u):
    return mp.quad(lambda r: phihat2(r)*mp.cos(r*u),[0,mp.inf])/mp.pi
PRIME=mp.mpf(0)
for n in range(2,2000):
    L=Lambda(n)
    if L==0: continue
    PRIME+=L/mp.sqrt(n)*g(mp.log(n))
PRIME*=2
Q=A+POLE-PRIME
# LHS zero-sum check
LHS=mp.mpf(0)
for k in range(1,500):
    gam=mp.im(mp.zetazero(k)); t=2*phihat2(gam); LHS+=t
    if t<mp.mpf(10)**(-25) and gam>20: break
print("phi=antisym pair at +-0.5, s=0.4 (support ~[-1.5,1.5], n=2,3 primes in range)")
print(f"ARCH  = {mp.nstr(A,12)}")
print(f"POLE  = {mp.nstr(POLE,12)}")
print(f"PRIME = {mp.nstr(PRIME,12)}")
print(f"Q=ARCH+POLE-PRIME = {mp.nstr(Q,12)}")
print(f"LHS=sum_rho|phihat(gamma)|^2 = {mp.nstr(LHS,12)}  (>=0, on-line check)")
print(f"Q - LHS = {mp.nstr(Q-LHS,8)}  (should be ~0: validates assembly)")
