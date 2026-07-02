"""
Correct pole term: h(r)=phihat(r) conj(phihat(r)) on REAL axis. Analytic continuation
h_c(w)=phihat(w) * conj(phihat)(w) where conj(phihat)(w):=overline{phihat(overline w)}.
At w=i/2: conj(phihat)(i/2)=overline{phihat(overline{i/2})}=overline{phihat(-i/2)}.
So h_c(i/2)=phihat(i/2)*overline{phihat(-i/2)}.  POLE=h_c(i/2)+h_c(-i/2).
"""
import mpmath as mp
mp.mp.dps=30
def psi(z): return mp.digamma(z)
def Lambda(n):
    mm=n;fac={};d=2
    while d*d<=mm:
        while mm%d==0:fac[d]=fac.get(d,0)+1;mm//=d
        d+=1
    if mm>1:fac[mm]=fac.get(mm,0)+1
    return mp.log(list(fac.keys())[0]) if len(fac)==1 else mp.mpf(0)
def test(centers,coeffs,s,label):
    s2=s*s
    def phihat_c(w): # analytic phihat(w)=sum c_k sqrt(2pi)s e^{-s2 w2/2} e^{-i w x_k}
        return sum(ck*mp.sqrt(2*mp.pi)*s*mp.e**(-s2*w*w/2)*mp.e**(-1j*w*xk) for ck,xk in zip(coeffs,centers))
    def conj_phihat(w): # overline{phihat(overline w)} = sum c_k sqrt(2pi)s e^{-s2 w2/2} e^{+i w x_k}
        return sum(ck*mp.sqrt(2*mp.pi)*s*mp.e**(-s2*w*w/2)*mp.e**(1j*w*xk) for ck,xk in zip(coeffs,centers))
    def h(r): return abs(phihat_c(r))**2
    def g(u): return mp.quad(lambda r: h(r)*mp.cos(r*u),[0,mp.inf])/mp.pi
    g0=g(mp.mpf(0))
    ARCH=mp.quad(lambda r: h(r)*(mp.re(psi(mp.mpf(1)/4+1j*r/2))),[-mp.inf,0,mp.inf])/(2*mp.pi)-mp.log(mp.pi)*g0
    half=1j*mp.mpf(1)/2
    POLE=phihat_c(half)*conj_phihat(half)+phihat_c(-half)*conj_phihat(-half)
    POLE=mp.re(POLE)
    PR=mp.mpf(0)
    for n in range(2,3000):
        L=Lambda(n)
        if L==0: continue
        PR+=L/mp.sqrt(n)*g(mp.log(n))
    PR*=2
    Q=ARCH+POLE-PR
    LHS=mp.mpf(0)
    for k in range(1,400):
        gam=mp.im(mp.zetazero(k)); t=2*h(gam); LHS+=t
        if t<mp.mpf(10)**(-25) and gam>20: break
    print(f"[{label}] POLE={mp.nstr(POLE,8)} Q={mp.nstr(Q,12)} LHS={mp.nstr(LHS,12)} diff={mp.nstr(Q-LHS,6)}")
test([mp.mpf('0.5'),mp.mpf('-0.5')],[mp.mpf(1),mp.mpf('-1')],mp.mpf('0.4'),"antisym")
test([mp.mpf('0.5'),mp.mpf('-0.5')],[mp.mpf(1),mp.mpf(1)],mp.mpf('0.4'),"sym")
test([mp.mpf('0.3'),mp.mpf('-0.7'),mp.mpf('0.1')],[mp.mpf(1),mp.mpf('-0.5'),mp.mpf('0.8')],mp.mpf('0.35'),"generic")
