"""
Resolve the antisym 1.068 discrepancy. The Weil explicit formula (Iwaniec-Kowalski 5.12)
for an even test function pair. KEY: my 'h(r)=|phihat(r)|^2' is even & >=0, g=its transform
even. The identity must close. The 1.068 gap for antisym phi means I mis-handled a term.
Let me compute Q DIRECTLY from the explicit formula in its most standard linear form and 
verify it equals sum over zeros, by brute force, for h(r)=|phihat(r)|^2 with antisym phi.

Standard (Iwaniec-Kowalski Thm 5.12), test fn h even, holomorphic in |Im r|<1/2+eps,
decaying; g(u)=(1/2pi)\int h(r)e^{-iru}dr:
  sum_rho h(gamma_rho) = h(i/2)+h(-i/2)              [poles at s=0,1]
                       - (1/2pi)\int h(r)[ (Gamma'/Gamma)(1/4+ir/2)... ] but with -log pi 
                       wait the arch is  + (1/2pi)\int h(r) Re(psi(1/4+ir/2)) dr - (log pi) g(0) ??? 
  Let me just include the g(0) log pi as separate and recompute. Maybe I folded -log pi into
  Omega but the g(0) weighting differs from the h-integral weighting for antisym (g(0) large).
"""
import numpy as np, mpmath as mp
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
    def phihat_c(r):
        return sum(ck*mp.sqrt(2*mp.pi)*s*mp.e**(-s2*r*r/2)*mp.e**(-1j*r*xk) for ck,xk in zip(coeffs,centers))
    def h(r): return abs(phihat_c(r))**2
    def g(u): return mp.quad(lambda r: h(r)*mp.cos(r*u),[0,mp.inf])/mp.pi  # even
    g0=g(mp.mpf(0))
    # ARCH split: + (1/2pi)\int h(r) Re psi(1/4+ir/2) dr   MINUS  (log pi) g(0)
    ARCH_psi=mp.quad(lambda r: h(r)*mp.re(psi(mp.mpf(1)/4+1j*r/2)),[-mp.inf,0,mp.inf])/(2*mp.pi)
    ARCH_logpi=mp.log(mp.pi)*g0
    # POLE
    ph=phihat_c(1j*mp.mpf(1)/2); phm=phihat_c(-1j*mp.mpf(1)/2)
    POLE=abs(ph)**2+abs(phm)**2
    # PRIME
    PR=mp.mpf(0)
    for n in range(2,3000):
        L=Lambda(n)
        if L==0: continue
        PR+=L/mp.sqrt(n)*g(mp.log(n))
    PR*=2
    Q=ARCH_psi - ARCH_logpi + POLE - PR
    LHS=mp.mpf(0)
    for k in range(1,400):
        gam=mp.im(mp.zetazero(k)); t=2*h(gam); LHS+=t
        if t<mp.mpf(10)**(-25) and gam>20: break
    print(f"[{label}] g0={mp.nstr(g0,6)} ARCHpsi={mp.nstr(ARCH_psi,6)} -logpi*g0={mp.nstr(-ARCH_logpi,6)} POLE={mp.nstr(POLE,6)} PRIME={mp.nstr(PR,6)}")
    print(f"        Q={mp.nstr(Q,10)}  LHS={mp.nstr(LHS,10)}  diff={mp.nstr(Q-LHS,6)}")

test([mp.mpf('0.5'),mp.mpf('-0.5')],[mp.mpf(1),mp.mpf('-1')],mp.mpf('0.4'),"antisym")
test([mp.mpf('0.5'),mp.mpf('-0.5')],[mp.mpf(1),mp.mpf(1)],mp.mpf('0.4'),"sym (control)")
