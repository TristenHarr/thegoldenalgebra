"""
The TOTAL prime form density: D_tot(r) = sum_p (log p) B_p(r) where
B_p(r)=Re(z/(1-z)), z=p^{-1/2}e^{i r log p}. The prime contribution to Q is
   PRIME_form(phi) = -(1/pi)\int |phihat(r)|^2 D_tot(r) dr.
Note sum_p (log p) sum_k p^{-k/2} e^{i k r log p} = sum_n Lambda(n) n^{-1/2} e^{i r log n}
   = -zeta'/zeta(1/2 - i r) (Dirichlet series). So D_tot(r)=Re(-zeta'/zeta(1/2 - i r))
   = -Re(zeta'/zeta(1/2+i r)) (even). Matches prime_indef.py's D up to factor.

ARCHIMEDEAN density: Omega(r)=Re psi(1/4+ir/2)-log pi. Connes: ARCH form >=0 on Sonin.
POLE density: the pole adds +cosh-type, effectively boosting low-r.

TOTAL bulk kernel for Q (ignoring pole, which only helps):
   K(r) = Omega(r) + 2 D_tot(r)   [need >=0 for unconditional global positivity]
Wait: Q = ARCH + POLE - PRIME, PRIME form = -(1/pi)\int|phihat|^2 D_tot... so
-PRIME = +(1/pi)\int |phihat|^2 D_tot. And ARCH=(1/2pi)\int|phihat|^2 Omega.
So bulk Q density (per |phihat(r)|^2) = (1/2pi)[Omega(r) + 2 D_tot(r)] + pole.
We already saw Omega+2 D_tot ~ 0 (functional eq). Let's PLOT both & their sum carefully
with the CORRECT D_tot (finite prime sum, NOT zeta'/zeta which embeds zeros).
"""
import numpy as np, mpmath as mp
mp.mp.dps=20
def vm(N):
    out={}
    for n in range(2,N+1):
        mm=n;fac={};d=2
        while d*d<=mm:
            while mm%d==0:fac[d]=fac.get(d,0)+1;mm//=d
            d+=1
        if mm>1:fac[mm]=fac.get(mm,0)+1
        if len(fac)==1:out[n]=np.log(list(fac.keys())[0])
    return out
PL=vm(100000)
def Dtot_finite(r, Ncut):
    # finite-prime version: only n<=Ncut. THIS is the unconditional object.
    s=0.0
    for n,lam in PL.items():
        if n>Ncut: break
        s+=lam/np.sqrt(n)*np.cos(r*np.log(n))
    return s
def Omega(r): return float(mp.re(mp.digamma(mp.mpf(1)/4+1j*mp.mpf(r)/2))-mp.log(mp.pi))

print("r       Omega(r)    2*Dtot(N=e^2)  2*Dtot(N=e^6)  2*Dtot(full)  Omega+2Dtot(full)")
for r in [0.5,2,5,10,14.13,20,30,50]:
    Om=Omega(r)
    d2=2*Dtot_finite(r,np.exp(2))
    d6=2*Dtot_finite(r,np.exp(6))
    dfull=2*Dtot_finite(r,100000)
    print(f"{r:6.2f} {Om:11.4f} {d2:13.4f} {d6:13.4f} {dfull:13.4f} {Om+dfull:13.4f}")
print()
print("Observe: Omega(r)<0 for moderate r (digamma small), grows ~+log(r/2) for large r.")
print("Dtot oscillates O(1). For FINITE cutoff (short support) the prime density is a")
print("trig polynomial in r -> bounded, so Omega(r)+2Dtot dominated by Omega sign.")
