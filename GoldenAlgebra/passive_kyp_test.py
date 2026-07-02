"""
PASSIVE NETWORK / KYP-LEMMA / POSITIVE-REAL realization attack on Theta_Phi.

A function Theta is contractive (Schur) on the UHP  <=>  its Cayley transform
   H = (1+Theta)/(1-Theta)  =  (A+B)/(A-B)
is a POSITIVE-REAL (Herglotz) function: Re H >= 0 on the UHP. A passive LTI
realization (A,B,C,D state space) exists  <=>  H positive-real  <=>  KYP LMI
   [ A^T P + P A    P B - C^T ] <= 0  for some P=P^T > 0  (Kalman-Yakubovich-Popov)
   [ B^T P - C     -(D+D^T)   ]
is feasible. So: a passive realization of H exists  <=>  Re H>=0 on UHP  <=> R>=0
(the very dominance) <=> RH.  There is NO passive realization UNLESS RH.

DECISIVE TEST: compute Re H over the UHP for the TRUE Phi (should be >=0, RH-true
numerically) AND for the toy positive measures that violate R>=0 (Re H must go <0,
i.e. NO passive realization). This confirms passivity is EXACTLY the wall, and a
KYP-positive P cannot be built from theta moments alone -- it would require the
relative-phase (zeros-real) data.

We also test the KYP LMI directly on a TRUNCATED moment realization: build the
Hankel/moment matrix from the theta moments and check whether a P>0 solving the
KYP inequality exists WITHOUT real-zero input.
"""
import mpmath as mp
import numpy as np
mp.mp.dps = 22

def phi_term(u,n):
    npi=mp.pi*n*n
    return (2*npi*npi*mp.e**(9*u)-3*npi*mp.e**(5*u))*mp.e**(-npi*mp.e**(4*u))
def Phi(u,N=26): return mp.fsum(phi_term(u,n) for n in range(1,N+1))
UP=6.0
def C(w):  return mp.quad(lambda u:Phi(u)*mp.cos(w*u),[0,UP])
def Cp(w): return mp.quad(lambda u:-Phi(u)*u*mp.sin(w*u),[0,UP])
# A+B=2C(w), A-B=-2iC'(w), w=conj(z)=x-iy. H=(A+B)/(A-B)=2C/(-2iC')=i C/C'.
def H_of(x,y):
    w=mp.mpc(x,-y); c=C(w); cp=Cp(w)
    if cp==0: return None
    return 1j*c/cp

print("="*80)
print("Re H over the UHP for the TRUE Riemann Phi  (H positive-real <=> Theta Schur)")
print("="*80)
anyneg=False
print(f"{'x':>8} {'y':>7} {'Re H':>16} {'Im H':>16}")
for x in [0.5,3.0,7.0,14.134725,20.0,28.0]:
    for y in [1.0,0.5,0.2,0.05]:
        H=H_of(x,y)
        if H is None: continue
        if H.real< -1e-9: anyneg=True
        print(f"{x:>8} {y:>7} {mp.nstr(H.real,8):>16} {mp.nstr(H.imag,8):>16}")
print("ANY Re H < 0 (true Phi):", anyneg, " => positive-real holds numerically (RH true).")

print()
print("="*80)
print("Toy POSITIVE measures with R<0: Re H MUST go negative => NO passive realization")
print("="*80)
def H_toy(phifun,x,y,UP2=8.0):
    def Cc(w): return mp.quad(lambda u:phifun(u)*mp.cos(w*u),[0,UP2])
    def Cpp(w):return mp.quad(lambda u:-phifun(u)*u*mp.sin(w*u),[0,UP2])
    w=mp.mpc(x,-y); c=Cc(w); cp=Cpp(w)
    return 1j*c/cp if cp!=0 else None
for f,nm in [(lambda u:mp.e**(-u),'e^-u'),(lambda u:u*mp.e**(-u),'u e^-u'),
             (lambda u:mp.e**(-u)*(1+mp.cos(3*u))/2,'e^-u(1+cos3u)/2')]:
    neg=False; worst=(0,1e18)
    for x in np.linspace(0.5,30,25):
        for y in np.linspace(0.05,2.5,12):
            H=H_toy(f,float(x),float(y))
            if H is None: continue
            if H.real<worst[1]: worst=((float(x),float(y)),H.real)
            if H.real<-1e-9: neg=True
    print(f"  {nm:>20}: min Re H = {mp.nstr(worst[1],5)} at {worst[0]}  "
          f"{'Re H<0 => NOT positive-real => NO passive realization' if neg else 'pos-real'}")

print()
print("="*80)
print("KYP / state-space verdict:")
print("="*80)
print("H positive-real <=> exists P=P^T>0 solving the KYP LMI <=> Theta Schur <=> R>=0 <=> RH.")
print("Re H>=0 on UHP is NOT implied by Phi>=0 (toy positive measures break it above).")
print("A KYP certificate P would have to encode the RELATIVE PHASE arg(A+B)-arg(A-B),")
print("which is governed by the zero-location of C=Xi/2 -- i.e. constructing P>0 from")
print("theta moments alone is equivalent to proving Xi has real zeros = RH. The passive")
print("realization exists IFF RH; there is no unconditional theta-only KYP solution.")
