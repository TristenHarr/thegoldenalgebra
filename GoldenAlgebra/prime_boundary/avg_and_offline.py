"""
avg_and_offline.py
==================
Task 2 (average) and Task 3 (off-line pole vs prime help).

PART A — exact x-average of the prime contribution to G on the top edge.
  s = sigma - i x,  sigma = 1/2 + Y.
  G_zeta(x) = -Re( Sum_n Lambda(n) n^{-s} ) = -Sum_n Lambda(n) n^{-sigma} cos(x log n).
  Average over x in [-X,X] of cos(x log n) -> 0 for every n>=2 (log n != 0).
  => <G_zeta>_x = 0   EXACTLY (mean-zero), NOT positive.
  The DC (n=1) term is absent because Lambda(1)=0.  So the Euler-product / prime
  positivity Lambda(n)>=0 gives the prime part MEAN ZERO, with both signs --
  NOT a sign-definite positive push.  We confirm numerically.

PART B — off-line zero pole vs prime help.
  Add a single off-line zero at s0 = beta0 + i*gamma0 (beta0>1/2) to the model,
  i.e. xi'/xi gets an extra atom 1/(s - s0) + 1/(s - conj? ...).  In the z-plane
  this is a pole of Lambda_Xi in the UHP at z0 = i(s0-1/2) ... we instead probe
  G directly with the residue atom (matching ScratchMaxPrinciple
  offline_zero_forces_G_negative_below) and compare its magnitude to the best the
  prime side can offer.

  Concretely: directly BELOW the off-line zero (z-plane), the residue atom drives
  G -> -infinity, while the prime part is BOUNDED (|G_zeta| <= sum Lambda(n)n^{-sigma}
  = |zeta'/zeta(sigma)| < infinity for sigma>1).  We quantify the bound and show
  the pole wins for any prime help once close enough to the zero.
"""
import mpmath as mp
mp.mp.dps = 30

_mang={}
def mangoldt(n):
    if n in _mang: return _mang[n]
    fac={}; mm=n; d=2
    while d*d<=mm:
        while mm%d==0: fac[d]=fac.get(d,0)+1; mm//=d
        d+=1
    if mm>1: fac[mm]=fac.get(mm,0)+1
    f=mp.log(list(fac.keys())[0]) if len(fac)==1 else mp.mpf(0)
    _mang[n]=f; return f

def G_zeta_primesum(x,Y,N=20000):
    # G_zeta = -Re(Sum Lambda(n) n^{-s}) = -Sum Lambda(n) n^{-sigma} cos(x log n)
    sigma=mp.mpf('0.5')+mp.mpf(Y); acc=mp.mpf(0)
    for n in range(2,N+1):
        Ln=mangoldt(n)
        if Ln!=0:
            acc+=Ln*mp.e**(-sigma*mp.log(n))*mp.cos(mp.mpf(x)*mp.log(n))
    return -acc

def zeta_ld_real(sigma,N=20000):
    s=mp.mpf(sigma); acc=mp.mpf(0)
    for n in range(2,N+1):
        Ln=mangoldt(n)
        if Ln!=0: acc+=Ln*mp.e**(-s*mp.log(n))
    return -acc  # zeta'/zeta(sigma) < 0

print("=== PART A: x-average of the prime contribution G_zeta on the top edge ===")
print("Exact prime form: G_zeta(x) = -Sum Lambda(n) n^{-sigma} cos(x log n).")
print("<cos(x log n)>_x -> 0 for every n>=2, and Lambda(1)=0, so <G_zeta>_x = 0 EXACTLY.\n")
for Y in [0.6,1.0,2.0,5.0]:
    sigma=0.5+Y
    X=400.0; M=800
    acc=mp.mpf(0)
    for k in range(M):
        x=-X + 2*X*(k+0.5)/M
        acc+=G_zeta_primesum(x,Y)
    avg=acc/M
    budget=zeta_ld_real(sigma)  # zeta'/zeta(sigma) < 0
    print(f"Y={Y:4.1f}(s={sigma:4.2f}) <G_zeta>_x ~ {float(avg):+.6f} (-> 0)   prime L1-budget |zeta'/zeta(sigma)|={float(abs(budget)):.4f}")

print()
print("=== PART B: off-line pole vs the bounded prime help (top edge below an off-line zero) ===")
print("Residue atom of an off-line zero at z-plane height beta drives G = -m/(beta-Y) -> -inf.")
print("Prime help is BOUNDED by |zeta'/zeta(sigma)|, sigma=1/2+Y.  Pole wins near the zero.\n")
beta=2.0; m=1.0   # off-line zero modeled at z-plane height beta=2 (i.e. s-abscissa 2.5)
for Y in [0.6,1.0,1.5,1.9,1.99]:
    sigma=0.5+Y
    pole = -m/(beta-Y)                       # residue contribution to G directly below zero
    prime_budget = float(abs(zeta_ld_real(sigma)))
    print(f"Y={Y:5.2f}(s={sigma:4.2f}) pole G_atom={pole:+8.3f}   max|prime help|={prime_budget:6.3f}   pole dominates? {abs(pole)>prime_budget}")
