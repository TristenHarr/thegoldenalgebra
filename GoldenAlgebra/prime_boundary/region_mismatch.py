"""
region_mismatch.py
==================
THE decisive structural point (Task 3 mechanism + Task 1 region analysis).

The top edge at height Y sits at s-abscissa sigma = 1/2 + Y.
  * Prime sum  Sum Lambda(n) n^{-s}  converges  <=>  sigma > 1  <=>  Y > 1/2.
  * Nontrivial zeros live in  0 < Re s < 1, i.e. -1/2 < (sigma-1/2) so the off-line
    zeros that the UHP wall is about have z-height  Y_zero = Re s - 1/2 in (0, 1/2).

=> The ONLY top edges the prime sum reaches (Y>1/2, sigma>1) are STRICTLY ABOVE
   every possible off-line zero (whose z-height is < 1/2, since Re s < 1).  And in
   sigma>1 zeta has NO zeros at all.  So where the prime side is available, there
   is nothing to control; where there is something to control (0<Y<1/2, sigma in
   (1/2,1)), the prime series DIVERGES and supplies no inequality.

This is the EXACT obstruction: prime positivity Lambda(n)>=0 is an inequality on
the half-plane sigma>1, which is disjoint from the critical strip where off-line
zeros could live.  The off-line pole is NOT reachable by the convergent Euler
product; analytic continuation past sigma=1 destroys term-positivity (the series
no longer represents zeta'/zeta, and the continued function takes both signs --
exactly the mean-zero behaviour of Part A pushed to its divergence boundary).

We confirm:
 (1) max possible z-height of an off-line zero = (sup Re s of a zero) - 1/2 < 1/2.
 (2) the prime sum's region of convergence Y>1/2 lies entirely ABOVE that.
 (3) at the boundary sigma=1 (Y=1/2) the prime budget |zeta'/zeta| blows up
     (pole of zeta at s=1) -- the Euler product degenerates exactly as it would
     need to start helping.
"""
import mpmath as mp
mp.mp.dps=25

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

def prime_budget(sigma,N=50000):
    s=mp.mpf(sigma); acc=mp.mpf(0)
    for n in range(2,N+1):
        Ln=mangoldt(n)
        if Ln!=0: acc+=Ln*mp.e**(-s*mp.log(n))
    return acc  # = -zeta'/zeta(sigma) > 0 for sigma>1

print("=== (1)/(2) Region mismatch: prime convergence vs off-line zeros ===")
print("Off-line zero at s=beta+i*gamma, 1/2<beta<1, has z-height Y_zero=beta-1/2 in (0,1/2).")
print("Prime sum converges only for sigma=1/2+Y>1, i.e. Y>1/2 > every Y_zero.  DISJOINT.\n")
print(" beta (Re s of zero) | z-height Y_zero | prime sum converges at that height?")
for beta in [0.51,0.6,0.75,0.9,0.99]:
    Yz=beta-0.5
    conv = (0.5+Yz)>1.0
    print(f"   {beta:4.2f}              |   {Yz:5.3f}        |  {conv}  (sigma_there={0.5+Yz:.3f})")

print()
print("=== (3) Prime L1-budget |zeta'/zeta(sigma)| as sigma -> 1+ (Y -> 1/2+) ===")
print("(Euler product degenerates -- budget blows up -- exactly where it would need to start helping.)\n")
for sigma in [3.0,2.0,1.5,1.2,1.1,1.05,1.02,1.01]:
    b=prime_budget(sigma)
    print(f" sigma={sigma:5.2f} (Y={sigma-0.5:5.2f})  |zeta'/zeta|={float(b):8.3f}")
print(" sigma->1+ : |zeta'/zeta| -> +inf (pole of zeta).  No bounded sign-definite help survives the limit.")

print()
print("=== CONCLUSION ===")
print("Prime positivity Lambda(n)>=0 is an inequality on the half-plane sigma>1, which is")
print("DISJOINT from the critical strip (sigma in (1/2,1)) where off-line zeros could sit.")
print("On the reachable top edges (Y>1/2) there are no zeros to control AND the prime part")
print("is mean-zero (Part A).  On the unreachable ones (0<Y<1/2) the series diverges.")
print("=> The off-line pole dominates; the prime side gives NO top-edge positivity beyond")
print("   what height-envelopes already give.  TopBoundaryPositive(Y) for all Y stays = RH.")
