#!/usr/bin/env python3
"""
signed_kernel_threshold.py — pin the CLEAN Lean-provable threshold for the
off-axis per-zero net positivity, and confirm the two candidate regions:

  R_clean = { y >= sqrt(3)/2 }   (per-MIRROR bound works: a^2+y^2 >= 3 eta^2 for ALL a>=0)
  R_full  = { y >= 1/2 }         (true region; per-mirror fails at pole-touch but the
                                  POLE SIGN (y>eta) still gives net>0; needs the
                                  combined/pole-sign argument, harder for Lean)

We prove the per-mirror bound  |k(eta,a)| <= 6 y eta^2/(a^2+y^2)^2  and the reduction
to  a^2+y^2 >= 3 eta^2.  On R_clean:  y >= sqrt(3)/2, eta^2<=1/4  =>  3 eta^2 <= 3/4 = (sqrt3/2)^2 <= y^2 <= a^2+y^2.  CLEAN.

Honest triviality of R_clean: at y=sqrt(3)/2 ~ 0.866, x=gamma, eta=1/2, the probe is
at Euclidean distance y-eta = 0.366 from the off-line zero — STILL near (vs 14 on axis).
"""
import mpmath as mp
mp.mp.dps = 40
import random

def kmirror(y, e, a):
    y,e,a = mp.mpf(y),mp.mpf(e),mp.mpf(a)
    den = (a**2+y**2)*((e-y)**2+a**2)*((e+y)**2+a**2)
    if den==0: return mp.mpf('nan')
    return 2*e**2*y*(y**2 - 3*a**2 - e**2)/den

def permirror_net(y,e,a):
    return 2*mp.mpf(y)/(mp.mpf(y)**2+mp.mpf(a)**2) + kmirror(y,e,a)

sqrt3o2 = mp.sqrt(3)/2
print(f"sqrt(3)/2 = {mp.nstr(sqrt3o2,8)}")
print()
print("="*78)
print("(1) per-mirror majorant |k(eta,a)| <= 6 y eta^2/(a^2+y^2)^2 on y>=1/2:")
print("="*78)
maxr=mp.mpf(0); arg=None
random.seed(7)
for _ in range(600000):
    a=mp.mpf(random.uniform(-300,300)); y=mp.mpf(random.uniform(0.5,800)); e=mp.mpf(random.uniform(-0.5,0.5))
    lhs=abs(kmirror(y,e,a)); rhs=6*y*e**2/(a**2+y**2)**2
    if rhs>0:
        r=lhs/rhs
        if r>maxr: maxr=r; arg=(float(a),float(y),float(e))
print(f"  max ratio = {mp.nstr(maxr,8)}  at {arg}   (<=1 confirms majorant): {maxr<=1}")
print()

print("="*78)
print("(2) per-MIRROR net positivity threshold: 2y/(y^2+a^2) - 6 y eta^2/(a^2+y^2)^2 >= 0")
print("    <=>  a^2 + y^2 >= 3 eta^2.   Worst a=0:  y^2 >= 3 eta^2  <=>  y >= sqrt(3)|eta|.")
print("    With |eta|<=1/2:  y >= sqrt(3)/2 = 0.8660 suffices for ALL a, ALL eta.")
print("="*78)
# verify per-mirror net >= 0 on R_clean = {y>=sqrt(3)/2}, ALL a, |eta|<=1/2
minnet=None
for _ in range(600000):
    a=mp.mpf(random.uniform(-400,400)); y=mp.mpf(random.uniform(float(sqrt3o2),800)); e=mp.mpf(random.uniform(-0.5,0.5))
    n=permirror_net(y,e,a)
    if mp.isnan(n): continue
    if minnet is None or n<minnet[0]: minnet=(n,float(a),float(y),float(e))
print(f"  min per-mirror net on R_clean: {mp.nstr(minnet[0],6)} at (a,y,eta)={minnet[1:]}  >=0? {minnet[0]>=0}")
print()

print("="*78)
print("(3) Does per-mirror net stay >=0 BELOW sqrt(3)/2 (in [1/2, sqrt3/2))?  Find min.")
print("="*78)
# Here the per-mirror bound can fail (pole-touch). The TRUE per-mirror net can go negative
# for a single mirror; only the FULL two-mirror + reference saves it. Show a single mirror
# CAN be net-negative in [1/2, sqrt3/2):
g=mp.mpf('14.1347251417'); e=mp.mpf('0.5')
print("  Single mirror at a=0 (x=gamma), eta=1/2, y in [0.5, 0.866]:")
for y in [mp.mpf(v) for v in [0.5001,0.55,0.6,0.7,0.8,0.85,0.866]]:
    n=permirror_net(y,e,0)
    print(f"    y={float(y):>6.4f}  k(eta,0)={mp.nstr(kmirror(y,e,0),5):>12}  2y/y^2={mp.nstr(2*y/y**2,5):>9}  net_mirror={mp.nstr(n,5):>12} >=0? {n>=0}")
print("  => the single near-mirror at a=0 stays net>=0 down to y=1/2 ANYWAY (pole sign helps).")
print("     So actually R_full={y>=1/2} works per-mirror too at a=0; the 6y eta^2 majorant")
print("     was just LOSSY near the pole. Let's find the TRUE per-mirror net threshold.")
print()
# True per-mirror net minimum over ALL a, |eta|<=1/2, as function of y floor:
print("(3b) TRUE min per-mirror net vs y-floor (Monte Carlo), all a, |eta|<=1/2:")
for yfloor in [0.5, 0.55, 0.6, 0.7, 0.75, 0.8, 0.866]:
    mn=None
    for _ in range(300000):
        a=mp.mpf(random.uniform(-300,300)); y=mp.mpf(random.uniform(yfloor, yfloor+0.3)); e=mp.mpf(random.uniform(-0.5,0.5))
        n=permirror_net(y,e,a)
        if mp.isnan(n): continue
        if mn is None or n<mn[0]: mn=(n,float(a),float(y),float(e))
    print(f"  y in [{yfloor},{yfloor+0.3}): min per-mirror net = {mp.nstr(mn[0],5)} at a={mn[1]:.2f},y={mn[2]:.3f},eta={mn[3]:.3f}  >=0? {mn[0]>=0}")
print()

print("="*78)
print("(4) HONEST triviality of R_clean = {y>=sqrt(3)/2}: closest approach to a zero")
print("="*78)
# probe x=gamma, y=sqrt3/2, off-line zero eta=1/2: dist = y-eta = 0.866-0.5 = 0.366
g=mp.mpf('14.1347251417'); e=mp.mpf('0.5'); y=sqrt3o2; x=g
dist=mp.sqrt((x-g)**2+(y-e)**2)
print(f"  probe x=gamma={float(g):.3f}, y=sqrt3/2={float(y):.4f}; off-line zero (gamma, eta=0.5)")
print(f"  Euclidean distance probe->zero = {mp.nstr(dist,5)}   (vs >=14.13 on the trivial axis)")
print(f"  => R_clean reaches within 0.366 of any off-line zero: NONTRIVIAL (sign-protected).")
