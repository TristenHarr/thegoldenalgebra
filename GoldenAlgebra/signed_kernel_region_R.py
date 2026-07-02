#!/usr/bin/env python3
"""
signed_kernel_region_R.py — THE OFF-AXIS REGION R and its honest triviality test.

FINDINGS so far (signed_kernel_offaxis.py, signed_kernel_signmap.py):
  K_z(eta,gamma) = k(eta,gamma+x) + k(eta,gamma-x),  per-mirror pole at (x=gamma, y=eta).
  Singular part near zero w=gamma+i eta:  K ~ +(y-eta)/|z-w|^2.
   * y>eta  => K->+inf  (HELP)
   * y<eta  => K->-inf  (HURT), and reference R stays bounded => per-zero net < 0.
  Off-line zeros have |eta| < 1/2.  So the HURT sliver lives ENTIRELY in y<1/2.

CANDIDATE REGION  R = { z = x + i y : y >= 1/2 }  (ALL x, the full half-plane strip
above height 1/2).  Claim to test:  on R, for EVERY off-line zero (gamma, eta) with
|eta|<=1/2, gamma>=14, the per-zero net  R_ref(x,y,gamma) + K_z(eta,gamma) >= 0
UNCONDITIONALLY.  This region is NONTRIVIAL: it lets x range over ALL abscissae,
including x = gamma (probe directly UNDER a zero), distance to the zero = y-eta
which can be as small as 1/2 - 1/2 -> 0.  Unlike the x=0 axis (always >=14 from
every zero), R *touches* the zeros (in abscissa) and approaches them to within ~0.
THE ONLY thing keeping us out of the pole is y >= 1/2 > |eta|: we stay ABOVE every
zero, where the pole HELPS.

This script:
  (A) verifies per-zero net >= 0 on a dense grid of R, including x=gamma, y just
      above 1/2, the WORST case (closest approach above the pole);
  (B) finds the worst-case per-zero net margin on R and where it occurs;
  (C) honest triviality verdict: how close (in actual Euclidean distance) does the
      worst probe get to its nearest zero? Compare to the trivial axis (dist>=14).
  (D) the clean Lean-provable bound for the per-zero net on R.
"""
import mpmath as mp
mp.mp.dps = 40

def kmirror(y, e, a):
    y,e,a = mp.mpf(y),mp.mpf(e),mp.mpf(a)
    num = 2*e**2*y*(y**2 - 3*a**2 - e**2)
    den = (a**2+y**2)*((e-y)**2+a**2)*((e+y)**2+a**2)
    if den == 0:
        return mp.mpf('nan')  # exact pole; excluded from the open region
    return num/den

def Kfull(x, y, e, g):
    return kmirror(y,e,g+x) + kmirror(y,e,g-x)

def Rref(x, y, g):
    x,y,g = mp.mpf(x),mp.mpf(y),mp.mpf(g)
    return 2*y/(y**2+(g+x)**2) + 2*y/(y**2+(g-x)**2)

print("="*80)
print("(A)/(B): WORST per-zero net on R = {y >= 1/2}, scanning x near gamma, y near 1/2")
print("="*80)
# Worst case heuristics: closest approach above the pole => y just above eta_max=1/2,
# x = gamma (a_-=0). Also the HURT mirror needs a_+ large but that's tiny. Scan.
worst = None
gammas = [14.1347, 21.022, 25.011, 30.425, 50.0, 100.0, 1000.0]
etas   = [0.5, 0.49, 0.4, 0.25, 0.1]
for g in gammas:
    for e in etas:
        for y in [0.5, 0.5001, 0.51, 0.55, 0.6, 0.75, 1.0, 2.0, 5.0]:
            # worst x is near gamma (a_-=0) for the pole; also sweep some x
            for x in [g, g-0.5, g-2, g-5, 0, g+5, 2*g]:
                K = Kfull(x,y,e,g); R = Rref(x,y,g); net = R+K
                if mp.isnan(net): continue
                if worst is None or net < worst[0]:
                    worst = (net, x, y, e, g, K, R)
print(f"WORST per-zero net (R+K) over R-grid: {mp.nstr(worst[0],6)}")
print(f"   at x={worst[1]}, y={worst[2]}, eta={worst[3]}, gamma={worst[4]}")
print(f"   K={mp.nstr(worst[5],6)}, R={mp.nstr(worst[6],6)}")
print(f"   net >= 0 ?  {worst[0] >= 0}")
print()

# Refine right at the boundary y=1/2, x=gamma, eta=1/2 (the pole-touch from above):
print("Boundary probe: y=1/2+delta, x=gamma, eta=1/2 (closest legal approach to pole):")
g = mp.mpf('14.1347251417')
e = mp.mpf('0.5')
print(f"{'y':>10} {'dist to zero=y-eta':>20} {'K':>16} {'R':>14} {'R+K':>16} {'net>=0':>8}")
for dy in [mp.mpf('1e-1'), mp.mpf('1e-2'), mp.mpf('1e-3'), mp.mpf('1e-5'), mp.mpf('1e-8')]:
    y = e + dy
    K = Kfull(g,y,e,g); R = Rref(g,y,g); net=R+K
    print(f"{float(y):>10.6f} {float(dy):>20.2e} {mp.nstr(K,5):>16} {mp.nstr(R,5):>14} "
          f"{mp.nstr(net,5):>16} {str(net>=0):>8}")
print()

print("="*80)
print("(C): HONEST TRIVIALITY VERDICT — Euclidean distance from worst probe to zero")
print("="*80)
# On R, the closest a probe gets to an off-line zero w=gamma+i eta is when x=gamma,
# y->eta from above (y>=1/2>eta). Euclidean dist = y-eta -> can be ~0 (if eta close
# to 1/2 and y close to 1/2). So R touches zeros to distance -> 0.  NONTRIVIAL.
print("On R (y>=1/2), take a hypothetical off-line zero at gamma, eta=0.499.")
print("Probe x=gamma, y=0.5: Euclidean distance to the zero = sqrt(0^2+(0.5-0.499)^2)=0.001.")
print("Compare the TRIVIAL axis x=0: distance to ANY zero >= gamma_1 = 14.13.")
print()
g=mp.mpf('14.1347251417'); e=mp.mpf('0.499'); y=mp.mpf('0.5'); x=g
dist = mp.sqrt((x-g)**2+(y-e)**2)
K=Kfull(x,y,e,g); R=Rref(x,y,g); net=R+K
print(f"  NEAR probe: x=gamma, y=0.5, eta=0.499 -> Euclid dist to zero = {mp.nstr(dist,4)}")
print(f"     K={mp.nstr(K,5)}, R={mp.nstr(R,5)}, net=R+K={mp.nstr(net,5)}, net>=0? {net>=0}")
print(f"  => R reaches within {mp.nstr(dist,3)} of an off-line zero and STILL nets >=0.")
print(f"     This is NONTRIVIAL: the domination is NOT 'safe by distance' (dist~0),")
print(f"     it is 'safe by SIGN' (we sit ABOVE the zero, where the pole HELPS).")
print()

print("="*80)
print("(D): THE CLEAN LEAN-PROVABLE PER-ZERO BOUND on R = {y >= 1/2}")
print("="*80)
print("Per-mirror:  k(eta,a) = 2 eta^2 y (y^2-3a^2-eta^2)/[(a^2+y^2)((y-eta)^2+a^2)((y+eta)^2+a^2)].")
print("We need a uniform LOWER bound k(eta,a) >= -(reference share). Try the analogue of")
print("the axis majorant |k(eta,a)| <= 6 y eta^2/(a^2+y^2)^2 and dominate by the mirror's")
print("OWN reference 2y/(y^2+a^2).  Check |k| <= 6 y eta^2/(a^2+y^2)^2 on R numerically:")
maxratio = mp.mpf(0); arg=None
import random
random.seed(1)
for _ in range(400000):
    a = mp.mpf(random.uniform(-200,200))
    y = mp.mpf(random.uniform(0.5, 500))
    e = mp.mpf(random.uniform(-0.5,0.5))
    lhs = abs(kmirror(y,e,a))
    rhs = 6*y*e**2/(a**2+y**2)**2
    if rhs>0:
        r = lhs/rhs
        if r>maxratio: maxratio=r; arg=(float(a),float(y),float(e))
print(f"  max |k(eta,a)| / [6 y eta^2/(a^2+y^2)^2]  over 4e5 random pts on R: {mp.nstr(maxratio,8)}")
print(f"     at (a,y,eta)={arg}")
print(f"  => banked per-mirror majorant  |k(eta,a)| <= 6 y eta^2/(a^2+y^2)^2  holds: {maxratio<=1}")
print()
print("Then per-mirror net = 2y/(y^2+a^2) + k(eta,a) >= 2y/(y^2+a^2) - 6 y eta^2/(a^2+y^2)^2")
print("   = (2y/(a^2+y^2))(1 - 3 eta^2/(a^2+y^2)) >= 0  iff  a^2+y^2 >= 3 eta^2.")
print("On R: y>=1/2 => y^2>=1/4 >= 3 eta^2  (since eta^2<=1/4, 3 eta^2<=3/4... NOT <=1/4).")
print("  Hmm 3 eta^2 can be 3/4 > 1/4. Need a^2+y^2 >= 3 eta^2 <= 3/4. y>=1/2 gives y^2>=1/4.")
print("  So need a^2 >= 3 eta^2 - y^2.  Worst a=0, eta=1/2, y=1/2: 3/4-1/4=1/2>0 => FAILS at a=0!")
print("  => the per-MIRROR bound fails at the pole-touch. Must use BOTH mirrors / the")
print("     reference of the OTHER mirror, OR y>=sqrt(3)/2*... Let's find the real threshold.")
print()
# Find: for which y does per-zero net (summing both mirrors + both refs) stay >=0
# at the worst x (=gamma) for eta=1/2? Scan y down from 1/2.
print("Per-ZERO (both mirrors) net at x=gamma, eta=1/2, gamma=14.13, vs y:")
g=mp.mpf('14.1347251417'); e=mp.mpf('0.5')
for y in [mp.mpf(v) for v in [0.5,0.55,0.6,0.7,0.75,0.8,0.85,0.86,0.87,0.9,1.0]]:
    K=Kfull(g,y,e,g); R=Rref(g,y,g); net=R+K
    print(f"   y={float(y):>5.3f}  K={mp.nstr(K,5):>12}  R={mp.nstr(R,5):>10}  net={mp.nstr(net,5):>12}  >=0? {net>=0}")
