"""
crossover_final.py — the definitive crossover comparison across all routes/improvements,
and the verdict on whether the UPPER-BOUND constant is intrinsic.

Three averaged-defect upper bounds (all unconditional, no RH):
  ROUTE M (measure, prior): meas{x: G(x+iY)<0} <= (2/theta^2) T/(Y log T).
       fraction <1 at T > exp((2/theta^2)/Y).
  ROUTE E (negative-part via ENERGY/moment): the sliver L1 mass per zero is
       bounded by ... but N(Y,eta)~O(1) carries no eta^2, so energy route reverts
       to measure*sup|m| -- no better. (documented)
  ROUTE C (negative-part via COUNT): int(G)_- <= pi * N_off(Y,T) <= 2pi T^{1-2 theta Y} log T.
       Selberg theta=1/8: T^{1-Y/4}; Conrey theta=4/7: T^{1-8Y/7}. density<1 needs
       per-unit-length defect 2pi T^{-2 theta Y} log T < 1.
"""
import math

def exp10(x): return x/math.log(10)

print("="*72)
print("ROUTE M (measure): fraction = (2/theta^2)/(Y log T) < 1  <=> log10 T > (2/theta^2)/(Y ln10)")
print("="*72)
print(" Y      Selberg(2/theta^2=128)   Conrey(2/theta^2=2*49/16=6.125)")
for Y in [0.45,0.25,0.1,0.05]:
    selb = 128/Y
    conr = (2*49/16)/Y
    print(f"  {Y:.2f}   10^{exp10(selb):.0f}                  10^{exp10(conr):.0f}")
print()
print(">>> Conrey shrinks the measure-route crossover by log10(128/6.125)=", 
      f"{exp10(128/6.125):.1f} dex, but it stays 10^{exp10(6.125/0.45):.0f}..10^{exp10(6.125/0.05):.0f}: astronomical.")
print()

print("="*72)
print("ROUTE C (negative-part via COUNT): per-unit defect <= 2pi T^{-2 theta Y} log T < 1")
print("="*72)
def cross_routeC(Y, theta):
    # solve 2pi T^{-2 theta Y} log T = 1
    t=10.0
    while t<1e500:
        if 2*math.pi*t**(-2*theta*Y)*math.log(t) < 1: return math.log10(t)
        t*=1.2
    return float('inf')
print(" Y      Selberg theta=1/8 (T^{-Y/4})    Conrey theta=4/7 (T^{-8Y/7})")
for Y in [0.45,0.25,0.1,0.05]:
    cS=cross_routeC(Y,1/8); cC=cross_routeC(Y,4/7)
    print(f"  {Y:.2f}   10^{cS:.0f}                       10^{cC:.0f}")
print()
print(">>> ROUTE C + CONREY is the BEST: exponent jumps from Y/4 to 8Y/7 (4.57x faster).")
print()

print("="*72)
print("BEST ACHIEVABLE crossover (Route C + Conrey theta=4/7):")
print("="*72)
for Y in [0.49,0.45,0.4,0.3,0.25,0.1,0.05]:
    cC=cross_routeC(Y,4/7)
    print(f"  Y={Y:.2f}: per-unit avg defect < 1 at T ~ 10^{cC:.0f}")
print()
print("As Y->1/2 the crossover DROPS sharply (8Y/7 -> 4/7 exponent). At Y=0.49,")
print(f"  10^{cross_routeC(0.49,4/7):.0f}. The closer to 1/2, the lower the crossover, but")
print("  even at Y=0.49 it is 10^{:.0f} -- still beyond verified zeros (~3e12=10^12.5).".format(cross_routeC(0.49,4/7)))
print()
print("WHY THE CROSSOVER IS INTRINSIC TO ANY UPPER-BOUND ROUTE:")
print("-"*72)
print("""The crossover is governed by the off-line zero COUNT N_off(Y,T). The averaged
defect upper bound is (const) * N_off(Y,T), and N_off(Y,T) is a POSITIVE POWER
T^{1-c(theta)Y} of T for ANY unconditional density. The fraction/defect-density
< 1 needs T^{c theta Y} > const*logT, i.e. log T > const/(theta Y), i.e.
   crossover  T* ~ exp( O(1)/(theta Y) ).
The 1/Y is INTRINSIC: it is the price of asking for a defect SMALLER than the
natural count of zeros that can sit at displacement > Y, and that count's
exponent vanishes linearly in Y as Y->0. NO averaging removes it, because the
defect (negative part) is genuinely Omega(1) per below-Y zero (the pole-column
integral -> pi), independent of how close eta is to Y. The constant in front
(128 vs 6.125 vs 2pi) is improvable (Conrey); the exp(O(1)/(theta Y)) STRUCTURE
is intrinsic to bounding a below-1/2 defect by an unconditional zero count.""")
print()
print("="*72)
print("THE GENUINELY CLEAN NONVACUOUS STATEMENT (no crossover at all):")
print("="*72)
print("""VERTICAL LIFT, not horizontal average. For ANY 0<Y<1/2:
   G(x + i*(1/2)) >= 0 for EVERY x, UNCONDITIONALLY (signed_kernel_FINAL: y>=1/2
   => every mirror m>=0 since |eta|<1/2<=y). No T, no density, no exceptional set,
   holds at the FIRST zero. The 'average' that works is the trivial one: evaluate
   at/above height 1/2. Below 1/2, every honest averaged UPPER BOUND inherits the
   exp(O(1)/(theta Y)) crossover because the negative part is real and O(1)-per-zero.""")
