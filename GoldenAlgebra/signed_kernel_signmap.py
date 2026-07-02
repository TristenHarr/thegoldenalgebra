#!/usr/bin/env python3
"""
signed_kernel_signmap.py — STEP 2/3/4: the HELP/HURT sign map off-axis, the
off-axis pole structure, the per-zero net (reference reservoir vs kernel), and
the HONEST triviality test (does net-positivity reach NEAR the zeros?).

KEY STRUCTURE (proven symbolically in signed_kernel_offaxis.py):
  K_z(eta,gamma) = k(eta, gamma+x) + k(eta, gamma-x),
      k(eta,a) = 2 eta^2 y (y^2 - 3 a^2 - eta^2)
                 / [ (a^2+y^2) ((eta-y)^2+a^2) ((eta+y)^2+a^2) ].
  sign k(eta,a) = sign(y^2 - 3 a^2 - eta^2).
  So a mirror at effective ordinate a HELPS (k>0) iff a < a* := sqrt((y^2-eta^2)/3),
  HURTS (k<0) iff a > a*.

  THE OFF-AXIS POLE: k(eta,a) blows up where (eta±y)^2 + a^2 -> 0, i.e.
  a -> 0 and y -> ±eta. With a = gamma - x, a=0 means x = gamma: the probe abscissa
  sits UNDER the zero ordinate gamma, and y near eta (the zero's tiny imaginary
  displacement in pullback coords). That is the HURT pole.

  THE ON-LINE REFERENCE RESERVOIR off-axis: every zero ALSO carries the +2y/(y^2+a^2)
  reference per mirror (the -2 K_g term). Summed over both mirrors:
      R(x,y,gamma) = 2y/(y^2+(gamma+x)^2) + 2y/(y^2+(gamma-x)^2).
  This is what protects G>=0; the question is whether K can overcome it off-axis.
"""
import mpmath as mp
mp.mp.dps = 30

# ---- exact mirror kernel and reference (match the symbolic forms) ----------
def kmirror(y, e, a):
    y,e,a = mp.mpf(y),mp.mpf(e),mp.mpf(a)
    num = 2*e**2*y*(y**2 - 3*a**2 - e**2)
    den = (a**2+y**2)*((e-y)**2+a**2)*((e+y)**2+a**2)
    return num/den

def Kfull(x, y, e, g):
    return kmirror(y,e,g+x) + kmirror(y,e,g-x)

def Rref(x, y, g):
    x,y,g = mp.mpf(x),mp.mpf(y),mp.mpf(g)
    return 2*y/(y**2+(g+x)**2) + 2*y/(y**2+(g-x)**2)

# ---------------------------------------------------------------------------
print("="*78)
print("STEP 2: HELP / HURT sign map of a SINGLE mirror at effective ordinate a")
print("="*78)
print("sign k(eta,a) = sign(y^2 - 3 a^2 - eta^2);  a* = sqrt((y^2-eta^2)/3).")
print("Mirror HELPS (k>0) iff a < a*,  HURTS (k<0) iff a > a*.")
print()
print("For the full off-axis kernel K = k(eta,g+x) + k(eta,g-x):")
print("  the NEAR mirror a_-=|g-x| can be made SMALL by taking x near g (probe under")
print("  the zero). Small a_- => a_-<a* => that mirror HELPS *if* y>eta... but a_- small")
print("  also drives the POLE. The FAR mirror a_+=g+x is large => HURTS (k<0) for high g.")
print()

# Numerically: for a single zero at gamma, sweep x and see where K flips sign,
# and compare |K| (what prior agent bounded) vs signed K.
g0 = mp.mpf('14.1347251417')   # gamma_1, the LOWEST zero (closest to real axis)
print(f"Probe a single zero at gamma={float(g0):.4f}, eta=0.25 (a hypothetical off-line zero).")
print(f"{'x':>8} {'y':>6} {'a_-=|g-x|':>10} {'a_+':>8} {'k(g-x)':>14} {'k(g+x)':>14} {'K':>14} {'R':>12} {'R+K':>14} {'net>=0':>7}")
e0 = mp.mpf('0.25')
worst = None
for x0 in [0, 5, 10, 13, 14, 14.13, 15, 20, 28]:
    for y0 in [1, 5, 14, 14.13, 20]:
        am = abs(g0 - x0); ap = g0 + x0
        km = kmirror(y0,e0,g0-x0); kp = kmirror(y0,e0,g0+x0)
        K = km+kp; R = Rref(x0,y0,g0); net = R+K
        if worst is None or net < worst[0]:
            worst = (net, x0, y0)
        print(f"{float(x0):>8.2f} {float(y0):>6.1f} {float(am):>10.3f} {float(ap):>8.2f} "
              f"{mp.nstr(km,4):>14} {mp.nstr(kp,4):>14} {mp.nstr(K,4):>14} "
              f"{mp.nstr(R,4):>12} {mp.nstr(net,4):>14} {str(net>=0):>7}")
print()
print(f"WORST per-zero net (R+K) over this scan: {mp.nstr(worst[0],5)} at x={worst[1]}, y={worst[2]}")
print()

# ---------------------------------------------------------------------------
print("="*78)
print("STEP 4 (HONESTY): does net-positivity hold when the probe is NEAR the zero?")
print("="*78)
print("The HURT pole is at a_-=|g-x|->0 (x->gamma) with y->eta. Probe THERE.")
print("The TRUE singular structure: the off-line zero w=gamma+i*eta is a pole of")
print("the field. Approaching it, K = -Im D_quad = -Im[1/(z-w)+...] and 1/(z-w)")
print("near w=gamma+i*eta: z=x+iy, z-w=(x-gamma)+i(y-eta). Im 1/(z-w)=-(y-eta)/|z-w|^2.")
print("So K's singular part = +(y-eta)/|z-w|^2:  POSITIVE for y>eta (probe ABOVE zero,")
print("HELP -> K->+inf), NEGATIVE for y<eta (probe BELOW zero, HURT -> K->-inf).")
print()
print("THE GENUINE HURT REGION: probe slightly BELOW an off-line zero (y<eta, x~gamma).")
print(f"{'x':>10} {'y':>7} {'a_-':>8} {'|z-w|':>9} {'K':>14} {'R':>11} {'R+K':>14} {'net>=0':>7}")
for (x0,y0) in [(g0, 0.24), (g0, 0.20), (g0, 0.10),
                (g0-0.01, 0.24), (g0-0.05, 0.20), (g0-0.1, 0.10),
                (g0, 0.26), (g0, 0.30), (g0, 0.5), (g0, 1.0)]:
    am = abs(g0-x0)
    zmw = mp.sqrt((x0-g0)**2 + (y0-e0)**2)
    K = Kfull(x0,y0,e0,g0); R = Rref(x0,y0,g0); net=R+K
    print(f"  x={float(x0):>8.4f} y={float(y0):>6.3f} a_-={float(am):>7.4f} "
          f"|z-w|={float(zmw):>7.4f} K={mp.nstr(K,4):>12} R={mp.nstr(R,4):>10} "
          f"R+K={mp.nstr(net,4):>12} {str(net>=0):>7}")
print()
print("READING: when x->gamma (probe abscissa under the zero) and y~eta, the NEAR")
print("mirror's pole dominates. Sign of the pole term decides HELP vs HURT there.")
