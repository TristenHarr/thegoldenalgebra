"""
poisson_defect.py — what x-Poisson-smoothing ACTUALLY does to the defect, honestly.

Per-mirror m(Y,eta,a), a=gamma-x, decomposes (partial fractions in a^2) into pole
kernels. The near mirror's NEGATIVE part comes from the pole pair at height eta
(ABOVE the probe when eta>Y). x-smoothing by P_h moves |Y-eta| -> |Y-eta|+h but
keeps the NEGATIVE sign while eta>Y. So:
  - x-smoothing does NOT lift past the zero; it cannot reach the unconditional region.
  - It DOES widen/dilute the negative kernel. Compute the smoothed negative defect.

We compute the smoothed per-mirror field directly and its negative-part L1 mass vs h,
to see whether ANY finite-energy x-average gives a clean reasonable constant.
Also test a COMPACT test function phi (not Poisson) for the weighted average.
"""
import mpmath as mp
mp.mp.dps = 30

def m(Y, eta, a):
    Y, eta, a = mp.mpf(Y), mp.mpf(eta), mp.mpf(a)
    num = 2*Y*(a**2 + Y**2 - eta**2)
    den = ((Y-eta)**2 + a**2)*((Y+eta)**2 + a**2)
    return num/den

def P_h(h,x):
    h,x=mp.mpf(h),mp.mpf(x)
    return (1/mp.pi)*h/(x**2+h**2)

# smoothed near-mirror at probe abscissa offset s = x0 - gamma (set gamma=0)
def smoothed_m(Y,eta,h,s):
    f=lambda x: m(Y,eta, -x)   # a = gamma - x = -x  (gamma=0)
    return mp.quad(lambda x: P_h(h,s-x)*f(x), [-mp.inf, 0, mp.inf])

print("="*72)
print("x-Poisson-smoothed near-mirror m(Y=0.1,eta=0.49): does smoothing kill <0?")
print("="*72)
Y,eta=0.1,0.49
for h in [0.0,0.05,0.1,0.2,0.4]:
    # min over s of the smoothed field (most negative)
    if h==0:
        vals=[m(Y,eta,-s) for s in mp.linspace(-1,1,400)]
    else:
        vals=[smoothed_m(Y,eta,h,s) for s in mp.linspace(-1,1,80)]
    mn=min(vals)
    print(f"  h={h:.2f}: min smoothed near-mirror = {mp.nstr(mn,6)}  (still <0: {mn<0})")
print()
print(">>> x-smoothing dilutes but NEVER removes the negative part (eta>Y stays above")
print(">>> the probe). The defect is INTRINSIC to the height Y; only VERTICAL lift")
print(">>> past 1/2 removes it. This is a structural CERTIFICATE, not a constant.")
print()

print("="*72)
print("WEIGHTED AVERAGE  int G(x+iY) phi(x) dx  -- can a clever phi give >= -small?")
print("="*72)
print("Per mirror int m * phi. Unweighted (phi=1): exactly 0. For phi a Poisson bump")
print("P_h centered at the zero abscissa, int m(Y,eta,gamma-x) P_h(x-gamma) dx =")
print("smoothed_m at s=0 (right under the zero) = MOST negative point. So weighting")
print("TOWARD the zero MAXIMIZES the negativity. Weighting AWAY picks up positive wings.")
for h in [0.05,0.1,0.2,0.5,1.0]:
    under = smoothed_m(Y,eta,h,0.0)
    print(f"  phi=P_{h} centered under zero: int m phi = {mp.nstr(under,6)} (<0 -- detects the zero!)")
print()
print(">>> A weight CONCENTRATED at the zero gives a NEGATIVE weighted average -- it")
print(">>> DETECTS the off-line zero (good for Task 5 detection!) but is the OPPOSITE")
print(">>> of a clean '>= -small': the weighted average is as negative as ~ -O(1).")
print(">>> A spread-out weight returns toward 0. There is NO phi giving a clean")
print(">>> sign-definite >=0 at height Y<1/2 with a reasonable constant, BECAUSE the")
print(">>> total mass is 0 and the negative part is genuine O(1)-per-zero.")
