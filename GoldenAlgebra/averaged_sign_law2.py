"""
averaged_sign_law2.py
=====================
The negative-part integral N(Y,eta) is O(1) per zero (NOT O(eta^2)). Investigate:
  - its exact limits (eta->Y+, eta->1/2),
  - whether Sum_{eta>Y} N is controllable by COUNT (not moment),
  - the resulting averaged sign-defect constant and crossover.

ALSO: the SMARTER AVERAGING ideas.
  (a) the unweighted x-average of m is 0 (pole cancels wings exactly) -- so int G dx
      is controlled but not sign-definite. The negative PART has O(1) mass per zero.
  (b) A POISSON average in x at height h: P_h * G = G(x + i(Y+h)) -- raising the probe!
      This is the KEY: smoothing G(.+iY) by a Poisson kernel of width h is EXACTLY
      evaluating the harmonic field higher up, at Y+h. If Y+h >= 1/2 we are back in the
      UNCONDITIONAL region where G>=0 with NO exceptional set. Quantify the defect for
      Y+h < 1/2.
"""
import mpmath as mp
mp.mp.dps = 40

def m(Y, eta, a):
    Y, eta, a = mp.mpf(Y), mp.mpf(eta), mp.mpf(a)
    num = 2*Y*(a**2 + Y**2 - eta**2)
    den = ((Y-eta)**2 + a**2)*((Y+eta)**2 + a**2)
    return num/den

def negmass(Y, eta):
    Y, eta = mp.mpf(Y), mp.mpf(eta)
    if eta <= Y: return mp.mpf(0)
    w = mp.sqrt(eta**2 - Y**2)
    # closed form
    return -2*mp.atan(w/(2*Y)) + 2*mp.atan((Y**2+eta**2)/(Y*w))

print("="*72)
print("N(Y,eta) is O(1) per below-zero zero -- the LIMITS")
print("="*72)
print(" eta->Y+ : second atan -> atan(+inf)=pi/2, first->atan(0)=0, so N->pi.")
print(" Each below-Y zero contributes up to ~pi of negative-part mass. Check:")
for Y in [0.45, 0.25, 0.1]:
    for eta in [Y+1e-6, Y+1e-4, Y+0.001, Y+0.01, 0.499]:
        if eta<=0.5:
            print(f"   Y={Y:.2f} eta={float(eta):.6f}  N={mp.nstr(negmass(Y,eta),6)}  (pi={mp.nstr(mp.pi,6)})")
    print()

print("="*72)
print("CONSEQUENCE: int (G(.+iY))_- dx <= Sum_{eta>Y,gamma<=T} N(Y,eta) <= pi * N_off(Y,T)")
print("  where N_off(Y,T) = #{off-line zeros with eta>Y, gamma<=T} is a COUNT.")
print("  Selberg count: N_off(Y,T) <= 2 T^{1-Y/4} log T -- a POSITIVE POWER of T.")
print("  So int(G)_- dx <= 2 pi T^{1-Y/4} log T. This is SUBLINEAR in T (exponent")
print("  1-Y/4 < 1), so the AVERAGE defect per unit length -> 0 like T^{-Y/4} log T.")
print("="*72)
import math
def defect_density(Y,T):
    # (1/T) int (G)_- dx  <= 2 pi T^{-Y/4} log T
    return 2*math.pi * T**(-Y/4) * math.log(T)
print(" Y      T          avg negative-part density (1/T)int(G)_- <= 2pi T^{-Y/4}logT")
for Y in [0.45,0.25,0.1,0.05]:
    for T in [1e3,1e6,1e12,1e30]:
        print(f"  {Y:.2f}  {T:.0e}    {defect_density(Y,T):.4e}")
    print()
print(">>> crossover density<1: 2pi T^{-Y/4} logT < 1.")
for Y in [0.45,0.25,0.1,0.05]:
    # solve T^{-Y/4} logT = 1/(2pi); approx
    # try
    Tc=None
    t=10
    while t<1e400:
        if 2*math.pi*t**(-Y/4)*math.log(t) < 1:
            Tc=t; break
        t*=10
    print(f"  Y={Y:.2f}: density<1 near T ~ {Tc:.0e}  (log10 ~ {math.log10(Tc):.0f})")
