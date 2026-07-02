"""
averaged_sign_law.py
====================
SERIOUS investigation: can the averaged anti-Herglotz sign law be made
NONVACUOUS at human-computable heights, or is the 128/Y constant intrinsic?

Per-mirror net (signed kernel, exact):
   m(Y,eta,a) = 2 Y (a^2 + Y^2 - eta^2) / [((Y-eta)^2+a^2)((Y+eta)^2+a^2)],   a=gamma-x.

Probe BELOW an off-line zero (eta>Y): near mirror goes NEGATIVE on |a|<w, w=sqrt(eta^2-Y^2).

TASK 1: trace the constant 128/Y factor by factor.
TASK 4: bound the NEGATIVE-PART integral  int (G(x+iY))_-  dx  -- a genuine
        averaged sign-defect bound -- and compute ITS constant.
"""
import mpmath as mp
import sympy as sp
mp.mp.dps = 40

def m(Y, eta, a):
    Y, eta, a = mp.mpf(Y), mp.mpf(eta), mp.mpf(a)
    num = 2*Y*(a**2 + Y**2 - eta**2)
    den = ((Y-eta)**2 + a**2)*((Y+eta)**2 + a**2)
    return num/den

print("="*72)
print("TASK 1 — TRACE THE CONSTANT 128/Y")
print("="*72)
print("""
The chain in ScratchTopEdgeMoment:
  |E_Y(T)|  <= 2 * Sum_{eta>Y,gamma<=T} w(eta,Y)      [sliver: net<0 on |a|<w]
            <= 2 * Sum eta              [F2a: w=sqrt(eta^2-Y^2) <= eta]
            <= (2/Y) * Sum eta^2        [F2b: eta <= eta^2/Y  since eta>Y]
            <= (2/Y) * (64 T/log T)     [Selberg moment envelope]
            =  128 T/(Y log T).

FACTORS:
  * 64   : the Selberg moment envelope const 1/theta^2 at theta=1/8.
           => Conrey theta=4/7 replaces 64 -> 49/16 = 3.0625.  (20.9x)
  * 2    : the SLIVER counts BOTH sides |a|<w  (full width 2w). INTRINSIC geometry.
  * 1/Y  : TWO compounding sources of 1/Y, see below. The KILLER factor.
""")

print("-"*72)
print("  1/Y source A: F2b  eta <= eta^2/Y   (converting WIDTH to ENERGY).")
print("  This is the lossy step. w = sqrt(eta^2-Y^2) is the TRUE width, but it is")
print("  bounded by eta (drop Y^2), then eta by eta^2/Y. Quantify the loss:")
print()
print("   Y      eta     true w        eta(F2a)    eta^2/Y(F2b)   loss ratio (eta^2/Y)/w")
for Y in [0.45, 0.25, 0.1, 0.05]:
    for eta in [0.49, 0.499]:
        if eta>Y:
            w = mp.sqrt(eta**2-Y**2)
            print(f"  {Y:.3f}  {eta:.4f}  {mp.nstr(w,6):>10}   {eta:.4f}     {mp.nstr(eta**2/Y,6):>10}     {mp.nstr((eta**2/Y)/w,5)}")
print()
print("  => F2b alone inflates by eta/Y (up to ~10x at Y=.05). Plus dropping Y^2 in F2a.")
print("  The width-to-energy conversion is what FORCES the 1/Y. It is needed ONLY")
print("  because we feed the SECOND moment Sum eta^2. If we had a FIRST-moment")
print("  density bound Sum_{eta>Y} eta or a COUNT, we would avoid 1/Y -- but those")
print("  are not T/log T summable (the count Sum 1 ~ T^{1-Y/4} is a positive power).")
print()

print("="*72)
print("TASK 4 — THE NEGATIVE-PART INTEGRAL  int (G)_-  dx  (genuine sign-defect)")
print("="*72)
print("""
Per mirror, the negative-part L1 mass is
   N(Y,eta) = int_{|a|<w} (-m(Y,eta,a)) da    (m<0 exactly there).
Closed form (sympy) below. KEY: N(Y,eta) is the EXACT averaged sign-defect of one
below-zero zero. Summed over the off-line population it gives  int (G)_- dx  <=
Sum_{eta>Y} N(Y,eta), a CLEAN averaged statement (no density-1 hand-waving).
""")
a = sp.symbols('a', real=True)
Ys, es = sp.symbols('Y eta', positive=True)
mexpr = 2*Ys*(a**2 + Ys**2 - es**2)/(((Ys-es)**2+a**2)*((Ys+es)**2+a**2))
w = sp.sqrt(es**2 - Ys**2)
# integrate -m over [-w, w]
Nint = sp.integrate(-mexpr, (a, -w, w))
Nint = sp.simplify(Nint)
print("Closed form  N(Y,eta) = int_{-w}^{w} (-m) da  =")
sp.pprint(Nint)
print()

# numeric: how big is N(Y,eta) vs eta^2?  Is it O(eta^2)? O(eta^3)? smaller?
def negmass(Y, eta):
    Y, eta = mp.mpf(Y), mp.mpf(eta)
    if eta <= Y: return mp.mpf(0)
    w = mp.sqrt(eta**2 - Y**2)
    f = lambda aa: -m(Y, eta, aa)
    return mp.quad(f, [-w, 0, w])

print(" Y      eta     negmass N      N/eta^2     N/eta^3     N/(eta^2-Y^2)^{3/2}")
for Y in [0.45, 0.25, 0.1, 0.05]:
    for eta in [0.49, 0.499]:
        if eta>Y:
            N = negmass(Y,eta)
            e=mp.mpf(eta); Yv=mp.mpf(Y)
            print(f"  {Y:.3f}  {eta:.4f}  {mp.nstr(N,6):>10}  {mp.nstr(N/e**2,5):>9}  {mp.nstr(N/e**3,5):>9}  {mp.nstr(N/(e**2-Yv**2)**mp.mpf('1.5'),5)}")
print()
print(">>> Watch the scaling of N(Y,eta) -- if N <= C * eta^2 with REASONABLE C")
print(">>> (no 1/Y blowup) then int(G)_- dx <= C * Sum eta^2 <= C*(1/theta^2) T/log T,")
print(">>> a clean averaged sign-defect with NO 1/Y -- potentially nonvacuous!")
