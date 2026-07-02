"""
top_edge_moment.py
==================
Quantify the OFF-LINE DAMAGE to the sign field G(x+iY) for a probe BELOW y=1/2,
i.e. 0 < Y < 1/2 (the HARD region). Test whether the displacement moment
Sum eta^2 << T/log T controls the damage in an AVERAGED or SPARSE-EXCEPTIONAL
sense, reaching genuinely below y=1/2.

The exact per-zero net (signed kernel, ScratchSignedKernelRegion) is
    mirrorNet(y,eta,a) = 2 y (a^2 + y^2 - eta^2) / [((y-eta)^2+a^2)((y+eta)^2+a^2)]
with a = gamma +/- x. Per-zero net = mirrorNet(y,eta,gamma+x)+mirrorNet(y,eta,gamma-x).

For a probe BELOW a zero (y < eta), the NEAR mirror (a = gamma - x ~ 0) goes NEGATIVE.
We compute:
  (A) integral over x of the near-mirror net  -- is the x-averaged damage finite/controlled?
  (B) the per-zero damage as a function of (eta - Y)  -- how it blows up at the pole.
  (C) the AGGREGATE damage over the off-line population using the moment bound.
"""
import mpmath as mp
import sympy as sp

mp.mp.dps = 40

def mirrorNet(y, eta, a):
    y, eta, a = mp.mpf(y), mp.mpf(eta), mp.mpf(a)
    num = 2*y*(a**2 + y**2 - eta**2)
    den = ((y-eta)**2 + a**2)*((y+eta)**2 + a**2)
    return num/den

# ----------------------------------------------------------------------
# (A) Integral over x (equivalently over the mirror ordinate a in R) of one
#     mirror net. Substitute a = gamma - x, so as x ranges over R, a ranges
#     over R. The x-average of the near mirror = integral over a of mirrorNet.
#     INT_{-inf}^{inf} mirrorNet(y,eta,a) da  -- does the negative pole-column
#     damage cancel against the positive wings when we integrate over x?
# ----------------------------------------------------------------------
print("="*70)
print("(A) x-integral of a single mirror net  INT mirrorNet(y,eta,a) da")
print("    (this is integral over horizontal probe position x)")
print("="*70)
a = sp.symbols('a', real=True)
ys, es = sp.symbols('y eta', positive=True)
expr = 2*ys*(a**2 + ys**2 - es**2)/(((ys-es)**2+a**2)*((ys+es)**2+a**2))
I = sp.integrate(expr, (a, -sp.oo, sp.oo))
I = sp.simplify(I)
print("symbolic INT over a (=over x):", I)

# numeric evaluation of the x-integral for both regimes
def x_integral(y, eta):
    f = lambda a: mirrorNet(y, eta, a)
    return mp.quad(f, [-mp.inf, 0, mp.inf])

print()
print("Numeric INT_x mirrorNet (per single mirror), various (y,eta):")
print("  regime y>eta (probe ABOVE zero, HELP) vs y<eta (probe BELOW, HURT)")
for (y,eta) in [(0.6,0.4),(0.55,0.45),(0.5,0.5),(0.4,0.5),(0.3,0.45),(0.1,0.45),(0.05,0.49),(0.49,0.5)]:
    val = x_integral(y, eta)
    regime = "ABOVE/help" if y>eta else ("BELOW/HURT" if y<eta else "edge")
    print(f"  y={y:.3f} eta={eta:.3f} [{regime:11s}]  INT_x net = {mp.nstr(val,8)}")

print()
print("="*70)
print("(A') The CLEAN closed form of INT_x mirrorNet (per mirror):")
print("     = 2*pi if y>|eta|,  = 0 if y<|eta|.  Step function in (y-|eta|).")
print("="*70)
# verify it equals pi*(1+sign(y-eta)) by residues. mirrorNet has poles in 'a'
# at a = +/- i(y-eta) and a = +/- i(y+eta). Closing in upper half a-plane:
# residue picks up poles with positive imag part: i(y+eta) always (eta,y>0),
# and i(y-eta) only if y>eta; if y<eta, i(y-eta) has NEGATIVE imag part.
# So the integral jumps by 2*pi exactly at y=eta.  This is a WINDING/RESIDUE fact.
for (y,eta) in [(0.6,0.4),(0.4,0.6),(0.49,0.5),(0.5,0.49)]:
    predicted = 2*mp.pi if y>eta else mp.mpf(0)
    actual = x_integral(y,eta)
    print(f"  y={y} eta={eta}: predicted={mp.nstr(predicted,6)} actual={mp.nstr(actual,6)} match={abs(predicted-actual)<1e-30}")

print()
print(">>> KEY: For a probe BELOW an off-line zero (y<eta), the x-AVERAGED")
print(">>> per-zero net is EXACTLY ZERO -- the pole-column damage cancels")
print(">>> the wings EXACTLY. The full mirror sum (gamma+x and gamma-x) is")
print(">>> 2x this. So INT_x [per-zero net] = 0 for EVERY below-zero zero.")

print()
print("="*70)
print("(B) The NEGATIVE PART of one below-zero mirror net, as fn of (eta,Y).")
print("    Near mirror a=gamma-x. net<0 exactly where a^2 < eta^2 - y^2,")
print("    i.e. |a| < sqrt(eta^2-Y^2) =: w(eta,Y). The DAMAGE WIDTH in x.")
print("="*70)
def damage_width(Y, eta):
    Y, eta = mp.mpf(Y), mp.mpf(eta)
    if eta <= Y: return mp.mpf(0)
    return mp.sqrt(eta**2 - Y**2)
def neg_mass(Y, eta):
    # L1 mass of negative part of single mirror net over a (= over x)
    w = damage_width(Y, eta)
    if w == 0: return mp.mpf(0)
    f = lambda a: -mirrorNet(Y, eta, a)  # positive where net<0
    return mp.quad(f, [-w, 0, w])
print(" Y      eta    damage-width w=sqrt(eta^2-Y^2)   L1 neg-mass")
for (Y,eta) in [(0.45,0.5),(0.4,0.5),(0.3,0.5),(0.1,0.5),(0.45,0.49),(0.49,0.5),(0.0,0.5)]:
    w = damage_width(Y,eta); nm = neg_mass(Y,eta)
    print(f" {Y:.3f}  {eta:.3f}   w={mp.nstr(w,6):10s}   negmass={mp.nstr(nm,6)}")

print()
print("="*70)
print("(C) SPARSE-EXCEPTIONAL: total x-measure of the damage set at height Y")
print("    Exceptional set E_Y(T) = union over off-line zeros with eta>Y,")
print("    gamma<=T, of x-interval [gamma-w, gamma+w], w=sqrt(eta^2-Y^2).")
print("    |E_Y(T)| <= Sum_{eta>Y} 2 w = 2 Sum_{eta>Y} sqrt(eta^2-Y^2).")
print("="*70)
print()
print("KEY BOUND: sqrt(eta^2-Y^2) <= sqrt(eta^2)/... no. But eta^2-Y^2 <= eta^2,")
print("so w <= eta. Thus |E_Y(T)| <= 2 Sum_{eta>Y} eta.")
print("Cauchy-Schwarz: Sum_{eta>Y} eta <= sqrt( N(eta>Y) * Sum eta^2 ).")
print()
print("Moment: Sum_{gamma<=T} eta^2 <= 64 T/log T   (banked).")
print("Count of eta>Y up to T: N(1/2+Y,T) <= 2 T^{1-Y/4} log T   (Selberg).")
print()
print("So |E_Y(T)| <= 2 sqrt( 2 T^{1-Y/4} log T * 64 T/log T )")
print("            = 2 sqrt(128) * T^{(1-Y/4)/2} * T^{1/2}")
print("            = 16*sqrt(2) * T^{1 - Y/8}.")
print()
# Tabulate the exceptional measure vs the available horizontal room (height window).
# The probes live on a horizontal line of length ~T (abscissas up to T).
# Exceptional FRACTION = |E_Y(T)| / T.
import math
def excep_measure_bound(Y, T):
    return 16*math.sqrt(2) * T**(1 - Y/8)
def excep_fraction(Y, T):
    return excep_measure_bound(Y,T)/T  # = 16 sqrt2 * T^{-Y/8}
print(" Y       T        |E_Y(T)| bound      fraction |E|/T")
for Y in [0.45, 0.4, 0.3, 0.2, 0.1, 0.05]:
    for T in [1e6, 1e12, 1e30]:
        print(f" {Y:.2f}  {T:.0e}   {excep_measure_bound(Y,T):.3e}     frac={excep_fraction(Y,T):.4e}")
    print()

print()
print("="*70)
print("(D) SHARPER: avoid Cauchy-Schwarz. For eta>Y use eta <= eta^2/Y.")
print("    |E_Y(T)| <= 2 Sum_{eta>Y} sqrt(eta^2-Y^2) <= 2 Sum_{eta>Y} eta")
print("             <= 2 Sum_{eta>Y} eta^2/Y <= (2/Y) Sum eta^2 <= 128 T/(Y log T).")
print("="*70)
def excep_moment(Y, T):
    return 128*T/(Y*math.log(T))
def frac_moment(Y, T):
    return excep_moment(Y,T)/T  # = 128/(Y log T)
print(" Y      T        |E_Y(T)| (moment)    fraction |E|/T = 128/(Y logT)")
for Y in [0.45,0.4,0.3,0.2,0.1,0.05]:
    for T in [1e6,1e12,1e30,1e100]:
        print(f" {Y:.2f}  {T:.0e}  {excep_moment(Y,T):.3e}   frac={frac_moment(Y,T):.4e}")
    print()
print(">>> fraction = 128/(Y log T) -> 0 as T->inf, for EACH FIXED Y in (0,1/2)!")
print(">>> This is NONVACUOUS: the exceptional fraction vanishes as T grows.")

print()
print("="*70)
print("(E) HONEST crossover: fraction 128/(Y logT) < 1  <=>  logT > 128/Y")
print("    <=>  T > exp(128/Y).  Below this the statement is VACUOUS (frac>1).")
print("="*70)
for Y in [0.45,0.4,0.3,0.2,0.1,0.05]:
    log10Tcross = (128/Y)/math.log(10)
    print(f"  Y={Y:.2f}: crossover T > exp({128/Y:.0f}) ~ 10^{log10Tcross:.0f}")
print()
print(">>> The crossover heights are ASTRONOMICAL (10^123 ... 10^1112).")
print(">>> Far beyond any verified zero (T~3e12). So as a CONCRETE statement")
print(">>> it is vacuous in the verifiable range; it is only an ASYMPTOTIC")
print(">>> density-zero statement. HONEST: nonvacuous in the limit, vacuous")
print(">>> at every finite verifiable height.")
print()
print("="*70)
print("(F) Does it REACH below y=1/2? YES in principle (any fixed Y<1/2),")
print("    but the constant 128/Y means smaller Y needs even larger T.")
print("    The statement: for each Y in (0,1/2), the set of abscissas x where")
print("    G(x+iY)<0 has UPPER DENSITY <= limsup 128/(Y logT) = 0.")
print("    i.e. G(x+iY) >= 0 for ALMOST EVERY x (density 1), each fixed Y<1/2.")
print("="*70)

print()
print("="*70)
print("SUMMARY OF BANKABLE FACTS for ScratchTopEdgeMoment.lean")
print("="*70)
print("""
F1 (exact damage geometry): single mirror net(Y,eta,a)<0  iff  a^2 < eta^2-Y^2.
   => below-zero damage in x confined to |x-gamma| < w := sqrt(eta^2-Y^2).
F2 (per-zero exceptional width): w(eta,Y) = sqrt(eta^2-Y^2) <= eta (since Y>=0)
   and w<=eta^2/Y  for eta>Y (since eta>Y => eta <= eta^2/Y).  [the key key]
F3 (exceptional measure, layer-cake via MOMENT, no count, no Cauchy-Schwarz):
   |E_Y(T)| <= 2 Sum_{eta>Y, gamma<=T} w(eta,Y)
            <= 2 Sum_{eta>Y} eta^2/Y
            <= (2/Y) Sum_{gamma<=T} eta^2
            <= (2/Y) * 64 T/log T  = 128 T /(Y log T).
F4 (density / nonvacuity): exceptional FRACTION |E_Y(T)|/T <= 128/(Y log T) -> 0.
   => For each fixed Y in (0,1/2): upper density of {x: G(x+iY)<0} is 0.
      G(x+iY) >= 0 for a density-1 set of abscissae x.  REACHES BELOW y=1/2.
F5 (honest crossover/triviality): frac<1 only for T>exp(128/Y) (10^124..10^1112).
   Vacuous at every verifiable height; nonvacuous only asymptotically.
   Genuinely nontrivial AS A LIMIT statement (density 0), trivial as concrete.
""")
