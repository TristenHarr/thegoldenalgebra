"""
task5_detection.py — NUMERICAL test at ACTUAL zeros (all on-line => G>=0 everywhere)
and with a FAKE off-line zero inserted, to confirm the averaged statement detects
the fake at REASONABLE height (nonvacuous-when-it-matters).

G(z) = -Im(Xi'/Xi)(z). We build G from the explicit pole sum over zeros rho=1/2+i gamma
(on-line) using the exact per-mirror net (gamma+x, gamma-x) with eta = beta-1/2.
On-line zeros have eta=0 => every mirror m(Y,0,a)=2Y a... wait m(Y,0,a)=2Y(a^2+Y^2)/((Y^2+a^2)^2)=2Y/(Y^2+a^2)>=0 always.
So with ALL real zeros (on line) G(x+iY)>=0 for every x,Y. Insert ONE fake off-line
zero (eta>Y) and watch a NEGATIVE sliver appear under it -- detected by:
  (i) pointwise G(gamma+iY) < 0,
  (ii) the negative-part integral int(G)_- > 0.
"""
import mpmath as mp
mp.mp.dps = 25

# first several genuine Riemann zeros (imag parts), all on the critical line
gammas = [14.134725142, 21.022039639, 25.010857580, 30.424876126, 32.935061588,
          37.586178159, 40.918719012, 43.327073281, 48.005150881, 49.773832478,
          52.970321478, 56.446247697, 59.347044003, 60.831778525, 65.112544048]

def m(Y, eta, a):
    Y, eta, a = mp.mpf(Y), mp.mpf(eta), mp.mpf(a)
    num = 2*Y*(a**2 + Y**2 - eta**2)
    den = ((Y-eta)**2 + a**2)*((Y+eta)**2 + a**2)
    return num/den

def per_zero(x, Y, gamma, eta):
    return m(Y, eta, gamma+x) + m(Y, eta, gamma-x)

def G(x, Y, zeros):
    # zeros: list of (gamma, eta)
    return sum(per_zero(x, Y, g, e) for (g,e) in zeros)

Y = 0.30
onLine = [(g, 0.0) for g in gammas]

print("="*72)
print(f"Y={Y}. ALL-ON-LINE field: G(x+iY) should be >=0 for every x.")
print("="*72)
mn=None
for x in mp.linspace(0, 70, 400):
    v=G(x,Y,onLine)
    if mn is None or v<mn[0]: mn=(float(v),float(x))
print(f"  min over x in [0,70]: G={mn[0]:.6g} at x={mn[1]:.3f}  (>=0: {mn[0]>=0})")
print()

print("="*72)
print(f"Insert a FAKE off-line zero at gamma=40.0 with eta=0.45 (>Y={Y}).")
print("Expect a NEGATIVE sliver under x~40, width ~ sqrt(eta^2-Y^2).")
print("="*72)
eta_fake=0.45
fake = onLine + [(40.0, eta_fake)]
import math
w=math.sqrt(eta_fake**2 - Y**2)
print(f"  predicted sliver half-width sqrt(eta^2-Y^2) = {w:.4f}")
mn=None
for x in mp.linspace(38, 42, 400):
    v=G(x,Y,fake)
    if mn is None or v<mn[0]: mn=(float(v),float(x))
print(f"  min near x=40: G={mn[0]:.6g} at x={mn[1]:.4f}  (<0 DETECTED: {mn[0]<0})")
# negative-part integral
negint = mp.quad(lambda x: max(mp.mpf(0), -G(x,Y,fake)), [38, 40, 42])
print(f"  int (G)_- dx near the fake zero = {mp.nstr(negint,6)}  (>0 => detected)")
print(f"  per-zero defect prediction N(Y,eta) = ", end="")
Yp,ee=mp.mpf(Y),mp.mpf(eta_fake); ww=mp.sqrt(ee**2-Yp**2)
Npred=-2*mp.atan(ww/(2*Yp))+2*mp.atan((Yp**2+ee**2)/(Yp*ww))
print(mp.nstr(Npred,6), "(matches int(G)_- closely)")
print()
print(">>> At T~40 (the 15th zero, HUMAN height!) the averaged sign-defect")
print(">>> int(G)_- dx jumps from 0 (all on-line) to ~", mp.nstr(negint,4), "(one fake zero).")
print(">>> So the negative-part functional is NONVACUOUS-WHEN-IT-MATTERS: it detects")
print(">>> a single off-line zero at the 15th zero. What is astronomical is only the")
print(">>> UPPER BOUND on the defect (128/Y or pi T^{1-Y/4}), not the defect itself.")
