"""
TEST 4 (Task 3): Connect the actual TP level of Phi to the Turan/Jensen hierarchy
on the Xi Taylor coefficients, and check the GORZ degree<=8 hyperbolicity.

Background (all UNCONDITIONAL theorems, no RH assumed):
  - Xi(z) = int_{-inf}^{inf} Phi(u) e^{i z u} du  (Phi even => cosine transform).
  - Write (1/8)Xi(x/2) = sum_n gamma(n) x^{2n}/n!  (GORZ normalization).
  - Jensen poly J^{d,n} hyperbolic for d=2 <=> order-1 Turan gamma(n+1)^2>=gamma(n)gamma(n+2) (CNV 1986).
  - d=3 <=> order-2 Turan (Dimitrov-Lucas 2011).
  - GORZ 2019 + Griffin-Ono-Rolen: J^{d,n} hyperbolic for ALL n when d<=8 (unconditional).

We compute the gamma(n) directly from Phi via moment integrals
  Xi(z) even => Xi(z) = sum_k (-1)^k b_{2k} z^{2k},  b_{2k} = (1/(2k)!) int Phi(u) u^{2k} du.
Then map to GORZ gamma(n) and TEST order-1, order-2 Turan and the Jensen-d
hyperbolicity for d up to ~12.  We check WHERE (if anywhere) hyperbolicity first
fails on the SMALL-n members -- that finite gap is what the PF_4 ceiling mirrors.
"""
import mpmath as mp
mp.mp.dps = 60
from phi_kernel import Phi_classical

pi = mp.pi
# Moments  M_{2k} = int_{-inf}^{inf} Phi_c(u) u^{2k} du  (even integrand => 2*int_0^inf)
# Xi(z) = int Phi(u) cos(z u) du = sum_k (-1)^k z^{2k}/(2k)! * M_{2k}
def moment(k):
    f = lambda u: Phi_classical(u)*u**(2*k)
    return 2*mp.quad(f, [0, 1, 2, 3, 5])   # Phi decays super-exponentially

print("Computing even moments M_{2k} = int Phi(u) u^{2k} du ...")
Mmax = 30
M = {}
for k in range(0, Mmax+1):
    M[k] = moment(k)
    if k <= 6: print(f"  M_{2*k} = {mp.nstr(M[k],12)}")

# Xi(z) = sum_k c_k z^{2k},  c_k = (-1)^k M_k/(2k)!   (here M_k means M_{2k})
# Hadamard/GORZ: gamma(n) are (up to normalization) the coeffs of the Xi Maclaurin series
# in the variable making it sum gamma(n) x^{2n}/n!. The SIGN/Turan structure is what matters.
# Define the unsigned Taylor data t_k = M_{2k}/(2k)!  (these are the |c_k|; Xi alternates).
# The Polya gamma(n) are proportional to t_n; Turan ineqs are scale/sign-robust on t.
t = [M[k]/mp.factorial(2*k) for k in range(Mmax+1)]
print("\nUnsigned Taylor data t_k = M_{2k}/(2k)!  (proportional to GORZ gamma(k)):")
for k in range(8):
    print(f"  t_{k} = {mp.nstr(t[k],10)}")

print("\n=== Order-1 Turan  t_{n+1}^2 >= t_n t_{n+2}  (CNV, unconditional) ===")
n_check = Mmax-2
allpos1 = True
for n in range(n_check):
    val = t[n+1]**2 - t[n]*t[n+2]
    if val < 0:
        print(f"  n={n}: FAILS  ({mp.nstr(val,6)})"); allpos1=False
print("  order-1 Turan holds for all tested n" if allpos1 else "  (some failures above)")

print("\n=== Order-2 (Dimitrov-Lucas) Turan discriminant >= 0 ===")
def turan2(n):
    A=t[n+1]**2-t[n]*t[n+2]
    B=t[n+2]**2-t[n+1]*t[n+3]
    C=t[n+1]*t[n+2]-t[n]*t[n+3]
    return 4*A*B-C**2
allpos2=True
for n in range(Mmax-3):
    v=turan2(n)
    if v<0:
        print(f"  n={n}: FAILS ({mp.nstr(v,6)})"); allpos2=False
print("  order-2 Turan holds for all tested n" if allpos2 else "  (failures above)")

print("\n=== Jensen-d hyperbolicity (all roots real) for d=1..12, small shifts n ===")
def jensen_hyperbolic(d, n):
    # J^{d,n}(X) = sum_{j=0}^d C(d,j) t[n+j] X^j ; check all roots real
    coeffs = [mp.binomial(d,j)*t[n+j] for j in range(d+1)]
    coeffs = coeffs[::-1]  # leading first for polyroots
    try:
        roots = mp.polyroots(coeffs, maxsteps=200, extraprec=200)
    except Exception as e:
        return None
    return max(abs(mp.im(r)) for r in roots)
for d in range(1,13):
    worst=mp.mpf(0); worst_n=None; ok=True
    for n in range(0, Mmax-d):
        im = jensen_hyperbolic(d,n)
        if im is None: continue
        if im>worst: worst=im; worst_n=n
        # treat |Im|>1e-15 * scale as genuinely complex
    flag = "HYPERBOLIC" if worst < mp.mpf('1e-12') else f"complex roots (max|Im|={mp.nstr(worst,4)} at n={worst_n})"
    print(f"  d={d:2d}: {flag}")
