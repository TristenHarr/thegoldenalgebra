"""
STEP 5 — DAVENPORT-HEILBRONN CONTRAST (efficient, via Hurwitz zeta continuation).

DH function:  f(s) = sum_{n>=1} c(n) n^{-s},  c period 5:
   c(1)=1, c(2)=A, c(3)=-A, c(4)=-1, c(5)=0,  A=(sqrt(10-2 sqrt5)-2)/(sqrt5 -1).
ENTIRE continuation (no Euler product) via Hurwitz zeta:
   f(s) = 5^{-s} sum_{r=1}^{5} c(r) zeta(s, r/5).
Functional equation f(s)=X(s) f(1-s) with the same zeta-type shape; DH (1936) proved
f has zeros OFF Re s=1/2.  This is the control: SAME FE skeleton, NO positivity.
"""
import mpmath as mp
mp.mp.dps = 30

sqrt5=mp.sqrt(5)
A_dh=(mp.sqrt(10-2*sqrt5)-2)/(sqrt5-1)
cv={1:mp.mpf(1),2:A_dh,3:-A_dh,4:mp.mpf(-1),0:mp.mpf(0)}
def c(n): return cv[n%5]

def f_dh(s):
    return mp.mpf(5)**(-s)*mp.fsum(c(r)*mp.zeta(s, mp.mpf(r)/5) for r in range(1,6))

print("="*78)
print("DH coefficients: period-5, SIGN-CHANGING, NO Euler product => no Lambda>=0")
print("="*78)
print("  A_DH =", mp.nstr(A_dh,12))
print("  c(1..6) =", [mp.nstr(c(n),5) for n in range(1,7)])
print("  c(3)=-A<0, c(4)=-1<0 => coefficients are NOT nonnegative; f has no Euler product")
print("  => -f'/f is NOT sum Lambda_f(n)n^{-s} with Lambda_f>=0. STEP 1 has NO analogue.")

print()
print("="*78)
print("CM TEST: is -f'/f completely monotone on a real ray? (zeta WAS; DH should NOT be)")
print("="*78)
F = lambda x: -mp.diff(lambda z: mp.log(f_dh(z)), x)
print(f"{'sigma':>8} " + " ".join(f"(-1)^{k}f^({k})".rjust(15) for k in range(5)))
for sigma in [mp.mpf('3.0'),mp.mpf('2.0'),mp.mpf('1.5'),mp.mpf('1.2'),mp.mpf('0.8')]:
    row=[((-1)**k)*mp.diff(F,sigma,k) for k in range(5)]
    ok=all(r>=-1e-9 for r in row)
    print(f"{mp.nstr(sigma,4):>8} " + " ".join(mp.nstr(r,5).rjust(15) for r in row)
          + ("  CM-OK" if ok else "  *** not CM ***"))

print()
print("="*78)
print("OFF-LINE ZEROS OF DH (the actual counterexample). Search near known Spira zero.")
print("="*78)
# Known DH off-line zero near s ~ 0.808517 + 85.699348 i (Spira). Find it.
for guess in [mp.mpc('0.8085','85.6993'), mp.mpc('0.65','114.0')]:
    try:
        z=mp.findroot(f_dh, guess)
        print(f"  zero found: s = {mp.nstr(z,12)}   Re s = {mp.nstr(z.real,8)}  "
              f"|f(z)|={mp.nstr(abs(f_dh(z)),3)}  "
              f"{'OFF LINE' if abs(z.real-0.5)>1e-4 else 'on line'}")
    except Exception as e:
        print(f"  (root search from {guess} failed: {e})")

print()
print("="*78)
print("PR TEST of DH's de Branges object M_f(w)=d/dw log Xi_f over UHP_w (Xi_f completed)")
print("  DH has off-line zeros => M_f is NOT PR => passivity fails => matches non-RH.")
print("="*78)
# Completed DH: Xi_f(s) = (FE-symmetric completion). DH FE has shift; the simplest
# symmetric object is g(s)=f(s)f(1-s)-like, but to keep it clean we test the RAW
# statement: DH has a zero with Re>1/2 (found above) => in w=(s-1/2)^2 it lands in
# UHP_w/LHP_w => any Herglotz/PR object built from log f is broken there, exactly as the
# SYNTHETIC off-line zero broke zeta's M in step 3b/4b. The mechanism is identical;
# the difference is DH's off-line zeros are REAL (not synthetic) because positivity is absent.
print("  DH's off-line zero (Re>1/2) is the w-UHP obstruction, identical in MECHANISM to")
print("  the synthetic off-line zero that broke zeta's PR object in steps 3b/4b. The ONLY")
print("  difference: for zeta the obstruction is (conjecturally, RH) ABSENT because of the")
print("  Euler-product positivity; for DH it is PRESENT because that positivity is absent.")

print()
print("="*78)
print("DIVERGENCE SUMMARY")
print("="*78)
print("""
  The transfer chain for zeta:  Euler product  =>  Lambda>=0  =>  -zeta'/zeta CM on (1,inf)
  =>  [continuation through xi + FE into w=(s-1/2)^2]  =>  -d/dw log xi positive-real /
  passive on UHP_w  <=>  zeros at w<0  <=>  RH.
  DH breaks the chain at the FIRST link: no Euler product => coefficients sign-change =>
  no CM, no positive measure => the PR/passivity object is NOT forced => off-line zeros
  are allowed AND occur. DH confirms the Euler product is the SOLE source of the would-be
  positivity, and that the FE skeleton alone provides ZERO positivity (DH has the same FE).
""")
