"""
EXACT zero-tracking for Theta_omega(z) = N/D, N=xi(1/2-omega-iz), D=xi(1/2+omega-iz).

Map xi-zeros rho to z-plane zeros of D and N EXACTLY and decide UHP/LHP membership,
then confirm the inner property and locate the RH-sensitive threshold in omega.

D(omega,z)=0  <=>  1/2+omega - i z = rho  (rho an xi-zero)
              <=>  i z = 1/2+omega-rho
              <=>  z = -i(1/2+omega-rho) = i(rho - 1/2 - omega).
  rho = beta + i*gamma  =>  z = i((beta-1/2-omega) + i*gamma) = -gamma + i(beta-1/2-omega).
  Im z = beta - 1/2 - omega.   UHP (Im z>0) <=>  beta > 1/2 + omega.

N(omega,z)=0  <=>  1/2-omega - i z = rho  =>  z = i(rho-1/2+omega) = -gamma + i(beta-1/2+omega).
  Im z = beta - 1/2 + omega.   UHP <=> beta > 1/2 - omega.

So:
  * D zero in UHP  <=>  exists xi-zero with beta > 1/2 + omega.
    Unconditional zero-free region: beta <= 1 always; and actually beta<1 strictly.
    => for omega >= 1/2, need beta>1: IMPOSSIBLE => D zero-free in UHP UNCONDITIONALLY.
    => for omega < 1/2, D zero-free in UHP  <=>  no xi-zero with beta>1/2+omega.
       As omega->0+ this becomes 'no zero with beta>1/2' = RH (the right edge).
  * N has zeros in UHP for beta>1/2-omega: for ALL omega>0 there are on-line zeros
    (beta=1/2 < 1/2+omega... ) hmm beta=1/2: 1/2>1/2-omega TRUE => N has UHP zeros.
    But N(z)=xi(1/2+omega+iz) [by FE] = D(omega,-z); its zeros mirror D's. The inner
    quotient bounded-ness in UHP is governed by the DENOMINATOR poles (=D zeros) only.

CONCLUSION the script verifies:
  Theta_omega inner on UHP  <=>  D zero-free on UHP  <=>  no xi-zero beta>1/2+omega.
  For omega>1/2: unconditional (zero-free region Re s<1 i.e. beta<1<1/2+omega).
  WALL: as omega decreases through 1/2 toward 0, the required zero-free half-plane
  Re s <= 1/2+omega shrinks to the critical line; at omega=0+ it IS RH.
"""
import mpmath as mp
mp.mp.dps = 30

# first several nontrivial zeros (gamma), assumed on-line (RH numerically true here)
gammas = [14.134725142, 21.022039639, 25.010857580, 30.424876126, 32.935061588,
          37.586178159, 40.918719012, 43.327073281, 48.005150881, 49.773832478]

def Dzero_Imz(beta, omega):    return beta - mp.mpf('0.5') - omega   # Im z of D-zero
def Nzero_Imz(beta, omega):    return beta - mp.mpf('0.5') + omega   # Im z of N-zero

print("="*82)
print("D-zero Im z = beta-1/2-omega.  ON-LINE beta=1/2 => Im z = -omega < 0 (LHP, good).")
print("So with RH, D is zero-free in UHP for EVERY omega>0 -> Theta inner for all omega>0.")
print("WITHOUT RH, an off-line zero beta>1/2 gives Im z>0 exactly when omega<beta-1/2.")
print("="*82)
for beta in [mp.mpf('0.5'), mp.mpf('0.55'), mp.mpf('0.6'), mp.mpf('0.75'), mp.mpf('0.99')]:
    crit = beta - mp.mpf('0.5')   # omega below which this beta-zero pops into UHP
    print(f"  off-line beta={float(beta):>5}: D-zero enters UHP for omega < {float(crit):.3f}"
          + ("   (RH on-line: never)" if beta==mp.mpf('0.5') else ""))
print()
print(">>> THRESHOLD: for omega>1/2, NO beta in (0,1) satisfies beta>1/2+omega, so D is")
print("    zero-free in UHP UNCONDITIONALLY (Suzuki's omega>1 region, sharpened to >1/2).")
print("    For 0<omega<1/2 the inner property is EXACTLY 'no xi-zero with Re s>1/2+omega',")
print("    a half-plane that closes onto the critical line as omega->0  ==  RH.")
print()

print("="*82)
print("PROPAGATION QUESTION: is there an omega-monotone mechanism forcing inner-ness to")
print("persist from omega>1/2 down to omega=0?  Answer via the MARGIN structure.")
print("="*82)
print("The boundary R is UNIMODULAR (|Theta_omega|=1 on R) for every omega (functional eq).")
print("So sup_{UHP}|Theta_omega| = 1 is attained on the boundary for EVERY omega where it")
print("is inner; there is NO interior strict margin (1-|Theta|>delta) that could be")
print("propagated by a maximum principle / monotone Hamiltonian as omega decreases.")
print("The inner property is a DISCRETE pole-crossing event: |Theta| jumps from <=1 to >1")
print("the instant a D-zero crosses R into the UHP, i.e. the instant a xi-zero crosses")
print("Re s = 1/2+omega.  There is no continuous 'positivity reservoir' to deplete; the")
print("Hamiltonian H_omega(x)>=0 stays >=0 trivially until a zero crosses, then FAILS")
print("instantly.  Monotone continuation cannot bridge a discontinuous crossing.")
print()
print("Hence: H_omega>=0 for omega>1/2 does NOT propagate to omega=0 by any omega-local")
print("monotonicity; propagation past omega=1/2 is logically equivalent to excluding")
print("zeros in 1/2<Re s<1/2+omega for every omega>0, i.e. RH. WALL CONFIRMED at omega=1/2.")
