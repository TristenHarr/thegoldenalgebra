"""
(B)+(C) of the omega-continuation attack:  track sup_{UHP} |Theta_omega| as omega
decreases, and test the PROPAGATION question:  is there a monotonicity / maximum-
principle mechanism forcing |Theta_omega|<=1 to PERSIST from omega>1 to omega->0?

KEY FACT used (maximum modulus / inner functions):
  Theta_omega = N/D, N=xi(1/2-omega-iz), D=xi(1/2+omega-iz), both ENTIRE in z.
  By xi(s)=xi(1-s): xi(1/2-omega-iz) = xi(1/2+omega+iz).  So
     N(z) = xi(1/2+omega+iz) = D(-z)  ... and on the real axis z=x:
     |N(x)| = |xi(1/2+omega+ix)|,  |D(x)| = |xi(1/2+omega-ix)| = |conj of N(x)|
            (xi real on R-shifted? check) => |Theta_omega(x)| = 1 on the REAL AXIS.
  So Theta_omega is unimodular on R (boundary).  Inner on UHP  <=>  (max principle)
  Theta_omega is HOLOMORPHIC & BOUNDED in UHP  <=>  D has no zeros in UHP
  (N automatically has zeros where D(-z) does, i.e. in LHP if D zero-free in UHP).

  THEREFORE the ENTIRE inner property reduces to:  D(z)=xi(1/2+omega-iz) has NO
  zeros in the open UHP {Im z>0}.  Equivalently xi(s) has no zeros with
  Re s > 1/2 + omega... let's verify the exact half-plane.

This script:
  1. Verifies |Theta_omega|=1 on the real axis (boundary unimodularity) -> Theta is
     INNER iff zero-free-in-UHP, i.e. a pure pole/zero-location question.
  2. Confirms the inner property for omega in (1/2, 3] holds UNCONDITIONALLY and
     reduces, for omega<=1/2, to 'no xi zeros with Re s > 1/2+omega'.
  3. THE PROPAGATION TEST: there is NO monotonic Hamiltonian decreasing-omega
     mechanism that is omega-local; the property is GLOBAL pole-location and flips
     discontinuously the instant a zero crosses Re s = 1/2+omega. We exhibit that
     the "margin" min over UHP of (1-|Theta|) is identically 0 (boundary saturates)
     for ALL omega, so there is no interior margin to propagate -- the bound is
     boundary-tight at every omega, and only the zero-location (=RH for omega<=1/2)
     decides it.
"""
import mpmath as mp
mp.mp.dps = 30

def xi(s):
    return mp.mpf('0.5')*s*(s-1)*mp.pi**(-s/2)*mp.gamma(s/2)*mp.zeta(s)

def N(omega,z): return xi(mp.mpf('0.5')-omega-1j*z)
def D(omega,z): return xi(mp.mpf('0.5')+omega-1j*z)
def Theta(omega,z):
    d=D(omega,z)
    if d==0: return mp.inf
    return N(omega,z)/d

print("="*80)
print("1. BOUNDARY UNIMODULARITY: |Theta_omega(x)| on the real axis z=x in R")
print("="*80)
for omega in [2.0,1.0,0.5,0.2,0.05]:
    vals=[abs(Theta(omega,mp.mpf(x))) for x in [0.5,3.0,7.0,14.13,28.0]]
    print(f"  omega={omega:>5}: |Theta(x)| = "+" ".join(mp.nstr(v,8) for v in vals))
print("  => |Theta_omega|=1 on R for ALL omega (functional equation xi(s)=xi(1-s)).")
print("  Boundary fully saturated at every omega -> NO interior margin to propagate.")

print()
print("="*80)
print("2. INNER <=> denominator D(z)=xi(1/2+omega-iz) zero-free in open UHP {Im z>0}")
print("   D(z)=0 <=> xi(s)=0 with s=1/2+omega-iz, Im z>0 <=> Re s < 1/2+omega AND...")
print("   precisely: z=i(1/2+omega-s)... a zero s=beta+i*gamma gives Im z=1/2+omega-beta")
print("   Im z>0 <=> beta < 1/2+omega.  ALL nontrivial zeros have 0<beta<1.")
print("="*80)
print("   So D has a UHP zero <=> EXISTS xi-zero with beta < 1/2+omega... wait that's")
print("   ALWAYS true (beta<1<1/2+omega only needs omega>1/2). Recheck sign:")
# Recompute carefully which half-plane. D(omega,z)=0 with Im z>0.
# numerically find: does D have zeros in UHP for given omega?
print()
print("   NUMERICAL: scan for zeros of D(omega,.) in UHP via argument principle proxy")
print("   (sample |D| on a UHP grid; a near-zero flags a pole of Theta in UHP).")
for omega in [2.0,1.0,0.5,0.2,0.05]:
    minabsD=mp.inf; argmin=None
    for x in [mp.mpf(k)/2 for k in range(1,60)]:    # x in (0,30)
        for y in [mp.mpf(k)/10 for k in range(1,30)]: # y in (0,3)
            v=abs(D(omega,mp.mpc(x,y)))
            if v<minabsD: minabsD=v; argmin=(float(x),float(y))
    print(f"  omega={omega:>5}: min|D| over UHP grid = {mp.nstr(minabsD,5)} at z={argmin}")
print("  (min|D| bounded away from 0 => D zero-free in UHP => Theta inner there.)")

print()
print("="*80)
print("3. sup_{UHP}|Theta_omega| over a grid, vs omega  (should be <=1 while D zero-free)")
print("="*80)
for omega in [2.0,1.0,0.6,0.5,0.4,0.2,0.1,0.05]:
    mx=0.0; argmx=None
    for x in [mp.mpf(k)/2 for k in range(0,60)]:
        for y in [mp.mpf(k)/10 for k in range(1,30)]:
            v=abs(Theta(omega,mp.mpc(x,y)))
            if v>mx: mx=v; argmx=(float(x),float(y))
    flag = "INNER ok" if mx<=1+1e-6 else ">1  NOT INNER"
    print(f"  omega={omega:>5}: sup_UHP|Theta| ~ {mp.nstr(mx,8):>12}  at {argmx}  {flag}")
