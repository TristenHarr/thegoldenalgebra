"""
TEST 3 (Task 2): Compare Phi against bona-fide PF_inf kernels.

Sanity-check the test machinery: the Gaussian e^{-x^2} is the archetypal PF_inf
function (Schoenberg). Its Toeplitz minors must ALL be >= 0 at every order,
including order 5 where Phi fails. If our det code reports Gaussian D_5 > 0 at the
SAME (u0,h) where Phi's D_5 < 0, that isolates the failure to Phi's arithmetic
(theta) structure, not a numerical artifact of the determinant routine.

Also tests sech(x) (PF_inf) and the single Gaussian theta-term truncations of Phi.
"""
import mpmath as mp
from phi_kernel import K_paper, toeplitz_det, Phi_paper
mp.mp.dps = 80

gauss = lambda u: mp.e**(-(mp.mpf(u))**2)
sech  = lambda u: 1/mp.cosh(mp.mpf(u))

# single-term n=1 piece of the theta kernel (still a *signed* combination, not a pure gaussian)
def Phi_term(u, N):
    u=mp.mpf(u); pi=mp.pi; s=mp.mpf(0)
    for n in range(1,N+1):
        n2=mp.mpf(n)**2; n4=n2*n2
        s+=(2*pi**2*n4*mp.e**(9*u)-3*pi*n2*mp.e**(5*u))*mp.e**(-pi*n2*mp.e**(4*u))
    return s
K_term = lambda N: (lambda u: Phi_term(abs(mp.mpf(u)), N))

print("=== PF_inf reference kernels at (u0=0.01,h=0.05) where Phi's D_5 < 0 ===")
for name,K in [("Gaussian e^{-x^2}",gauss),("sech x",sech)]:
    print(f"  {name}:")
    for r in range(2,8):
        D=toeplitz_det(K,'0.01','0.05',r)
        print(f"     D_{r} = {mp.nstr(D,8)}  {'NEG' if D<0 else ''}")

print("\n=== Phi truncated to N theta-terms: does D_5 sign depend on # terms? ===")
for N in [1,2,3,5,50]:
    D5=toeplitz_det(K_term(N),'0.01','0.05',5)
    print(f"  N={N:3d} terms: D_5 = {mp.nstr(D5,8)}  {'NEG' if D5<0 else 'pos'}")

print("\n=== Is the n=1 single theta-term ALONE PF_5 here? ===")
for r in range(2,8):
    D=toeplitz_det(K_term(1),'0.01','0.05',r)
    print(f"  (n=1 only) D_{r} = {mp.nstr(D,8)}  {'NEG' if D<0 else ''}")
