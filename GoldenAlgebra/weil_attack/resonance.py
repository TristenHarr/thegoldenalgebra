"""
RESONATING test function. Take h(r) = |phi(r)|^2 with phi(r)=e^{-b(r-gamma0)^2}+e^{-b(r+gamma0)^2}
(even, positive-type via |.|^2). This h is PEAKED at r=+/-gamma0, so it "sees" a zero
near height gamma0. 

CRUCIAL EXPERIMENT: 
 (1) Compute Q = ARCH+POLE-PRIME (the computable side). Under RH it equals
     sum over REAL zeros of h(gamma) >= 0. We confirm Q>0 for the TRUE zeta.
 (2) Now imagine RH false: a zero at 1/2+delta+i*gamma0. Its contribution to the
     zero-sum is h evaluated at the COMPLEX point gamma0 - i*delta (and partners).
     We compute that complex contribution and show that for the resonating h it is
     O(1) NEGATIVE and NOT exponentially killed -- because h is centered AT gamma0.
 This is the naked obstruction: the prime+arch side is FIXED (depends only on zeta's
 Euler product + Gamma), while the hypothetical off-line zero would ADD a negative
 O(1) amount to what must equal that fixed side. Positivity is then a NONTRIVIAL
 inequality between the (computable) right side and zero, with no algebraic slack.
"""
import mpmath as mp
from sympy import isprime as _isprime
mp.mp.dps=25
def dig(z): return mp.digamma(z)
PRIMES=[p for p in range(2,40000) if _isprime(p)]
gamma0=mp.mpf('14.134725')  # near first zero
b=mp.mpf('1.5')
# phi(r)=e^{-b(r-g0)^2}+e^{-b(r+g0)^2}; h=phi^2 (phi real even) -> h(r)=phi(r)^2
def phi(z): return mp.e**(-b*(z-gamma0)**2)+mp.e**(-b*(z+gamma0)**2)
def h(z): return phi(z)**2
# autocorrelation g: h=|hatpsi|^2 where psi = inverse FT of phi. 
# phi(r)=sum of 2 gaussians in FREQUENCY -> psi(x) is modulated gaussian. 
# Easier: g(u) = (1/2pi) int h(r) e^{i r u} dr  (inverse transform of h). Compute numerically.
def g(u):
    f=lambda r: h(r)*mp.e**(1j*r*u)
    val=mp.quad(f,[-mp.inf,-2*gamma0,-gamma0,0,gamma0,2*gamma0,mp.inf])
    return (val/(2*mp.pi)).real
W=lambda r: mp.re(dig(mp.mpf(1)/4+1j*r/2))-mp.log(mp.pi)
A=mp.quad(lambda r:h(r)*W(r),[-mp.inf,-2*gamma0,-gamma0,0,gamma0,2*gamma0,mp.inf])/(2*mp.pi)
P=mp.re(h(1j/2)+h(-1j/2))
s=mp.mpf(0)
for p in PRIMES:
    lp=mp.log(p)
    for k in range(1,60):
        u=k*lp;gu=g(u);t=lp*p**(-mp.mpf(k)/2)*gu;s+=t
        if abs(t)<mp.mpf(10)**(-22) and u>30:break
PR=2*s
Q=mp.re(A+P-PR)
print("Resonating h peaked at gamma0=14.13")
print("ARCH=",mp.nstr(A,12)); print("POLE=",mp.nstr(P,12)); print("PRIME=",mp.nstr(PR,12))
print("Q = ARCH+POLE-PRIME =",mp.nstr(Q,12))
# true zero sum
ZS=mp.mpf(0)
for n in range(1,2000):
    gm=mp.im(mp.zetazero(n));t=2*h(gm);ZS+=t
    if t<mp.mpf(10)**(-22) and gm>3*gamma0:break
print("true ZS =",mp.nstr(ZS,12)," (Q should match)")
print("diff:",mp.nstr(Q-ZS,6))
# hypothetical off-line contribution at gamma0 with delta:
print("\nHypothetical off-line zero at 1/2+delta+i*gamma0 contributes h(gamma0 - i delta)+partners:")
for d in [mp.mpf('0.1'),mp.mpf('0.2'),mp.mpf('0.3')]:
    args=[gamma0-1j*d,gamma0+1j*d,-gamma0-1j*d,-gamma0+1j*d]
    contrib=mp.re(sum(h(z) for z in args))
    print(f"  delta={float(d)}: off-line contrib={mp.nstr(contrib,8)}  (vs on-line h(gamma0)={mp.nstr(h(gamma0),8)})")
