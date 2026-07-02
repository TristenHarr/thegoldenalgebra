"""
The cancellation K(xi)=0 IS the identity:
  Re[ Gamma'/Gamma stuff - log pi ]  +  2 Re zeta'/zeta(1/2+i xi) = 0  pointwise?
Let's understand. Completed xi(s)= (1/2)s(s-1) pi^{-s/2} Gamma(s/2) zeta(s).
log-deriv: xi'/xi(s) = 1/(s) ... actually:
  xi'/xi(s) = 1/s + 1/(s-1) - (1/2)log pi + (1/2) psi(s/2) + zeta'/zeta(s).
Hadamard: xi'/xi(s) = sum_rho 1/(s-rho)  (symmetric sum), B + sum...
On s=1/2+i xi: by functional eq xi(s)=xi(1-s), so xi'/xi(1/2+it) is purely... 
  xi(1/2+it) is REAL for real t (Riemann). => d/dt log xi(1/2+it) is real =>
  xi'/xi(1/2+it)* i = real => Re[ xi'/xi(1/2+it) ] relates to derivative of |xi|...
Actually xi(1/2+it) real => xi'/xi(1/2+it) = (real)/(real) * ... Let me just verify:
  Claim: Re[ (1/2)psi(1/4+it/2) - (1/2)log pi + zeta'/zeta(1/2+it) + 1/s+1/(s-1) ] = 0.
"""
import mpmath as mp
mp.mp.dps=25
def test(t):
    s=mp.mpf(1)/2+1j*t
    pole=1/s+1/(s-1)
    gam=mp.mpf(1)/2*mp.digamma(s/2)-mp.mpf(1)/2*mp.log(mp.pi)
    zz=mp.zeta(s,derivative=1)/mp.zeta(s)
    xilog=pole+gam+zz
    return xilog
for t in [mp.mpf(x) for x in [3,7,14.13,20,25,30]]:
    v=test(t)
    print(f"t={float(t):6.2f}: xi'/xi(1/2+it)={mp.nstr(v,8)}  Re={mp.nstr(mp.re(v),6)}")
print()
print("=> Re(xi'/xi(1/2+it)) should be EXACTLY 0 (functional eq), confirming the kernel identity.")
print("This Re=0 statement is EQUIVALENT to: xi(1/2+it) has constant phase = real,")
print("i.e. NO zero off the line in this range. THAT is where RH enters.")
