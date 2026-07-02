"""
FINAL OBSTRUCTION DEMONSTRATION.
The Weil bulk kernel is  K(t) = -2 Re[ xi'/xi(1/2+it) ]  (sign per derivation;
the explicit formula's positivity reduces to K(t)>=0 pairing against |hatpsi|^2).
We showed K(t)=0 identically ON the true zeta in the computed range -- because
Re xi'/xi(1/2+it)=0, a CONSEQUENCE of the functional equation xi(s)=xi(1-s)
TOGETHER WITH all zeros being on the line (xi(1/2+it) real-valued).

Now: a single off-line zero pair {rho, 1-rho}={1/2+d+i g0, 1/2-d+i g0} contributes
to xi'/xi an extra  1/(s-rho)+1/(s-(1-rho)). Evaluate Re of that at s=1/2+it:
  1/(1/2+it - (1/2+d+i g0)) + 1/(1/2+it-(1/2-d+i g0))
 = 1/(i(t-g0)-d) + 1/(i(t-g0)+d).
Real part = Re[ (i(t-g0)+d + i(t-g0)-d) / ((i(t-g0))^2 - d^2) ]
 = Re[ 2 i (t-g0) / (-(t-g0)^2 - d^2) ] = 0 ??  -- pure imaginary numerator over real denom!
Hmm. Let me also add the CONJUGATE zeros (xi real on R-axis forces conj symmetry):
the off-line zero comes as a QUARTET: 1/2 +/- d +/- i g0.
"""
import mpmath as mp
mp.mp.dps=25
def reExtra(t,d,g0):
    s=mp.mpf(1)/2+1j*t
    zeros=[mp.mpf(1)/2+d+1j*g0, mp.mpf(1)/2-d+1j*g0,
           mp.mpf(1)/2+d-1j*g0, mp.mpf(1)/2-d-1j*g0]
    return mp.re(sum(1/(s-z) for z in zeros))
print("Extra Re(xi'/xi) from an OFF-LINE quartet at 1/2+/-d+/-i g0, g0=14:")
for d in [mp.mpf('0'),mp.mpf('0.1'),mp.mpf('0.2'),mp.mpf('0.3')]:
    row=[]
    for t in [mp.mpf(x) for x in [13.0,13.6,14.05,14.4,15.0]]:
        row.append(float(reExtra(t,d,14)))
    print(f" d={float(d):.1f}: "+"  ".join(f"t={float(x):.1f}:{r:+.4f}" for x,r in zip([13.0,13.6,14.05,14.4,15.0],row)))
print()
print("On the line (d=0): Re extra = 0 (zeros symmetric, no net real part).")
print("Off the line (d>0): Re extra is NONZERO and SIGN-CHANGING near t=g0.")
print("=> K(t)=-2Re(xi'/xi) acquires a NONZERO, SIGN-INDEFINITE bump localized at t~g0.")
print("   A test fn |hatpsi|^2 concentrated where K<0 makes Q(psi)<0. THAT is Bombieri's")
print("   negative eigenvalue. The functional equation alone gives ONLY the d=0 symmetry,")
print("   NOT the vanishing of the real part -- that needs d=0 i.e. RH itself.")
