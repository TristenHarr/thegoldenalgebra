"""
Is the PRIME functional g -> -2 sum_n Lambda(n)/sqrt(n) g(log n) sign-definite
on positive-type g (g=autocorr, hat g>=0)? If it were a positive pairing we could
hope to combine with Connes archimedean positivity. Test: build the prime-term-only
quadratic form P[m,n] in a basis and check eigenvalue signs. The prime term as a
quadratic form in psi (g=psi corr psi) is
  -2 sum_n Lambda(n)/sqrt(n) (psi corr psi)(log n)
  = -2 sum_n Lambda(n)/sqrt(n) sum int psi(x)psi(x-log n) dx
This is NEGATIVE of a Toeplitz-like form. Its definiteness:
  Quad(psi) = -2 sum_n w_n <psi, T_{log n} psi>, w_n=Lambda(n)/sqrt(n)>0, T=shift.
Since shifts T_a have spectrum on unit circle (e^{i a xi}), 
  Quad = - (1/2pi) int |hatpsi(xi)|^2 * [2 sum_n w_n cos(xi log n)] dxi.
So prime term = -(1/2pi) int |hatpsi(xi)|^2 D(xi) dxi, D(xi)=2 sum_n Lambda(n) n^{-1/2} cos(xi log n).
=> prime term sign is governed by sign of D(xi). D(xi)= -2 Re sum Lambda(n) n^{-1/2 - i xi}
   = -2 Re ( -zeta'/zeta (1/2 + i xi) ).  Since sum Lambda(n) n^{-s} = -zeta'/zeta(s).
So D(xi) = -2 Re( zeta'/zeta(1/2 + i xi) ).  
The prime term is POSITIVE iff D(xi)<=0 i.e. Re(zeta'/zeta(1/2+ixi))>=0 -- which is
FALSE in general (it oscillates wildly, sign changes at every zero!). 
=> The prime quadratic form is INDEFINITE. Confirm numerically: plot D(xi).
"""
import mpmath as mp
mp.mp.dps=20
def D(xi):
    return -2*mp.re(mp.zeta(mp.mpf(1)/2+1j*xi, derivative=1)/mp.zeta(mp.mpf(1)/2+1j*xi))
for xi in [mp.mpf(x)/2 for x in range(0,60,3)]:
    try:
        d=D(xi)
        print(f" xi={float(xi):5.1f}: D={mp.nstr(d,8):>16}  prime-form-density sign={'+pos' if d<0 else '-NEG'}")
    except Exception as e:
        print(f" xi={float(xi):5.1f}: (near zero/pole) {e}")
