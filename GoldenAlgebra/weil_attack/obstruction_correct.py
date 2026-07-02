"""
CORRECTED obstruction. The Weil form is Q(psi)=sum_rho h(gamma_rho), gamma_rho=(rho-1/2)/i.
For a zero ON the line rho=1/2+i g: gamma_rho=g (real), contributes h(g)>=0. Good.
For an off-line QUARTET rho=1/2+/-d+/-i g0: gamma_rho = (rho-1/2)/i:
  rho=1/2+d+i g0 -> gamma=(d+i g0)/i = g0 - i d
  rho=1/2-d+i g0 -> gamma=g0 + i d
  rho=1/2+d-i g0 -> gamma=-g0 - i d
  rho=1/2-d-i g0 -> gamma=-g0 + i d
So the quartet contributes h(g0-id)+h(g0+id)+h(-g0-id)+h(-g0+id).
For h EVEN this = 2[h(g0-id)+h(g0+id)] = 4 Re h(g0+id) (h real on R, h(conj)=conj h).
So contribution = 4 Re h(g0 + i d).
Take h>=0 of positive type, h(r)=|F(r)|^2 with F entire. h(g0+id)=F(g0+id)F*(g0+id)
where F*(z):=conj(F(conj z)). 4 Re h(g0+id) CAN BE NEGATIVE.
Demonstrate with h(r)=(cos(a r))^2 * e^{-eps r^2} type, peaked, made negative off-axis.
"""
import mpmath as mp
mp.mp.dps=25
# choose F real-even so h=F^2; F(z)=e^{-eps z^2} cos(w z). h(r)=e^{-2eps r^2} cos^2(w r)>=0 on R.
def make(eps,w):
    def F(z): return mp.e**(-eps*z*z)*mp.cos(w*z)
    def h(z): return F(z)*F(z)   # analytic continuation of F^2
    return h
print("Off-line quartet contribution = 4 Re h(g0+i d), h=F^2, F=e^{-eps z^2}cos(w z):")
print("Searching for NEGATIVE contribution (=> Q can be pushed negative by off-line zero):")
found=False
for eps in [mp.mpf('0.01'),mp.mpf('0.05'),mp.mpf('0.1')]:
    for w in [mp.mpf('0.5'),mp.mpf('1.0'),mp.mpf('2.0')]:
        h=make(eps,w)
        for g0 in [mp.mpf('5'),mp.mpf('10'),mp.mpf('14')]:
            for d in [mp.mpf('0.5'),mp.mpf('1.0'),mp.mpf('2.0')]:
                c=4*mp.re(h(g0+1j*d))
                onaxis=h(g0).real  # >=0
                if c<-mp.mpf('1e-6')*max(1,abs(onaxis)):
                    print(f"  NEG: eps={float(eps)},w={float(w)},g0={float(g0)},d={float(d)}: contrib={mp.nstr(c,6)}  (on-axis h(g0)={mp.nstr(onaxis,5)})")
                    found=True
if not found: print("  none in grid")
# concrete clean one:
h=make(mp.mpf('0.02'),mp.mpf('1.5'))
print("\nConcrete: eps=0.02,w=1.5,g0=10:")
for d in [mp.mpf(x)/10 for x in range(0,21,2)]:
    print(f"  d={float(d):.1f}: 4Re h(10+id)={mp.nstr(4*mp.re(h(10+1j*d)),7)}")
