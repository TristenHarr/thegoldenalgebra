"""
GROUND TRUTH check: For psi=sum a_n bump_n, h(r)=|hatpsi(r)|^2, the Weil
functional value Q(psi)=ARCH+POLE-PRIME MUST equal sum_rho h(gamma_rho) by the
explicit formula. Compute the zero-sum directly and compare. If they match,
then Q(eigvec)<0 means sum_rho |hatpsi(gamma)|^2 < 0 -- impossible if all
gamma are REAL. So a mismatch reveals the bug; a match means h(gamma) for the
chosen psi is NOT >=0 (i.e. h not actually of positive type / not |.|^2 on R).
"""
import mpmath as mp
mp.mp.dps=25
sig=mp.mpf('1.0');C=2*mp.pi*sig*sig
vec=[mp.mpf(x) for x in ['-0.69254','-0.17057','-0.1291','-0.21003','-0.33588','-0.37533','0.42051']]
us=[mp.mpf(n) for n in range(7)]
def h(r):
    S=sum(c*mp.e**(-1j*r*u) for c,u in zip(vec,us))
    return C*mp.e**(-(sig*sig)*r*r)*abs(S)**2
# is h>=0 on real axis? 
print("h(0)=",mp.nstr(h(0),8)," h(1)=",mp.nstr(h(1),8)," h(2.3)=",mp.nstr(h(2.3),8))
mn=min(mp.re(h(mp.mpf(t)/10)) for t in range(-300,301))
print("min over real r in [-30,30]:",mp.nstr(mn,8))
# zero sum
s=mp.mpf(0)
for n in range(1,2000):
    g=mp.im(mp.zetazero(n))
    t=2*mp.re(h(g));s+=t
    if abs(t)<mp.mpf(10)**(-22) and g>15:break
print("zero sum 2*sum h(gamma):",mp.nstr(s,12))
