"""
THE OBSTRUCTION, made explicit. Suppose RH is FALSE: a zero off the line at
rho = 1/2 + delta + i*gamma0 (delta>0) and its functional-equation partner
1-rho = 1/2 - delta + i*gamma0 (same gamma0), plus complex-conjugate partners.
In the explicit formula the zero sum term for rho is h(gamma_rho) where
gamma_rho = (rho - 1/2)/i = gamma0 - i*delta  (a COMPLEX argument to h).

The four zeros rho, 1-rho, conj(rho), conj(1-rho) give arguments:
  gamma0 - i delta,  -gamma0 - i delta,  gamma0 + i delta, -gamma0 + i delta  (signs)
Actually betas: 1/2+/-delta, gammas +/- gamma0. The four h-arguments are
  +/-gamma0 +/- i delta.  Sum of h over them, for h>=0 on R, can be NEGATIVE
because h(gamma0 + i delta) probes h off the real axis where positivity fails.

Demonstrate: pick h(r)=e^{-a r^2} (positive type), compute
  T(delta) = h(gamma0+i delta)+h(gamma0-i delta)+h(-gamma0+i delta)+h(-gamma0-i delta)
and show it goes NEGATIVE for suitable a, gamma0, delta. THAT is the term the
prime+arch side would have to cancel, and the whole obstruction.
"""
import mpmath as mp
mp.mp.dps=25
def T(a,gamma0,delta):
    h=lambda z: mp.e**(-a*z*z)
    args=[gamma0+1j*delta,gamma0-1j*delta,-gamma0+1j*delta,-gamma0-1j*delta]
    return mp.re(sum(h(z) for z in args))
# h(gamma0 +- i delta)=e^{-a(gamma0^2 - delta^2 +- 2i gamma0 delta)} 
# real part: 2 e^{-a(gamma0^2-delta^2)} cos(2 a gamma0 delta) per +/- gamma0, times 2
# => T = 4 e^{-a(gamma0^2-delta^2)} cos(2 a gamma0 delta)
for (a,g0,d) in [(mp.mpf('0.01'),14,mp.mpf('0.2')),
                 (mp.mpf('0.02'),14,mp.mpf('0.3')),
                 (mp.mpf('0.05'),14,mp.mpf('0.4'))]:
    closed=4*mp.e**(-a*(g0*g0-d*d))*mp.cos(2*a*g0*d)
    print(f"a={float(a)}, gamma0={g0}, delta={float(d)}: T={mp.nstr(T(a,g0,d),10)}  closed={mp.nstr(closed,10)}")
# find a making it negative: need cos(2 a gamma0 delta)<0 => 2 a gamma0 delta > pi/2
print("\n-- pushing to negative --")
for a in [mp.mpf(x)/1000 for x in [5,6,7,8,9,10]]:
    g0=14;d=mp.mpf('0.4')
    print(f"a={float(a)}: T={mp.nstr(T(a,g0,d),8)}  (2a g0 d={float(2*a*g0*d):.3f}, pi/2={float(mp.pi/2):.3f})")
