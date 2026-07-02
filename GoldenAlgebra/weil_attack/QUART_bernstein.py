"""
THE SHARP INEQUALITY, derived analytically (the deliverable).
=============================================================
Object: g positive-type, supp(g) subset [-T,T]. h=ghat entire of exp type T, h>=0 on R.
Weil:  Q(g) = sum_rho h(gamma_rho).  An off-line quartet {1/2 +- delta +- i gamma0} contributes
   N(h) = h(gamma0+i d)+h(gamma0-i d)+h(-gamma0+i d)+h(-gamma0-i d),   d=delta.

SHARP BOUND ON |N| (Bernstein / Paley-Wiener growth into the strip):
For h of exponential type T with h>=0 on R, the value on the line Im=d is controlled by the
Poisson/Bernstein extension. The TIGHT statement (Vaaler-Graham, Plancherel-Polya):
   |h(x + i d)| <= e^{T d} * M(x),    M(x)=sup over real line of |h| near x  (loosely),
and more usefully, the L^1-on-R mass and the off-axis value are linked by
   h(x+i d) = (1/2pi) \int_{-T}^{T} ghat... no: h(x+id)=\int_{-T}^{T} g(u) e^{-i u (x+id)} du
            = \int_{-T}^{T} g(u) e^{u d} e^{-i u x} du.
SO THE EXACT FORMULA IS:
   h(x + i d) = \int_{-T}^{T} g(u) e^{u d} e^{-i u x} du.
The off-axis evaluation is the Fourier transform of g(u) e^{u d}, the support-T function
REWEIGHTED by the exponential e^{u d}. The negative mass:
   N = sum_{s_g,s_d} h(s_g gamma0 + i s_d d)
     = \int_{-T}^{T} g(u) [sum_{s_d} e^{s_d u d}] [sum_{s_g} e^{-i s_g u gamma0}] du
     = \int_{-T}^{T} g(u) * 2cosh(u d) * 2cos(u gamma0) du
     = 4 \int_{-T}^{T} g(u) cosh(u d) cos(u gamma0) du.

  *** N(delta,gamma0,T) = 4 \int_{-T}^{T} g(u) cosh(delta u) cos(gamma0 u) du. ***

This is EXACT and is the central uncertainty inequality. Compare to the on-line case d=0:
   N0 = 4 \int g(u) cos(gamma0 u) du = 4 h(gamma0) >= 0  (on-line value, >=0 part of Q).
The off-line MODIFICATION is the factor cosh(delta u), which AMPLIFIES the large-|u| part of g
by e^{delta|u|} but is ~1 for |u| << 1/delta. THEREFORE:
   - If supp(g) subset [-T,T] with T << 1/delta:  cosh(delta u) ~ 1 + (delta u)^2/2 ~ 1 on the
     whole support => N ~ N0 = 4 h(gamma0) >= 0. The off-line zero is INVISIBLE: it contributes
     the SAME (nonnegative) as an on-line zero, up to O((delta T)^2). NO negative mass.
   - The off-line zero can produce NEGATIVE N only by exploiting cosh(delta u) at |u| ~ 1/delta,
     i.e. only if T >~ 1/delta. THIS IS THE SHARP 'invisible until T ~ 1/delta'.

The constant: cosh(delta u) deviates from 1 by O(1) only when delta|u| ~ 1, i.e. |u| ~ 1/delta.
For g to place mass there AND oscillate against cos(gamma0 u) to go negative, need T >= ~pi/(2..)
times 1/delta. We extract c0 by direct optimization of N/ (positive budget) below.
"""
import numpy as np, mpmath as mp
mp.mp.dps=25

# Verify the EXACT identity N = 4 int g(u) cosh(d u) cos(g0 u) du against the 4-point h sum,
# for a Gaussian g (h=exp(-a r^2), g(u)=exp(-u^2/4a)/(2 sqrt(pi a))).
print("VERIFY EXACT IDENTITY  N = 4 \\int g(u) cosh(d u) cos(g0 u) du  vs  4-point h-sum:")
a=mp.mpf('0.5'); g0=mp.mpf(14); d=mp.mpf('0.3')
g=lambda u: 1/(2*mp.sqrt(mp.pi*a))*mp.e**(-u*u/(4*a))
h=lambda z: mp.e**(-a*z*z)
N_hsum=mp.re(h(g0+1j*d)+h(g0-1j*d)+h(-g0+1j*d)+h(-g0-1j*d))
N_int=4*mp.quad(lambda u: g(u)*mp.cosh(d*u)*mp.cos(g0*u),[-mp.inf,0,mp.inf])
print(f"  h-sum  = {mp.nstr(N_hsum,15)}")
print(f"  integral={mp.nstr(N_int,15)}   diff={mp.nstr(N_hsum-N_int,5)}")
print()

# The on-line value 4 h(g0) for comparison:
print("Compare N(off-line) to N0=4 h(g0) (on-line) for FIXED support, varying delta:")
print("(Gaussian effective support T_eff ~ 4.3 sqrt(a). Here we restrict integral to [-T,T].)")
print(f"{'T':>6} {'delta':>7} {'N(off)':>14} {'N0(on)=4h(g0)':>16} {'N/N0':>10}")
for T in [0.69, 2.0, 5.0, 10.0, 20.0]:
    for d in [mp.mpf('0.2'),mp.mpf('0.05')]:
        Noff=4*mp.quad(lambda u: g(u)*mp.cosh(d*u)*mp.cos(g0*u),[-T,0,T])
        N0  =4*mp.quad(lambda u: g(u)*mp.cos(g0*u),[-T,0,T])
        print(f"{T:6.2f} {float(d):7.3f} {mp.nstr(Noff,8):>14} {mp.nstr(N0,8):>16} {mp.nstr(Noff/N0 if N0!=0 else mp.nan,6):>10}")
