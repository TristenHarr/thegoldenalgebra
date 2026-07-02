"""
SHARP QUANTITATIVE UNCERTAINTY: off-line zero quartet vs bounded-support Weil positivity.
====================================================================================
Setup (Weil explicit formula, Bombieri/Connes normalization). A positive-type test
function g = phi * phi~ has supp(g) subset [-T,T]; its transform h(r)=ghat(r)=|phihat(r)|^2
is ENTIRE OF EXPONENTIAL TYPE T (Paley-Wiener) and h>=0 on the REAL axis.

  Q(g) = sum_rho h(gamma_rho),  gamma_rho=(rho-1/2)/i.

If RH holds all gamma_rho are real and Q>=0 (since h>=0 on R). An OFF-LINE zero
rho=1/2+delta+i*gamma0 (delta>0) and its 3 functional-equation/conjugate partners
1-rho, conj(rho), conj(1-rho) give gamma_rho in {+-gamma0 +- i*delta} : OFF the real axis.

Their contribution to Q (the "negative mass" the rest of Q must absorb):
  N(g) = h(gamma0+i*delta)+h(gamma0-i*delta)+h(-gamma0+i*delta)+h(-gamma0-i*delta).
Because h is positive on R but NOT on horizontal lines Im=+-delta, N can be < 0.

TASK 1: size of N as a function of (delta,gamma0,T).
TASK 2: optimal T(delta,gamma0) where N first goes detectably negative; the constant.
TASK 3: at T=log2 (Yoshida unconditional cone), compare |N| to the positive ARCH+POLE floor.
TASK 4: support T(w) for a width-w zero-free region; show T->inf as w->0.

KEY ANALYTIC FACT (sharp, Bernstein/Paley-Wiener):
For h entire of exp type T,  h(x+i*delta) "lives" at scale e^{|delta|*T} relative to h on R.
Concretely for h(r)=hbar(r) a bump of type T centered at gamma0:
  the four points pull h to argument gamma0 +- i delta. Writing the unique band-limited
  positive 'matched filter' h(r) = |D_T(r-gamma0)|^2 + |D_T(r+gamma0)|^2 with D_T the
  Dirichlet/Fejer kernel of type T/2 (so |D|^2 has type T), N is computed exactly.
We do BOTH: (A) a clean Gaussian-with-type-cap analytic model giving the closed-form
threshold, and (B) the EXACT band-limited extremal (Fejer^2) to pin the true constant.
"""
import numpy as np, mpmath as mp
mp.mp.dps = 30

# ---------------------------------------------------------------------------
# MODEL A: Gaussian h(r)=exp(-a r^2) shifted to gamma0. NOT compactly supported in u,
# but its support is "effectively" |u|<~ T with the Gaussian g(u)=exp(-u^2/4a)/(2 sqrt(pi a)).
# Effective additive support: g(u) drops to e^{-K^2/4} of peak at |u|=K*sqrt(2a)... use
# T_eff = c*sqrt(a). The quartet contribution has the EXACT closed form (offline_model.py):
#   N_gauss(a,gamma0,delta) = 4 e^{-a(gamma0^2 - delta^2)} cos(2 a gamma0 delta).
# This is FIRST NEGATIVE when 2 a gamma0 delta = pi/2, i.e. a = pi/(4 gamma0 delta).
# ---------------------------------------------------------------------------
def N_gauss(a, g0, d):
    return 4*mp.e**(-a*(g0*g0 - d*d))*mp.cos(2*a*g0*d)

print("="*78)
print("MODEL A (Gaussian, closed form N=4 e^{-a(g0^2-d^2)} cos(2 a g0 d))")
print("First sign change at 2 a g0 d = pi/2  =>  a* = pi/(4 g0 d).")
print("="*78)
for g0 in [14, 50, 100]:
    for d in [mp.mpf('0.1'), mp.mpf('0.05'), mp.mpf('0.01')]:
        a_star = mp.pi/(4*g0*d)
        print(f"  gamma0={g0:5}, delta={float(d):6.3f}:  a* = {float(a_star):.4e}")

print("""
The Gaussian width a sets the additive support. For exp(-a r^2) in frequency,
g(u)=exp(-u^2/(4a))/(2 sqrt(pi a)); g(u)/g(0)=e^{-u^2/(4a)}. Define support T at the
1% level: e^{-T^2/(4a)}=0.01 => T = 2 sqrt(a ln 100) = 2 sqrt(a)*2.146 = 4.29 sqrt(a).
At the threshold a*=pi/(4 g0 d):  T_thr = 4.29 * sqrt(pi/(4 g0 d)) = 3.80 / sqrt(g0 d).
""")
for g0 in [14, 50, 100, 1000]:
    for d in [mp.mpf('0.1'), mp.mpf('0.01'), mp.mpf('0.001')]:
        a_star = mp.pi/(4*g0*d)
        T_thr = 4.29*mp.sqrt(a_star)
        print(f"  gamma0={g0:5}, delta={float(d):7.4f}: a*={float(a_star):.3e}  T_thr(1%)={float(T_thr):.4f}")
