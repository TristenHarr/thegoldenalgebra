"""
MODEL B (SHARP): exact band-limited h of exponential type T. This is the CORRECT object:
supp(g) subset [-T,T]  <=>  h=ghat is entire of exponential type <= T (Paley-Wiener).
The Gaussian (Model A) is NOT band-limited; its threshold T~1/sqrt(g0 d) is an artifact of
the Gaussian tail reaching up to height gamma0. The genuine uncertainty law uses the SHARP
growth of a type-T function off the real axis.

THE BERNSTEIN / PALEY-WIENER GROWTH LAW (sharp):
If h has exponential type T and is bounded on R, then for the matched extremal,
   |h(x + i*delta)| grows like e^{delta * T} relative to its real-axis scale.
More precisely, for the Fejer kernel F_{T}(r) = (sin(T r/2)/(T r/2))^2 * (T/2pi) ... we take
the positive-type band-limited bump
   h(r) = K_a(r - gamma0) + K_a(r + gamma0),   K_a(r) = (sin(a r)/(a r))^2   (type 2a).
So h has exponential type 2a; supp(g)=[-2a,2a] => T = 2a, i.e. a = T/2.
K_a is POSITIVE on R (it is |sinc|^2 = |phihat|^2 with phihat=box of width a => phi*phi~).
This is a genuine positive-type test function with EXACT support [-T,T].

Quartet contribution:
  N(T,gamma0,delta) = sum over s1,s2 in {+,-} of  K_a(s1*gamma0 + i*s2*delta)  ...
  with the +gamma0 and -gamma0 bumps. By symmetry only the bump CENTERED near the zero
  dominates: K_a((gamma0) - gamma0 +- i delta) = K_a(+- i delta)  -> the ON-CENTER value,
  PLUS the far bump K_a(2 gamma0 +- i delta) (tiny). So the leading negative mass is
       N ~ 2 Re K_a(i delta) + 2 Re K_a(-i delta)  (from the matched bump)
  Wait: the FOUR zeros are at +-gamma0 +- i delta. The bump K_a(r-gamma0) evaluated there:
     at  gamma0 + i delta : K_a(i delta)
     at  gamma0 - i delta : K_a(-i delta)
     at -gamma0 + i delta : K_a(-2 gamma0 + i delta)  (far, ~1/gamma0^2 -> negligible)
     at -gamma0 - i delta : K_a(-2 gamma0 - i delta)  (far)
  and symmetrically for K_a(r+gamma0). So the DOMINANT quartet mass is
       N_dom(T,delta) = 2 * Re[ K_a(i delta) + K_a(-i delta) ] = 4 Re K_a(i delta).
  K_a(i delta) = (sin(i a delta)/(i a delta))^2 = (sinh(a delta)/(a delta))^2  (REAL, >=1).
  => N_dom = 4 (sinh(a delta)/(a delta))^2 > 0  ALWAYS for |sinc|^2!  -- POSITIVE, never neg.

  THIS IS THE POINT: |sinc|^2 is positive-type AND its analytic continuation
  (sinh/.)^2 stays POSITIVE on the imaginary shift. A single positive bump CANNOT make N<0.
  To get N<0 we need an OSCILLATING band-limited h (the negative lobes), i.e. h must change
  the SIGN of its imaginary-shift continuation while staying >=0 on R. That requires
  h to have ZEROS on R near gamma0 (double zeros, to stay >=0), i.e. resolution finer than
  the spacing => type T large. The threshold is exactly when h of type T can place a
  resolved double-zero structure at scale delta around gamma0.
"""
import numpy as np, mpmath as mp
mp.mp.dps = 30

def Ka(z, a):   # (sin(a z)/(a z))^2, analytic
    if z == 0: return mp.mpf(1)
    return (mp.sin(a*z)/(a*z))**2

print("="*78)
print("SINGLE POSITIVE BUMP (|sinc|^2): N_dom = 4 (sinh(a*delta)/(a*delta))^2 >= 4 > 0.")
print("A single positive-type band-limited bump gives POSITIVE quartet mass -> CANNOT")
print("detect the off-line zero. Confirms: bounded support + crude positive test = blind.")
print("="*78)
for T in [mp.log(2), mp.mpf(1), mp.mpf(2), mp.mpf(4), mp.mpf(8)]:
    a = T/2
    for d in [mp.mpf('0.2'), mp.mpf('0.1')]:
        Ndom = 4*(mp.sinh(a*d)/(a*d))**2
        print(f"  T={float(T):6.3f} a={float(a):5.3f} delta={float(d):4.2f}:  N_dom = {float(Ndom):+.6f}")

print("""
KEY: the matched single bump is BLIND (N>0). To produce negative quartet mass you must use
an OSCILLATING band-limited h with a double zero at gamma0 (Selberg/Beurling-type extremal).
Its imaginary-axis continuation flips sign. The minimal type T to resolve scale delta is the
true threshold. We compute it now via the BERNSTEIN extremal.
""")
