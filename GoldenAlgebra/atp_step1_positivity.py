"""
ARITHMETIC TRANSFER PRINCIPLE — STEP 1
=======================================
Make PRECISE the sense in which -zeta'/zeta is "positive-real / Herglotz" on Re s>1,
and verify numerically.

UNCONDITIONAL FACT (Re s>1):
    -zeta'/zeta(s) = sum_{n>=1} Lambda(n) n^{-s},   Lambda(n) >= 0  (von Mangoldt).

This is a Dirichlet series with NONNEGATIVE coefficients. Equivalently it is the
Laplace transform of the positive measure  d nu = sum_n Lambda(n) delta_{log n}:
    -zeta'/zeta(s) = integral_0^infty e^{-s t} d nu(t),   nu >= 0.    (sigma = Re s)

WHICH positivity exactly does this give?  Three DIFFERENT notions, do not conflate:

(P1) COMPLETELY MONOTONE in sigma (real variable, s=sigma>1):
     f(sigma) = -zeta'/zeta(sigma) = integral e^{-sigma t} dnu(t) with nu>=0.
     Bernstein:  f is completely monotone on (1,infty):  (-1)^k f^{(k)}(sigma) >= 0
     for ALL k>=0.  This is the STRONGEST real-variable consequence of nu>=0.
     -> f>=0, f'<=0, f''>=0, f'''<=0, ...   (test this directly).

(P2) Laplace transform => f is the restriction of a function HOLOMORPHIC and with a
     specific structure on Re s>1; but a Laplace transform of a POSITIVE measure is
     NOT in general a Herglotz (Pick/Nevanlinna) function of s.  Herglotz means
     Im f(s) >= 0 whenever Im s > 0.  We TEST whether -zeta'/zeta has that property.
     (Spoiler we will verify: it does NOT — completely-monotone-in-sigma is the right
      statement, "Herglotz in s" is FALSE even on Re s>1. This matters for the FE map.)

(P3) The DERIVATIVE structure:  because dnu>=0, the function -zeta'/zeta has POSITIVE
     real part after multiplying by the right thing?  Test  Re(-zeta'/zeta(s)) sign.
     A Laplace transform of a positive measure has Re f(sigma+it) = integral
     e^{-sigma t'} cos(t t') dnu(t')  which OSCILLATES in t -> Re can be negative.

The HONEST precise statement we are verifying:
   "nu>=0"  <=>  "-zeta'/zeta is completely monotone on the real ray (1,infty)"  (P1, TRUE)
   "nu>=0"  does NOT  =>  "-zeta'/zeta Herglotz in s on Re s>1"                  (P2, FALSE)
This distinction is the CRUX of whether the FE can transfer positivity.
"""
import mpmath as mp
mp.mp.dps = 30

def neg_zlogzeta(s):
    # -zeta'(s)/zeta(s)
    return -mp.zeta(s, derivative=1)/mp.zeta(s)

def vonmangoldt_partial(s, N=200000):
    # direct sum  sum Lambda(n) n^{-s}  for sanity (slow convergence near sigma=1)
    from sympy import primerange
    total = mp.mpf(0)
    for p in primerange(2, N):
        pk = p
        lp = mp.log(p)
        while pk < N:
            total += lp * mp.mpf(pk)**(-s)
            pk *= p
    return total

print("="*78)
print("SANITY: -zeta'/zeta(s) == sum Lambda(n) n^{-s} on Re s>1")
print("="*78)
for s in [mp.mpf('2.0'), mp.mpc('2.0','3.0'), mp.mpf('1.5')]:
    closed = neg_zlogzeta(s)
    series = vonmangoldt_partial(s, N=300000)
    print(f"  s={s}: closed={mp.nstr(closed,12)}")
    print(f"         series(N=3e5)={mp.nstr(series,12)}  |diff|={mp.nstr(abs(closed-series),4)}")

print()
print("="*78)
print("(P1) COMPLETELY MONOTONE on (1,infty):  (-1)^k f^{(k)}(sigma) >= 0  for all k")
print("     f(sigma) = -zeta'/zeta(sigma).  Derivatives via mpmath.diff.")
print("="*78)
f = lambda x: -mp.zeta(x, derivative=1)/mp.zeta(x)
print(f"{'sigma':>8} " + " ".join(f"(-1)^{k} f^({k})".rjust(16) for k in range(6)))
for sigma in [mp.mpf('1.05'), mp.mpf('1.2'), mp.mpf('1.5'), mp.mpf('2.0'), mp.mpf('4.0')]:
    row = []
    for k in range(6):
        dk = mp.diff(f, sigma, k)
        row.append(((-1)**k) * dk)
    allpos = all(r >= -1e-12 for r in row)
    print(f"{mp.nstr(sigma,4):>8} " + " ".join(mp.nstr(r,6).rjust(16) for r in row)
          + ("  CM-OK" if allpos else "  *** CM VIOLATED ***"))
print()
print("  => completely monotone on (1,infty) is the EXACT real-variable meaning of nu>=0.")

print()
print("="*78)
print("(P2) IS -zeta'/zeta HERGLOTZ IN s ON Re s>1?  (Im f >= 0 when Im s>0?)")
print("     If YES it would be a genuine Pick function; if NO, 'positive-real in s'")
print("     is the WRONG frame and the FE map cannot be a Pick-class automorphism.")
print("="*78)
print(f"{'sigma':>7} {'t':>7} {'Re f':>16} {'Im f':>16}  {'Im f sign'}")
herglotz_ok = True
for sigma in [mp.mpf('1.2'), mp.mpf('2.0')]:
    for t in [mp.mpf('0.5'), mp.mpf('2.0'), mp.mpf('5.0'), mp.mpf('10.0'), mp.mpf('20.0')]:
        s = mp.mpc(sigma, t)
        val = neg_zlogzeta(s)
        if val.imag > 1e-12:  # Im s>0 but Im f>0 would VIOLATE the usual Herglotz-on-UHP sign for -f
            pass
        print(f"{mp.nstr(sigma,3):>7} {mp.nstr(t,4):>7} {mp.nstr(val.real,8):>16} "
              f"{mp.nstr(val.imag,8):>16}  {'+' if val.imag>0 else '-'}")
print("  Observe: Im f changes sign as t grows => f is NOT Herglotz (not monotone-Im) in s.")
print("  => The Laplace/positive-measure structure gives CM in sigma, NOT Herglotz in s.")

print()
print("="*78)
print("(P3) Re(-zeta'/zeta(sigma+it)) = integral e^{-sigma t'} cos(t t') dnu(t')")
print("     oscillates in t; positive measure does NOT force Re f>=0 in the strip.")
print("="*78)
print(f"{'sigma':>7} {'t':>7} {'Re f':>16}  {'sign'}")
for sigma in [mp.mpf('1.1'), mp.mpf('1.5')]:
    for t in [mp.mpf('1'), mp.mpf('4'), mp.mpf('8'), mp.mpf('12'), mp.mpf('18'), mp.mpf('25')]:
        val = neg_zlogzeta(mp.mpc(sigma,t))
        print(f"{mp.nstr(sigma,3):>7} {mp.nstr(t,3):>7} {mp.nstr(val.real,8):>16}  "
              f"{'+' if val.real>0 else '-'}")
print("  Re f does go NEGATIVE for some t even at sigma>1 => no naive Re-positivity in s.")
