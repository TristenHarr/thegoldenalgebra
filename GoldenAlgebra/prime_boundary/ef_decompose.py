"""
ef_decompose.py
================
SERIOUS test: can the PRIME side (explicit formula / Euler product) control the
TOP boundary G(x+iY) >= 0 of the harmonic max-principle reformulation?

Setup (matching ScratchMaxPrinciple.lean):
  Lambda[Xi](z) = (Xi'/Xi)(z),  G(z) = -Im( Xi'/Xi )(z), harmonic off zeros.
  Anti-Herglotz on UHP  <=>  G >= 0 on Im z > 0.
  Top edge at height Y:  TopBoundaryPositive(Y) := for all x, G(x+iY) >= 0.

We work in the CLASSICAL s-plane with the Riemann xi, then translate.  The
pullback Xi in rh.lean makes the critical line the real axis; a height Y in the
z-plane corresponds to moving off the critical line by Y in the s-plane.

For the actual ARITHMETIC content we must use zeta, because xi has no Euler
product / prime sum; only zeta does.  The bridge:

  xi(s) = (1/2) s (s-1) pi^{-s/2} Gamma(s/2) zeta(s)
  => xi'/xi (s) = [1/s + 1/(s-1)] + [-1/2 log pi + 1/2 psi(s/2)] + zeta'/zeta (s)
                = ARCHIMEDEAN(s)                                  + zeta'/zeta(s)

and for Re(s) > 1:   zeta'/zeta(s) = - Sum_n Lambda(n) n^{-s}   (PRIME SUM).

So on a vertical line Re(s)=sigma>1 (which is the region where the prime sum
converges), we can split
   -Im( xi'/xi (s) ) = -Im(ARCH(s)) + Im( Sum_n Lambda(n) n^{-s} ).

The 'top edge' of the strip in the z-geometry is a HORIZONTAL line at height Y.
In the s-geometry, Xi(z) = xi(1/2 + i z) (the standard critical-line pullback,
up to rh.lean's exact normalization).  Then a point z = x + iY maps to
   s = 1/2 + i(x + iY) = (1/2 - Y) + i x.
So Im z = Y  <=>  Re s = 1/2 - Y :  a VERTICAL line in the s-plane at abscissa
sigma = 1/2 - Y.  The top edge going UP (Y increasing) moves the abscissa sigma
to the LEFT (sigma = 1/2 - Y decreasing below 1/2).

CRITICAL OBSERVATION to test: the prime sum Sum Lambda(n) n^{-s} converges only
for Re s > 1, i.e. sigma > 1, i.e. Y < -1/2.  But the top edge with Y>0 sits at
sigma = 1/2 - Y < 1/2 < 1: DEEP inside the critical strip, where the Dirichlet
series DIVERGES.  So the prime sum is NOT directly available on the top edge.

This script measures, numerically and honestly:
  (A) G(x+iY) via xi'/xi directly (ground truth, all Y).
  (B) the archimedean (Gamma) part of G on the top edge.
  (C) whether the prime sum, where it converges (sigma>1, i.e. the BOTTOM / Y<0
      direction), is sign-definite in the way the task hypothesizes.
  (D) what happens to G on the top edge near/below the first zero ordinate.
"""
import mpmath as mp
mp.mp.dps = 30

# ---- xi and its log-derivative (ground truth, valid everywhere) ----
def xi(s):
    return mp.mpf('0.5') * s * (s - 1) * mp.pi**(-s/2) * mp.gamma(s/2) * mp.zeta(s)

def xi_logderiv(s):
    # xi'/xi (s) via component decomposition (avoids differentiating zeta directly badly)
    # xi'/xi = 1/s + 1/(s-1) - 1/2 log pi + 1/2 psi(s/2) + zeta'/zeta(s)
    h = mp.mpf('1e-12')
    # zeta'/zeta via numerical derivative of log zeta (zeta nonzero here)
    zlog = lambda t: mp.log(mp.zeta(t))
    zld = mp.diff(zlog, s)
    arch = 1/s + 1/(s-1) - mp.mpf('0.5')*mp.log(mp.pi) + mp.mpf('0.5')*mp.digamma(s/2)
    return arch, zld, arch + zld

# Pullback geometry: Xi(z) = xi(1/2 - i z).  An off-line zero s=beta+i*gamma with
# beta>1/2 maps to z with Im z = beta-1/2 > 0, putting it in the UHP, matching
# rh.lean's convention that UHP <-> right-of-critical-line (Re s > 1/2).
#   s = 1/2 - i z  =>  z = i(s - 1/2),  Im z = Re s - 1/2.
# (Xi'/Xi)(z) = -i * (xi'/xi)(1/2 - i z).
def Lambda_Xi(z):
    s = mp.mpf('0.5') - 1j*z
    _, _, xld = xi_logderiv(s)
    return -1j * xld

def G(z):
    return -(Lambda_Xi(z)).imag

# archimedean-only G (drop zeta'/zeta entirely)
def G_arch(z):
    s = mp.mpf('0.5') - 1j*z
    arch, _, _ = xi_logderiv(s)
    return -(-1j*arch).imag

# prime-sum-only contribution to G, when it converges (sigma>1)
def G_prime_via_dirichlet(z, N=20000):
    # contribution of zeta'/zeta to G:  -Im( -i * zeta'/zeta(s) ),
    # with zeta'/zeta(s) = - Sum Lambda(n) n^{-s}  (Re s > 1).
    s = mp.mpf('0.5') - 1j*z
    total = mp.mpc(0)
    for n in range(2, N+1):
        Ln = mangoldt(n)
        if Ln != 0:
            total += Ln * mp.e**(-s*mp.log(n))
    zld = -total   # zeta'/zeta
    return -(-1j*zld).imag

# von Mangoldt
_mang_cache = {}
def mangoldt(n):
    if n in _mang_cache: return _mang_cache[n]
    f = mp.mpf(0)
    m = n; p = 2; isprimepow = False; base = None
    # factor
    fac = {}
    mm = n; d = 2
    while d*d <= mm:
        while mm % d == 0:
            fac[d] = fac.get(d,0)+1; mm//=d
        d+=1
    if mm>1: fac[mm]=fac.get(mm,0)+1
    if len(fac)==1:
        p = list(fac.keys())[0]
        f = mp.log(p)
    _mang_cache[n]=f
    return f

if __name__ == "__main__":
    # first nontrivial zero ordinate
    gamma1 = mp.mpf('14.134725141734693790')
    print("=== GROUND TRUTH: G(x+iY) on horizontal lines (top edges) ===")
    print("z-plane Im z = Y  <->  s-plane Re s = 1/2 + Y")
    for Y in [0.1, 0.5, 1.0, 5.0, 10.0, 13.0, 14.0, 14.5]:
        vals = []
        for x in [0.5, 2.0, 5.0, 10.0, 13.0, 14.134725, 16.0, 20.0]:
            z = mp.mpf(x) + 1j*mp.mpf(Y)
            try:
                vals.append(float(G(z)))
            except Exception as e:
                vals.append(float('nan'))
        sigma = 0.5 + Y
        mn = min(vals)
        print(f"Y={Y:5.2f} (sigma={sigma:6.2f})  min_x G = {mn:+.4f}   sample G@x=14.13: {vals[5]:+.4f}")
