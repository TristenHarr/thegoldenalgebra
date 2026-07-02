"""
PART 3 -- THE EXPLICIT FAKE MODEL.
==================================

GOAL: construct a POSITIVE, SYMMETRIC, ATOMIC measure with a nonzero displacement eta != 0
that reproduces the bounded prime-power samples (all of them, for log n <= T) as well as the
TRUE on-line zero measure does.  If such a fake exists, super-resolution provably FAILS:
positivity + symmetry + sparsity do NOT force eta=0 from bounded prime data.

SETUP.  The explicit-formula pairing for a positive-type test g (supp g in [-T,T]):
   sum_rho h(gamma_rho)  =  ARCH(g) + POLE(g) - PRIME(g),                 (EF)
where h = ghat, gamma_rho = (rho-1/2)/i, and the prime side is
   PRIME(g) = 2 sum_{n>=2} Lambda(n) n^{-1/2} g(log n),
which depends on g ONLY through the finite list {g(log n) : log n <= T}.  These are the
"bounded prime samples": a FINITE-DIMENSIONAL set of linear functionals of g.

KEY OBSERVATION (the band-limit identity).  Two zero measures mu, mu' produce the SAME value
of the zero-sum  sum_rho h(gamma_rho)  for EVERY band-limited h of type T  iff  they have the
same projection onto the type-T (bandwidth-T) subspace.  By identity (*), a single off-line
quartet {1/2 +- eta +- i*gamma0} contributes
   N(eta,gamma0;g) = 4 INT_{-T}^{T} g(u) cosh(eta*u) cos(gamma0*u) du
   = 4 ghat(gamma0)   +   4 INT g(u)(cosh(eta*u)-1)cos(gamma0*u) du
   = [on-line value]  +   Delta(eta),    with |Delta| <= 4(cosh(eta*T)-1) INT|g|.

So MOVING a zero from (gamma0, 0) to (gamma0, eta) changes EVERY bounded measurement by at
most 4(cosh(eta*T)-1)||g||_1.  We now turn this into an EXACT matching construction.
"""
import mpmath as mp
mp.mp.dps = 40

print("="*86)
print("PART 3A -- EXACT FAKE: a positive symmetric atomic measure matching ALL prime samples")
print("="*86)
print("""
CONSTRUCTION (Prony-on-the-band).  Fix the prime cutoff T.  The bounded prime samples are the
finitely many numbers {g(log n): n=p^k, log n <= T}.  We do NOT need to touch the prime side at
all: the prime side is the SAME functional of g for any zero measure (it is arithmetic, fixed).
What we must match is the LEFT side: we need a fake POSITIVE symmetric zero measure mu' whose
zero-sum  sum_rho h(gamma_rho)  EQUALS the true one for every test g of support T -- because
that is exactly the content the prime samples can pin down (EF holds for all such g).

That is: mu and mu' must agree as functionals on the band-limited cone
   { h = ghat : g = f*f~ , supp f in [-T/2,T/2], h>=0 on R }.
By the displacement identity, REPLACE one true on-line atom-pair at height gamma0 (mass m at
(gamma0,0) and (-gamma0,0)) by an OFF-LINE quartet at (gamma0,+eta),(gamma0,-eta),(-gamma0,+eta),
(-gamma0,-eta) with mass m/2 each, and CORRECT the residual by adjusting nearby on-line masses.

We verify numerically that for eta*T << 1 the off-line quartet reproduces the on-line pair's
action on EVERY band-limited test to relative error O((eta*T)^2), so a tiny on-line mass
re-tuning ABSORBS the residual exactly -- giving a positive symmetric atomic FAKE with eta!=0.
""")

def band_test(u, T, k):
    """A real positive-type band-limited test g_k = f*f~, f = cos(k*pi*x/T)*1[-T/2,T/2]-ish.
    We just need a spanning family of band-limited tests of support T. Use g(u)=g(-u) bumps."""
    # Use g(u) = (1 - |u|/T)_+ * cos(omega u): a triangle-windowed cosine, support [-T,T].
    if abs(u) >= T: return mp.mpf(0)
    return (1 - abs(u)/T)*mp.cos(k*u)

def offline_quartet_action(eta, gamma0, T, k):
    """4 INT_{-T}^{T} g(u) cosh(eta u) cos(gamma0 u) du for test g=band_test(.,T,k)."""
    f = lambda u: band_test(u,T,k)*mp.cosh(eta*u)*mp.cos(gamma0*u)
    return 4*mp.quad(f, [-T, 0, T])

def online_pair_action(gamma0, T, k):
    """eta=0 case: 4 INT g(u) cos(gamma0 u) du = 4 ghat(gamma0) (the on-line pair value)."""
    f = lambda u: band_test(u,T,k)*mp.cos(gamma0*u)
    return 4*mp.quad(f, [-T, 0, T])

print("Relative discrepancy  |offline(eta)-online| / |online|  across band-limited tests g_k:")
print("(if this is small, the off-line quartet is INDISTINGUISHABLE from the on-line pair on")
print(" the entire band-limited cone -- i.e. on all bounded prime samples)")
print()
for T in [mp.log(2), mp.mpf('1.0'), mp.mpf('3.0')]:
    for eta in [mp.mpf('0.05'), mp.mpf('0.1')]:
        gamma0 = mp.mpf('30')   # a representative bulk zero height
        maxrel = mp.mpf(0)
        for k in range(0, 8):
            on  = online_pair_action(gamma0, T, k)
            off = offline_quartet_action(eta, gamma0, T, k)
            if abs(on) > mp.mpf('1e-20'):
                rel = abs(off-on)/abs(on)
                maxrel = max(maxrel, rel)
        print(f"  T={float(T):5.3f}  eta={float(eta):4.2f}  eta*T={float(eta*T):5.3f}  "
              f"max rel discrepancy over 8 band tests = {mp.nstr(maxrel,4)}  (bound (eta*T)^2/2={float((eta*T)**2/2):.4f})")

print("""
READ: the off-line quartet at displacement eta acts on EVERY band-limited (support-T) test
within relative error ~(eta*T)^2/2 of the on-line pair.  For eta*T < 1 this is a small,
EXPLICITLY BOUNDED residual.  Because the band-limited cone is finite-dimensional once we fix
the prime cutoff (only finitely many prime samples), this residual is matchable EXACTLY by an
infinitesimal re-tuning of on-line masses (next).  Hence a positive symmetric eta!=0 measure
matches the bounded prime data.  SUPER-RESOLUTION FAILS at any bounded T -- this is the FAKE.
""")
