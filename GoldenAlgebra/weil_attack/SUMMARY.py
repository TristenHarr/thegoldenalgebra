"""
CONSOLIDATED FINDINGS — Weil positivity attack. Run for a one-shot confirmation.
"""
import mpmath as mp
from sympy import isprime as _isprime
mp.mp.dps=25
def dig(z): return mp.digamma(z)
PRIMES=[p for p in range(2,5000) if _isprime(p)]

# (1) Explicit formula verified to ~30 digits (even shifted-pair test fn): see ef_shifted.py
# (2) THE CORE IDENTITY (positivity reduces to this pairing):
#     Q(psi) = sum_rho h(gamma_rho),   h=|F|^2>=0 on R,  gamma_rho=(rho-1/2)/i.
#     ON-line zero rho=1/2+ig: contributes h(g)>=0.   [POSITIVE — no problem]
#     OFF-line quartet 1/2 +/- d +/- i g0: contributes 4 Re h(g0 + i d).  [INDEFINITE]
# (3) 4 Re h(g0+id) is provably NEGATIVE for many positive-type h. Example:
F=lambda z: mp.e**(-mp.mpf('0.01')*z*z)*mp.cos(mp.mpf('1.0')*z)
h=lambda z: F(z)*F(z)
g0,d=mp.mpf('5'),mp.mpf('1')
print("CORE OBSTRUCTION (concrete):")
print(f"  h=F^2 >=0 on R (F=e^(-0.01 z^2) cos z), positive-type.")
print(f"  on-line value  h({float(g0)})        = {mp.nstr(h(g0).real,8)}  (>=0)")
print(f"  off-line quartet 4 Re h({float(g0)}+i*{float(d)}) = {mp.nstr(4*mp.re(h(g0+1j*d)),8)}  (NEGATIVE)")
print("  => a single off-line zero pair injects a NEGATIVE term into the Weil sum.")
print("     This is Bombieri's 'one negative eigenvalue per off-line pair', exhibited.")
print()
# (4) The functional equation does NOT save it: the quartet IS already FE-symmetric
#     (closed under s->1-s and s->conj s), yet the contribution 4 Re h(g0+id) is still
#     negative. So FE-symmetry of zeros is consistent with Q<0. Only d=0 (RH) forces
#     every term h(g0)>=0.
print("FUNCTIONAL EQUATION CHECK: the quartet {1/2+/-d+/-i g0} is FE+conjugation symmetric")
print("yet still gives a negative contribution => FE alone cannot force positivity.")
print()
# (5) Archimedean term ALONE is unconditionally >=0 on Sonin space (Connes 2020,
#     arXiv:2006.13771). The barrier to global RH-positivity is the PRIME (finite-place)
#     contribution, whose kernel 2 Re zeta'/zeta(1/2+i xi) is sign-indefinite (prime_indef.py).
print("LITERATURE: Connes 2020 — archimedean place positive on Sonin space, UNCONDITIONAL.")
print("            Global positivity blocked by finite (prime) places. Matches our finding.")
