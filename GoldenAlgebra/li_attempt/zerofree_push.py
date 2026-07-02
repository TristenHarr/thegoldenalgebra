"""
THE ONLY GENUINE UNCONDITIONAL ROUTE: can a zero-free region force lambda_n>=0
for n >= N, leaving finitely many to check?

Setup. lambda_n = Sbar_n + S_n.
 Sbar_n >= c1 * n log n  (c1 = 1/2) for n>=N0, unconditional, POSITIVE.
 We need: |S_n| < Sbar_n for all large n, UNCONDITIONALLY.

A zero rho=beta+i*gamma contributes to S_n a pair term of modulus ~ M(rho)^n where
   M(rho) = max(|1-1/rho|, |1-1/(1-rho)|).
For beta in [1/2, 1], with t=Im:
   |1-1/rho|^2 = ((beta-1)^2+t^2)/(beta^2+t^2).
   The mirror (beta'=1-beta) gives the >1 factor:
   M(rho) = sqrt((beta^2+t^2)/((1-beta)^2+t^2))   when beta>1/2.
Let's see how big M is, and CRUCIALLY whether the GROWTH RATE q=sup_rho M(rho)
can be < 1 + (something) so that q^n is beaten by the n log n archimedean term.

KEY OBSTRUCTION: there are INFINITELY many zeros, all with M>=1 (=1 exactly on line).
If even ONE zero has beta>1/2, M(rho)>1 strictly => M^n beats n log n => lambda_n
oscillates with exp growth (Voros). So a fixed zero-free region (de la Vallee Poussin:
beta < 1 - c/log t) does NOT give M<1 -- it bounds beta AWAY from 1 but NOT away
from 1/2.  The relevant question for Li positivity is beta<=1/2, which is RH itself.

Quantify: for a zero just inside the classical zero-free region (beta = 1 - c/log t),
M(rho) ~ ?  Show it's still >1 (exp growth), i.e. zero-free region is USELESS for Li.
"""
import math

def M(beta, t):
    a = ((beta-1)**2 + t*t)/(beta*beta + t*t)   # |1-1/rho|^2
    a = math.sqrt(a)
    b = beta if False else None
    # mirror
    bm = 1-beta
    am = math.sqrt(((bm-1)**2 + t*t)/(bm*bm + t*t))
    return max(a, am)

print("How large is the per-zero growth base M(rho), for zeros at the EDGE of the")
print("classical zero-free region beta = 1 - c/log t  (c=1, de la Vallee Poussin scale)?\n")
print("   t      beta_edge     M(rho)        M^n at n=1000 (log10)")
for t in [50, 100, 1000, 1e4, 1e6, 1e9]:
    beta = 1 - 1.0/math.log(t)
    m = M(beta, t)
    log10_pow = 1000*math.log10(m)
    print(f"{t:>8.0f}  {beta:.6f}   {m:.8f}    {log10_pow:+.3f}")

print("\n--- If RH-violating zero is at beta=1/2+delta (just off line) ---")
print("  delta      t        M(rho)       n needed for M^n=10 (detection scale)")
for delta in [1e-1, 1e-3, 1e-6, 1e-9]:
    t = 1e3
    m = M(0.5+delta, t)
    if m>1:
        nneed = math.log(10)/math.log(m)
    else:
        nneed = float('inf')
    print(f"  {delta:.0e}   {t:.0e}   {m:.12f}   n~{nneed:.3e}")

print("""
CONCLUSION OF THE PUSH:
 * The archimedean main term Sbar_n ~ (n/2) log n is POSITIVE & unconditional.
 * BUT a single off-line zero (beta=1/2+delta) gives a term ~ M^n with M>1, which
   EVENTUALLY (n ~ log(.)/log M ~ 1/delta times a log) overwhelms n log n.
 * A classical zero-free region bounds beta away from 1, NOT away from 1/2; at the
   edge beta=1-c/log t, M(rho) is STILL >1, so it does NOT yield M<1.
 * Therefore NO known zero-free region forces |S_n| < Sbar_n for all large n.
 * The remainder S_n is exactly the object whose unconditional control IS RH.
 ==> The 'finitely many to check' strategy CANNOT close unconditionally: the bad n
     (if a zero is at height t) is around n ~ t/delta -> infinity as delta->0, i.e.
     there is no finite N independent of the (unknown) off-line zeros.
""")
