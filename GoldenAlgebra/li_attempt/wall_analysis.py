"""
THE WALL: quantify the unconditional decomposition and why positivity is NOT
unconditionally forced.

lambda_n = Sbar_n + S_n   (Voros eq 20/21).

Sbar_n (archimedean, UNCONDITIONAL all-orders asymptotic, eq 24):
   Sbar_n ~ (n/2)(log n + gamma - 1 - log 2pi) + 3/4 - sum_k B_{2k}/(4k) n^{1-2k}.
   ==> POSITIVE and ~ (n/2) log n  for n>=N0, UNCONDITIONALLY.  We find N0.

S_n (arithmetic): 
   [RH true]  S_n = o(n).
   [RH false] S_n ~ sum_{arg tau_k>0} ((tau_k + i/2)/(tau_k - i/2))^n + c.c.  (eq 26)
       A SINGLE off-line zero rho=beta+i*gamma (beta!=1/2) gives a term of modulus
       |z|^n where, for the pair, the relevant ratio has modulus = 
            |1-1/rho|  with rho the off-line zero (Re>1/2 side picks |.|<1, but the
            functional-equation partner on Re<1/2 gives |.|>1).
   Precisely: off-line zero at beta>1/2 has |1-1/rho|<1 (decaying), but its
   mirror 1-rho has beta'<1/2 with |1-1/(1-rho)|>1 (GROWING). So |S_n| ~ q^n,
   q = max over off-line zeros of |1 - 1/(1-rho)| = |rho|/|1-rho| ... let's just
   compute |1-1/rho| for a HYPOTHETICAL off-line zero and show it exceeds 1.
"""
import mpmath as mp, math
mp.mp.dps = 40
gamma = float(mp.euler)

# ---- Sbar_n unconditional asymptotic, find when it becomes positive & dominant
def Sbar_asym(n, K=8):
    val = 0.5*n*(math.log(n) + gamma - 1 - math.log(2*math.pi)) + 0.75
    nn = float(n)
    for k in range(1, K+1):
        B = float(mp.bernoulli(2*k))
        val -= B/(4*k) * nn**(1-2*k)
    return val

print("=== Archimedean part Sbar_n (UNCONDITIONAL asymptotic) ===")
print("  n |   Sbar_asym(n)   |  (n/2)log n")
for n in [1,2,3,4,5,6,7,8,10,20,50,100,1000]:
    print(f"{n:5d} | {Sbar_asym(n):14.6f} | {0.5*n*math.log(n) if n>0 else 0:12.4f}")

# zero crossing of the smooth trend (n/2)(log n + gamma-1-log2pi):
# positive when log n > 1 + log2pi - gamma  => n > exp(1+log2pi-gamma)
nstar = math.exp(1 + math.log(2*math.pi) - gamma)
print(f"\nSmooth archimedean trend (n/2)(log n+gamma-1-log2pi) > 0  <=>  n > {nstar:.4f}")
print(" => for n>=10 the archimedean part is positive and growing ~ (n/2)log n, UNCONDITIONALLY.")

# ---- A single OFF-LINE zero: contribution modulus ----
print("\n=== Off-line zero contribution modulus  |1-1/rho| and |1-1/(1-rho)| ===")
print(" (if any beta != 1/2, one of the mirror pair has modulus > 1 => exp growth)")
for beta in [0.5, 0.51, 0.55, 0.6, 0.7, 0.9]:
    t = 100.0
    rho = complex(beta, t)
    one = complex(1,0)
    w1 = abs(one - one/rho)
    rhom = complex(1-beta, t)   # functional-eq mirror 1-rho (same t by symmetry of zeros)
    w2 = abs(one - one/rhom)
    print(f" beta={beta:4.2f} t={t}:  |1-1/rho|={w1:.8f}   |1-1/(1-rho)|={w2:.8f}   max={max(w1,w2):.8f}")

print("\nNOTE: beta=1/2 gives EXACTLY 1.0 for both (the marginal case).")
print("Any beta>1/2 makes the mirror modulus >1  => term grows like q^n, q>1 => lambda_n -> +-infinity.")
