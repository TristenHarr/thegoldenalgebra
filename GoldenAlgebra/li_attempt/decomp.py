"""
Voros decomposition  lambda_n = S_n + Sbar_n.

Sbar_n  (archimedean, UNCONDITIONAL closed/asymptotic form, eq 21/24):
   Sbar_n = 1 - ((log 4pi + gamma)/2) n + Shat_n,
   Shat_n = sum_{j=2}^n binom(n,j) (-1)^j (1 - 2^{-j}) zeta(j).
   Asymptotically (eq 24, UNCONDITIONAL, all orders):
   Sbar_n ~ (1/2) n (log n + gamma - 1 - log 2pi) + 3/4 - sum_k B_{2k}/(4k) n^{1-2k}.

S_n (arithmetic, eq 20):
   S_n = - sum_{j=1}^n binom(n,j) eta_{j-1},
   where eta_j are the "Stieltjes cumulants": log[s zeta(1+s)] = - sum_{n>=1} eta_{n-1} s^n / n.
   eta_0 = -gamma.

We compute BOTH exactly (high precision) and compare:
   - Sbar_n vs its unconditional asymptotic (positivity of archimedean part)
   - S_n  (the part that needs RH to stay o(n))
   - lambda_n = S_n + Sbar_n  vs the zero-sum value (cross-check).
"""
import mpmath as mp
mp.mp.dps = 60

NMAX = 400

# ---- Sbar_n exactly via Shat_n (eq 21) ----
# Shat_n = sum_{j=2}^n C(n,j)(-1)^j (1-2^{-j}) zeta(j)
gamma = mp.euler
log4pi = mp.log(4*mp.pi)

# precompute zeta(j)
zetas = {j: mp.zeta(j) for j in range(2, NMAX+1)}

def Sbar(n):
    s = mp.mpf(0)
    for j in range(2, n+1):
        c = mp.binomial(n, j)
        s += c * (-1)**j * (1 - mp.power(2,-j)) * zetas[j]
    return 1 - (log4pi + gamma)/2 * n + s

# unconditional asymptotic (eq 24) up to Bernoulli order K
def Sbar_asym(n, K=6):
    val = mp.mpf('0.5')*n*(mp.log(n) + gamma - 1 - mp.log(2*mp.pi)) + mp.mpf('3')/4
    for k in range(1, K+1):
        val -= mp.bernoulli(2*k)/(4*k) * mp.power(n, 1-2*k)
    return val

# ---- eta_j (Stieltjes cumulants) from log[s zeta(1+s)] ----
# Build Taylor series of g(s)=log(s zeta(1+s)) = log(1 + sum stieltjes...) around s=0.
# s zeta(1+s) = 1 + sum_{m>=0} (-1)^m/m! gamma_m s^{m+1}  (gamma_m Stieltjes)
# We get eta via: g(s) = -sum_{n>=1} eta_{n-1} s^n/n  => eta_{n-1} = -n [s^n] g.
# Use mpmath taylor of the function h(s)= log(s*zeta(1+s)); careful at s=0 (limit=0).
def szeta1p(s):
    if s == 0:
        return mp.mpf(1)
    return s*mp.zeta(1+s)
# taylor of log(szeta1p) ; define f(s)=log(szeta1p(s)), f(0)=0
def f(s):
    if s == 0:
        return mp.mpf(0)
    return mp.log(s*mp.zeta(1+s))

print("computing eta via taylor...")
coeffs = mp.taylor(f, 0, NMAX+2)   # coeffs[n] = [s^n] f
# eta_{n-1} = -n * coeffs[n]
eta = {}
for n in range(1, NMAX+1):
    eta[n-1] = -n*coeffs[n]
print("eta_0 =", mp.nstr(eta[0],15), " (should be -gamma =", mp.nstr(-gamma,15),")")

def S_n(n):
    s = mp.mpf(0)
    for j in range(1, n+1):
        s += mp.binomial(n,j)*eta[j-1]
    return -s

print("\n   n |      Sbar_n      |   Sbar_asym   |     S_n      |  lambda=S+Sbar")
for n in [1,2,5,10,20,50,100,200,300,400]:
    sb = Sbar(n)
    sa = Sbar_asym(n)
    sn = S_n(n)
    lam = sn + sb
    print(f"{n:5d} | {mp.nstr(sb,12):>14} | {mp.nstr(sa,10):>12} | {mp.nstr(sn,8):>12} | {mp.nstr(lam,12)}")

# save lambda from decomposition
with open("lambda_decomp.txt","w") as fout:
    for n in range(1, NMAX+1):
        fout.write(f"{n}\t{mp.nstr(S_n(n)+Sbar(n),25)}\t{mp.nstr(Sbar(n),25)}\t{mp.nstr(S_n(n),25)}\n")
print("saved lambda_decomp.txt")
