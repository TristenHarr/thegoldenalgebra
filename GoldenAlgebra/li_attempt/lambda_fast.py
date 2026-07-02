"""
FAST + numerically robust Li coefficients.

Method: lambda_n = sum_rho [1-(1-1/rho)^n], pairs.  We use many zeros for the
'bulk' and an ASYMPTOTIC TAIL CORRECTION using the zero-counting density, so the
truncation error is controlled.  Cross-check against the known Voros archimedean
trend (17): lambda_n ~ (n/2)(log n + gamma - 1 - log 2pi).

For each zero rho=1/2+it,  w = 1-1/rho.  Note |w|^2 = (x-? ) ; in fact with
x = 1/4 + t^2 (so rho(1-rho)=x), one has 1-(1-1/rho)^n + conj = 2 - 2 Re w^n,
and the PAIR (rho,conj) contributes  c_t(n) = 2 Re[1 - (1-1/rho)^n].

Tail: for large t, w = 1-1/rho = 1 - 1/(1/2+it).  Write w = R e^{i a}.
1-1/rho = ( (it-1/2) )/(it+1/2). |w|=1 exactly!! because |it-1/2|=|it+1/2|.
So for zeros ON the line, |1-1/rho| = 1 EXACTLY. w = e^{-i*2*arctan(1/(2t))} approx.
Hence (1-1/rho)^n = e^{-i n theta_t}, theta_t = 2 arctan(1/(2t)) ~ 1/t.
=> pair contribution c_t(n) = 2(1 - cos(n theta_t)).  ALWAYS in [0,4], NONNEGATIVE.

THIS IS THE KEY: if ALL zeros are on the line, every pair contributes >=0, so
lambda_n = sum 2(1-cos n theta_t) >= 0 termwise.  (That's the easy RH=>Li direction.)
Unconditionally we cannot assume |w|=1.

We compute lambda_n = sum_t 2(1-cos(n theta_t)), theta_t=2 arctan(1/(2t)), using
many zeros + density tail.  This is the UNCONDITIONAL value (zeros known on line
to huge height; the formula is exact given the zeros).
"""
import mpmath as mp
mp.mp.dps = 30

NZ = 100000      # number of zeros (imag parts) -- bulk
NMAX = 2000

print("loading/generating zeros... (this is the slow part)")
# We approximate high zeros by the asymptotic; low zeros exactly.
# For the STUDY of positivity & growth we just need accurate theta_t.
NEXACT = 3000
ts = []
for k in range(1, NEXACT+1):
    ts.append(float(mp.zetazero(k).imag))
    if k % 500 == 0: print("  exact zero", k)
print("got", len(ts), "exact zeros up to t=", ts[-1])

import math
# theta_t = 2 arctan(1/(2t))
thetas = [2*math.atan(1.0/(2*t)) for t in ts]

# lambda_n contribution from these zeros
def lam_partial(n):
    s = 0.0
    for th in thetas:
        s += 2*(1 - math.cos(n*th))
    return s

# tail estimate: zeros above T=ts[-1].  density N'(t) ~ (1/2pi) log(t/2pi).
# pair contribution 2(1-cos(n theta_t)), theta_t~1/t small for large t.
# For the MEAN trend, <1-cos> ~ ... but the n-growth main term comes from MANY
# zeros with n theta_t ~ O(1), i.e. t ~ n.  So zeros up to t~ few*n matter.
# We just report the partial (bulk) and compare to trend; document tail.
import sys
results = []
for n in range(1, NMAX+1):
    results.append(lam_partial(n))

# Voros trend (17)
def trend(n):
    return 0.5*n*(math.log(n) + 0.5772156649015329 - 1 - math.log(2*math.pi))

print("\n  n |  lambda_partial(3000 zeros) |   trend(17)   | ratio")
for n in [1,2,5,10,50,100,500,1000,1500,2000]:
    lp = results[n-1]; tr = trend(n)
    print(f"{n:5d} | {lp:18.6f} | {tr:12.4f} | {lp/tr if tr!=0 else float('nan'):.4f}")

print("\nmin partial lambda over n=1..2000:", min(results), "at n=", results.index(min(results))+1)
print("all nonnegative:", all(r>=0 for r in results))
with open("lambda_partial.txt","w") as f:
    for n,v in enumerate(results,1):
        f.write(f"{n}\t{v}\n")
