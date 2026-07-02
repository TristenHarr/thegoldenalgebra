"""
Compute Li/Keiper coefficients lambda_n via the zeta-zero sum:
   lambda_n = sum_rho [ 1 - (1 - 1/rho)^n ]   (paired rho, rho-bar => real)
We use mpmath's zetazero to get the imaginary parts of the nontrivial zeros
(on the critical line; unconditionally these are the zeros with 0<Re<1 and
the first ~10^13 are known on the line). For a numerical study we use t_k.

This is the UNCONDITIONAL COMPUTATION of the lambda_n (the values are
unconditional; positivity for all n is RH).
"""
import mpmath as mp
mp.mp.dps = 40

# number of zeros and max n
NZ = 2000   # zeros (pairs)
NMAX = 400  # lambda_n up to here

# get zeros rho = 1/2 + i t_k
print("computing zeros...")
ts = []
for k in range(1, NZ+1):
    ts.append(mp.zetazero(k).imag)
    if k % 200 == 0:
        print("  zero", k)

rhos = [mp.mpf('0.5') + 1j*t for t in ts]

# lambda_n = sum over rho and conjugate of [1 - (1-1/rho)^n]
# pairing rho and conj(rho): contribution is 2*Re(1 - (1-1/rho)^n)
print("summing lambda_n...")
lam = []
for n in range(1, NMAX+1):
    s = mp.mpf(0)
    for rho in rhos:
        w = 1 - 1/rho
        term = 1 - w**n
        s += 2*term.real   # rho and conjugate
    lam.append(s)
    if n % 50 == 0:
        print("  n", n, "lambda_n approx", mp.nstr(s, 8))

# save
with open("lambda_zerosum.txt","w") as f:
    for n,v in enumerate(lam, start=1):
        f.write(f"{n}\t{mp.nstr(v,20)}\n")
print("done. min lambda:", mp.nstr(min(lam),10))
