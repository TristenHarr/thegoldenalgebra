"""
MOMENT / HANKEL structural test.

Strategy from the prompt: are the lambda_n a Stieltjes/Hausdorff moment sequence
for a structural reason?  If (lambda_n) were a Hamburger moment sequence, the
Hankel matrices H1=[lambda_{i+j}] and H2=[lambda_{i+j+1}] would be PSD => positivity
would be 'automatic'.  TEST THIS NUMERICALLY -- if it FAILS, that route is dead.

We use the termwise on-line model lambda_n = sum_t 2(1-cos n theta_t) (the true
values modulo tail), n=1..N, build Hankel matrices, check eigenvalue signs.

Also test the *increments* and the binomial/Pascal transform structure:
  lambda_n = sum_{j} (-1)^{j+1} C(n,j) sigma_j   (sigma_j = sum_rho rho^{-j}),
a BINOMIAL TRANSFORM of (sigma_j).  Positivity of a binomial transform is NOT
implied by positivity of sigma_j in general -> test whether sign-preservation
could hold structurally.
"""
import mpmath as mp, math
mp.mp.dps = 30

# load partial lambdas (on-line termwise model, accurate for small/mid n)
lam = []
with open("lambda_partial.txt") as f:
    for line in f:
        a,b = line.split()
        lam.append(float(b))

# 1-indexed: lam[0] = lambda_1
def L(n): return lam[n-1]

# ---- Hankel test (Hamburger moment necessary condition) ----
# Treat lambda_1, lambda_2, ... as moments m_0=lambda_1? We test the raw sequence.
import numpy as np
for K in [4, 6, 8, 10]:
    # H[i,j] = lambda_{i+j+1}, i,j=0..K-1  (needs up to lambda_{2K-1})
    H = np.array([[L(i+j+1) for j in range(K)] for i in range(K)], dtype=float)
    ev = np.linalg.eigvalsh(H)
    print(f"Hankel K={K}: min eig = {ev.min():.4e}  (PSD if >=0)  -> {'PSD' if ev.min()>=-1e-9 else 'NOT PSD'}")

# shifted Hankel (Stieltjes)
print()
for K in [4,6,8,10]:
    H = np.array([[L(i+j+2) for j in range(K)] for i in range(K)], dtype=float)
    ev = np.linalg.eigvalsh(H)
    print(f"Shifted Hankel K={K}: min eig = {ev.min():.4e} -> {'PSD' if ev.min()>=-1e-9 else 'NOT PSD'}")
