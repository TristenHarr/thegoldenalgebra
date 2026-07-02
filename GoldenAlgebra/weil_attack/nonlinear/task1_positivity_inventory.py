"""
TASK 1: Positivity inventory BEFORE vs AFTER log-differentiation.

For a Dirichlet series  F(s)=sum_n a(n) n^{-s}  with a(n)>=0 (n>=1, a(1) may be 0),
on sigma>sigma_abs we have TWO equivalent positivity facts:

  (CM)  For fixed t, sigma -> F(sigma) (a(n) real>=0) is COMPLETELY MONOTONE on (sigma_abs,inf):
          (-1)^k F^{(k)}(sigma) = sum a(n)(log n)^k n^{-sigma} >= 0.
        <=> F(sigma) is the Laplace transform of a positive measure (mu = sum a(n) delta_{log n}).
  (PD)  For fixed sigma, t -> F(sigma+it) = sum a(n)n^{-sigma} e^{-it log n} is POSITIVE-DEFINITE
          (Bochner): it is the Fourier transform of the positive measure sum a(n)n^{-sigma} delta_{log n}.
        => the Toeplitz/Gram matrix [F(sigma+i(t_j-t_k))]_{jk} is PSD.

We test (PD) numerically (cleanest) for each object via the Gram matrix being PSD, and (CM)
via the alternating-sign-of-derivatives / Laplace representation, for:
  (a) zeta(s) itself                         a(n)=1 >=0   => PD/CM on sigma>1
  (b) log zeta(s)=sum_{p,k} 1/k p^{-ks}      coeffs >=0   => PD/CM on sigma>1
  (c) -zeta'/zeta=sum Lambda(n)n^{-s}        Lambda(n)>=0 => PD/CM on sigma>1
  (d) zeta'/zeta = -(c)                       coeffs <=0   => -PD (anti), CM with flipped sign
  (e) xi'/xi (completed)                      NO Dirichlet series with one sign (Gamma added)

KEY QUESTION: do (a),(b),(c) ALL have PD on sigma>1, and does any of them have a BETTER
continuation (PD persisting as sigma -> 1 and into the strip) than the others?
"""
import mpmath as mp
import numpy as np
mp.mp.dps = 30

def gram_min_eig(fn, sigma, ts):
    """Min eigenvalue of Hermitian Toeplitz Gram [fn(sigma+i(t_j-t_k))]. PD => >= -eps."""
    n = len(ts)
    M = np.zeros((n, n), dtype=complex)
    for j in range(n):
        for k in range(n):
            val = fn(mp.mpf(sigma) + 1j*(ts[j]-ts[k]))
            M[j, k] = complex(val)
    M = (M + M.conj().T)/2
    return np.linalg.eigvalsh(M).min()

# Objects as functions of s (complex)
def f_zeta(s):      return mp.zeta(s)
def f_logzeta(s):   return mp.log(mp.zeta(s))
def f_negzp(s):     # -zeta'/zeta
    return -mp.zeta(s, derivative=1)/mp.zeta(s)
def f_poszp(s):     # +zeta'/zeta
    return mp.zeta(s, derivative=1)/mp.zeta(s)

# xi'/xi via xi(s)=1/2 s(s-1) pi^{-s/2} Gamma(s/2) zeta(s)
def f_logxi_deriv(s):
    # d/ds log xi = 1/s + 1/(s-1) - (1/2)log pi + (1/2)psi(s/2) + zeta'/zeta
    return 1/s + 1/(s-1) - 0.5*mp.log(mp.pi) + 0.5*mp.digamma(s/2) + mp.zeta(s,derivative=1)/mp.zeta(s)

objs = [
    ("(a) zeta",        f_zeta),
    ("(b) log zeta",    f_logzeta),
    ("(c) -zeta'/zeta", f_negzp),
    ("(d) +zeta'/zeta", f_poszp),
    ("(e) xi'/xi",      f_logxi_deriv),
]

ts = [0.0, 0.5, 1.1, 1.9, 2.7, 3.4]
print("PD TEST: min eig of Hermitian Gram [F(sigma + i(t_j-t_k))]. PD <=> min eig >= 0.")
print("(positive-Dirichlet-coeff objects must be PD for sigma > sigma_abs=1)\n")
hdr = f"{'object':>16} | " + " ".join(f"sig={sg:>5.2f}" for sg in [3.0,2.0,1.5,1.2,1.05,0.9,0.7,0.5])
print(hdr)
sigmas = [3.0, 2.0, 1.5, 1.2, 1.05, 0.9, 0.7, 0.5]
for name, fn in objs:
    row = f"{name:>16} | "
    for sg in sigmas:
        try:
            me = gram_min_eig(fn, sg, ts)
            tag = "+" if me > -1e-9 else "-"
            row += f"{me:+9.2e}".replace("e","e")[:9].rjust(9) + " "
        except Exception as ex:
            row += "   ERR   "
    print(row)
print()
print("Legend: positive min-eig => Gram PSD => F is PD in t at that sigma (Bochner, positive spectral measure).")
print("Watch the sigma=1 pole crossing: where does PD die for each object?")
