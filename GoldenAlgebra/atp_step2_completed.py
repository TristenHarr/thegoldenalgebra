"""
ARITHMETIC TRANSFER PRINCIPLE — STEP 2
=======================================
The COMPLETED logarithmic derivative and the functional-equation symmetry.

xi(s) = (1/2) s(s-1) pi^{-s/2} Gamma(s/2) zeta(s),   xi(s)=xi(1-s).
=>  xi'/xi(s) = -xi'/xi(1-s)      (FE symmetry: ODD about s=1/2).

Hadamard:  xi'/xi(s) = B + sum_rho [ 1/(s-rho) + 1/rho ]   (rho = nontrivial zeros).
Equivalently the standard explicit decomposition of -zeta'/zeta:
   -zeta'/zeta(s) = (1/(s-1)) - (1/2) log pi + (1/2) psi(s/2+1)
                    - sum_rho [1/(s-rho)+1/rho] - ... (trivial-zero terms)
We split:
   -zeta'/zeta(s) = PRIME-SIDE  =  ARCHIMEDEAN(s)  -  ZEROS(s)  -  POLE(s)
   PRIME-SIDE = sum Lambda(n) n^{-s}            (positive measure; CM in sigma)
   ARCH(s)    = (1/2) log pi - (1/2) psi(s/2+1)  [from -d/ds log(pi^{-s/2}Gamma(s/2))-ish]
   ZEROS+POLE = (1/(s-1)) - sum_rho[1/(s-rho)+1/rho] + trivial

GOAL: track positivity (completely-monotone-in-sigma) of the PRIME piece as we
continue from sigma>1 toward sigma=1/2, and locate EXACTLY where the prime-side
representation breaks down.  The prime Dirichlet series  sum Lambda(n) n^{-s}
CONVERGES iff sigma>1; on  1/2 < sigma <= 1  it does NOT converge, so the
"positive measure" representation of -zeta'/zeta literally CEASES TO EXIST as a
convergent object at sigma=1.  The analytic continuation past sigma=1 is NOT a
Laplace transform of a positive measure anymore.

KEY QUESTION (the user's task 2):  As sigma decreases through the strip, does the
loss of the positive-measure representation happen
   (a) at sigma=1  (abscissa of convergence, the POLE), uniformly — a HALF-PLANE wall, or
   (b) exactly at the zeros (sigma = Re rho) — a ZERO-by-ZERO wall (=> RH)?
We test by checking complete-monotonicity of  -zeta'/zeta along REAL sigma in (1/2,1):
the continued function is real-analytic there (no zeros on the real segment), so we
CAN evaluate it; does it stay completely monotone below sigma=1?
"""
import mpmath as mp
mp.mp.dps = 30

f = lambda x: -mp.zeta(x, derivative=1)/mp.zeta(x)

print("="*78)
print("(A) Complete monotonicity of -zeta'/zeta along the REAL segment sigma in (1/2,1)")
print("    The continuation is real-analytic on (-inf,1) except the pole at sigma=1.")
print("    nu>=0 forced CM on (1,inf).  Does CM SURVIVE below sigma=1?")
print("="*78)
print(f"{'sigma':>8} " + " ".join(f"(-1)^{k}f^({k})".rjust(15) for k in range(5)))
for sigma in [mp.mpf('0.95'),mp.mpf('0.85'),mp.mpf('0.75'),mp.mpf('0.6'),mp.mpf('0.55'),mp.mpf('0.51')]:
    row=[((-1)**k)*mp.diff(f,sigma,k) for k in range(5)]
    ok = all(r>=-1e-9 for r in row)
    print(f"{mp.nstr(sigma,4):>8} " + " ".join(mp.nstr(r,5).rjust(15) for r in row)
          + ("  CM-OK" if ok else "  *** CM BROKEN ***"))
print()
print("  Interpretation: the POLE at s=1 dominates near sigma=1 (1/(s-1) is itself CM)")
print("  so CM can persist just below 1.  Watch where the FIRST sign flip occurs.")

print()
print("="*78)
print("(B) The PRIME piece alone, continued: define  P(s) = -zeta'/zeta(s) - 1/(s-1).")
print("    P removes the pole. On Re s>1, P(s) = sum Lambda(n)n^{-s} - 1/(s-1).")
print("    Is the *pole-subtracted* prime side still CM below 1?  (the pole was the")
print("    only manifestly-CM part; this isolates the genuine arithmetic content)")
print("="*78)
P = lambda x: -mp.zeta(x, derivative=1)/mp.zeta(x) - 1/(x-1)
print(f"{'sigma':>8} " + " ".join(f"(-1)^{k}P^({k})".rjust(15) for k in range(5)))
for sigma in [mp.mpf('2.0'),mp.mpf('1.2'),mp.mpf('0.9'),mp.mpf('0.75'),mp.mpf('0.6'),mp.mpf('0.51')]:
    row=[((-1)**k)*mp.diff(P,sigma,k) for k in range(5)]
    ok = all(r>=-1e-9 for r in row)
    print(f"{mp.nstr(sigma,4):>8} " + " ".join(mp.nstr(r,5).rjust(15) for r in row)
          + ("  CM-OK" if ok else "  not-CM"))
print("  NOTE: P = -1/2 log pi + 1/2 psi(s/2+1) - sum_rho[...] - trivial; this is the")
print("  arch + zeros content. CM here is NOT guaranteed by nu>=0.")

print()
print("="*78)
print("(C) ABSCISSA OF CONVERGENCE vs ZEROS — the structural answer to (a) vs (b).")
print("="*78)
print("""
  FACT (unconditional, provable): the Dirichlet series sum Lambda(n) n^{-s} has
  abscissa of CONVERGENCE  sigma_c = 1  (because of the pole of zeta at 1; partial
  sums  psi(x) ~ x).  It does NOT converge anywhere in 1/2<sigma<=1 regardless of RH.

  Therefore the *positive-measure / Laplace-transform* representation of -zeta'/zeta
  is a HALF-PLANE object with a HARD WALL at sigma=1, and that wall is the POLE,
  NOT the zeros.  RH is about the abscissa where the ANALYTIC CONTINUATION is
  pole/zero-free, which is a different (larger) region than convergence.

  CONSEQUENCE: prime-side positive-measure positivity DOES NOT, by itself, continue
  past sigma=1. Any transfer to sigma=1/2 must go through the COMPLETED xi and the
  FE, using the *analytic continuation*, where the 'positive measure' is gone and
  replaced by the Hadamard sum over zeros. The positivity that remains is the
  complete-monotonicity tested in (A)/(B), whose breakdown we now localize.
""")
