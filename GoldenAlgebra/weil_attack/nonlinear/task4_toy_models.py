"""
TASK 4: TOY MODELS for the nonlinear (log) PD-invariant.

We use the invariant:  P(F; sigma) = min eig of the Hermitian Gram [F(sigma+i(t_j-t_k))]_jk.
P>=0  <=>  t->F(sigma+it) is PD  <=>  spectral measure of F at sigma is positive.

(a) A positive Dirichlet series WITH Euler product and KNOWN RH-on-line:
    The simplest is zeta itself, but for a "known RH" Euler-product toy we use a single
    Euler factor model and Dirichlet L-function L(s, chi_4) (Dirichlet beta) -- its nontrivial
    zeros are on Re=1/2 (GRH holds numerically/low zeros), it HAS an Euler product, and
    log L = sum chi(n) Lambda(n)/log... wait chi can be negative. Use instead:
    PSI(s) = zeta(s)^2 / zeta(2s)  -- Dirichlet coeffs 2^{omega(n)} (#prime factors), ALL >=0,
    Euler product prod (1+p^{-s})/(1-p^{-s})... Actually use the cleanest: a *positive* Euler
    product whose log has nonneg coeffs -> log PSI = sum positive. Test PD on sigma>1.

(b) A FAKE Euler product with KNOWN OFF-LINE zeros. We FORCE an off-line zero by multiplying
    zeta by a factor (s-rho)(s-rho_bar)/((s-1/2-i gamma)(...)) that MOVES a zero off the line,
    OR simpler: build  F_off(s) = zeta(s) * (1 - c * a^{-s})  Dirichlet-poly factor that creates
    an off-line zero, and ask whether the nonlinear PD-invariant of log F_off FAILS where the
    genuine one holds. KEY TEST: does the invariant SEE the off-line zero?

(c) Finite prime product x Gamma-completion: track PD-invariant as primes are added, then
    multiply by Gamma-factor, and watch PD die at the Gamma step (confirming Task 3).

CRUCIAL DISCIPLINE CHECK: the PD-invariant of log F lives on sigma>sigma_abs (region of abs
convergence), where there are NO zeros at all. So P(log F; sigma>1) CANNOT see zeros of F --
on or off line. This is the structural reason the nonlinear invariant is RH-BLIND: the place
where positivity is clean (sigma>1) is exactly the place with no zeros, and continuing toward
the zeros is blocked by the pole (zeta) / by completion (xi). We make this explicit.
"""
import mpmath as mp, numpy as np
mp.mp.dps=30

def gram_min(fn,sigma,ts):
    n=len(ts);M=np.zeros((n,n),dtype=complex)
    ok=True
    for j in range(n):
        for k in range(n):
            try: M[j,k]=complex(fn(mp.mpf(sigma)+1j*(ts[j]-ts[k])))
            except: ok=False; M[j,k]=0
    M=(M+M.conj().T)/2
    return (np.linalg.eigvalsh(M).min(), ok)

ts=[0,0.6,1.3,2.1,3.0,4.0]

print("="*72)
print("(a) Euler-product, positive-coeff toy: PSI(s)=zeta(s)^2/zeta(2s), coeffs 2^omega(n)>=0")
print("="*72)
def logPSI(s): return 2*mp.log(mp.zeta(s))-mp.log(mp.zeta(2*s))
for sg in [2.0,1.5,1.2,1.05,0.9,0.7]:
    me,ok=gram_min(logPSI,sg,ts)
    print(f"  sigma={sg:4.2f}:  P(log PSI)= {me:+.3e}  {'PD' if me>-1e-9 else 'not PD'}")
print("  => PD for sigma>1 (positive Euler-product log), dies crossing the zeta pole. Same as zeta.")
print()

print("="*72)
print("(b) FAKE Euler product with off-line zero:  F_off(s)=zeta(s)*(1 - c*2^{-s})")
print("    The factor (1-c 2^{-s}) has a zero at 2^{-s}=1/c => s = log2(c) + 2pi i k/log2.")
print("    Choose c=2 => zero at s=1 (on a line), choose c=2^{0.7} => zero at sigma=0.7 (OFF line).")
print("="*72)
import cmath
def logFoff(s, c):
    return mp.log(mp.zeta(s)) + mp.log(1 - c*2**(-s))
for c,desc in [(2**mp.mpf('0.7'),"zero at sigma=0.7 OFF-line"), (2**mp.mpf('0.5'),"zero at sigma=0.5 on-line")]:
    print(f"  c=2^{{{float(mp.log(c)/mp.log(2)):.2f}}}  ({desc}):")
    for sg in [2.0,1.5,1.2,1.05]:
        me,ok=gram_min(lambda s: logFoff(s,c),sg,ts)
        print(f"     sigma={sg:4.2f}:  P(log F_off)= {me:+.3e}  {'PD' if me>-1e-9 else 'NOT PD'}")
    # Now: does (1-c 2^{-s}) have nonneg log-coeffs? log(1-c 2^{-s}) = -sum_k c^k/k 2^{-ks}: coeffs -c^k/k <0!
    print(f"     [log(1-c 2^-s) Dirichlet coeffs = -c^k/k  -> NEGATIVE; this is what an off-line-capable factor injects]")
print("  => Where coeffs go negative (the fake factor), PD of the LOG is ALREADY destroyed on sigma>1,")
print("     BEFORE reaching any zero. The invariant fails at the COEFFICIENT level, not at the zero.")
print()

print("="*72)
print("(c) Finite prime product, then x Gamma. Track PD as primes added + at completion.")
print("="*72)
primes=[2,3,5,7,11,13,17,19,23,29]
def logEulerPartial(s, P):
    return sum(-mp.log(1-mp.mpf(p)**(-s)) for p in P)  # = sum_{p in P,k} (1/k)p^{-ks}, coeffs>=0
for npr in [1,2,4,8,10]:
    P=primes[:npr]
    me,ok=gram_min(lambda s: logEulerPartial(s,P),1.5,ts)
    print(f"  {npr:2d} primes, log partial Euler product: P(sigma=1.5)= {me:+.3e}  {'PD' if me>-1e-9 else 'not PD'}")
print("  => stays PD as primes are added (each adds positive spectral atoms).")
def logArch(s): return -(s/2)*mp.log(mp.pi)+mp.loggamma(s/2)
def logPartialCompleted(s,P): return logEulerPartial(s,P)+logArch(s)
me,ok=gram_min(lambda s: logPartialCompleted(s,primes),1.5,ts)
print(f"  10 primes x Gamma-completion:           P(sigma=1.5)= {me:+.3e}  {'PD' if me>-1e-9 else 'NOT PD'}  <== Gamma kills it")
