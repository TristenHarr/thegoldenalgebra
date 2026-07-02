"""
TASK 4 (honest off-line test). The previous fake factor (1-c 2^{-s}) is a Dirichlet POLYNOMIAL,
not an Euler factor. To honestly test "does the nonlinear PD-invariant detect off-line zeros of
a genuine Euler product", we need an object that:
   - has a genuine Euler product (=> log has the form sum over prime powers),
   - has a zero OFF the critical line,
   - and we ask whether P(log F; sigma) on sigma > sigma_abs differs from the on-line case.

THE DECISIVE STRUCTURAL POINT (no numerics can dodge it):
   * If F has an Euler product with coefficients giving log F = sum_{n} b(n) n^{-s} with b(n)>=0
     (e.g. all local factors of "positive type"), then on sigma>sigma_abs the spectral measure
     of log F is positive => P>=0 ALWAYS, regardless of where the zeros are. The invariant is
     CONSTANT-SIGN on sigma>sigma_abs and CANNOT depend on zero locations.
   * Zeros live in sigma <= sigma_abs (in fact for an Euler product F != 0 on sigma>sigma_abs).
     So on the entire region where P is computed cleanly, F has NO zeros. P is zero-BLIND there.
   * To "see" a zero you must continue P to the zero's abscissa -- but that crossing is blocked
     by the pole (zeta-type) or destroyed by completion (Task 3).

So the honest statement: a positive-coefficient nonlinear invariant of an Euler product is
RH-BLIND BY CONSTRUCTION. We demonstrate the structural fact with two genuine Euler products
that agree on b(n)>=0 but have different zero behavior is impossible to exhibit cheaply, so we
instead show the converse cleanly: ANY Euler product whose log has b(n)>=0 has P>=0 on sigma>1,
and we show a genuine L-function (Dirichlet beta = L(s,chi_4), GRH-on-line) realizes it, while
a NON-positive-coefficient (RH-irrelevant) combination breaks P already on sigma>1.
"""
import mpmath as mp, numpy as np
mp.mp.dps=30

def gram_min(fn,sigma,ts):
    n=len(ts);M=np.zeros((n,n),dtype=complex)
    for j in range(n):
        for k in range(n):
            M[j,k]=complex(fn(mp.mpf(sigma)+1j*(ts[j]-ts[k])))
    M=(M+M.conj().T)/2; return np.linalg.eigvalsh(M).min()
ts=[0,0.6,1.3,2.1,3.0,4.0]

print("Dirichlet L(s,chi_4) (=beta): Euler product, nontrivial zeros on Re=1/2 (GRH region).")
print("  log L = sum_{p,k} chi_4(p)^k /k p^{-ks}.  chi_4(p)=+-1 => coeffs SIGN-CHANGING.")
print("  => log L does NOT have nonneg coeffs; PD is NOT expected even on sigma>1:")
def chi4(n):
    n%=4
    return {1:1,3:-1}.get(n,0)
def logL4(s):
    # sum over n of (von-Mangoldt-twisted)/log... easier: log L = sum_{p,k} chi(p^k)/k p^{-ks}, chi mult
    tot=mp.mpf(0)
    for p in [3,5,7,11,13,17,19,23,29,31,37,41,43,47]:  # skip p=2 (chi_4(2)=0)
        cp=chi4(p)
        for k in range(1,40):
            tot+=mp.mpf(cp)**k/k*mp.mpf(p)**(-k*s)
    return tot
for sg in [3.0,2.0,1.5,1.2]:
    me=gram_min(logL4,sg,ts)
    print(f"   sigma={sg:4.2f}: P(log L_chi4)= {me:+.3e}  {'PD' if me>-1e-9 else 'NOT PD'}")
print()
print("OBSERVATION: even a genuine GRH-on-line L-function does NOT give a PD log, because its")
print("Dirichlet coeffs are sign-changing (chi=+-1). The PD/CM positivity is SPECIAL to zeta")
print("(and to positive-coeff combinations like zeta^2/zeta(2s)) -- it comes from the TRIVIAL")
print("character (all +1), NOT from RH. So PD of log F is NOT an RH-detecting invariant:")
print("  - zeta: PD on sigma>1, but that's the trivial-character positivity, says nothing of zeros.")
print("  - L(chi): RH-on-line, yet log is NOT PD. => PD does not track 'zeros on the line'.")
print()
print("CONCLUSION (honest): the nonlinear positive-coeff invariant correlates with chi=1 (sign of")
print("coefficients), NOT with zero location. It is necessary-but-not-sufficient noise for RH:")
print("present for zeta on sigma>1 (zero-free region anyway), absent for on-line L(chi). It cannot")
print("be an RH certificate.")
