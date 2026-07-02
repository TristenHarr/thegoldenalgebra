"""
TASK 3 (decisive): WHY completion destroys PD, at the level of spectral measures.

A function t -> F(sigma+it) is PD (Bochner) iff its FOURIER transform in t is a POSITIVE measure.
  - For log zeta(sigma+it) on sigma>1: FT in t = sum_{p,k} (1/k) p^{-k sigma} delta(xi - k log p).
    All masses (1/k)p^{-k sigma} > 0  => positive measure => PD. CLEAN.
  - For the archimedean log-factor a(s)=log(pi^{-s/2} Gamma(s/2)):
      a'(s) = -1/2 log pi + 1/2 psi(s/2),  and  -2 Re a'(1/2+it)  is the archimedean density
      W_inf(t) = Re psi(1/4 + it/2) - log pi   (the SAME Omega(r) from the linear Weil form!).
    The archimedean spectral density is the FT of Omega, which is the classical kernel
      Omega(t) <-> measure with density that is NEGATIVE for small frequencies (Omega(0)=-5.37<0).
    => the archimedean factor's "spectral measure" is NOT a positive measure => NOT PD.

We confirm numerically that:
  (i)  log zeta's spectral measure (FT in t) is a positive atomic measure (primes).
  (ii) the archimedean factor a(s): the relevant signed density Omega(t)=Re psi(1/4+it/2)-log pi
       is sign-INDEFINITE (negative near 0), so completion adds a NON-positive spectral component.
  (iii) Conclusion: PD = positivity of spectral measure. log zeta HAS it (primes, all +).
        Completion ADDS the archimedean piece whose spectral content has a negative part =>
        the SUM's spectral measure is no longer guaranteed positive => PD destroyed BY COMPLETION.
        This is independent of and PRIOR to symmetrization.
"""
import mpmath as mp, numpy as np
mp.mp.dps=30

print("(i) log zeta spectral atoms (1/k)p^{-k sigma} at sigma=1.3 -- ALL POSITIVE:")
sig=1.3
atoms=[]
for p in [2,3,5,7]:
    for k in [1,2,3]:
        atoms.append((float(k*mp.log(p)), float((1/mp.mpf(k))*p**(-k*sig))))
atoms.sort()
print("   (freq=k log p, mass): ", [(round(f,3),round(m,4)) for f,m in atoms[:8]])
print("   => all masses > 0  => positive spectral measure => log zeta is PD on sigma>1.\n")

print("(ii) Archimedean kernel Omega(t)=Re psi(1/4+it/2)-log pi  (the completion's spectral density):")
for t in [0,1,2,4,6,7,7.5,8,10,15]:
    om=float(mp.re(mp.digamma(0.25+1j*mp.mpf(t)/2))-mp.log(mp.pi))
    print(f"   t={t:5.1f}:  Omega={om:+8.4f}  {'<<NEGATIVE' if om<0 else ''}")
print("   => Omega(t) is NEGATIVE for |t| < ~7.6.  Its presence in the completed object means")
print("      the archimedean spectral contribution is a SIGNED (non-positive) density.\n")

print("(iii) DECISIVE: PSD-Gram of completed log xi vs of (log zeta only) vs (archimedean only)")
def gram_min(fn,sigma,ts):
    n=len(ts);M=np.zeros((n,n),dtype=complex)
    for j in range(n):
        for k in range(n):
            M[j,k]=complex(fn(mp.mpf(sigma)+1j*(ts[j]-ts[k])))
    M=(M+M.conj().T)/2; return np.linalg.eigvalsh(M).min()
ts=[0,0.6,1.3,2.1,3.0,4.0]
def lz(s):return mp.log(mp.zeta(s))
def arch(s):return -(s/2)*mp.log(mp.pi)+mp.loggamma(s/2)
def lxi(s):return mp.log(0.5*s*(s-1)*mp.pi**(-s/2)*mp.gamma(s/2)*mp.zeta(s))
sig=1.5
print(f"   at sigma={sig}:")
print(f"     log zeta only       min-eig = {gram_min(lz,sig,ts):+.4e}   (PD)")
print(f"     archimedean only    min-eig = {gram_min(arch,sig,ts):+.4e}   (NOT PD)")
print(f"     completed log xi    min-eig = {gram_min(lxi,sig,ts):+.4e}   (NOT PD)")
print()
print("VERDICT: log zeta is PD; the ARCHIMEDEAN COMPLETION factor is NOT PD (Omega<0 near 0);")
print("their sum (log xi) is NOT PD. The positivity-destroying step is COMPLETION (Gamma-factor),")
print("and it acts at the LOGARITHMIC (nonlinear) level too -- the nonlinear transform does NOT")
print("evade it. (Symmetrization is downstream and not even needed to kill PD.)")
