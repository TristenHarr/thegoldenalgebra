"""
TASK 3: Pin the EXACT step that destroys positivity, for the NONLINEAR object log zeta / log xi.

We track a single positivity property -- POSITIVE-DEFINITENESS in t (PSD Toeplitz Gram),
equivalently "spectral measure of t->F(sigma+it) is a positive measure" -- through the four
operations, applied to the NONLINEAR (log) object:

  STEP 0  log zeta on sigma>1                : PD?  (positive Dirichlet coeffs 1/k)
  STEP 1  CONTINUATION across sigma=1 pole    : PD survive? (log-singularity, milder)
  STEP 2  LOG-DIFFERENTIATION d/ds (-> -z'/z) : PD survive? (this is the linear EF kernel)
  STEP 3  COMPLETION (add archimedean log-Gamma factor): PD survive?
  STEP 4  SYMMETRIZATION (functional equation s<->1-s): PD survive?

For each we report min eig of the Hermitian Gram in t at a few sigma. The point: identify the
FIRST step at which the sign is irreparably lost for the NONLINEAR invariant.
"""
import mpmath as mp, numpy as np
mp.mp.dps = 30

def gram_min(fn, sigma, ts):
    n=len(ts); M=np.zeros((n,n),dtype=complex)
    for j in range(n):
        for k in range(n):
            M[j,k]=complex(fn(mp.mpf(sigma)+1j*(ts[j]-ts[k])))
    M=(M+M.conj().T)/2
    return np.linalg.eigvalsh(M).min()

ts=[0.0,0.6,1.3,2.1,3.0,4.0]

# log zeta
def logzeta(s): return mp.log(mp.zeta(s))
# archimedean log-factor of log xi: g(s)= -(s/2)log pi + log Gamma(s/2) + log(s/2) + log((s-1))...
# Use full log xi and the pure archimedean piece separately.
def logxi(s):
    return mp.log(0.5*s*(s-1)*mp.pi**(-s/2)*mp.gamma(s/2)*mp.zeta(s))
def logGammaFactor(s):  # the completion piece alone: log( pi^{-s/2} Gamma(s/2) )
    return -(s/2)*mp.log(mp.pi)+mp.loggamma(s/2)
def logxi_sym(s):
    # symmetrized: log xi is already symmetric; test PD of (log xi(s)+log xi(1-s))/2 = log xi(s)
    return logxi(s)

print("Min eig of Hermitian Gram in t. PD <=> >=0. Track step by step.\n")
sigmas=[2.0,1.5,1.2,1.05,1.0,0.9,0.7,0.5]
header=f"{'object/step':>26} | "+" ".join(f"{sg:>6.2f}" for sg in sigmas)
print(header)
def row(name,fn):
    r=f"{name:>26} | "
    for sg in sigmas:
        try:
            me=gram_min(fn,sg,ts); r+=f"{me:+6.1e} ".replace("e","e")
        except: r+="  ERR   "
    print(r)

row("STEP0/1 log zeta", logzeta)
row("STEP3 log(pi^-s/2 Gam) only", logGammaFactor)
row("STEP3 log xi (completed)", logxi)
print()
print("Reading:")
print(" - log zeta PD for sigma>1, dies at the sigma=1 pole-crossing (continuation).")
print(" - The archimedean log-Gamma factor ALONE: is it PD? if NOT, completion injects indefiniteness.")
print(" - log xi (completed): PD anywhere? This is the decisive nonlinear-completed object.")
