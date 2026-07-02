"""
TASK 1 (refined) + TASK 2.

(A) WHY does PD die at sigma=1 for all of zeta, log zeta, -zeta'/zeta? Characterize the
    singularity at s=1:
       zeta(s)      ~ 1/(s-1)              (simple pole, residue 1)
       -zeta'/zeta  ~ 1/(s-1)              (simple pole, residue 1)
       log zeta(s)  ~ log(1/(s-1)) = -log(s-1)   (LOG singularity, MILDER)
    The integral (log zeta) has a MILDER (logarithmic) singularity than the derivative (pole).
    QUESTION: does that milder singularity let log-zeta's positive structure survive closer
    to / past sigma=1 in a USABLE sense? We test the Laplace/CM representation directly.

(B) TASK 2: log-convexity / monotonicity of log|zeta| and log|xi| in sigma into the strip.
    Hadamard three-lines => sigma -> log max_t |xi(sigma+it)| is CONVEX. We test the POINTWISE
    version: is sigma -> log|xi(sigma+it)| convex in sigma at fixed t? If pointwise-convex AND
    symmetric about sigma=1/2 (funct eqn), convexity forces the min at sigma=1/2 => would give
    a sign law. Test whether pointwise convexity actually holds (it generically does NOT; the
    zeros are log-singularities of log|xi| that break convexity exactly off the line).
"""
import mpmath as mp
import numpy as np
mp.mp.dps = 30

print("="*70)
print("(A) Singularity at s=1: integral (log zeta) is MILDER than derivative")
print("="*70)
for s in [mp.mpf('1.2'), mp.mpf('1.05'), mp.mpf('1.01'), mp.mpf('1.001')]:
    z   = mp.zeta(s)
    zp  = -mp.zeta(s, derivative=1)/mp.zeta(s)
    lz  = mp.log(mp.zeta(s))
    eps = s-1
    print(f" s-1={float(eps):8.4f}:  zeta={float(z):11.4f} (~1/eps={float(1/eps):11.4f})  "
          f"-z'/z={float(zp):11.4f} (~1/eps)  log zeta={float(lz):9.4f} (~-log eps={float(-mp.log(eps)):9.4f})")
print(" => log zeta has only a LOG singularity. As a Laplace transform of the POSITIVE measure")
print("    mu=sum_{p,k} (1/k) delta_{k log p}, it is finite-energy much closer to the boundary.")
print()

# CM / Laplace check: log zeta(sigma) = int_0^inf e^{-sigma u} dM(u), M = sum (1/k) delta_{k log p}
# Verify (-1)^j (d/dsigma)^j log zeta(sigma) >= 0 (complete monotonicity) for sigma>1.
print("Complete-monotonicity check (sign of (-1)^j d^j/dsigma^j) at sigma=1.05:")
sig = mp.mpf('1.05')
def logzeta(x): return mp.log(mp.zeta(x))
def negzp(x):   return -mp.zeta(x,derivative=1)/mp.zeta(x)
for name, f in [("log zeta", logzeta), ("-zeta'/zeta", negzp)]:
    signs=[]
    for j in range(0,5):
        d = mp.diff(f, sig, j)
        signs.append(int(mp.sign(((-1)**j)*d)))
    print(f"  {name:>14}: signs of (-1)^j d^j (j=0..4) = {signs}  {'CM-consistent' if all(x>=0 for x in signs) else 'NOT CM'}")
print()

print("="*70)
print("(B) TASK 2: POINTWISE log-convexity of log|xi(sigma+it)| in sigma?")
print("="*70)
def logxi_abs(sig, t):
    s = mp.mpf(sig)+1j*mp.mpf(t)
    xi = 0.5*s*(s-1)*mp.pi**(-s/2)*mp.gamma(s/2)*mp.zeta(s)
    return float(mp.log(abs(xi)))

def second_diff(t, sig, h=1e-3):
    return (logxi_abs(sig+h,t) - 2*logxi_abs(sig,t) + logxi_abs(sig-h,t))/h**2

print("d^2/dsigma^2 log|xi(sigma+it)| (>0 => convex at that point):")
print(f"{'t':>6} | " + " ".join(f"s={sg:>4.2f}" for sg in [0.1,0.3,0.5,0.7,0.9]))
for t in [0.0, 2.0, 5.0, 10.0, 14.13, 14.5, 21.0]:
    row=f"{t:6.2f} | "
    for sg in [0.1,0.3,0.5,0.7,0.9]:
        try:
            d2=second_diff(t,sg)
            row += f"{('+' if d2>0 else '-')}{abs(d2):6.1e} "
        except: row+="  ERR   "
    print(row)
print()
print("If any '-' appears, pointwise log-convexity in sigma FAILS => no pointwise sign law from")
print("three-lines. (Three-lines only gives convexity of the MAX over t, not pointwise.)")
print("Note t=14.13 is the first zero height: near a zero, log|xi|->-inf, strongly NON-convex.")
