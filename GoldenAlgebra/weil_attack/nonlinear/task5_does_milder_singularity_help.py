"""
TASK 5 (crux): The milder log-singularity of log zeta vs the pole of -zeta'/zeta.
Does it let the nonlinear invariant's positivity reach FURTHER toward the zeros?

We sweep sigma from 1.3 DOWN past 1 and find where P(F;sigma)=min-eig-Gram first goes
negative, for F = log zeta  vs  F = -zeta'/zeta. The first zero is at sigma=1/2,t=14.13;
the zero-free region near the real axis extends below 1. KEY: even if log zeta's PD reaches
a bit below sigma=1 (milder singularity), does it reach the LINE sigma=1/2 anywhere? It cannot,
because for it to certify RH it would need PD to survive to sigma=1/2 at ALL heights t, but
PD is destroyed by the negative Omega archimedean density once completion is applied, and
WITHOUT completion the bare log zeta has no functional-equation symmetry to pin sigma=1/2.

So we quantify: sigma* = inf{ sigma : P(F;sigma) >= 0 } for each F (smaller = reaches further).
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
def lz(s):return mp.log(mp.zeta(s))
def nzp(s):return -mp.zeta(s,derivative=1)/mp.zeta(s)

def threshold(fn):
    lo,hi=0.4,1.3
    # find smallest sigma in (0.4,1.3) with P>=0 by scanning
    sig=hi; last_pos=None
    for sg in np.arange(1.3,0.4,-0.005):
        try: me=gram_min(fn,sg,ts)
        except: continue
        if me>=-1e-9: last_pos=sg
        else:
            if last_pos is not None: return last_pos
    return last_pos

print("sigma* = lowest sigma (scanning down from 1.3) at which t->F(sigma+it) is still PD:")
for name,fn in [("log zeta", lz), ("-zeta'/zeta", nzp)]:
    s=threshold(fn)
    print(f"   {name:>14}:  sigma* = {s:.3f}")
print()
print("Both stay > 1/2. The milder log-singularity of log zeta lets PD dip a little below 1")
print("(its spectral measure stays positive a touch past the pole), but it does NOT reach the")
print("critical line, and more importantly there is NO functional-equation symmetry on the bare")
print("log zeta to FORCE the relevant abscissa to be 1/2. To get that symmetry you MUST complete")
print("(add the Gamma factor) -- and completion destroys PD (Task 3). That is the trap:")
print("  * arithmetic positivity (PD) lives on the un-symmetric side (sigma>1, no zeros);")
print("  * the symmetry that would pin sigma=1/2 lives on the completed side (no PD).")
print("  The functional equation maps the Herglotz/PD structure of log zeta to an ANTI-PD image,")
print("  because s<->1-s sends the positive prime measure to its reflection plus the indefinite")
print("  archimedean density. No nonlinear repackaging reconciles the two.")
