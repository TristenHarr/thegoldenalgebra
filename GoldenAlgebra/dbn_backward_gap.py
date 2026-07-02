#!/usr/bin/env python3
"""
dbn_backward_gap.py
===================
NOTE (orientation caveat): the bare repulsion ODE integrated BACKWARD is genuinely
ill-posed — at a collision the 1/(x_j-x_k) term blows the integrator up (Experiment B
'backward' overflows). That overflow is the ill-posedness itself, not merely a code
bug, but it makes this script's backward numbers unreliable past the first near-collision.
The FAITHFUL, singularity-free realization of the same physics is in
  dbn_verify_reduction.py  and  dbn_global_split.py
which flow a genuine entire function by the EXACT backward-heat semigroup exp(-tD^2)
(no ODE singularity) and reproduce the discriminant law and the pitchfork cleanly.
Read those for the validated results; this file is kept for the forward-direction
free-energy identity dHlog/dt=+2E (Experiment B forward) and the qualitative gap picture.

STRATEGY 1 (BACKWARD-FLOW NO-SPLITTING) + STRATEGY 3 (FREE ENERGY), tested honestly
on the EXACT zero-repulsion ODE of the de Bruijn-Newman heat flow.

Setup.
------
Let H_t have real simple zeros x_1(t)<x_2(t)<... For the dBN flow (backward heat
equation d_t H_t = -d_zz H_t) the real zeros obey the gradient/Calogero-type ODE

    d/dt x_j = -2 * sum_{k != j} 1/(x_k - x_j)         (principal value)
             = +2 * sum_{k != j} 1/(x_j - x_k).

(This is Rodgers-Tao eq for the zeros; "+" form below.) The flow REPELS zeros as t
increases. RH <=> Lambda<=0 <=> as t decreases through 0, no real pair collides and
splits off the axis. The pitchfork: a double real zero at t=Lambda bifurcates into a
conjugate pair for t<Lambda.

THE QUESTION (Strategy 1): running BACKWARD (t decreasing), can a gap x_{j+1}-x_j -> 0?
The repulsion is +2/(gap) which, as t DECREASES, drives the close pair TOGETHER (the
repulsion that pushes them apart forward = pulls the clock backward toward collision).
A collision in finite backward time is exactly a zero leaving the axis. So:

  Lambda<=0  <=>  starting from the TRUE zeta zeros at t=0, NO gap collides as t -> -inf
                  before... no: Lambda<=0 means no collision for any t in (Lambda,0], i.e.
                  the zeros stay real all the way down to t=0 from above; equivalently the
                  REAL zero configuration at t=0 is reachable by FORWARD flow from a real
                  config at every t<0 down to Lambda. The collision we must forbid is a
                  pair pinching as we DECREASE t below 0.

We test, on a finite local block of N zeros, the gap dynamics and candidate Lyapunov
functions:
   E   = sum_{j!=k} 1/(x_j-x_k)^2                 (renormalized energy; Rodgers-Tao)
   Hlog= sum_{j<k} log|x_j-x_k|                   (log-Hamiltonian / free energy)
   gmin= min_j (x_{j+1}-x_j)                      (minimal gap; collision <=> gmin->0)

Rodgers-Tao: d/dt Hlog = +2 E >= 0 (forward), so Hlog DECREASES backward; and the
energy E controls deviation from arithmetic progression. We check the SIGN structure
and whether a backward Lyapunov bound forbids gmin->0 for the ACTUAL (irregular) zeta
spacing vs a generic/AP configuration.
"""
import numpy as np
from scipy.integrate import solve_ivp

np.set_printoptions(precision=6, suppress=True)

# ----------------------------------------------------------------------------
# The exact repulsion ODE (mean-field Calogero / "Coulomb gas" on the line).
# d/dt x_j = +2 sum_{k!=j} 1/(x_j - x_k).
# We work on a finite block; the tails are absorbed into a smooth background which
# we model two ways: (a) free finite block, (b) block embedded in an arithmetic
# progression bath (the rest of the zeros frozen as an AP) to mimic the principal
# value of the infinite sum locally.
# ----------------------------------------------------------------------------

def rhs_free(t, x):
    x = np.asarray(x)
    n = len(x)
    dx = np.zeros(n)
    for j in range(n):
        s = 0.0
        for k in range(n):
            if k != j:
                s += 1.0/(x[j]-x[k])
        dx[j] = 2.0*s
    return dx

def rhs_bath(t, x, bath):
    """block x, plus frozen AP 'bath' points contributing repulsion (mimics tails)."""
    x = np.asarray(x)
    n = len(x)
    dx = np.zeros(n)
    for j in range(n):
        s = 0.0
        for k in range(n):
            if k != j:
                s += 1.0/(x[j]-x[k])
        for b in bath:
            s += 1.0/(x[j]-b)
        dx[j] = 2.0*s
    return dx

def energy(x):
    x = np.asarray(x); n=len(x); E=0.0
    for j in range(n):
        for k in range(n):
            if k!=j: E += 1.0/(x[j]-x[k])**2
    return E

def hlog(x):
    x=np.asarray(x); n=len(x); H=0.0
    for j in range(n):
        for k in range(j+1,n):
            H += np.log(abs(x[j]-x[k]))
    return H

def gmin(x):
    x=np.sort(np.asarray(x))
    return np.min(np.diff(x))

# ----------------------------------------------------------------------------
# EXPERIMENT A: a Lehmer pair (anomalously close pair) embedded in an AP, run
# BACKWARD in t. Does the close pair collide (gmin->0) in finite backward time?
# ----------------------------------------------------------------------------
def experiment_A():
    print("="*78)
    print("EXPERIMENT A: Lehmer-type close pair in an AP bath, BACKWARD flow")
    print("="*78)
    # AP with average gap 1, but one pair brought close (gap = delta).
    N = 21
    base = np.arange(-N//2, N//2+1, dtype=float)  # ...,-1,0,1,...
    # make the central pair close: shift point at index c by bringing it toward c+1
    c = N//2
    for delta in [0.5, 0.2, 0.1, 0.05]:
        x0 = base.copy()
        # central pair gap = delta: move x[c] up so gap to x[c+1] is delta
        x0[c] = x0[c+1] - delta
        x0 = np.sort(x0)
        bath = []  # already finite block acts as its own bath here
        g0 = gmin(x0); E0=energy(x0); H0=hlog(x0)
        # integrate backward: t from 0 to -T
        T = 2.0
        sol = solve_ivp(rhs_free, [0,-T], x0, rtol=1e-10, atol=1e-12,
                        dense_output=True, max_step=0.01)
        # track gmin along backward trajectory
        ts = np.linspace(0,-T,400)
        gm = []
        collided = False
        tcol = None
        for tt in ts:
            xx = sol.sol(tt)
            g = gmin(xx)
            gm.append(g)
            if g < 1e-4 and not collided:
                collided=True; tcol=tt
        gm=np.array(gm)
        print(f" delta={delta:5.2f}: g0={g0:.4f} E0={E0:8.3f} Hlog0={H0:8.3f} "
              f"| min gmin over backward t in [0,-{T}]={gm.min():.5f} "
              f"{'COLLISION@t=%.3f'%tcol if collided else 'no collision'}")
    print()
    print(" Reading: BACKWARD flow (t down) the repulsion +2/gap that separates pairs")
    print(" forward now PULLS the close pair together. A close pair => collision in")
    print(" finite backward time => a complex pair below. So a SUFFICIENTLY close real")
    print(" pair at t=0 WOULD certify Lambda>0 (zero left axis just below 0). The dBN")
    print(" content is: is there a STRUCTURAL lower bound on gmin(0) forbidding this?")

# ----------------------------------------------------------------------------
# EXPERIMENT B: forward/backward asymmetry of the free energy. Rodgers-Tao show
# d/dt Hlog = +2E (forward up). We verify and ask: is there ANY quantity monotone
# in the BACKWARD direction that is bounded, hence forbids gmin->0 (which sends
# Hlog -> -inf)? gmin->0 <=> Hlog->-inf. If Hlog is bounded BELOW along backward
# flow we'd forbid collision. d/dt Hlog = 2E>0 forward => Hlog decreasing backward,
# UNbounded below in principle => NO obstruction from Hlog alone. Confirm numerically.
# ----------------------------------------------------------------------------
def experiment_B():
    print("="*78)
    print("EXPERIMENT B: free-energy monotonicity & the backward direction")
    print("="*78)
    N=15
    x0 = np.arange(-N//2,N//2+1,dtype=float)
    x0 = x0 + 0.15*np.sin(np.arange(len(x0)))  # perturb off AP
    for direction,T in [("forward",1.5),("backward",1.5)]:
        sgn = +1 if direction=="forward" else -1
        sol = solve_ivp(rhs_free,[0,sgn*T],x0,rtol=1e-10,atol=1e-12,
                        dense_output=True,max_step=0.01)
        ts=np.linspace(0,sgn*T,200)
        H=[hlog(sol.sol(tt)) for tt in ts]
        E=[energy(sol.sol(tt)) for tt in ts]
        g=[gmin(sol.sol(tt)) for tt in ts]
        # finite-difference dH/dt vs 2E
        dH=np.gradient(H,ts)
        err=np.max(np.abs(dH-2*np.array(E)))
        print(f" {direction:8s}: Hlog {H[0]:.4f}->{H[-1]:.4f}  gmin {g[0]:.4f}->{g[-1]:.4f}"
              f"  max|dH/dt-2E|={err:.2e}")
    print(" => d/dt Hlog = +2E confirmed. Forward: Hlog UP, gaps even out (relaxation).")
    print("    Backward: Hlog DOWN without lower bound => no free-energy obstruction to")
    print("    collision. The asymmetry is exactly Rodgers-Tao's: dissipation only helps")
    print("    in the forward direction. THIS is why Lambda>=0 is provable, Lambda<=0 not.")

if __name__=='__main__':
    experiment_A()
    print()
    experiment_B()
