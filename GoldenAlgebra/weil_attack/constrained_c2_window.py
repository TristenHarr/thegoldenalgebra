"""
TASK 2+3 on the decisive object: does any natural CONSTRAINT widen the PSD window in c2?

Unconstrained (knife_edge): Q_{c2} is PSD only at c2=Lambda(2)=log2 (knife edge). If a
constraint C neutralizes the n=2 negative mode, then on the constrained subspace Q_{c2} would
stay PSD for a RANGE of c2 around log2 (a genuine margin) -- and in particular the ζ value
log2 would be in the INTERIOR, giving an unconditional cone past log2. We test, on the
constrained cone, the width of {c2 : min-eig_constrained(c2) >= 0}.

Constraints (each a linear functional l.c=0 on the triangle-coeff vector c):
  (a) perp 2-adic oscillatory mode:  <phi, cos(x log2)> = 0   (cos_mode, omega=log2)
  (b) one vanishing moment:          int g = 0  <=> (sum c_k * area) ... = int phi =0 (sum rule)
  (c) perp first prime mode cos(x log2) AND sin: full 2-adic projection
  (d) odd symmetry (phi(-x)=-phi(x)): c_k = -c_{mirror}
We report, for each, the PSD c2-window [c2_lo, c2_hi]. If the window has POSITIVE WIDTH and
contains log2 in its interior -> REAL expanded cone. If it stays the single point {log2}
(or empty) -> the constraint does NOT neutralize the n=2 mode.
"""
import numpy as np
import single_prime_exact as M
import c2_sweep_dh as CS

def cos_mode(nodes,h,omega):
    # <phi_k, cos(omega .)> = Re bhat_k(omega) = cos(omega c_k)*H(omega)
    C=np.array(nodes,float)
    return np.array([np.real(M.bhat(omega,c,h)) for c in C])
def sin_mode(nodes,h,omega):
    C=np.array(nodes,float)
    return np.array([np.imag(M.bhat(omega,c,h)) for c in C])
def integral_mode(nodes,h):
    # int phi_k dx = bhat_k(0) = H(0)=h (constant) -> sum c_k =0
    return np.ones(len(nodes))

def window(nodes,h,cons,grid):
    pts=[]
    for c2 in grid:
        Q,G=CS.build_c2(nodes,h,c2)
        me=M.mineig(Q,G,constraints=cons if cons else None)
        if me is not None: pts.append((c2,me))
    pos=[c2 for c2,me in pts if me>=-1e-9]
    return (min(pos),max(pos)) if pos else None, pts

if __name__=="__main__":
    l2=M.l2
    T=0.95; n=21; half=T/2; h=(2*half)/(n+1); nodes=np.linspace(-half+h,half-h,n)
    grid=np.linspace(0.2,1.2,41)
    print(f"PSD c2-window under constraints. T={T}, n={n}. Lambda(2)=log2={l2:.4f}.")
    print("A window of POSITIVE WIDTH containing log2 in interior => expanded unconditional cone.")
    configs={
      'UNCONSTRAINED':[],
      'perp cos(x log2)':[cos_mode(nodes,h,l2)],
      'perp cos&sin(x log2)':[cos_mode(nodes,h,l2),sin_mode(nodes,h,l2)],
      'int g=0 (sum c=0)':[integral_mode(nodes,h)],
      'int g=0 + perp cos(xlog2)':[integral_mode(nodes,h),cos_mode(nodes,h,l2)],
      'CONTROL perp cos(x*0.5)':[cos_mode(nodes,h,0.5)],          # non-arithmetic mode
      'CONTROL perp cos(x*1.7)':[cos_mode(nodes,h,1.7)],          # non-arithmetic mode
      'CONTROL random direction':[np.linalg.svd(np.random.RandomState(0).randn(1,len(nodes)))[2][0]],
    }
    for name,cons in configs.items():
        win,pts=window(nodes,h,cons,grid)
        if win is None:
            print(f"  {name:28s}: PSD window EMPTY (no c2 gives PSD on this cone)")
        else:
            lo,hi=win; width=hi-lo; interior = lo<l2<hi
            print(f"  {name:28s}: window=[{lo:.4f},{hi:.4f}] width={width:.4f} contains-log2-interior={interior}")
    print()
    print("If every window has width ~0 (= {log2}) or excludes log2-interior, NO constraint")
    print("neutralizes the n=2 mode: the negative direction reappears. (branch b certificate)")
