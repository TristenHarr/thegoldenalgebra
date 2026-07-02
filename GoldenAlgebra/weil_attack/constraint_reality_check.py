"""
REALITY CHECK on the constrained-window 'margin' (Task 4 discipline).

constrained_c2_window.py found that 'perp cos(x log2)' and 'int g=0' open a PSD c2-window
around log2. BUT: does the constraint genuinely keep the n=2 PRIME coupling ALIVE, or does it
secretly DELETE it (g(log2)->0 on the cone => trivially back to empty-prime Yoshida)?

We measure, on the MIN-eigenvector of the constrained form at c2=log2:
  (1) g(log2) = <phi,S_{log2}phi>  -- the n=2 coupling. If ~0, the prime term is DELETED.
  (2) the PRIME energy  2*W2*g(log2)  vs the ARCH+POLE energy. If PRIME~0, no real test.
  (3) support reach: does phi have genuine mass at |x|>log2/2 (so g reaches past log2)?

If the constraint forces g(log2)=0, the 'expanded cone' is FAKE (deleted prime), and the
honest verdict is branch (b): you cannot neutralize the n=2 mode WITHOUT killing its coupling.
We also run the SAME constraint with a NON-log2 mode (perp cos(x*0.5)) as a control: if THAT
also opens a window, the widening is generic regularization, not a real n=2 neutralization.
"""
import numpy as np
import single_prime_exact as M
import c2_sweep_dh as CS
import constrained_c2_window as CW

def min_eigvec(Q,G,cons):
    n=Q.shape[0]
    Ac=np.array(cons); u,sv,vt=np.linalg.svd(Ac)
    rank=int((sv>1e-10*sv.max()).sum()); K=vt[rank:].T
    Qk=K.T@Q@K; Gk=K.T@G@K
    w,V=np.linalg.eigh(Gk); keep=w>w.max()*1e-9
    U=V[:,keep]/np.sqrt(w[keep]); B=U.T@Qk@U
    ev,EV=np.linalg.eigh((B+B.T)/2)
    cstar=K@(U@EV[:,0])
    return cstar

def g_at(nodes,h,c,u):
    # g(u)=sum_{ij} c_i c_j (b_i*b_j~)(u) = sum c_i c_j triangle_corr(node_i,node_j,h,u)
    tot=0.0
    for i,ci in enumerate(c):
        for j,cj in enumerate(c):
            tot+=ci*cj*M.triangle_corr(nodes[i],nodes[j],h,u)
    return tot

if __name__=="__main__":
    l2=M.l2
    T=0.95; n=21; half=T/2; h=(2*half)/(n+1); nodes=np.linspace(-half+h,half-h,n)
    Q,G=CS.build_c2(nodes,h,l2)   # at the zeta value c2=log2
    print(f"Constraint reality check. T={T}, n={n}, c2=Lambda(2)=log2={l2:.4f}.")
    print("On the constrained min-eigenvector: g(log2) (=n2 coupling), g(0)(=norm), support reach.")
    print(f"{'constraint':>26} {'g(log2)':>12} {'g(0)':>10} {'g(log2)/g(0)':>13} {'max|x|>log2/2?':>14}")
    configs={
      'UNCONSTRAINED':[],
      'perp cos(x log2)':[CW.cos_mode(nodes,h,l2)],
      'perp cos&sin(x log2)':[CW.cos_mode(nodes,h,l2),CW.sin_mode(nodes,h,l2)],
      'int g=0 (sum c=0)':[CW.integral_mode(nodes,h)],
      'CONTROL perp cos(x*0.5)':[CW.cos_mode(nodes,h,0.5)],   # non-arithmetic mode
    }
    for name,cons in configs.items():
        if not cons:
            # unconstrained min eigenvector
            w,V=np.linalg.eigh(G); keep=w>w.max()*1e-9
            U=V[:,keep]/np.sqrt(w[keep]); B=U.T@Q@U
            ev,EV=np.linalg.eigh((B+B.T)/2); c=U@EV[:,0]
        else:
            c=min_eigvec(Q,G,cons)
        c=c/np.sqrt(abs(g_at(nodes,h,c,0.0)))
        glog2=g_at(nodes,h,c,l2); g0=g_at(nodes,h,c,0.0)
        # support reach: weight of |c| at nodes with |node|>log2/2... but support of g reaches
        # 2*(max node + h). Report whether any node with mass has |x|>log2/2 - h (genuine past-log2)
        reach=any(abs(ci)>0.05*np.max(np.abs(c)) and abs(nd)>l2/2 - h for ci,nd in zip(c,nodes))
        print(f"{name:>26} {glog2:12.5f} {g0:10.4f} {glog2/g0:13.5f} {str(reach):>14}")
    print()
    print("If 'perp cos(x log2)' gives g(log2)~0 => the constraint DELETES the n=2 coupling")
    print("(fake cone). If the CONTROL (non-arithmetic mode) also opened a window in")
    print("constrained_c2_window, the widening is generic, not an n=2-specific neutralization.")
