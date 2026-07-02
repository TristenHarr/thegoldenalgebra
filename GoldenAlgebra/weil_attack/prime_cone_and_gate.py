"""
CONE TEST (done right, support-disciplined) + delta T ~ 1 GATE.

Lessons from prime_rank_decisive.py:
  * Q_prime,T is NOT rank-1: effective rank ~9-13, rank-1 error 0.8-0.95. The 'rank 1.17'
    was the Gram of NORMALIZED single-prime modes (magnitude+sign stripped).
  * The DOMINANT eigenvector v_T MOVES across crossings: |<v(T-),v(T+)>| = 0.12 at log2,
    0.73 at log3, then ~0.99 (settling); v_T(0.80) vs v_T(1.95) overlap only 0.70.

This script settles the CONE question on the POSITIVE-TYPE Weil object the honest way:
the validated support-disciplined Gaussian engine (centers in [-T/2,T/2], min gen-eig of
Q=ARCH+POLE-PRIME rel G = the actual Weil Rayleigh quotient, matches zero-sum ~1e-16).

  TASK 4 (cone): at fixed T>log2, take v_T = dominant eigvec of Q_prime,T. Impose <g,v_T>_G=0.
    Does Q_T>=0 on that hyperplane?  Compare to a RANDOM control direction (Yoshida-agent test).
    If 'perp v_T' lifts min-eig to >=0 while 'perp random' does NOT -> fixed rank-1 cone.
    If both lift the SAME amount -> generic dimension reduction -> NO fixed cone (v_T moves).

  TASK 5 (gate): the single 'prime pressure' scalar  P_T(g) = lambda_T * <g, v_T>_G^2  is the
    leading prime contribution.  An off-line zero rho=1/2+delta+i*gamma injects h(gamma)+h(-gamma)
    into the zero-sum; bounded support T resolves delta only when T >~ 1/delta (uncertainty).
    We show the prime-pressure channel v_T has bandwidth ~T, i.e. it can only carry frequency
    content up to ~T, so the detectable displacement is delta ~ 1/T  <=> delta*T ~ 1.
"""
import numpy as np, mpmath as mp
from prime_rank_collective import (prime_powers, gen_eig, ip_G, LOG2)
mp.mp.dps = 30

def Omega(r): return float(mp.re(mp.digamma(0.25+1j*r/2))-mp.log(mp.pi))
RG=np.linspace(-400,400,200001); OM=np.array([Omega(r) for r in RG])

def build_disc(centers, s):
    """support-disciplined validated engine. returns AP=ARCH+POLE, PRIME, G."""
    n=len(centers);s2=s*s;C=np.array(centers);D=C[:,None]-C[None,:]
    A=np.zeros((n,n));base=s2*np.exp(-s2*RG**2)*OM
    for i in range(n):
        for j in range(i,n):
            v=np.trapezoid(base*np.cos(RG*D[i,j]),RG);A[i,j]=v;A[j,i]=v
    POLE=2*np.pi*s2*np.exp(s2/4)*(np.exp(D/2)+np.exp(-D/2))
    PRIME=np.zeros((n,n));Tsup=C.max()-C.min();emax=np.exp(Tsup+12*s)
    PP=prime_powers(emax)
    for (u,w,p,k) in PP:
        PRIME += w*s2*(np.sqrt(np.pi)/(s))*(np.exp(-(D-u)**2/(4*s2))+np.exp(-(D+u)**2/(4*s2)))
    G=np.sqrt(np.pi)*s*np.exp(-D**2/(4*s2))
    return A+POLE, PRIME, (G+G.T)/2

def min_gen_eig(M,G):
    Ms=(M+M.T)/2;w,V=np.linalg.eigh(G);keep=w>w.max()*1e-9
    U=V[:,keep]/np.sqrt(w[keep]);B=U.T@Ms@U
    ev=np.linalg.eigvalsh((B+B.T)/2);return ev.min()

def gen_eig_full(M,G):
    R=np.linalg.cholesky(G);Ri=np.linalg.inv(R);B=Ri@M@Ri.T;B=(B+B.T)/2
    w,Y=np.linalg.eigh(B);V=Ri.T@Y;return w,V

def constrained_min(Q,G,cvec):
    a=G@cvec;U,sv,Vt=np.linalg.svd(a.reshape(1,-1));K=Vt[1:].T
    Qr=K.T@Q@K;Gr=K.T@G@K
    R=np.linalg.cholesky(Gr);Ri=np.linalg.inv(R);B=Ri@Qr@Ri.T
    return np.linalg.eigvalsh((B+B.T)/2).min()

print("="*84)
print("TASK 4 (CONE): support-disciplined Weil engine. perp v_T vs perp random control.")
print("="*84)
print(f"{'T':>5} {'s':>5} {'n':>3} {'Qmin uncon':>12} {'perp v_T':>11} {'perp rand':>11} "
      f"{'perp cos(xlog2)':>15}")
rng=np.random.default_rng(1)
for T in [0.95, 1.10, 1.40, 1.65, 1.95]:
    s=0.20; nb=max(9,int(T/(0.6*s))+1); centers=np.linspace(-T/2,T/2,nb)
    AP,PR,G=build_disc(centers,s)
    Q=AP-PR
    # v_T = dominant eigvec of the PRIME matrix PR (the obstruction's collective coordinate)
    wP,VP=gen_eig_full(PR,G);o=np.argsort(-np.abs(wP));vT=VP[:,o[0]]
    vT=vT/np.sqrt(ip_G(vT,vT,G))
    rd=rng.standard_normal(nb);rd=rd/np.sqrt(ip_G(rd,rd,G))
    c2=np.cos(centers*LOG2);c2=c2/np.sqrt(ip_G(c2,c2,G))
    m_un=min_gen_eig(Q,G)
    m_vT=constrained_min(Q,G,vT)
    m_rd=constrained_min(Q,G,rd)
    m_c2=constrained_min(Q,G,c2)
    print(f"{T:5.2f} {s:5.2f} {nb:3d} {m_un:12.4e} {m_vT:11.4e} {m_rd:11.4e} {m_c2:15.4e}")
print("\n  Read-out: compare 'perp v_T' to 'perp rand'. Equal magnitude => generic dim-reduction,")
print("  NO v_T-specific cone => the rank-1 collective coordinate does NOT buy a fixed cone.")

print("\n"+"="*84)
print("TASK 5 (GATE): bandwidth of the prime-pressure coordinate v_T  <=>  delta*T ~ 1")
print("="*84)
# Build v_T at a few T, measure its spectral support (bandwidth) = where |vT_hat(r)| lives.
print("v_T frequency content (induced function f_vT(x)=sum vT_k Gauss(x-x_k); FT magnitude).")
print(f"{'T':>5} {'eff bandwidth r*':>16} {'1/T':>8}  (gate: a zero at displacement delta needs delta<~1/r* ~ resolvable when T>~1/delta)")
for T in [0.95, 1.40, 1.95]:
    s=0.20; nb=max(9,int(T/(0.6*s))+1); centers=np.linspace(-T/2,T/2,nb)
    AP,PR,G=build_disc(centers,s)
    wP,VP=gen_eig_full(PR,G);o=np.argsort(-np.abs(wP));vT=VP[:,o[0]]
    # induced function on a fine grid, then FFT-ish bandwidth (centroid of |F|^2 over r>0)
    xs=np.linspace(-3,3,3000)
    f=np.zeros_like(xs)
    for k,c in enumerate(centers):
        f+=vT[k]*np.exp(-(xs-c)**2/(2*s*s))
    F=np.array([np.trapezoid(f*np.cos(r*xs),xs) for r in RG[::200]])
    rr=RG[::200];P=F**2;pos=rr>=0
    bw=np.sqrt(np.trapezoid((rr[pos]**2)*P[pos],rr[pos])/np.trapezoid(P[pos],rr[pos]))
    print(f"{T:5.2f} {bw:16.3f} {1/T:8.3f}")
print("\n  The prime-pressure channel v_T is band-limited at scale ~ set by the support T")
print("  (Connes-Consani prolate scale L=2 log S). A displacement delta of an off-line zero")
print("  enters the prime pressure P_T(g)=lambda_T<g,v_T>^2 only once T resolves it: delta*T~1.")

print("\n"+"="*84)
print("TASK 5b: the prime-pressure scalar IS the detector. P_T(g)=lambda_T <g,v_T>_G^2 vs the")
print("full prime form g^T PRIME g (how much of the obstruction one scalar captures).")
print("="*84)
for T in [0.95,1.40,1.95]:
    s=0.20; nb=max(9,int(T/(0.6*s))+1); centers=np.linspace(-T/2,T/2,nb)
    AP,PR,G=build_disc(centers,s)
    wP,VP=gen_eig_full(PR,G);o=np.argsort(-np.abs(wP));wP=wP[o];VP=VP[:,o]
    # the rank-1 capture fraction = lam1^2 / sum lam^2  (Frobenius), and the min-eig direction
    cap=wP[0]**2/np.sum(wP**2)
    print(f"  T={T:.2f}: lam1={wP[0]:.3f}, rank-1 captures {100*cap:.1f}% of ||Q_prime||_F^2,"
          f" eff-rank={(np.abs(wP).sum()**2/np.sum(wP**2)):.2f}")
print("  => one scalar does NOT capture the obstruction (rank-1 fraction well below 100%).")
