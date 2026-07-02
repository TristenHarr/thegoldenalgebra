"""
DECISIVE single-prime contrast: Q(g)=ARCH+POLE - 2*(c2/sqrt2)*g(log2) on compact support
(log2,log3) where ONLY the n=2 term is active. Sweep the n=2 coefficient c2:
   zeta:  c2 = Lambda(2) = log2 (>0, the prime-power coefficient).
   DH:    c2 = the Dirichlet coeff of -f'/f at n=2, which for a non-Euler-product f is
          UNCONSTRAINED in sign/size (sign-changing, no Lambda>=0).
Find c2* = the threshold where min-eig of the form crosses zero. Report margin for zeta and
whether a DH-type c2 (e.g. negative, or different magnitude) lands in the NEGATIVE region.

We use the compact triangle basis (exact prime cutoff). We REPORT min-eig as a function of c2
and the unconstrained vs constrained (orthogonal to cos(x log2) mode) cones.
"""
import numpy as np
import single_prime_exact as M

def build_c2(nodes,h,c2):
    n=len(nodes); C=np.array(nodes,float)
    A=np.zeros((n,n)); POLE=np.zeros((n,n)); PR=np.zeros((n,n)); G=np.zeros((n,n))
    Hr=M._H(M.RG,h); BH=np.exp(-1j*np.outer(C,M.RG))*Hr[None,:]
    for i in range(n):
        for j in range(n):
            A[i,j]=np.trapz(M.OM*np.real(BH[i]*np.conj(BH[j])),M.RG)/(2*np.pi)
            phi=M.bhat_imag(C[i],h,0.5); phj=M.bhat_imag(C[j],h,0.5)
            phim=M.bhat_imag(C[i],h,-0.5); phjm=M.bhat_imag(C[j],h,-0.5)
            POLE[i,j]=phi*phj+phim*phjm
            G[i,j]=M.triangle_corr(C[i],C[j],h,0.0)
            PR[i,j]=2*(c2/np.sqrt(2))*M.triangle_corr(C[i],C[j],h,M.l2)
    Q=A+POLE-PR
    return (Q+Q.T)/2,(G+G.T)/2

if __name__=="__main__":
    l2=M.l2
    print("min-eig of single-prime form vs n=2 coefficient c2 (zeta: c2=log2=%.4f)."%l2)
    print("Compact basis, T=0.95 (log2<T<log3), n=21.")
    T=0.95; n=21; half=T/2; h=(2*half)/(n+1)
    nodes=np.linspace(-half+h,half-h,n)
    print(f"{'c2':>9} {'mineig':>14}   note")
    for c2 in [-1.0,-0.5,-0.2,0.0,0.2,0.4,0.6931,0.8,1.0,1.5,2.0,3.0]:
        Q,G=build_c2(nodes,h,c2)
        me=M.mineig(Q,G)
        note=''
        if abs(c2-l2)<1e-6: note='<-- ZETA (Lambda(2))'
        print(f"{c2:9.4f} {me:14.5e}   {note}")
    print()
    print("Interpretation: c2>0 (zeta) SUBTRACTS a term that is +(g(log2)<0) on the ARCH+POLE")
    print("minimizer, so larger c2 RAISES min-eig. A DH-type c2<0 LOWERS it (drives negative).")
