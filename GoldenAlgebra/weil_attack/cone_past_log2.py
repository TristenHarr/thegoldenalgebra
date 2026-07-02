"""
THE CONE JUST PAST log 2. For supp(g) in (-T,T) with log2 < T < log3 (=1.099), ONLY the
n=2 prime power is active. Q(g) = ARCH(g)+POLE(g) - 2*(log2/sqrt2)*g(log2).
Since g=phi*phi~ positive type, g(log2)=<phi, S_{log2} phi> can be POSITIVE or NEGATIVE.
  - If g(log2)<=0: -2 w2 g(log2)>=0, so Q>=ARCH+POLE. Is ARCH+POLE>=0? (Yoshida cone, YES on
    the smaller support; need to check it persists / find when ARCH+POLE can go <0.)
  - If g(log2)>0: the prime term is a genuine SUBTRACTION; Q can drop. Worst case.
We compute, over positive-type phi supp[-T/2,T/2], the quantity
   R(T) = min_phi [ARCH+POLE](phi) - 2 w2 max(g(log2),0)... 
Actually directly: min over phi of Q. We use the fact Q's TRUE value = zero-sum>=0, so the
UNCONDITIONAL question is whether the *formula* (not knowing zeros) certifies >=0.
Cleanest unconditional certificate: ARCH+POLE - PRIME >= 0 as a form. We test the single-prime
regime: build 2x2..4x4 matrices for T in (log2, log3) at HIGH precision, check PSD.
This is a GENUINE finite computation with only ONE prime -> fully analyzable.
"""
import mpmath as mp
mp.mp.dps=30
Omega=lambda r: mp.re(mp.digamma(mp.mpf(1)/4+1j*r/2))-mp.log(mp.pi)
l2=mp.log(2); w2=l2/mp.sqrt(2)
def mat(centers,s,nprimes_u):  # nprimes_u: list of (u,weight) active
    n=len(centers);s2=s*s
    Q=mp.matrix(n,n);G=mp.matrix(n,n)
    for i in range(n):
        for j in range(i,n):
            d=centers[i]-centers[j]
            A=s2*mp.quad(lambda r: mp.e**(-s2*r*r)*mp.cos(r*d)*Omega(r),[-mp.inf,0,mp.inf])
            POLE=2*mp.pi*s2*mp.e**(s2/4)*(mp.e**(d/2)+mp.e**(-d/2))
            PR=mp.mpf(0)
            for (u,w) in nprimes_u:
                PR+=w*s2*(mp.sqrt(mp.pi)/(2*s))*(mp.e**(-(d-u)**2/(4*s2))+mp.e**(-(d+u)**2/(4*s2)))
            PR*=2
            Q[i,j]=A+POLE-PR;Q[j,i]=Q[i,j]
            gg=mp.sqrt(mp.pi)*s*mp.e**(-d*d/(4*s2));G[i,j]=gg;G[j,i]=gg
    return Q,G
def mineig(Q,G):
    n=Q.rows;R=mp.cholesky(G);Ri=R**-1;B=Ri.T*Q*Ri
    Bs=mp.matrix(n,n)
    for i in range(n):
        for j in range(n):Bs[i,j]=(B[i,j]+B[j,i])/2
    return min(mp.eigsy(Bs,eigvals_only=True))
print("SINGLE-PRIME regime log2<T<log3. Only n=2 active. min eig of Weil form (HP).")
print("If >=0 throughout, the cone extends to T=log3 unconditionally (one-prime certificate).")
print(f"{'T':>7} {'s':>5} {'min_eig':>16}")
log3=float(mp.log(3))
for T in [0.8,0.9,1.0,1.09]:
    s=mp.mpf('0.30');n=6
    centers=[mp.mpf(-T)/2+mp.mpf(T)*k/(n-1) for k in range(n)]
    active=[(l2,w2)] if T>float(l2) else []
    Q,G=mat(centers,s,active)
    print(f"{T:7.3f} {float(s):5.2f} {mp.nstr(mineig(Q,G),10):>16}")
print(f"(log2={float(l2):.4f}, log3={log3:.4f})")
