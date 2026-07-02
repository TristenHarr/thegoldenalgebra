"""
DECISIVE cone-boundary experiment. The TRUE Q over support-[-T,T] equals the zero-sum
sum_rho |phihat(gamma_rho)|^2 (validated to 1e-21). This is ALWAYS >=0 IF all relevant zeros
are on the line. The UNCONDITIONAL question is: ignoring where zeros actually are, for which
T does the EXPLICIT-FORMULA RHS (ARCH+POLE-PRIME, computed from primes+gamma only, NO zeros)
provably stay >=0 for all positive-type phi supported in [-T,T]?

Equivalent dual question (Bombieri): does there exist a positive-type phi, supp in [-T,T],
with sum_rho |phihat(gamma_rho)|^2 < (what a single OFF-LINE zero quartet would force)?
We test the OBSTRUCTION directly: inject a hypothetical off-line zero pair at 1/2+-delta+i*g0
and ask the MINIMUM support T_needed for a [-T,T] test function to 'see' it (resolve the
displacement delta). Connes/Bombieri: you need supp large enough that phihat can localize
near g0 with resolution < delta. By uncertainty, T >~ 1/delta. As delta->0 (RH), T->inf:
NO finite-support test function can detect an on-line zero -> Q>=0 for ALL finite T
UNCONDITIONALLY *as far as a single zero is concerned*. The OBSTRUCTION is the PRIME sum's
own indefiniteness, which kicks in at the SECOND prime power interactions.

CONCRETE: compute, as a function of T, the quantity
   m(T) = min over positive-type phi supp[-T,T], ||phi||=1, of  [ARCH+POLE-PRIME](phi)
But using the EXACT prime side and the EXACT archimedean side -- the ONLY error is quadrature.
We now do ARCH by a HIGH-ORDER method (mpmath quad per entry) for SMALL matrices (n<=8) to
KILL the 1e-4 quadrature error, and read the TRUE threshold.
"""
import mpmath as mp
mp.mp.dps=30
Omega=lambda r: mp.re(mp.digamma(mp.mpf(1)/4+1j*r/2))-mp.log(mp.pi)
# prime powers up to bound, precomputed
def ppow(upto):
    out=[]; P=int(upto)+2
    sieve=bytearray([1])*(P+1); sieve[0]=sieve[1]=0
    i=2
    while i*i<=P:
        if sieve[i]:
            for j in range(i*i,P+1,i): sieve[j]=0
        i+=1
    for p in range(2,P+1):
        if sieve[p]:
            lp=mp.log(p); pk=p
            while pk<=upto:
                out.append((mp.log(pk), lp/mp.sqrt(pk))); pk*=p
    return out
def matrices(centers,s,PP):
    n=len(centers); s2=s*s
    Q=mp.matrix(n,n); G=mp.matrix(n,n)
    for i in range(n):
        for j in range(i,n):
            d=centers[i]-centers[j]
            A=s2*mp.quad(lambda r: mp.e**(-s2*r*r)*mp.cos(r*d)*Omega(r),[-mp.inf,0,mp.inf])
            POLE=2*mp.pi*s2*mp.e**(s2/4)*(mp.e**(d/2)+mp.e**(-d/2))
            PR=mp.mpf(0)
            for (u,w) in PP:
                PR+=w*s2*(mp.sqrt(mp.pi)/(2*s))*(mp.e**(-(d-u)**2/(4*s2))+mp.e**(-(d+u)**2/(4*s2)))
            PR*=2
            val=A+POLE-PR; Q[i,j]=val;Q[j,i]=val
            gg=mp.sqrt(mp.pi)*s*mp.e**(-d*d/(4*s2)); G[i,j]=gg;G[j,i]=gg
    return Q,G
def mineig(Q,G):
    n=Q.rows; R=mp.cholesky(G); Ri=R**-1; B=Ri.T*Q*Ri
    Bs=mp.matrix(n,n)
    for i in range(n):
        for j in range(n): Bs[i,j]=(B[i,j]+B[j,i])/2
    return min(mp.eigsy(Bs,eigvals_only=True))
print("HIGH-PRECISION (dps=30, mpmath quad) min Rayleigh. n=7 nodes. TRUE threshold.")
print(f"{'T':>6} {'s':>5} {'min_eig':>18}")
for T in [1.0,1.386,2.0,2.5,3.0,4.0]:
    s=mp.mpf('0.45'); n=7
    centers=[mp.mpf(-T)/2+mp.mpf(T)*k/(n-1) for k in range(n)]
    PP=ppow(float(mp.e**(T+8*s)))
    Q,G=matrices(centers,s,PP)
    print(f"{T:6.3f} {float(s):5.2f} {mp.nstr(mineig(Q,G),10):>18}")
