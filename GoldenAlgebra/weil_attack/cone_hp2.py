"""
DEFINITIVE high-precision cone threshold. mpmath dps=40, prime list precomputed once.
Orthonormalize basis against Gram to kill conditioning: we compute the Weil form
in a FIXED gaussian basis, but report min eig of the GENERALIZED problem M x = lam G x
(G = L2 Gram of the basis) -- that's the true Rayleigh quotient sign over the SPAN,
robust to basis conditioning. min generalized eig >=0  <=>  Q>=0 on span. 
"""
import mpmath as mp
mp.mp.dps=40
# precompute (log p^? ) actually need Lambda(n) and sqrt(n) for prime powers up to e^{T+tail}
def prime_powers(upto):
    # returns list of (u=log n, weight=Lambda(n)/sqrt(n)) for prime powers n<=upto
    out=[]
    # sieve primes
    P=int(upto)+1
    sieve=bytearray([1])*(P+1); sieve[0]=sieve[1]=0
    i=2
    while i*i<=P:
        if sieve[i]:
            for j in range(i*i,P+1,i): sieve[j]=0
        i+=1
    for p in range(2,P+1):
        if sieve[p]:
            lp=mp.log(p); pk=p; k=1
            while pk<=upto:
                out.append((mp.log(pk), lp/mp.sqrt(pk)))
                pk*=p; k+=1
    return out

Omega=lambda r: mp.re(mp.digamma(mp.mpf(1)/4+1j*r/2))-mp.log(mp.pi)

def matrices(centers, s, PP):
    n=len(centers); s2=s*s
    M=mp.matrix(n,n); G=mp.matrix(n,n)
    for i in range(n):
        for j in range(i,n):
            d=centers[i]-centers[j]
            # ARCH
            A=s2*mp.quad(lambda r: mp.e**(-s2*r*r)*mp.cos(r*d)*Omega(r),[-mp.inf,0,mp.inf])
            POLE=2*mp.pi*s2*(mp.e**(d/2)+mp.e**(-d/2))*mp.e**(s2/4)
            PR=mp.mpf(0)
            for (u,w) in PP:
                PR+=w*mp.sqrt(mp.pi)*s*mp.e**(-(u-d)**2/(4*s2))
            PR*=2
            val=A+POLE-PR
            M[i,j]=val; M[j,i]=val
            # L2 Gram of gaussians: <phi_i,phi_j>=sqrt(pi) s exp(-d^2/(4 s^2))
            gg=mp.sqrt(mp.pi)*s*mp.e**(-d*d/(4*s2))
            G[i,j]=gg; G[j,i]=gg
    return M,G

def min_gen_eig(M,G):
    # solve G = R^T R (cholesky), then eig of R^-T M R^-1
    n=M.rows
    R=mp.cholesky(G)
    Rinv=R**-1
    B=Rinv.T*M*Rinv
    Bs=mp.matrix(n,n)
    for i in range(n):
        for j in range(n): Bs[i,j]=(B[i,j]+B[j,i])/2
    ev=mp.eigsy(Bs,eigvals_only=True)
    return min(ev)

print("dps=40 generalized-eig (Rayleigh) min over gaussian span. n=6, s=0.4.")
print(f"{'T':>6} {'mineig_normalized':>22}")
for T in [4.0,6.0,8.0,10.0,12.0,14.0,16.0]:
    s=mp.mpf('0.4'); n=6
    centers=[mp.mpf(-T)/2+mp.mpf(T)*k/(n-1) for k in range(n)]
    upto=mp.e**(T+8*s)
    PP=prime_powers(upto)
    M,G=matrices(centers,s,PP)
    mn=min_gen_eig(M,G)
    print(f"{T:6.1f} {mp.nstr(mn,12):>22}")
