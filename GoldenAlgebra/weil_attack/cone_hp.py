"""
HIGH-PRECISION cone threshold. Basis of even cosine-Gaussian packets in FREQUENCY:
  F_c(r) = exp(-b r^2) cos(c r)   (real, even).  h = (sum a_k F_{c_k})^2 >= 0 positive type.
Test fn g = inverse-transform autocorr. Support of g in u: F_c has freq-width ~1/sqrt(b);
g(u) lives near u where... Actually for the SUPPORT constraint we must bound supp(g).
g = ghat-inverse of h. h=sum_{kl} a_k a_l F_{c_k}F_{c_l}. Product of cos-gaussians ->
gaussians at c_k +- c_l with width. The TIME support is governed by b: g(u) ~ exp(-u^2/(4b))
=> effectively supported in |u| <~ R*sqrt(b). So short support <=> small b... but small b
=> wide in freq. Tradeoff. 

Cleaner for the SUPPORT cone: parametrize directly by g compactly supported.
Use g = (phi * phi~), phi = sum a_k T_k, T_k = TRIANGLE/bump at node x_k in [-T/2,T/2].
We compute EXACT-ish entries with mpmath quad. n small (<=8) for trust.
"""
import mpmath as mp
mp.mp.dps=25
Omega=lambda r: mp.re(mp.digamma(mp.mpf(1)/4+1j*r/2))-mp.log(mp.pi)
def Lambda(n):
    mm=n;fac={};d=2
    while d*d<=mm:
        while mm%d==0: fac[d]=fac.get(d,0)+1;mm//=d
        d+=1
    if mm>1: fac[mm]=fac.get(mm,0)+1
    return mp.log(list(fac.keys())[0]) if len(fac)==1 else mp.mpf(0)

# Gaussian bump basis in TIME: phi_k(x)=exp(-(x-xk)^2/(2 s^2)). EXACT entries:
def entries(centers, s):
    n=len(centers); s2=s*s
    A=mp.matrix(n,n); POLE=mp.matrix(n,n); PRIME=mp.matrix(n,n)
    for i in range(n):
        for j in range(n):
            d=centers[i]-centers[j]
            # ARCH = s^2 \int exp(-s^2 r^2) cos(r d) Omega(r) dr
            A[i,j]=s2*mp.quad(lambda r: mp.e**(-s2*r*r)*mp.cos(r*d)*Omega(r),[-mp.inf,0,mp.inf])
            # POLE = 2 pi s^2 (e^{d/2}+e^{-d/2}) e^{s^2/4}
            POLE[i,j]=2*mp.pi*s2*(mp.e**(d/2)+mp.e**(-d/2))*mp.e**(s2/4)
            # PRIME = 2 sum Lambda/sqrt(n) sqrt(pi) s exp(-(log n - d)^2/(4 s^2))
            ssum=mp.mpf(0)
            for nn in range(2,200000):
                L=Lambda(nn)
                if L==0: continue
                u=mp.log(nn)
                term=L/mp.sqrt(nn)*mp.sqrt(mp.pi)*s*mp.e**(-(u-d)**2/(4*s2))
                ssum+=term
            PRIME[i,j]=2*ssum
    M=mp.matrix(n,n)
    for i in range(n):
        for j in range(n):
            M[i,j]=A[i,j]+POLE[i,j]-PRIME[i,j]
    return M

print("HIGH-PRECISION Weil matrix min-eig vs support T (n=7 gaussian nodes).")
print(f"{'T':>6} {'s':>6} {'mineig':>16}")
for T in [2.0,4.0,6.0,8.0,10.0,12.0,14.0,16.0,18.0,20.0]:
    s=mp.mpf('0.3')
    n=7
    centers=[(-T/2+T*k/(n-1)) for k in range(n)]
    centers=[mp.mpf(c) for c in centers]
    M=entries(centers,s)
    Ms=mp.matrix(n,n)
    for i in range(n):
        for j in range(n): Ms[i,j]=(M[i,j]+M[j,i])/2
    ev=mp.eigsy(Ms,eigvals_only=True)
    mn=min(ev)
    print(f"{T:6.1f} {float(s):6.2f} {mp.nstr(mn,10):>16}")
