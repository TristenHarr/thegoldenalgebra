"""
Is the tiny negative min-eigenvalue past T~2.7 a REAL obstruction or the numerical floor?
Probe: at the most-negative T points, recompute min generalized eig at HIGH precision
(mpmath dps=40) with well-conditioned basis, AND compute the TRUE Weil value on the
min-eigenvector via the zero-sum  Q = sum_rho |phihat(gamma)|^2  (validated identity).
If zero-sum >= 0 while matrix-min < 0, the negative is the conditioning/quadrature floor.
This does NOT assume RH to BUILD Q (Q is built from primes only); the zero-sum is used
ONLY as an independent CHECK of the matrix arithmetic on a specific vector.
"""
import numpy as np, mpmath as mp
mp.mp.dps = 40
Omega = lambda r: mp.re(mp.digamma(mp.mpf(1)/4 + 1j*r/2)) - mp.log(mp.pi)
SQ2PI = mp.sqrt(2*mp.pi)

def ppow(upto):
    out = []; P = int(upto)+2
    sieve = bytearray([1])*(P+1); sieve[0]=sieve[1]=0; i=2
    while i*i <= P:
        if sieve[i]:
            for j in range(i*i, P+1, i): sieve[j]=0
        i += 1
    for p in range(2, P+1):
        if sieve[p]:
            lp = mp.log(p); pk = p
            while pk <= upto:
                out.append((mp.log(pk), lp/mp.sqrt(pk))); pk *= p
    return out

def matrices(centers, s, PP):
    n = len(centers); s2 = s*s; Q = mp.matrix(n,n); G = mp.matrix(n,n)
    for i in range(n):
        for j in range(i, n):
            d = centers[i]-centers[j]
            A = s2*mp.quad(lambda r: mp.e**(-s2*r*r)*mp.cos(r*d)*Omega(r), [-mp.inf,0,mp.inf])
            POLE = 2*mp.pi*s2*mp.e**(s2/4)*(mp.e**(d/2)+mp.e**(-d/2))
            PR = mp.mpf(0)
            for (u, w) in PP:
                PR += w*s2*(mp.sqrt(mp.pi)/(2*s))*(mp.e**(-(d-u)**2/(4*s2))+mp.e**(-(d+u)**2/(4*s2)))
            PR *= 2
            Q[i,j] = A+POLE-PR; Q[j,i] = Q[i,j]
            gg = mp.sqrt(mp.pi)*s*mp.e**(-d*d/(4*s2)); G[i,j] = gg; G[j,i] = gg
    return Q, G

def mineig_vec(Q, G):
    n = Q.rows; R = mp.cholesky(G); Ri = R**-1; B = Ri.T*Q*Ri
    Bs = mp.matrix(n,n)
    for i in range(n):
        for j in range(n): Bs[i,j] = (B[i,j]+B[j,i])/2
    ev, EV = mp.eigsy(Bs)
    k = min(range(n), key=lambda t: float(ev[t]))
    y = mp.matrix([EV[r,k] for r in range(n)]); c = Ri*y
    return ev[k], c

def zerosum(centers, c, s, nz=1500):
    s2 = s*s; tot = mp.mpf(0)
    for k in range(1, nz):
        gam = mp.im(mp.zetazero(k))
        ph = sum(c[t]*SQ2PI*s*mp.e**(-s2*gam*gam/2)*mp.e**(-1j*gam*centers[t]) for t in range(len(centers)))
        t_ = 2*abs(ph)**2; tot += t_
        if t_ < mp.mpf(10)**(-30) and gam > 40: break
    return tot

# condition number of G for a given basis
def condG(G):
    n = G.rows; w = mp.eigsy(G, eigvals_only=True)
    wf = [float(x) for x in w]
    return max(wf)/min(wf)

print("FLOOR PROBE at the most-negative T points from the fast sweep.")
print("Build Q from PRIMES only (dps=40, mpmath quad). Check min eig vs TRUE zero-sum on min-vector.")
print(f"{'T':>6} {'nb':>3} {'s':>6} {'condG':>10} {'matrix_min':>14} {'zerosum_minvec':>16} {'verdict':>22}")
for (T, nb, s) in [(2.72, 9, mp.mpf('0.20')), (3.20, 9, mp.mpf('0.24')),
                   (3.40, 9, mp.mpf('0.26')), (3.40, 11, mp.mpf('0.21')),
                   (3.20, 7, mp.mpf('0.30'))]:
    centers = [mp.mpf(-T)/2 + mp.mpf(T)*k/(nb-1) for k in range(nb)]
    PP = ppow(float(mp.e**(mp.mpf(T)+10*s)))
    Q, G = matrices(centers, s, PP)
    cG = condG(G)
    me, cvec = mineig_vec(Q, G)
    zs = zerosum(centers, cvec, s)
    mef = float(me); zsf = float(zs)
    verdict = "FLOOR (zs>=0)" if (mef < 0 and zsf >= -1e-12) else ("REAL NEG" if mef < -1e-7 else "~0")
    print(f"{T:6.2f} {nb:3d} {float(s):6.3f} {cG:10.2e} {mef:14.6e} {zsf:16.6e} {verdict:>22}")
print()
print("If matrix_min<0 but zerosum_minvec>=0: the negative is conditioning/quadrature floor,")
print("NOT a genuine Q<0 direction. The TRUE form value on that vector is the zero-sum (>=0).")
