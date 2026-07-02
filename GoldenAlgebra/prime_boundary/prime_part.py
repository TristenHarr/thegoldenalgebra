"""
prime_part.py
=============
Tasks 1 & 2: decompose G(x+iY) = G_arch + G_prime + G_zero on the top edge, and
test whether the prime part is sign-definite / positive-on-average.

Geometry: z = x + iY  ->  s = 1/2 + Y - i x  (so Re s = 1/2 + Y, Im s = -x).
Equivalently the top edge at height Y is the VERTICAL line Re s = sigma := 1/2+Y.

The prime sum  -zeta'/zeta(s) = Sum_n Lambda(n) n^{-s}  CONVERGES for sigma>1,
i.e. for top edges with Y > 1/2.  We test there.

Contribution of the zeta log-derivative to G:
  G(z) = -Im( Lambda_Xi(z) ),  Lambda_Xi = -i*(xi'/xi)(s) = -i*(arch(s)+zeta'/zeta(s)).
  G = -Im(-i*arch) - Im(-i*zeta'/zeta) =: G_arch + G_zeta.
With zeta'/zeta(s) = -Sum Lambda(n) n^{-s} =: -P(s),
  G_zeta = -Im(-i*(-P)) = -Im(i*P) = -Re(P)... let's just compute Im(-i*w) = -Re(w).
  So  -Im(-i*w) = Re(w).   Hence:
    G_arch = Re( arch(s) )
    G_zeta = Re( zeta'/zeta(s) ) = -Re( P(s) ) = -Re( Sum Lambda(n) n^{-s} ).
"""
import mpmath as mp
mp.mp.dps = 30

_mang = {}
def mangoldt(n):
    if n in _mang: return _mang[n]
    fac={}; mm=n; d=2
    while d*d<=mm:
        while mm%d==0: fac[d]=fac.get(d,0)+1; mm//=d
        d+=1
    if mm>1: fac[mm]=fac.get(mm,0)+1
    f = mp.log(list(fac.keys())[0]) if len(fac)==1 else mp.mpf(0)
    _mang[n]=f; return f

def s_of(x,Y): return mp.mpf('0.5')+mp.mpf(Y) - 1j*mp.mpf(x)

def arch(s):
    return 1/s + 1/(s-1) - mp.mpf('0.5')*mp.log(mp.pi) + mp.mpf('0.5')*mp.digamma(s/2)

def zeta_ld(s):
    return mp.diff(lambda t: mp.log(mp.zeta(t)), s)

def G_total(x,Y):
    s=s_of(x,Y)
    return mp.re(arch(s)+zeta_ld(s))   # G = Re(xi'/xi(s)) under this geometry

def G_arch(x,Y):
    return mp.re(arch(s_of(x,Y)))

def G_zeta_truth(x,Y):
    return mp.re(zeta_ld(s_of(x,Y)))

def G_zeta_primesum(x,Y,N=50000):
    s=s_of(x,Y)
    tot=mp.mpc(0)
    for n in range(2,N+1):
        Ln=mangoldt(n)
        if Ln!=0: tot += Ln*mp.e**(-s*mp.log(n))
    # zeta'/zeta = -tot ; G_zeta = Re(zeta'/zeta) = -Re(tot)
    return -mp.re(tot)

if __name__=="__main__":
    print("=== Verify prime-sum reproduces G_zeta (top edges with Y>1/2, sigma>1) ===")
    for Y in [0.6, 1.0, 2.0, 5.0]:
        x=7.0
        gt=G_zeta_truth(x,Y); ps=G_zeta_primesum(x,Y)
        print(f"Y={Y}: G_zeta truth={float(gt):+.6f}  primesum={float(ps):+.6f}  diff={float(gt-ps):+.2e}")

    print()
    print("=== TASK 2: is the prime contribution G_zeta = Re(zeta'/zeta) sign-definite on the top edge? ===")
    print("    (Recall G_zeta = -Re(Sum Lambda(n) n^{-s}), Lambda(n)>=0.)")
    for Y in [0.6, 1.0, 2.0, 5.0, 10.0]:
        sigma=0.5+Y
        vals=[float(G_zeta_truth(x,Y)) for x in [0,1,2,3,5,7,11,13,14,17,23,50]]
        avg=sum(vals)/len(vals)
        print(f"Y={Y:4.1f} (sigma={sigma:5.2f}) G_zeta over x: min={min(vals):+.4f} max={max(vals):+.4f} avg={avg:+.4f}")

    print()
    print("=== Sign of the three pieces on the top edge ===")
    for Y in [0.6, 1.0, 2.0, 5.0]:
        sigma=0.5+Y
        xs=[0,2,5,7,11,14,20,40]
        ga=[float(G_arch(x,Y)) for x in xs]
        gz=[float(G_zeta_truth(x,Y)) for x in xs]
        gt=[float(G_total(x,Y)) for x in xs]
        print(f"Y={Y:4.1f}(s={sigma:4.1f}) arch:min={min(ga):+.3f} zeta:min={min(gz):+.3f} tot:min={min(gt):+.3f}  arch>=0? {all(v>=0 for v in ga)}  zeta>=0? {all(v>=0 for v in gz)}")
