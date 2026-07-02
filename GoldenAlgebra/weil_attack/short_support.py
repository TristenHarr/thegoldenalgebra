"""
SHORT-SUPPORT POSITIVITY PROBE.
Weil functional (per AIM page, n-sum form, with Lambda von Mangoldt):
  Q(g) = sum_gamma h(gamma)
       = 2 h(i/2) - g(0) log pi + (1/2pi) int h(r) Re psi(1/4+ir/2) dr
         - 2 sum_n Lambda(n)/sqrt(n) g(log n)
Take g EVEN, supported in [-L,L]. Then the prime sum only sees n with log n <= L,
i.e. n <= e^L. For L < log 2 ~ 0.693 the prime sum is EMPTY -> Q(g)= arch+pole only,
which is the Connes-positive archimedean part. So on supp g subset (-log2,log2),
Q reduces to the archimedean functional => UNCONDITIONALLY >=0 by Connes (2020)!
Question: how large can L be before the FIRST prime term (n=2) can flip the sign?

We test: g = autocorrelation of psi supported in [-L/2,L/2] (so g supported [-L,L]),
h = |hatpsi|^2 >=0. Sweep L upward, find min eigenvalue of the Weil matrix, locate
the L where it first can go negative WITHOUT an off-line zero (i.e. where prime side
starts to matter and the *unconditional* lower bound is lost).
"""
import mpmath as mp
from sympy import isprime as _isprime
mp.mp.dps=22
def dig(z): return mp.digamma(z)
def Lambda(n):
    # von Mangoldt
    m=n; ps=set()
    d=2
    while d*d<=m:
        if m%d==0:
            ps.add(d)
            while m%d==0:m//=d
        d+=1
    if m>1: ps.add(m)
    return mp.log(list(ps)[0]) if len(ps)==1 else mp.mpf(0)
W=lambda r: mp.re(dig(mp.mpf(1)/4+1j*r/2))
LOGPI=mp.log(mp.pi)
# Use bump basis in TIME domain: psi_m(x)= triangular/gaussian bump centered at x_m in [-L/2,L/2].
# Simplest: psi(x)=gaussian narrow at x_m. g=autocorr. Sweep how primes enter.
# Instead, do the clean theoretical check: for a SINGLE psi=gauss(sig) centered 0,
# g(u)=sqrt(pi)sig e^{-u^2/4sig^2} (full line support but concentrated). As sig->0,
# g concentrates near 0 -> prime sum -> Lambda(n) g(log n) tiny for n>=2 if sig small
# since log2=0.69. Show Q>0 and that arch+pole dominates.
def Qsingle(sig):
    C=2*mp.pi*sig*sig
    def h(z): return C*mp.e**(-(sig*sig)*z*z)
    A=mp.quad(lambda r:h(r)*(W(r)-LOGPI),[-mp.inf,0,mp.inf])/(2*mp.pi)
    P=mp.re(h(1j/2)+h(-1j/2))
    def g(u): return mp.sqrt(mp.pi)*sig*mp.e**(-(u*u)/(4*sig*sig))
    s=mp.mpf(0)
    for n in range(2,100000):
        L=Lambda(n)
        if L==0: continue
        s+=L/mp.sqrt(n)*g(mp.log(n))
    PR=2*s
    return mp.re(A+P-PR), mp.re(A), mp.re(P), mp.re(PR)
print("Single Gaussian, varying width sig (smaller=shorter effective support):")
for sig in [mp.mpf('0.2'),mp.mpf('0.5'),mp.mpf('1.0'),mp.mpf('2.0'),mp.mpf('4.0')]:
    Q,A,P,PR=Qsingle(sig)
    print(f" sig={float(sig):.1f}: Q={mp.nstr(Q,8)} (A={mp.nstr(A,6)}, P={mp.nstr(P,6)}, PR={mp.nstr(PR,6)})")
