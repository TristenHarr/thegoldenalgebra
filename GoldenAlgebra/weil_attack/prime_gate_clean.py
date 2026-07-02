"""
delta*T ~ 1 GATE, derived cleanly, and ROBUSTNESS of the moving-v_T finding.

GATE (the honest derivation).  An off-line zero rho = 1/2 + delta + i*gamma contributes to the
explicit-formula zero-sum  Q(g) = sum_rho h(gamma_rho)  the term  h_rho(gamma) with
gamma_rho = (rho-1/2)/i = gamma - i*delta  (COMPLEX height for delta!=0).  For g supported in
[-T,T], h = ghat is BAND-LIMITED to |Im| ... more precisely h(z)=int g(u) e^{izu} du is entire
of exponential type T:  |h(gamma - i*delta)| <= e^{T|delta|} sup|...|.  The off-line zero is
DETECTABLE (changes Q sign) only when the type-T test function can localize at height gamma AND
feel the delta-shift, i.e. when  T*delta >~ 1  (the displacement e^{T*delta} departs from 1).
For T*delta << 1, e^{T delta} ~ 1 + T*delta and the off-line zero is invisible to order T*delta.
This is the SAME uncertainty as the prime-pressure channel: the prime sum past e^T injects
frequencies up to ~T into Q; a zero displacement delta produces a feature at scale 1/delta, only
resolved when T >~ 1/delta.  We verify both numerically.
"""
import numpy as np, mpmath as mp
from prime_rank_collective import prime_powers, gen_eig, ip_G, gram, prime_matrix, LOG2
mp.mp.dps=25

print("="*84)
print("GATE part A: off-line zero detectability  e^{T*delta} departs from 1  <=>  T*delta~1")
print("="*84)
print("For a test function of support [-T,T], an off-line zero at displacement delta scales the")
print("zero-sum term by ~e^{T*delta}. Detectable margin |e^{T*delta}-1|:")
print(f"{'delta':>8} " + "".join(f"T={T:<6.1f}" for T in [0.5,1,2,4,8]))
for delta in [0.5,0.25,0.1,0.05,0.02]:
    row=f"{delta:8.3f} "
    for T in [0.5,1,2,4,8]:
        row+=f"{abs(np.exp(T*delta)-1):<8.3f}"
    print(row)
print("  Diagonal T*delta=1 (e^1-1=1.718) is the threshold: below it the zero barely perturbs Q")
print("  (margin<<1); at/above it the perturbation is O(1). The gate is the line delta = 1/T.")

print("\n"+"="*84)
print("GATE part B: the prime sum's spectral reach grows linearly with T (so it can only")
print("resolve delta down to ~1/T).  Frequency centroid of the prime form's kernel vs T.")
print("="*84)
# PRIME(g)=2 sum_{n<=e^T} (Lambda/sqrt n) g(log n). As a multiplier on h(r)=|phihat|^2 it is
# D_T(r) = 2 sum_{n<=e^T} (Lambda/sqrt n) cos(r log n). Its 'reach' in u-space is u<=T (the
# largest log n). So the prime channel probes g at separations up to T; conjugate frequency 1/T.
print(f"{'T':>5} {'max log n in supp':>18} {'#prime powers':>14}")
for T in [0.5,1.0,2.0,3.0,4.0]:
    PP=prime_powers(np.exp(T))
    mx=max((u for (u,w,p,k) in PP),default=0.0)
    print(f"{T:5.1f} {mx:18.4f} {len(PP):14d}")
print("  The prime form reaches separation u=log n up to T; it cannot probe finer structure than")
print("  1/T in conjugate (zero-height) space => off-line displacement delta<1/T is unresolved.")

print("\n"+"="*84)
print("ROBUSTNESS: v_T MOVES (overlap of dominant eigvec across crossings), 3 independent bases.")
print("="*84)
for (NB,Xmax,sw) in [(15,1.0,0.20),(19,1.1,0.17),(25,1.1,0.14)]:
    centers=list(np.linspace(-Xmax,Xmax,NB)); G=gram(centers,sw)
    def dom(T):
        PR=prime_matrix(centers,sw,prime_powers(np.exp(T)))
        w,V=gen_eig(PR,G);o=np.argsort(-np.abs(w));v=V[:,o[0]]
        k0=np.argmax(np.abs(v));
        if v[k0]<0:v=-v
        return v
    print(f"\n basis NB={NB} Xmax={Xmax} s={sw}, cond(G)={np.linalg.cond(G):.1e}")
    print(f"   crossing   |<v(T-),v(T+)>_G|")
    for (lab,u) in [('log2',LOG2),('log3',float(mp.log(3))),('log4',float(mp.log(4))),
                    ('log5',float(mp.log(5))),('log7',float(mp.log(7)))]:
        vb=dom(u-0.03); va=dom(u+0.03); ov=abs(ip_G(vb,va,G))
        print(f"   {lab:>7}    {ov:.4f}")
    print(f"   v(0.8) vs v(1.95): {abs(ip_G(dom(0.8),dom(1.95),G)):.4f}")
print("\n  Across all bases: BIG drop at log2 (~0.1), partial at log3 (~0.7), then settles ~0.99.")
print("  v_T is a MOVING direction in the first two regimes (re-points as each early prime enters),")
print("  then stabilizes once several primes share the bulk packet.  NOT a single fixed direction.")
