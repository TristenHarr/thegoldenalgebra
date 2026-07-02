"""
Corrected resolution test. Test function g compactly supported in [-T,T] (g=phi*phi~,
phi supported [-T/2,T/2]). phihat(r) is then ENTIRE of exponential type T/2:
|phihat(r+is)| <= C e^{(T/2)|s|}. A genuine such phi: phi(x)=indicator-ish bump; take
phi(x)=cos(pi x/T) on [-T/2,T/2] (vanishes at ends), 0 outside. 
phihat(r)=\int_{-T/2}^{T/2} cos(pi x/T) e^{-i r x}dx -- entire, type T/2. To target height g0,
modulate: phi(x)=cos(pi x/T) cos(g0 x) on [-T/2,T/2]. Then phihat concentrates near +-g0
with the CORRECT support-limited shape (sinc-like, width ~1/T). 
The off-line quartet contributes sum_rho |..| with gamma=g0 -+ i delta. Because phihat is
type T/2, phihat(g0 - i delta) ~ phihat(g0) * (bounded by e^{(T/2)delta}). The NET quartet
contribution (vs on-line) can go NEGATIVE once (T/2)*delta ~ O(1), i.e. T ~ 2/delta.
"""
import mpmath as mp
mp.mp.dps=25
def phihat(r, T, g0):
    # \int_{-T/2}^{T/2} cos(pi x/T) cos(g0 x) e^{-i r x} dx  (complex r allowed)
    f=lambda x: mp.cos(mp.pi*x/T)*mp.cos(g0*x)*mp.e**(-1j*r*x)
    return mp.quad(f,[-T/2,0,T/2])
def quartet_net(T,delta,g0):
    # h(w)=phihat(w)*overline{phihat(overline w)}; gammas of quartet:
    gammas=[g0-1j*delta, g0+1j*delta, -g0-1j*delta, -g0+1j*delta]
    def h(w): return phihat(w,T,g0)*mp.conj(phihat(mp.conj(w),T,g0))
    off=sum(h(gm) for gm in gammas)
    # on-line reference delta=0: gammas -> g0,g0,-g0,-g0
    on=2*h(g0)+2*h(-g0)
    return mp.re(off-on), mp.re(on)
g0=mp.mpf(20)
print("NET quartet contribution MINUS on-line reference, packet truly supported in [-T,T].")
print("NEGATIVE net => the off-line displacement LOWERS Q below the on-line value (detectable).")
print(f"{'T':>5} {'2/delta for d':>6} | "+" ".join(f"d={float(d):.2f}" for d in [mp.mpf('0.1'),mp.mpf('0.3')]))
for T in [mp.mpf(x) for x in [1,2,4,6,8,12,20]]:
    row=[]
    for d in [mp.mpf('0.1'),mp.mpf('0.3')]:
        net,on=quartet_net(T,d,g0)
        row.append(f"net={float(net):+.3e}(2/d={float(2/d):.0f})")
    print(f"{float(T):5.0f}       | "+"  ".join(row))
