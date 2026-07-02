"""
TASK 4: is the cone RH-equivalent or PARTIAL? 
Test the resolution-scaling claim: a hypothetical off-line zero quartet at 1/2+-delta+-i*g0
injects a NEGATIVE contribution into the Weil sum ONLY for test functions with support
T large enough to resolve displacement delta near height g0. Below that T, Q stays >=0
EVEN IF the zero is off-line => bounded-support positivity does NOT see off-line zeros =>
the cone is a PARTIAL (RH-incomplete) result.

Off-line quartet contribution to Q(phi)= sum over the 4 zeros of |phihat(gamma_rho)|^2 where
gamma_rho=(rho-1/2)/i is now COMPLEX: for rho=1/2+delta+i g0, gamma=g0 - i delta.
|phihat(g0 - i delta)|^2 vs the on-line |phihat(g0)|^2. The 4 zeros give
  2 Re[ phihat(g0-i delta) conj(phihat(-g0-i delta)) ] *2 ... 
We compute the NET contribution of the quartet for a wave packet phihat centered at g0 with
freq-width ~1/T (support T), and find the MIN over packets => the most negative it gets,
as a function of T and delta. Threshold T*(delta) where it first goes negative ~ 1/delta.
"""
import mpmath as mp
mp.mp.dps=25
def quartet_contrib(T, delta, g0):
    # wave packet phi supported [-T/2,T/2]: model phihat(r)=sinc-like, width 1/T centered +-g0.
    # Use phihat(r)=exp(-T^2(r-g0)^2/4)+exp(-T^2(r+g0)^2/4) (Gaussian, eff support ~[-T,T]... 
    # actually time-support ~ 1/(freq width)=... we PARAMETRIZE by T=support directly via
    # gaussian of time-width T: phihat(r)=exp(-(r-g0)^2 * (T/2)^2)+... )
    a=(T/2)**2
    def ph(w):  # analytic phihat
        return mp.e**(-a*(w-g0)**2)+mp.e**(-a*(w+g0)**2)
    def conjph(w):
        return mp.e**(-a*(mp.conj(w)-g0)**2)+mp.e**(-a*(mp.conj(w)+g0)**2)
    def conjph_bar(w):  # overline{phihat(overline w)}
        return mp.conj(ph(mp.conj(w)))
    # zeros gamma for quartet 1/2+-delta+-i g0: gamma=(rho-1/2)/i
    # rho=1/2+delta+i g0 -> gamma=(delta+i g0)/i = g0 - i delta
    # rho=1/2-delta+i g0 -> gamma= g0 + i delta
    # rho=1/2+delta-i g0 -> gamma=-g0 - i delta
    # rho=1/2-delta-i g0 -> gamma=-g0 + i delta
    gammas=[g0-1j*delta, g0+1j*delta, -g0-1j*delta, -g0+1j*delta]
    # contribution sum_rho h(gamma), h(w)=ph(w)*overline{ph(overline w)} (=|ph|^2 on R)
    tot=mp.mpf(0)
    for gm in gammas:
        tot+=ph(gm)*conjph_bar(gm)
    # subtract the on-line reference (delta=0): all 4 -> 2*(|ph(g0)|^2+|ph(-g0)|^2)
    return mp.re(tot)
g0=mp.mpf(20)
print("Net Weil contribution of an OFF-LINE quartet {1/2+-d+-i*20} for a wave packet of support T.")
print("delta = displacement off the line. NEGATIVE => the quartet lowers Q (detectable).")
print(f"{'T':>5} | " + " ".join(f"d={float(d):.2f}" for d in [mp.mpf('0.05'),mp.mpf('0.1'),mp.mpf('0.2'),mp.mpf('0.4')]))
for T in [mp.mpf(x) for x in [0.5,1,2,4,8,16,32]]:
    row=[]
    for d in [mp.mpf('0.05'),mp.mpf('0.1'),mp.mpf('0.2'),mp.mpf('0.4')]:
        c=quartet_contrib(T,d,g0)
        row.append(f"{float(c):+.3e}")
    print(f"{float(T):5.1f} | "+"  ".join(row))
print()
print("Expectation: contribution stays >=0 (on-line-like) until T ~ 1/delta, then goes NEGATIVE.")
print("=> small-support positivity CANNOT detect off-line zeros => cone is PARTIAL, not RH.")
