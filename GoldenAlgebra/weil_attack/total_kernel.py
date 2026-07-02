"""
The TOTAL Weil kernel in frequency xi:
  K(xi) = W_inf(xi) + 2 Re zeta'/zeta(1/2+i xi)
where W_inf(xi) = Re psi_Gamma(1/4 + i xi/2) - log pi   (archimedean, from Gamma factor)
                 [the POLE term 2h(i/2) corresponds to a DELTA-like / boundary piece in xi,
                  handled separately; for resonating psi concentrated at high xi the pole
                  term hat g(i/2) ~ |hatpsi(i/2)|^2 -> we set it aside to expose the bulk kernel].
The Weil criterion (modulo the pole/main term) is that the BULK kernel K(xi)>=0 for all xi.
KEY: near a zeta zero rho=1/2+i gamma, zeta'/zeta has a POLE with residue +1, so
  Re zeta'/zeta(1/2+i xi) ~ Re 1/(i(xi-gamma)) = 0 at xi=gamma but the term
  -zeta'/zeta = sum Lambda(n) n^{-s} ... Let's just evaluate K(xi) and see if it dips
  negative, and WHERE. The archimedean W_inf(xi) ~ log(xi) grows (Stirling). The prime
  term oscillates O(1)..but near zeros has log-scale spikes. Check the competition.
"""
import mpmath as mp
mp.mp.dps=20
def Winf(xi): return mp.re(mp.digamma(mp.mpf(1)/4+1j*xi/2))-mp.log(mp.pi)
def primeK(xi): return 2*mp.re(mp.zeta(mp.mpf(1)/2+1j*xi,derivative=1)/mp.zeta(mp.mpf(1)/2+1j*xi))
print("xi      W_inf      primeK     K=W+prime")
mn=(None,1e9)
for t in range(2,120):
    xi=mp.mpf(t)/4
    try:
        w=Winf(xi);pk=primeK(xi);K=w+pk
        if K<mn[1]: mn=(float(xi),float(K))
        if t%4==0 or K<0:
            print(f"{float(xi):6.2f}  {mp.nstr(w,6):>10}  {mp.nstr(pk,6):>10}  {mp.nstr(K,6):>10}  {'<<NEG' if K<0 else ''}")
    except: pass
print("min K found:",mn)
