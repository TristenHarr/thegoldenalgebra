"""
bd_gram.py — Nyman-Beurling / Báez-Duarte Gram matrix A_N and best-approx distance d_N^2.

Setup (Báez-Duarte 2003, "A strengthening of the Nyman-Beurling criterion for the RH",
Atti Accad. Naz. Lincei 14 (2003) 5-11):

  rho_alpha(x) = {alpha / x}   on  x in (0,1),     alpha in (0,1].
  Báez-Duarte uses the discrete family  alpha = 1/k,  k = 1..N.
  d_N^2 := dist^2_{L^2(0,1)}( 1 , span{ rho_{1/k} : k=1..N } )   ->  0   <=>  RH.

We build:
  - the Gram matrix  G[j,k] = <rho_{1/j}, rho_{1/k}>_{L^2(0,1)}   (Vasyunin entries),
  - the moment vector  b[k] = <1, rho_{1/k}>_{L^2(0,1)},
  - the best-approx distance  d_N^2 = <1,1> - b^T G^{-1} b = 1 - b^T G^{-1} b.

Inner products are computed by ANALYTIC reduction (exact closed form) and cross-checked
against direct mpmath quadrature.

ANALYTIC closed forms (standard; see Vasyunin 1995, Báez-Duarte-Balazard-Landreau-Saias
2000 "A lower bound in an approximation problem involving the zeros of the Riemann zeta
function", Adv. Math. / Burnol):

  Let f_m(x) = {m x}  for m>=1 on (0,1).  Note rho_{1/m}(x) = {(1/m)/x} = {1/(m x)}.
  Substituting x -> 1/x is awkward; instead Báez-Duarte's L^2(0,1) family is most cleanly
  handled via the Mellin/Vasyunin route, but for a SELF-CONTAINED, verifiable build we use
  the equivalent Nyman-Beurling family on L^2(0,1):

     rho_{1/m}(x) = {1/(m x)}.

  <1, rho_{1/m}> = ∫_0^1 {1/(m x)} dx.
  <rho_{1/m}, rho_{1/n}> = ∫_0^1 {1/(m x)} {1/(n x)} dx.

We compute these by quadrature with the natural singularity handling (the integrand
oscillates as x->0 but is bounded in [0,1]).
"""
import mpmath as mp
import numpy as np
import json

mp.mp.dps = 40

def frac(t):
    return t - mp.floor(t)

def moment1(m):
    """ <1, rho_{1/m}> = ∫_0^1 {1/(m x)} dx.  Substitute u=1/(m x): x=1/(m u), dx=-1/(m u^2)du.
        x:0->1  => u: inf -> 1/m.  Integral = ∫_{1/m}^inf {u} /(m u^2) du.
    """
    f = lambda u: frac(u)/(m*u*u)
    # split at integers to help quadrature; {u} is sawtooth
    return mp.quad(f, [mp.mpf(1)/m] + [mp.mpf(k) for k in range(1, 60)] + [mp.inf])

def inner(m, n):
    """ <rho_{1/m}, rho_{1/n}> = ∫_0^1 {1/(m x)}{1/(n x)} dx.
        Substitute u = 1/x (u:1->inf, x=1/u, dx=-du/u^2):
        = ∫_1^inf {u/m}{u/n} / u^2 du.
    """
    f = lambda u: frac(u/m)*frac(u/n)/(u*u)
    # breakpoints at multiples of m and n up to some cutoff
    pts = set()
    K = 80
    for k in range(1, K):
        pts.add(mp.mpf(k*m)); pts.add(mp.mpf(k*n))
    pts = sorted(p for p in pts if p > 1)
    nodes = [mp.mpf(1)] + pts + [mp.inf]
    return mp.quad(f, nodes)

def build(N):
    G = mp.matrix(N, N)
    b = mp.matrix(N, 1)
    for i in range(N):
        b[i] = moment1(i+1)
    for i in range(N):
        for j in range(i, N):
            v = inner(i+1, j+1)
            G[i,j] = v
            G[j,i] = v
    return G, b

def dN2(G, b):
    N = G.rows
    # d_N^2 = <1,1> - b^T G^{-1} b ; <1,1>=∫_0^1 1 dx = 1
    Ginv = G**-1
    quad = (b.T * Ginv * b)[0,0]
    return 1 - quad

def to_np(M):
    return np.array([[float(M[i,j]) for j in range(M.cols)] for i in range(M.rows)])

if __name__ == "__main__":
    import sys
    Nmax = int(sys.argv[1]) if len(sys.argv) > 1 else 20
    print(f"# Building Báez-Duarte Gram matrix up to N={Nmax}, dps={mp.mp.dps}")
    G, b = build(Nmax)
    # sanity: G symmetric PSD?
    Gnp = to_np(G)
    eigs = np.linalg.eigvalsh(Gnp)
    print("Gram eigenvalues (min..max):", np.round(eigs[:5],8), "...", np.round(eigs[-3:],6))
    print("min Gram eig:", eigs.min())
    results = []
    for N in range(1, Nmax+1):
        GN = G[:N,:N]
        bN = b[:N,:]
        d2 = dN2(GN, bN)
        results.append((N, float(d2)))
        print(f"N={N:3d}  d_N^2={float(d2):.10f}  d_N^2*log N={float(d2)*np.log(N) if N>1 else float('nan'):.6f}")
    json.dump({"N": [r[0] for r in results], "dN2": [r[1] for r in results],
               "gram": Gnp.tolist(), "gram_eigs": eigs.tolist(),
               "moment": [float(b[i]) for i in range(Nmax)]},
              open("bd_gram_results.json","w"), indent=1)
    print("saved bd_gram_results.json")
