"""
RANK & COLLECTIVE COORDINATE OF THE PRIME OBSTRUCTION  Q_prime,T
================================================================
SERIOUS structure-revealing mission.  Decompose

    Q_T  =  Q_arch,T  +  Q_pole,T  -  Q_prime,T

and study Q_prime,T = sum_{n=p^k <= e^T} (Lambda(n)/sqrt(n)) * R_{log n}
where R_u is the rank-2 shift+reflect form  g -> <g, (S_u + S_{-u}) g>.
In the Gaussian-bump basis its matrix entry is the (validated) PRIME assembly:

    PRIME_ij = 2 sum_n w_n s^2 (sqrt(pi)/(2s)) [ e^{-(D-u_n)^2/4s^2} + e^{-(D+u_n)^2/4s^2} ]
    w_n = Lambda(n)/sqrt(n) = log p / sqrt(p^k),   D = x_i - x_j,   u_n = log n.

KEY DISCIPLINE (vs prior prime_mode_gram which compared NORMALIZED single-mode eigenvectors
with sign ambiguity): we work in a SINGLE FIXED basis (centers, width fixed, independent of T)
so that the eigenvector v_T of Q_prime,T lives in the SAME coordinate space for every T.
Only then is "does v_T move with T" a well-posed question.  We diagonalize Q_prime,T in the
G-metric (generalized eigenproblem  Q_prime v = mu G v) so eigvecs are L2-orthonormal and
directly comparable across T (overlaps = honest L2 cosines).

NO RH assumed.  Q built from primes only.  Zero-sum never used to define anything.

Outputs:
  - rank / eigenvalue decay of Q_prime,T vs T (rank-1 quality, low-rank error)
  - the dominant eigenvector v_T, its overlap with candidate functionals
  - whether v_T is a FIXED direction or MOVES as T crosses log p^k
  - the "prime pressure" scalar lambda_T * <g,v_T>^2 and the delta T ~ 1 gate
"""
import numpy as np
import mpmath as mp
import json, sys, time

mp.mp.dps = 30
LOG2 = float(mp.log(2))

# ----------------------------------------------------------------------------
def Omega_mp(r):
    return mp.re(mp.digamma(mp.mpf(1)/4 + 1j*r/2)) - mp.log(mp.pi)

def prime_powers(upto):
    out = []
    P = int(upto) + 2
    if P < 2:
        return out
    sieve = bytearray([1]) * (P + 1)
    sieve[0] = sieve[1] = 0
    i = 2
    while i * i <= P:
        if sieve[i]:
            for j in range(i * i, P + 1, i):
                sieve[j] = 0
        i += 1
    for p in range(2, P + 1):
        if sieve[p]:
            lp = mp.log(p); pk = p; k = 1
            while pk <= upto:
                out.append((float(mp.log(pk)), float(lp/mp.sqrt(pk)), p, k))
                pk *= p; k += 1
    out.sort()
    return out

# ----------------------------------------------------------------------------
# FIXED-BASIS assembly.  centers, s fixed.  Everything in float (well-conditioned regime).
# ----------------------------------------------------------------------------
def gram(centers, s):
    n = len(centers); s2 = s*s; sqpi = np.sqrt(np.pi)
    C = np.array(centers)
    D = C[:,None] - C[None,:]
    return sqpi*s*np.exp(-D*D/(4*s2))

def arch_matrix(centers, s):
    """ARCH_ij = s^2 * int e^{-s^2 r^2} cos(rD) Omega(r) dr  (mpmath quad, cached by |D|)."""
    n = len(centers); s2 = mp.mpf(s)**2
    C = np.array(centers)
    Dmat = C[:,None] - C[None,:]
    cache = {}
    A = np.zeros((n,n))
    for i in range(n):
        for j in range(i, n):
            d = abs(round(Dmat[i,j], 12))
            if d not in cache:
                val = float(s2 * mp.quad(lambda r: mp.e**(-s2*r*r)*mp.cos(r*mp.mpf(d))*Omega_mp(r),
                                         [-mp.inf, 0, mp.inf]))
                cache[d] = val
            A[i,j] = A[j,i] = cache[d]
    return A

def pole_matrix(centers, s):
    n = len(centers); s2 = s*s
    C = np.array(centers)
    D = C[:,None] - C[None,:]
    return 2*np.pi*s2*np.exp(s2/4)*(np.exp(D/2) + np.exp(-D/2))

def prime_matrix(centers, s, PP):
    """Q_prime,T as a matrix: 2 sum_n w_n s^2 (sqrt(pi)/(2s)) [e^{-(D-u)^2/4s^2}+e^{-(D+u)^2/4s^2}]."""
    n = len(centers); s2 = s*s; sqpi = np.sqrt(np.pi)
    C = np.array(centers)
    D = C[:,None] - C[None,:]
    PR = np.zeros((n,n))
    pref = 2 * s2 * (sqpi/(2*s))
    for (u, w, p, k) in PP:
        PR += w * (np.exp(-(D-u)**2/(4*s2)) + np.exp(-(D+u)**2/(4*s2)))
    return pref * PR

def single_prime_matrix(centers, s, u, w):
    n = len(centers); s2 = s*s; sqpi = np.sqrt(np.pi)
    C = np.array(centers)
    D = C[:,None] - C[None,:]
    pref = 2 * s2 * (sqpi/(2*s))
    return pref * w * (np.exp(-(D-u)**2/(4*s2)) + np.exp(-(D+u)**2/(4*s2)))

# ----------------------------------------------------------------------------
# generalized symmetric eigendecomposition  M v = mu G v ,  G-orthonormal eigvecs.
# returns eigenvalues (descending |.| not enforced; we sort) and eigvecs as columns in
# ORIGINAL coordinates, G-orthonormal:  v_a^T G v_b = delta_ab.
# ----------------------------------------------------------------------------
def gen_eig(M, G):
    # G = R R^T (cholesky). y = R^T v. (R^-1 M R^-T) y = mu y, symmetric.
    R = np.linalg.cholesky(G)
    Rinv = np.linalg.inv(R)
    B = Rinv @ M @ Rinv.T
    B = (B + B.T)/2
    w, Y = np.linalg.eigh(B)          # ascending
    V = Rinv.T @ Y                     # original coords, G-orthonormal columns
    return w, V

def ip_G(a, b, G):
    return float(a @ G @ b)

# ----------------------------------------------------------------------------
def candidate_functionals(centers, s, G, T):
    """Build candidate collective-coordinate directions as G-normalized coefficient vectors.
       Each candidate is a functional g -> L(g); we represent it as the vector c s.t.
       L(phi)=<c, phi>_G.  For a point/packet functional we sample its kernel at centers.
       (a) delta at log2: evaluation g->g(log2) ~ bump kernel centered to peak the value at log2
       (b) low-frequency packet: cos(omega x) with small omega (omega->0 limit: constant)
       (c) prime-phase packet:  sum_p (Lambda(p)/sqrt p) cos(x log p)
       (d) boundary delta at 0 (g->g(0)=||phi||^2 ; the trivial 'mass' direction)
       (e) prolate-ish: the top eigvec of the band-limit/time-limit projection (approx by
           Gaussian-weighted low-pass) -- we use the leading eigvec of the 'concentration'
           operator G itself (smoothest direction) as a proxy low-pass extremizer.
    All returned as G-normalized vectors (c^T G c = 1)."""
    C = np.array(centers)
    out = {}
    def norm(c):
        nn = np.sqrt(max(ip_G(c, c, G), 1e-300))
        return c / nn
    # (a) delta at log2: pick coefficient vector whose induced function peaks at log2.
    #     induced function f(x)=sum c_k Gauss(x-x_k); to evaluate g(log2) for g=phi*phi~ the
    #     natural functional vector is the Gram column for a bump at log2 -> sample exp(-(x_k-log2)^2/...)
    s2 = s*s
    out['delta_log2']  = norm(np.exp(-(C-LOG2)**2/(4*s2)))
    out['delta_0']     = norm(np.exp(-(C-0.0)**2/(4*s2)))
    out['delta_logT2'] = norm(np.exp(-(C-T/2.0)**2/(4*s2)))   # delta at support edge
    # (b) low-frequency packets cos(omega x)
    for om, name in [(0.0,'const'), (0.5,'cos0.5'), (1.0,'cos1.0'), (2.0,'cos2.0')]:
        out['lowfreq_'+name] = norm(np.cos(om*C))
    # (c) prime-phase packet  sum_p (Lambda(p)/sqrt p) cos(x log p)  (primes p<=e^T)
    PP = prime_powers(float(np.exp(T)))
    ppphase = np.zeros(len(C))
    for (u, w, p, k) in PP:
        ppphase += w * np.cos(C*u)
    out['prime_phase'] = norm(ppphase)
    # (e) smoothest direction: leading eigvec of G (largest eigenvalue = lowest 'frequency')
    wG, VG = np.linalg.eigh(G)
    out['smoothest_G'] = norm(VG[:, -1])
    return out

# ----------------------------------------------------------------------------
def analyze(T, centers, s, Gmat):
    PP = prime_powers(float(np.exp(T)))
    PR = prime_matrix(centers, s, PP)
    # eigendecomp of Q_prime,T in G-metric
    w, V = gen_eig(PR, Gmat)
    # sort by magnitude descending
    order = np.argsort(-np.abs(w))
    w = w[order]; V = V[:, order]
    return w, V, PP, PR

# ============================================================================
if __name__ == '__main__':
    # FIXED basis covering up to log7+ (so we can probe log2<T<log7).
    # centers span [-Xmax, Xmax] in additive coordinate; we keep them FIXED across T.
    Xmax = 1.05   # half-support; covers x=log p up to ~ e^{2.1}~8 . log7=1.946 < 2.1.
    NB = 21
    centers = list(np.linspace(-Xmax, Xmax, NB))
    s = 0.16      # fixed width, well-conditioned for this spacing
    Gmat = gram(centers, s)
    condG = np.linalg.cond(Gmat)
    print(f"FIXED BASIS: NB={NB} centers in [{-Xmax},{Xmax}], s={s}, cond(G)={condG:.2e}")
    print(f"log2={LOG2:.4f} log3={float(mp.log(3)):.4f} log4={float(mp.log(4)):.4f} "
          f"log5={float(mp.log(5)):.4f} log7={float(mp.log(7)):.4f}")
    print()

    # T grid straddling log2..log7, dense near crossings
    crossings = []
    for (u, w, p, k) in prime_powers(50):
        if u <= 2.0:
            crossings.append((u, p**k, p, k))
    Tgrid = sorted(set(
        [round(t,4) for t in np.linspace(0.5, 2.0, 31)] +
        [round(u+0.02,4) for (u,n,p,k) in crossings] +
        [round(u-0.02,4) for (u,n,p,k) in crossings if u>0.5]
    ))
    Tgrid = [t for t in Tgrid if 0.5 <= t <= 2.0]

    cand_names = list(candidate_functionals(centers, s, Gmat, 2.0).keys())
    records = []
    v_prev = None
    print(f"{'T':>6} {'#pp':>4} {'lam1':>10} {'lam2':>10} {'|lam2/lam1|':>11} "
          f"{'rank1err':>9} {'effrank':>7} {'drift':>7}  top_overlap")
    for T in Tgrid:
        w, V, PP, PR = analyze(T, centers, s, Gmat)
        npp = len(PP)
        lam1 = w[0]; v1 = V[:,0]
        lam2 = w[1] if len(w)>1 else 0.0
        # rank-1 approximation error in G-Frobenius:  ||PR - lam1 v1 v1^T_G|| / ||PR||
        # In G-metric, PR = sum mu_a (G v_a)(G v_a)^T / ... easier: Frobenius of eigenvalues.
        fro_all = np.sqrt(np.sum(w**2))
        rank1err = np.sqrt(np.sum(w[1:]**2)) / fro_all if fro_all>0 else 0.0
        # effective rank (participation ratio of |eigenvalues|, like the prior 1.17 metric)
        aw = np.abs(w); effrank = (aw.sum()**2)/np.sum(aw**2) if aw.sum()>0 else 0.0
        # sign-fix v1 (largest |component| positive) for drift tracking
        k0 = np.argmax(np.abs(v1));
        if v1[k0] < 0: v1 = -v1
        # drift = 1 - |<v1(T), v1(T_prev)>_G|
        drift = np.nan
        if v_prev is not None:
            ov = abs(ip_G(v1, v_prev, Gmat))
            drift = 1 - ov
        v_prev = v1.copy()
        # overlaps with candidates
        cands = candidate_functionals(centers, s, Gmat, T)
        overlaps = {nm: abs(ip_G(v1, cands[nm], Gmat)) for nm in cands}
        top = max(overlaps, key=overlaps.get)
        records.append({'T':T, 'npp':npp, 'lam1':lam1, 'lam2':lam2,
                        'ratio': abs(lam2/lam1) if lam1!=0 else 0.0,
                        'rank1err':rank1err, 'effrank':effrank, 'drift':drift,
                        'eigs': w.tolist(),
                        'overlaps':overlaps, 'top':top,
                        'v1': v1.tolist()})
        print(f"{T:6.3f} {npp:4d} {lam1:10.4f} {lam2:10.4f} {abs(lam2/lam1):11.4f} "
              f"{rank1err:9.4f} {effrank:7.3f} {drift if not np.isnan(drift) else -1:7.4f}  "
              f"{top}={overlaps[top]:.3f}")

    json.dump({'centers':centers,'s':s,'condG':condG,'records':records},
              open('prime_rank_collective.json','w'), indent=1)
    print("\nSaved prime_rank_collective.json")
