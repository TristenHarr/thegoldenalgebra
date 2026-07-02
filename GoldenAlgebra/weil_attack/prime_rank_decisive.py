"""
DECISIVE rank + collective-coordinate diagnostic for Q_prime,T.
Reconciles the prior 'effective rank 1.17' claim, computes the TRUE rank of the WEIGHTED
form, identifies v_T, and tracks v_T(T) drift across each log p^k crossing.

Three things made precise here:
 (1) RECONCILE: prior Gram (rank 1.17) was the Gram of NORMALIZED single-mode eigenvectors
     (sign+magnitude stripped).  We compute BOTH:
       (i) the true eigenspectrum of the weighted Q_prime,T  (the real object)
       (ii) the Gram of normalized modes (to reproduce ~1.17 and show it discards magnitude).
 (2) EIGENVALUE DECAY of Q_prime,T per T -> actual numerical rank.
 (3) v_T(T): G-overlap of the dominant eigvec between consecutive T, BOTH within a fixed
     prime regime (must be 1) and ACROSS each crossing (the decisive 'does it move' test).
     Also the FIXED-vT cone test: pick v* = v_T at one T, impose <g,v*>_G=0, ask if Q_T>=0.
"""
import numpy as np
import mpmath as mp
import json
from prime_rank_collective import (Omega_mp, prime_powers, gram, arch_matrix, pole_matrix,
                                    prime_matrix, single_prime_matrix, gen_eig, ip_G, LOG2)
mp.mp.dps = 30

def safe_gen_eig(M, G, ridge=0.0):
    if ridge>0:
        G = G + ridge*np.eye(G.shape[0])
    return gen_eig(M, G)

# ---------------------------------------------------------------------------
# Use a MODERATELY conditioned fixed basis (fewer, wider bumps) to keep cond(G) sane,
# AND a finer one for the rank decay. Two bases -> robustness.
# ---------------------------------------------------------------------------
def make_basis(NB, Xmax, s):
    centers = list(np.linspace(-Xmax, Xmax, NB))
    G = gram(centers, s)
    return centers, s, G

def eig_spectrum(centers, s, G, T):
    PP = prime_powers(float(np.exp(T)))
    PR = prime_matrix(centers, s, PP)
    w, V = gen_eig(PR, G)
    order = np.argsort(-np.abs(w))
    return w[order], V[:,order], PP, PR

# ---------------------------------------------------------------------------
print("="*88)
print("PART 1: TRUE eigenspectrum of the WEIGHTED Q_prime,T  (the real object)")
print("="*88)
for (NB, Xmax, s) in [(15, 1.0, 0.20), (21, 1.05, 0.16)]:
    centers, s, G = make_basis(NB, Xmax, s)
    condG = np.linalg.cond(G)
    print(f"\nBASIS NB={NB} Xmax={Xmax} s={s} cond(G)={condG:.1e}")
    print(f"{'T':>6} {'#pp':>4}  top-6 |eigenvalues| of Q_prime,T (G-metric)        effrank rank1err")
    for T in [0.80, 1.10, 1.40, 1.65, 1.95]:
        w, V, PP, PR = eig_spectrum(centers, s, G, T)
        aw = np.abs(w)
        eff = (aw.sum()**2)/np.sum(aw**2)
        fro = np.sqrt(np.sum(w**2))
        r1 = np.sqrt(np.sum(w[1:]**2))/fro if fro>0 else 0
        top = "  ".join(f"{x:6.3f}" for x in aw[:6])
        print(f"{T:6.3f} {len(PP):4d}  {top}   {eff:6.2f}  {r1:6.3f}")

# ---------------------------------------------------------------------------
print("\n"+"="*88)
print("PART 2: RECONCILE prior 'rank 1.17' = Gram of NORMALIZED single-prime modes")
print("(strips magnitude & sign; only captures the common SHAPE, not the true rank)")
print("="*88)
centers, s, G = make_basis(21, 1.05, 0.16)
# single-prime modes, normalized (reproduce prior pipeline) but in the FIXED basis
PPc = [(u,w,p,k) for (u,w,p,k) in prime_powers(50) if u < 2.0]
modes = []
for (u,w,p,k) in PPc:
    M = single_prime_matrix(centers, s, u, w)
    ev, V = gen_eig(M, G)
    order = np.argsort(-np.abs(ev))
    v = V[:,order[0]]
    v = v/np.sqrt(ip_G(v,v,G))
    modes.append((f"n={p**k}", ev[order[0]], v))
m = len(modes)
Gram = np.zeros((m,m))
for a in range(m):
    for b in range(m):
        Gram[a,b] = ip_G(modes[a][2], modes[b][2], G)
gw = np.linalg.eigvalsh(Gram)
eff_norm = (np.abs(gw).sum()**2)/np.sum(gw**2)
print(f"normalized-mode Gram eigenvalues: {np.round(np.sort(gw)[::-1],3)}")
print(f"  -> top eig {gw.max():.3f} of trace {m}  ({100*gw.max()/m:.1f}% mass), effective rank {eff_norm:.3f}")
print("  THIS reproduces the prior ~1.17 'collinear' picture: the NORMALIZED modes share one")
print("  common shape.  But this is NOT the rank of Q_prime,T (Part 1) -- normalization deleted")
print("  the magnitudes AND each prime's SECOND rank-2 lobe.")
# Now the WEIGHTED, signed sum of the SAME single-prime forms = the true Q_prime at T=2.0:
PR_full = sum(single_prime_matrix(centers, s, u, w) for (u,w,p,k) in PPc)
wf, Vf = gen_eig(PR_full, G); wf = wf[np.argsort(-np.abs(wf))]
awf=np.abs(wf); print(f"\nWEIGHTED sum (true Q_prime, all these primes): top|eig|={awf[:6].round(3)}")
print(f"  effective rank of the WEIGHTED form = {(awf.sum()**2)/np.sum(awf**2):.2f}  (NOT ~1)")

# ---------------------------------------------------------------------------
print("\n"+"="*88)
print("PART 3: DOES v_T MOVE?  G-overlap of dominant eigvec across each crossing")
print("="*88)
centers, s, G = make_basis(21, 1.05, 0.16)
crossings = sorted(set(round(u,4) for (u,w,p,k) in prime_powers(50) if 0.5<u<2.0))
labels = {round(u,4):f"log{p**k}" for (u,w,p,k) in prime_powers(50)}
# sample just-before and just-after each crossing
def domvec(T):
    w,V,PP,PR = eig_spectrum(centers,s,G,T)
    v = V[:,0];
    k0=np.argmax(np.abs(v));
    if v[k0]<0: v=-v
    return w[0], v, len(PP)
print(f"{'crossing':>10} {'T-':>7}{'T+':>7}  {'|<v(T-),v(T+)>_G|':>18}  {'lam1 before':>11}{'lam1 after':>11}")
vt_at = {}
for u in crossings:
    eps=0.03
    l_b,v_b,n_b = domvec(u-eps)
    l_a,v_a,n_a = domvec(u+eps)
    ov = abs(ip_G(v_b,v_a,G))
    vt_at[u]=(v_a,l_a)
    print(f"{labels[u]:>10} {u-eps:7.3f}{u+eps:7.3f}  {ov:18.4f}  {l_b:11.4f}{l_a:11.4f}")
# overall: overlap of v_T at first regime vs last regime
v_first = domvec(0.80)[1]; v_last = domvec(1.95)[1]
print(f"\n  v_T at T=0.80 (1 prime) vs T=1.95 (5 primes):  |overlap|_G = {abs(ip_G(v_first,v_last,G)):.4f}")
print("  -> if << 1 the collective coordinate genuinely MOVES with T.")

# ---------------------------------------------------------------------------
print("\n"+"="*88)
print("PART 4: FIXED-vT CONE TEST.  Pick v* = dominant eigvec at one T0; impose <g,v*>_G=0;")
print("is the FULL Q_T = ARCH+POLE-PRIME >= 0 on that hyperplane for T>T0?  (vs random control)")
print("="*88)
ARCH = arch_matrix(centers, s)
POLE = pole_matrix(centers, s)
def full_Q(T):
    PP = prime_powers(float(np.exp(T)))
    return ARCH + POLE - prime_matrix(centers, s, PP)
def constrained_min_eig(Q, G, cvec):
    # cvec is the functional direction (coeff vector). constraint <g,cvec>_G=0 i.e. (G cvec)^T g=0.
    a = G @ cvec
    # nullspace of a^T  (1 x n) -> n-1 dim
    U,sv,Vt = np.linalg.svd(a.reshape(1,-1))
    K = Vt[1:].T   # n x (n-1)
    Qr = K.T@Q@K; Gr = K.T@G@K
    R = np.linalg.cholesky(Gr); Ri=np.linalg.inv(R)
    B = Ri@Qr@Ri.T; B=(B+B.T)/2
    return np.linalg.eigvalsh(B).min()
# v* from T0 = 0.80 (first regime, single prime). Then test at larger T.
v_star = domvec(0.80)[1]
rng = np.random.default_rng(0)
rand_dir = rng.standard_normal(len(centers)); rand_dir/=np.sqrt(ip_G(rand_dir,rand_dir,G))
print(f"v* = dominant eigvec of Q_prime at T0=0.80 (the single-prime collective coordinate)")
print(f"{'T':>6} {'Qmin uncon':>11} {'Qmin perp v*':>13} {'Qmin perp rand':>15} {'Qmin perp v_T(T)':>17}")
for T in [0.80, 0.95, 1.10, 1.40, 1.65, 1.95]:
    Q = full_Q(T)
    # unconstrained
    R=np.linalg.cholesky(G);Ri=np.linalg.inv(R);B=Ri@Q@Ri.T;m_un=np.linalg.eigvalsh((B+B.T)/2).min()
    m_vs = constrained_min_eig(Q,G,v_star)
    m_rd = constrained_min_eig(Q,G,rand_dir)
    # perp to the CURRENT (moving) v_T(T)
    vT = domvec(T)[1]
    m_vT = constrained_min_eig(Q,G,vT)
    print(f"{T:6.3f} {m_un:11.4e} {m_vs:13.4e} {m_rd:15.4e} {m_vT:17.4e}")
print("  CONE VERDICT: if 'perp v*' (FIXED) gives Qmin>=0 past log2 while 'perp rand' does NOT,")
print("  there is a fixed cone -> Q_prime rank-1 with fixed v_T.  If 'perp v*' ~ 'perp rand'")
print("  (both same generic lift) -> NO fixed cone -> v_T moves (the honest result).")
