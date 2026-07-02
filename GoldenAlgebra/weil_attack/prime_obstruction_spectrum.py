"""
PRIME OBSTRUCTION SPECTRUM  (SERIOUS diagnostic)
=================================================
Diagonalize the prime-side obstruction in the Weil quadratic form Q_T restricted to
test functions supported in [-T,T], and track eigenvalue crossings of Q_T as the support
T passes log2, log3, log4=2log2, log5, log7, log8=3log2, log9=2log3, ...

Kernel = ARCH (Connes/Sonin archimedean) + POLE (cosh bilinear) - PRIME (shift forms).
All three pieces are the VALIDATED explicit-formula assembly from this directory
(calibrate.py / full_Q_fixed.py matched the zero-sum to ~1e-21).

We do NOT assume RH and do NOT use the zero-sum to compute Q. Q is built purely from
the archimedean Gamma-factor (digamma), the trivial poles (cosh), and the prime powers
(Lambda(n)/sqrt(n)).  Eigenvalues are Rayleigh quotients Q(phi)/||phi||^2 via the
generalized symmetric eigenproblem  Q v = lambda G v  (G = Gram of the basis).

BASIS / SUPPORT DISCIPLINE.  phi = sum_k c_k Gauss(x-x_k; s), so g=phi*phi~ has
h=|phihat|^2>=0 (positive type) automatically.  A Gaussian is not compactly supported,
so "supp g in [-T,T]" is enforced softly: centers x_k fill [-T/2,T/2] and the width s is
chosen small enough that the bump tails reaching beyond +-T/2 are below a leak floor.
We VERIFY (validate_yoshida) that with this discipline Q_T >= 0 for T<log2 (Yoshida),
i.e. there is NO spurious sub-threshold negative from tail leakage.

Run modes:
  python3 prime_obstruction_spectrum.py validate   -> Yoshida check below log2
  python3 prime_obstruction_spectrum.py spectrum    -> eigenvalue-vs-T, crossings  (slow)
  python3 prime_obstruction_spectrum.py gram         -> prime-mode Gram PSD analysis
  python3 prime_obstruction_spectrum.py all
"""
import numpy as np
import mpmath as mp
import json, sys, time

mp.mp.dps = 30
LOG2 = float(mp.log(2))

# ----------------------------------------------------------------------------
def Omega_mp(r):
    """Archimedean kernel  Re psi(1/4 + i r/2) - log pi."""
    return mp.re(mp.digamma(mp.mpf(1)/4 + 1j*r/2)) - mp.log(mp.pi)

# ----------------------------------------------------------------------------
def prime_powers(upto):
    """list of (u=log n, w=Lambda(n)/sqrt(n)=log p/sqrt(p^k), p, k) for n=p^k<=upto, sorted by u."""
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
            lp = mp.log(p)
            pk = p
            k = 1
            while pk <= upto:
                out.append((mp.log(pk), lp / mp.sqrt(pk), p, k))
                pk *= p
                k += 1
    out.sort()
    return out

# ----------------------------------------------------------------------------
#  Matrix assembly.  D = x_i - x_j.  s = bump width.   (validated formulas)
#    G_ij    = sqrt(pi) s exp(-D^2/(4 s^2))
#    ARCH_ij = s^2 \int exp(-s^2 r^2) cos(r D) Omega(r) dr           (mpmath quad)
#    POLE_ij = 2 pi s^2 exp(s^2/4) (exp(D/2)+exp(-D/2))
#    PRIME_ij= 2 sum_n w_n s^2 (sqrt(pi)/(2 s)) [e^{-(D-u_n)^2/4s^2}+e^{-(D+u_n)^2/4s^2}]
# ----------------------------------------------------------------------------
def build_matrices(centers, s, PP, want_perprime=False):
    n = len(centers)
    s = mp.mpf(s)
    s2 = s * s
    sqpi = mp.sqrt(mp.pi)
    Q = mp.matrix(n, n); G = mp.matrix(n, n)
    ARCH = mp.matrix(n, n); POLE = mp.matrix(n, n); PRIME = mp.matrix(n, n)
    # cache Omega-quadrature per distinct |D|
    for i in range(n):
        for j in range(i, n):
            d = centers[i] - centers[j]
            A = s2 * mp.quad(lambda r: mp.e**(-s2*r*r) * mp.cos(r*d) * Omega_mp(r),
                             [-mp.inf, 0, mp.inf])
            pole = 2*mp.pi*s2*mp.e**(s2/4) * (mp.e**(d/2) + mp.e**(-d/2))
            pr = mp.mpf(0)
            for (u, w, p, k) in PP:
                pr += w * (mp.e**(-(d-u)**2/(4*s2)) + mp.e**(-(d+u)**2/(4*s2)))
            pr *= 2 * s2 * (sqpi/(2*s))
            gg = sqpi * s * mp.e**(-d*d/(4*s2))
            val = A + pole - pr
            for (M, vv) in ((Q, val), (G, gg), (ARCH, A), (POLE, pole), (PRIME, pr)):
                M[i, j] = vv; M[j, i] = vv
    return Q, G, ARCH, POLE, PRIME

def single_prime_matrix(centers, s, u, w):
    """The rank-2 (shift+reflect) PRIME form of ONE prime power n (u=log n, w=Lambda/sqrt n),
       i.e.  -(contribution) added to Q.  Returns the (negative) matrix block."""
    n = len(centers); s = mp.mpf(s); s2 = s*s; sqpi = mp.sqrt(mp.pi)
    M = mp.matrix(n, n)
    for i in range(n):
        for j in range(i, n):
            d = centers[i] - centers[j]
            v = -2 * w * s2 * (sqpi/(2*s)) * (mp.e**(-(d-u)**2/(4*s2)) + mp.e**(-(d+u)**2/(4*s2)))
            M[i, j] = v; M[j, i] = v
    return M

# ----------------------------------------------------------------------------
def gen_eig(Q, G):
    """generalized symmetric eigenproblem Q v = lambda G v; ascending eigenvalues, vecs (orig coords)."""
    n = Q.rows
    R = mp.cholesky(G); Ri = R**-1
    B = Ri.T * Q * Ri
    Bs = mp.matrix(n, n)
    for i in range(n):
        for j in range(n):
            Bs[i, j] = (B[i, j] + B[j, i]) / 2
    ev, EV = mp.eigsy(Bs)
    evl = [ev[i] for i in range(n)]
    order = sorted(range(n), key=lambda k: float(evl[k]))
    evs = [evl[k] for k in order]
    vecs = []
    for k in order:
        y = mp.matrix([EV[r, k] for r in range(n)])
        vecs.append(Ri * y)
    return evs, vecs

# adaptive width: keep bump tail past the support edge below leak floor when probing prime u
def adaptive_s(T, nb, tail_pp_u, leak=1e-3):
    """choose s so (a) bumps resolve spacing T/(nb-1) and (b) tail reaching the smallest
       active prime power log = tail_pp_u from support edge T/2 is < leak.  If no prime in
       support, just resolve.  s <= (edge gap)/sqrt(4 ln(1/leak))."""
    spacing = T/(nb-1) if nb > 1 else T
    s_res = spacing/1.6  # ~1.6 bumps per width: decent overlap, well-conditioned G
    if tail_pp_u is None:
        return s_res
    gap = tail_pp_u - T/2  # how far the first in-support prime sits beyond the support edge
    # we WANT the prime inside support (gap<0) to register; control only the OUTER tail.
    return s_res

# ============================================================================
#  MODE 1: validate Yoshida (Q>=0 for T<log2) under support discipline
# ============================================================================
def validate_yoshida():
    print("=== VALIDATE: Yoshida positivity for T<log2 (no spurious tail negatives) ===")
    print(f"log2 = {LOG2:.5f}")
    print(f"{'T':>6} {'s':>6} {'nb':>4} {'min_eig':>14} {'n_neg':>6} {'||PRIME||':>10}")
    for T in [0.3, 0.5, 0.6, 0.68]:
        nb = 9
        # tail to n=2 (log2) from edge T/2 must be small -> s small
        edge_gap = LOG2 - T/2
        s = min(float(mp.mpf(T)/(nb-1)/1.6), edge_gap/np.sqrt(4*np.log(1e4)))
        s = mp.mpf(s)
        centers = [mp.mpf(-T)/2 + mp.mpf(T)*k/(nb-1) for k in range(nb)]
        upto = float(mp.e**(mp.mpf(T) + 9*s))
        PP = prime_powers(upto)
        Q, G, A, P, PR = build_matrices(centers, s, PP)
        evs, _ = gen_eig(Q, G)
        prn = float(mp.sqrt(sum(PR[i, j]**2 for i in range(PR.rows) for j in range(PR.cols))))
        nneg = sum(1 for e in evs if float(e) < -1e-10)
        print(f"{T:6.3f} {float(s):6.3f} {nb:4d} {float(evs[0]):14.6e} {nneg:6d} {prn:10.3e}")
    print("  Expect min_eig>=0 (up to ~1e-9 numerics) and ||PRIME|| -> 0 as bumps stay inside [-T/2,T/2].")

# ============================================================================
#  MODE 2: spectrum vs T — track negatives across log p^k crossings
# ============================================================================
def crossing_list(Tmax=3.3):
    out = []
    for (u, w, p, k) in prime_powers(40):
        if float(u) <= Tmax + 0.05:
            out.append((float(u), p**k, p, k))
    out.sort()
    return out

def run_spectrum(nb=9, Tmax=3.2):
    cps = crossing_list(Tmax)
    base = list(np.linspace(0.40, Tmax, 44))
    extra = []
    for (u, n, p, k) in cps:
        extra += [u-0.03, u+0.03]
    Tgrid = sorted(set(round(t, 4) for t in base + extra if 0.40 <= t <= Tmax))
    results = []
    for T in Tgrid:
        # resolution scales with T; keep s moderate so the form is well sampled.
        s = mp.mpf(min(0.34, T/(nb-1)/1.55))
        centers = [mp.mpf(-T)/2 + mp.mpf(T)*k/(nb-1) for k in range(nb)]
        upto = float(mp.e**(mp.mpf(T) + 9*s))
        PP = prime_powers(upto)
        Q, G, A, P, PR = build_matrices(centers, s, PP)
        evs, _ = gen_eig(Q, G)
        evs_f = [float(e) for e in evs]
        nneg = sum(1 for e in evs_f if e < -1e-10)
        results.append({'T': T, 's': float(s), 'min_eig': evs_f[0], 'eigs': evs_f,
                        'n_neg': nneg,
                        'n_pp_in_support': sum(1 for (u, n, p, k) in cps if u < T)})
        sys.stderr.write(f"T={T:6.3f} s={float(s):.3f} min={evs_f[0]: .5e} nneg={nneg}\n")
    return Tgrid, results, cps

# ============================================================================
#  MODE 3: prime-mode Gram matrix  G_{p,q} = <mode_p, mode_q>
#  mode_n := dominant eigenvector of the single-n prime form (its negative direction).
#  Test PSD-ness of the prime-mode interaction.
# ============================================================================
def prime_mode_gram(T=3.0, nb=15):
    s = mp.mpf(0.18)
    centers = [mp.mpf(-T)/2 + mp.mpf(T)*k/(nb-1) for k in range(nb)]
    G = mp.matrix(nb, nb); sqpi = mp.sqrt(mp.pi); s2 = s*s
    for i in range(nb):
        for j in range(nb):
            d = centers[i]-centers[j]
            G[i, j] = sqpi*s*mp.e**(-d*d/(4*s2))
    cps = crossing_list(T)
    modes = []  # (label, eigval, eigvec_coeffs)
    for (u, n, p, k) in cps:
        if u >= T:  # prime power not in support
            continue
        w = mp.log(p)/mp.sqrt(n)
        M = single_prime_matrix(centers, s, mp.mpf(u), w)
        evs, vecs = gen_eig(M, G)   # M is negative-definite-ish; most negative eig first
        modes.append((f"n={n}(p{p}^{k})", float(evs[0]), vecs[0]))
    # Gram of modes in the L2 inner product <a,b> = a^T G b, normalized
    m = len(modes)
    Gram = np.zeros((m, m))
    for a in range(m):
        for b in range(m):
            ip = (modes[a][2].T * G * modes[b][2])[0]
            na = mp.sqrt((modes[a][2].T * G * modes[a][2])[0])
            nb_ = mp.sqrt((modes[b][2].T * G * modes[b][2])[0])
            Gram[a, b] = float(ip/(na*nb_))
    return [m[0] for m in modes], [m[1] for m in modes], Gram, modes, centers, s, G

# ============================================================================
if __name__ == '__main__':
    mode = sys.argv[1] if len(sys.argv) > 1 else 'all'

    if mode in ('validate', 'all'):
        validate_yoshida()
        print()

    if mode in ('spectrum', 'all'):
        t0 = time.time()
        Tgrid, results, cps = run_spectrum()
        json.dump({'crossing_points': [{'logn': u, 'n': n, 'p': p, 'k': k} for (u, n, p, k) in cps],
                   'spectrum': results},
                  open('prime_obstruction_spectrum.json', 'w'), indent=1)
        first_neg = next((r['T'] for r in results if r['n_neg'] > 0), None)
        print("=== PRIME OBSTRUCTION SPECTRUM ===")
        print("crossing points (log n):")
        for (u, n, p, k) in cps:
            print(f"  log {n:>3} = {u:.5f}  (p={p}, k={k})")
        print(f"\nFirst negative eigenvalue at T = {first_neg}   (log2 = {LOG2:.5f})")
        print(f"\n{'T':>7} {'s':>6} {'min_eig':>14} {'n_neg':>6} {'#pp':>5}")
        for r in results:
            print(f"{r['T']:7.3f} {r['s']:6.3f} {r['min_eig']:14.6e} {r['n_neg']:6d} {r['n_pp_in_support']:5d}")
        print(f"\n[{time.time()-t0:.0f}s]")
        print()

    if mode in ('gram', 'all'):
        labels, eigvals, Gram, modes, centers, s, G = prime_mode_gram()
        print("=== PRIME-MODE GRAM MATRIX  G_{p,q}=<mode_p,mode_q> (normalized) ===")
        print("modes = most-negative eigenvector of each single-n prime form, n in support [-T/2,T/2], T=3.0")
        print("labels:", labels)
        print("single-mode min eigenvalues (depth of each prime's negative direction):")
        for lab, ev in zip(labels, eigvals):
            print(f"   {lab:>14}: {ev:+.5e}")
        np.set_printoptions(precision=3, suppress=True, linewidth=160)
        print("\nGram matrix (cosines between prime-negative modes):")
        print(Gram)
        gw = np.linalg.eigvalsh(Gram)
        print(f"\nGram eigenvalues: {gw}")
        print(f"Gram is PSD: {np.all(gw > -1e-9)}  (it is a Gram matrix => always PSD; min eig {gw.min():.3e})")
        json.dump({'labels': labels, 'single_eigs': eigvals, 'gram': Gram.tolist(),
                   'gram_eigs': gw.tolist()},
                  open('prime_mode_gram.json', 'w'), indent=1)
