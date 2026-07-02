"""
FAST prime obstruction spectrum sweep.
Same VALIDATED assembly (cosh POLE, matched to zero-sum ~3e-8) but ARCH via a single fine
precomputed Omega grid + numpy trapezoid (good to ~1e-8, ample to locate eigenvalue crossings
that are O(1e-3..1)).  Cross-checked against the mpmath dps=30 version at sample T.

Tracks, as T sweeps past log2, log3, log4=2log2, log5, log7, log8, log9, log11, ...:
   - min generalized eigenvalue of Q_T (Q v = lambda G v)
   - dimension of the negative eigenspace
   - full eigenvalue vector
Support discipline: centers fill [-T/2,T/2]; s scales with T so the form is well sampled
and bump tails past support are controlled (validated Yoshida >=0 below log2).
"""
import numpy as np
import mpmath as mp
import json, sys

mp.mp.dps = 25
LOG2 = float(mp.log(2))

# precompute Omega on a fine grid (this is the only transcendental piece)
RG = np.linspace(-500, 500, 400001)
OM = np.array([float(mp.re(mp.digamma(0.25 + 1j*r/2)) - mp.log(mp.pi)) for r in RG])
DR = RG[1] - RG[0]

def prime_powers(upto):
    out = []
    P = int(upto) + 2
    if P < 2:
        return out
    sieve = bytearray([1])*(P+1); sieve[0] = sieve[1] = 0
    i = 2
    while i*i <= P:
        if sieve[i]:
            for j in range(i*i, P+1, i):
                sieve[j] = 0
        i += 1
    for p in range(2, P+1):
        if sieve[p]:
            lp = float(mp.log(p)); pk = p; k = 1
            while pk <= upto:
                out.append((float(mp.log(pk)), lp/np.sqrt(pk), p, k)); pk *= p; k += 1
    out.sort()
    return out

def build(centers, s, PP):
    C = np.asarray(centers, float); n = len(C); s2 = s*s; D = C[:, None]-C[None, :]
    sqpi = np.sqrt(np.pi)
    # ARCH: s^2 \int e^{-s2 r2} cos(rD) Omega dr   (even integrand)
    base = s2*np.exp(-s2*RG**2)*OM
    A = np.empty((n, n))
    for i in range(n):
        for j in range(i, n):
            v = np.trapezoid(base*np.cos(RG*D[i, j]), RG); A[i, j] = v; A[j, i] = v
    POLE = 2*np.pi*s2*np.exp(s2/4)*(np.exp(D/2)+np.exp(-D/2))
    PRIME = np.zeros((n, n))
    for (u, w, p, k) in PP:
        PRIME += 2*w*s2*(sqpi/(2*s))*(np.exp(-(D-u)**2/(4*s2))+np.exp(-(D+u)**2/(4*s2)))
    Q = A + POLE - PRIME
    G = sqpi*s*np.exp(-D**2/(4*s2))
    return Q, G, A, POLE, PRIME

def gen_eig(Q, G):
    Qs = (Q+Q.T)/2; Gs = (G+G.T)/2
    w, V = np.linalg.eigh(Gs)
    keep = w > w.max()*1e-12
    U = V[:, keep]/np.sqrt(w[keep])
    B = U.T@Qs@U; B = (B+B.T)/2
    ev, EV = np.linalg.eigh(B)
    vecs = U@EV
    return ev, vecs   # ascending

def crossing_list(Tmax):
    out = []
    for (u, w, p, k) in prime_powers(60):
        if u <= Tmax+0.05:
            out.append((u, p**k, p, k))
    out.sort()
    return out

def sweep(nb=11, Tmax=3.4, smax=0.30):
    cps = crossing_list(Tmax)
    base = list(np.linspace(0.40, Tmax, 120))
    extra = []
    for (u, n, p, k) in cps:
        extra += [u-0.02, u+0.02, u]
    Tgrid = sorted(set(round(t, 4) for t in base+extra if 0.40 <= t <= Tmax))
    results = []
    for T in Tgrid:
        s = min(smax, T/(nb-1)/1.5)
        centers = list(np.linspace(-T/2, T/2, nb))
        upto = float(np.exp(T + 9*s))
        PP = prime_powers(upto)
        Q, G, A, P, PR = build(centers, s, PP)
        ev, _ = gen_eig(Q, G)
        nneg = int(np.sum(ev < -1e-9))
        results.append({'T': T, 's': s, 'min_eig': float(ev[0]), 'eigs': ev.tolist(),
                        'n_neg': nneg,
                        'n_pp_in_support': sum(1 for (u, n, p, k) in cps if u < T)})
        sys.stderr.write(f"T={T:6.3f} s={s:.3f} min={ev[0]: .5e} nneg={nneg}\n")
    return Tgrid, results, cps

if __name__ == '__main__':
    Tgrid, results, cps = sweep()
    json.dump({'crossing_points': [{'logn': u, 'n': n, 'p': p, 'k': k} for (u, n, p, k) in cps],
               'spectrum': results, 'method': 'fast numpy, cosh-POLE validated'},
              open('prime_obstruction_spectrum_fast.json', 'w'), indent=1)
    first_neg = next((r['T'] for r in results if r['n_neg'] > 0), None)
    print("=== FAST PRIME OBSTRUCTION SPECTRUM ===")
    print(f"first negative eigenvalue at T = {first_neg}  (log2={LOG2:.5f})")
    print("crossing points:")
    for (u, n, p, k) in cps:
        print(f"  log {n:>3} = {u:.5f}  (p={p} k={k})")
    print(f"\n{'T':>7} {'s':>6} {'min_eig':>14} {'n_neg':>6} {'#pp':>5}")
    prev = None
    for r in results:
        mark = ''
        for (u, n, p, k) in cps:
            if (prev is not None) and prev < u <= r['T']:
                mark = f'  <-- crossed log{n}'
        print(f"{r['T']:7.3f} {r['s']:6.3f} {r['min_eig']:14.6e} {r['n_neg']:6d} {r['n_pp_in_support']:5d}{mark}")
        prev = r['T']
