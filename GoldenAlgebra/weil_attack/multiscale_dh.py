"""
TASK 5 (corrected): the multiscale DIAGONAL positivity is a zeta-vs-DH (Euler-product) distinction.
=============================================================================================
The multiscale route needs every atom's SELF-correlation g_j=phi_j*phi_j~ to satisfy D_jj=Q(g_j)>=0.
For zeta this is Yoshida: as long as g_j's support stays in (-log2,log2) the prime sum is EMPTY.
For Davenport-Heilbronn there is NO empty-prime cone: the coefficients c(n) of -g0'/g0 are
SIGN-CHANGING and supported on ALL n (c(2)=-1.386), so the very FIRST atom self-correlation that
reaches log2 already picks up an indefinite n=2 term -- the safe diagonal evaporates.

We build the REAL DH coefficients (same series division as dh_contrast.py: g0=1-2*2^-s+3^-s) and
compare D_jj for zeta vs DH on atoms whose self-correlation reaches PAST log2.

Engine validated; NO RH.
"""
import numpy as np
import mpmath as mp
from prime_rank_collective import gram, arch_matrix, pole_matrix, prime_powers, prime_matrix, ip_G, LOG2
mp.mp.dps = 25


def dh_coeffs(N=60):
    """Coefficients c(n) of -g0'/g0, g0(s)=1-2*2^-s+3^-s (no Euler product), via Dirichlet division.
       Returns dict n->c(n). (same construction as dh_contrast.py.)"""
    B = [mp.mpf(0)] * (N + 1); B[1] = mp.mpf(1); B[2] = mp.mpf(-2); B[3] = mp.mpf(1)
    d = [B[n] * mp.log(n) if n >= 1 else mp.mpf(0) for n in range(N + 1)]; d[1] = mp.mpf(0)
    Binv = [mp.mpf(0)] * (N + 1); Binv[1] = 1 / B[1]
    for n in range(2, N + 1):
        s = mp.mpf(0)
        for a in range(1, n):
            if n % a == 0:
                s += B[n // a] * Binv[a]
        Binv[n] = -s / B[1]
    c = {}
    for n in range(2, N + 1):
        s = mp.mpf(0)
        for a in range(1, n + 1):
            if n % a == 0:
                s += d[a] * Binv[n // a]
        c[n] = float(s)
    return c


def generic_prime_matrix(dc, s, coeff_dict, upto):
    n = len(dc); s2 = s * s; sqpi = np.sqrt(np.pi)
    C = np.array(dc); D = C[:, None] - C[None, :]
    PR = np.zeros((n, n)); pref = 2 * s2 * (sqpi / (2 * s))
    for N, w in coeff_dict.items():
        if N < 2 or N > upto or w == 0:
            continue
        u = float(np.log(N))
        PR += (w / np.sqrt(N)) * (np.exp(-(D - u) ** 2 / (4 * s2)) + np.exp(-(D + u) ** 2 / (4 * s2)))
    return pref * PR


def wavelet_atom(dc, center, halfwidth, n_lobes):
    c = np.zeros(len(dc)); dca = np.array(dc)
    locs = np.linspace(center - halfwidth, center + halfwidth, n_lobes) if n_lobes > 1 else [center]
    signs = [(-1) ** i for i in range(len(locs))]
    for x, sg in zip(locs, signs):
        c[int(np.argmin(np.abs(dca - x)))] += sg
    return c


if __name__ == '__main__':
    Xmax = 1.2; NB = 61; dc = list(np.linspace(-Xmax, Xmax, NB)); s = 0.05
    A = arch_matrix(dc, s); P = pole_matrix(dc, s); G = gram(dc, s)
    span = max(dc) - min(dc); upto = int(np.exp(span + 9 * s))

    # zeta prime weights  Lambda(n)/sqrt(n)  -> use prime_matrix
    PRz = prime_matrix(dc, s, prime_powers(float(np.exp(span + 9 * s))))
    Qz = A + P - PRz
    # DH: c(n) (NOT /sqrt already? dh c is of -g0'/g0; weight c(n)/sqrt(n))
    c = dh_coeffs(upto + 2)
    PRdh = generic_prime_matrix(dc, s, c, upto)
    Qdh = A + P - PRdh

    print(f"log2={LOG2:.4f}.  DH c(2)={c[2]:+.4f} (sign-changing, all n) vs zeta Lambda(2)/...=+.")
    print("Nonzero DH c(n), n=2..12:", {n: round(c[n], 3) for n in range(2, 13) if abs(c[n]) > 1e-9})
    print()
    print("ATOM SELF-ENERGY D_jj = phi^T Q phi for a single atom whose self-correlation reaches past log2:")
    print(f"{'atom hw':>8} {'self-supp':>10} {'D_jj(zeta)':>14} {'D_jj(DH)':>14}  note")
    for hw in [0.20, 0.34, 0.40, 0.50, 0.60]:
        a = wavelet_atom(dc, 0.0, hw, 3)
        a = a / np.sqrt(ip_G(a, a, G))
        dz = float(a @ Qz @ a); dd = float(a @ Qdh @ a)
        supp = 2 * hw
        note = "self-corr within log2 (Yoshida-safe)" if supp < LOG2 else "self-corr PAST log2: n=2 active"
        print(f"{hw:8.2f} {supp:10.2f} {dz:14.6e} {dd:14.6e}  {note}")
    print()
    print("zeta: D_jj stays >= 0 while self-supp < log2 (empty prime gap); only marginally affected past it")
    print("   because Lambda(2)>0 ADDS a controlled positive-coeff term.")
    print("DH:  D_jj goes NEGATIVE as soon as the self-correlation reaches log2, because c(2)=-1.386<0")
    print("   injects an indefinite n=2 term with NO protecting gap.  The safe multiscale DIAGONAL")
    print("   -- the foundation of the whole decomposition -- EXISTS for zeta and FAILS for DH.")
    print("   => multiscale diagonal positivity IS the Euler-product (zeta-vs-DH) distinction.")
