"""
DOES SAFE-CONE MULTISCALE SATURATE THE OBSTRUCTION?  (the adversarial test)
=============================================================================================
multiscale_wavelet.py found: safe-cone atom families (every g_j=phi_j*phi_j~ in (-log2,log2),
D_jj>=0) give Q|_V PSD past log2, and capture only a small fraction of the full negative vstar.
ADVERSARIAL objection: maybe that's just because 9 atoms span a small subspace.  Here we ENRICH
the safe-cone family as much as possible -- many translations, multiple safe half-widths (true
multiscale), signed lobes -- and ask:

   As dim(V) grows (with EVERY diagonal still safe, 2*hw < log2), does
     (1) Q|_V stay PSD  (=> structural: safe self-cones cannot build the obstruction; PARTIAL
         POSITIVITY THEOREM past log2 on the multiscale class), or
     (2) Q|_V go negative  (=> richer interference reconstructs the obstruction; cone fails)?

We also compute ||P_V vstar||_G as dim V grows: does the safe family eventually CAPTURE the
obstruction (->1, then min-eig<0) or is it STRUCTURALLY BLOCKED (->plateau<1, min-eig>=0)?

CRITICAL CONTROL: we compare against an UNCONSTRAINED family of the SAME dimension whose atoms
are allowed wide self-support (2*hw > log2, diagonal NOT safe).  If the unconstrained family of
the same dim DOES capture vstar and go negative while the safe family does not, the safe-cone
constraint is doing real work (not just dimension).

Engine: validated ARCH+POLE-PRIME.  NO RH.  Zero-sum unused.
"""
import numpy as np
import mpmath as mp
from prime_rank_collective import (prime_powers, gram, arch_matrix, pole_matrix,
                                   prime_matrix, gen_eig, ip_G, LOG2)
mp.mp.dps = 30


def build_engine(dc, s):
    G = gram(dc, s); A = arch_matrix(dc, s); P = pole_matrix(dc, s)
    span = max(dc) - min(dc)
    PP = prime_powers(float(np.exp(span + 9 * s)))
    PR = prime_matrix(dc, s, PP)
    return A + P - PR, G, PP


def wavelet_atom(dc, center, halfwidth, n_lobes):
    c = np.zeros(len(dc)); dca = np.array(dc)
    locs = np.linspace(center - halfwidth, center + halfwidth, n_lobes) if n_lobes > 1 else [center]
    signs = [(-1) ** i for i in range(len(locs))]
    for x, sg in zip(locs, signs):
        c[int(np.argmin(np.abs(dca - x)))] += sg
    return c


def restrict_spectrum(Q, G, atoms):
    m = len(atoms)
    Aa = np.array(atoms)
    M = Aa @ Q @ Aa.T; Gm = Aa @ G @ Aa.T
    M = (M + M.T) / 2; Gm = (Gm + Gm.T) / 2
    wG, UG = np.linalg.eigh(Gm)
    keep = wG > 1e-9 * wG.max()              # drop null space of the atom Gram
    r = int(keep.sum())
    # restrict to range of Gm via its eigenbasis, then solve generalized eig there
    U = UG[:, keep]; d = wG[keep]
    Whalf = U / np.sqrt(d)                    # Gm-orthonormalizer on the range
    B = Whalf.T @ M @ Whalf; B = (B + B.T) / 2
    wM, _ = np.linalg.eigh(B)
    return wM, r, np.diag(M)


def captured(Q, G, atoms, vstar):
    Aa = np.array(atoms)
    Gm = Aa @ G @ Aa.T; Gm = (Gm + Gm.T) / 2
    wG, UG = np.linalg.eigh(Gm)
    keep = wG > 1e-9 * wG.max()
    U = UG[:, keep]; d = wG[keep]
    Whalf = U / np.sqrt(d)
    E = Aa.T @ Whalf                          # dict-coords, G-orthonormal columns spanning V
    y = E.T @ (G @ vstar)
    return float(np.sqrt(np.sum(y ** 2)))


if __name__ == '__main__':
    print("=" * 92)
    Xmax = 1.4; NB = 71; dc = list(np.linspace(-Xmax, Xmax, NB)); s = 0.045
    Q, G, PP = build_engine(dc, s)
    w_full, V_full = gen_eig(Q, G); o = np.argsort(w_full)
    w_full = w_full[o]; V_full = V_full[:, o]
    vstar = V_full[:, 0]; vstar = vstar / np.sqrt(ip_G(vstar, vstar, G))
    print(f"FULL engine: min-eig={w_full[0]:+.4e} n_neg={int((w_full<-1e-9).sum())} #pp={len(PP)}")
    print(f"log2={LOG2:.4f}\n")

    # SAFE half-widths: all 2*hw < log2.  TRUE multiscale = several scales.
    SAFE_HW = [0.10, 0.20, 0.30]      # self-supports 0.20,0.40,0.60 all < 0.693 SAFE
    UNSAFE_HW = [0.45, 0.60]          # self-supports 0.90,1.20 > log2  NOT safe (control)

    print("SAFE multiscale family (every atom self-support < log2), growing # translations & scales:")
    print(f"{'n_trans':>8} {'lobes':>6} {'dimV':>6} {'min-eig Q|V':>14} {'captured':>9} {'sumD':>10} {'theta':>8}")
    for n_trans in [5, 9, 15, 21, 29]:
        for lobes in [2, 3]:
            atoms = []
            for hw in SAFE_HW:
                for ct in np.linspace(-1.1, 1.1, n_trans):
                    atoms.append(wavelet_atom(dc, ct, hw, lobes))
            wM, r, diag = restrict_spectrum(Q, G, atoms)
            cap = captured(Q, G, atoms, vstar)
            off = None
            # theta from full atom Gram
            Aa = np.array(atoms); M = Aa @ Q @ Aa.T
            sumD = np.trace(M); off = (np.triu(M, 1)).sum()
            theta = -off / sumD if sumD != 0 else float('nan')
            print(f"{n_trans:8d} {lobes:6d} {r:6d} {wM.min():+14.6e} {cap:9.4f} "
                  f"{sumD:10.3e} {theta:+8.4f}")
    print("  => if min-eig stays > 0 and captured plateaus < 1 as dimV grows: SAFE CONE BLOCKS the")
    print("     obstruction structurally (partial positivity past log2).  If min-eig<0: it fails.\n")

    print("CONTROL: UNSAFE family (atom self-support > log2, diagonal NOT in Yoshida cone), same dims:")
    print(f"{'n_trans':>8} {'lobes':>6} {'dimV':>6} {'min-eig Q|V':>14} {'captured':>9}")
    for n_trans in [5, 9, 15, 21, 29]:
        atoms = []
        for hw in UNSAFE_HW:
            for ct in np.linspace(-1.1, 1.1, n_trans):
                atoms.append(wavelet_atom(dc, ct, hw, 3))
        wM, r, diag = restrict_spectrum(Q, G, atoms)
        cap = captured(Q, G, atoms, vstar)
        print(f"{n_trans:8d} {3:6d} {r:6d} {wM.min():+14.6e} {cap:9.4f}")
    print("  => if the UNSAFE family of the same dim DOES go negative / capture vstar while the SAFE")
    print("     one does not, the safe-cone constraint -- not dimension -- is what blocks the obstruction.")
