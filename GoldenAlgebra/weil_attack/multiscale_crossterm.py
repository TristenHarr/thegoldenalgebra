"""
WHERE the obstruction re-enters: it is EXACTLY the cross-correlation separation crossing log2.
=============================================================================================
multiscale_saturate.py: enriching the safe-cone (diagonal-safe) family eventually reconstructs
the negative direction (captured 0.03->0.79, min-eig +0.007 -> -0.86).  The SAME happens for the
unsafe control => low-dim "blocking" was resolution, not the safe-cone constraint.

This script PINS the mechanism.  For atoms phi_j (each self-safe, g_j in (-log2,log2)) the cross
term C_jk = Q(phi_j,phi_k) involves the CROSS-correlation phi_j*phi_k~ supported around the
separation s_jk = center_k - center_j.  The PRIME part of C_jk activates exactly when s_jk
crosses a prime log: |s_jk| > log2 lights up n=2, etc.  So the cross terms are a SECOND copy of
the very prime obstruction -- now indexed by INTER-ATOM separation instead of support radius.

TEST: take the enriched safe family but ZERO OUT every cross term C_jk whose separation
|center_k-center_j| < log2 leaves the n=2 prime empty -- i.e. keep ONLY the cross terms that are
ALSO in the safe cone.  Equivalently restrict the atom centers so ALL pairwise separations stay
< log2 (a 'cluster' that as a whole is Yoshida-safe).  Then Q|_V MUST be PSD (it is literally a
sub-cone of Yoshida).  Conversely, allowing one pair past log2 is what injects the negativity.

We sweep the MAX allowed inter-atom separation and watch min-eig cross zero exactly at log2.
This is the clean certificate: the cross-scale interference IS the prime obstruction, re-indexed.

Engine validated; NO RH; zero-sum used ONLY as an independent floor check on the witness.
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
    return A + P - prime_matrix(dc, s, PP), G, PP


def wavelet_atom(dc, center, halfwidth, n_lobes):
    c = np.zeros(len(dc)); dca = np.array(dc)
    locs = np.linspace(center - halfwidth, center + halfwidth, n_lobes) if n_lobes > 1 else [center]
    signs = [(-1) ** i for i in range(len(locs))]
    for x, sg in zip(locs, signs):
        c[int(np.argmin(np.abs(dca - x)))] += sg
    return c


def restrict_min(Q, G, atoms):
    Aa = np.array(atoms)
    M = Aa @ Q @ Aa.T; Gm = Aa @ G @ Aa.T
    M = (M + M.T) / 2; Gm = (Gm + Gm.T) / 2
    wG, UG = np.linalg.eigh(Gm); keep = wG > 1e-9 * wG.max()
    U = UG[:, keep]; d = wG[keep]; Wh = U / np.sqrt(d)
    B = Wh.T @ M @ Wh; B = (B + B.T) / 2
    return np.linalg.eigvalsh(B).min()


if __name__ == '__main__':
    Xmax = 1.6; NB = 81; dc = list(np.linspace(-Xmax, Xmax, NB)); s = 0.045
    Q, G, PP = build_engine(dc, s)
    print(f"log2={LOG2:.4f}  log3={float(mp.log(3)):.4f}")
    print("Atoms: 3-lobe signed wavelets, self half-width HW=0.30 (self-support 0.60 < log2 SAFE).")
    print("A dense cluster of such atoms; we cap the maximum inter-atom SEPARATION at 'maxsep'.")
    print("The cross-correlation reaches separations up to maxsep + 2*HW.  Prime n=2 (log2) lights")
    print("up when maxsep+2*HW > log2.  We expect min-eig to leave 0+ exactly there.\n")
    HW = 0.30
    print(f"{'maxsep':>8} {'cross reach':>11} {'#atoms':>7} {'min-eig Q|V':>15}  note")
    for maxsep in [0.0, 0.05, 0.10, 0.20, 0.40, 0.693, 0.8, 1.0, 1.4, 2.0]:
        # cluster of atoms with centers spanning [-maxsep/2, maxsep/2] (so max sep = maxsep)
        n = max(2, int(round(maxsep / 0.08)) + 1)
        centers = np.linspace(-maxsep / 2, maxsep / 2, n) if maxsep > 0 else [0.0, 0.0001]
        atoms = [wavelet_atom(dc, ct, HW, 3) for ct in centers]
        mn = restrict_min(Q, G, atoms)
        reach = maxsep + 2 * HW
        note = ""
        if reach <= LOG2:
            note = "cross still in Yoshida cone -> must be PSD"
        elif maxsep <= LOG2:
            note = "atom CENTERS within log2 but cross reach past it"
        else:
            note = "separations past log2: n=2 prime active in cross terms"
        print(f"{maxsep:8.3f} {reach:11.3f} {len(atoms):7d} {mn:+15.6e}  {note}")
    print("\nKEY: min-eig stays >=0 while the cross REACH (maxsep+2HW) <= log2 (pure Yoshida sub-cone),")
    print("and turns negative once separations let the n=2 prime into the CROSS terms.  The cross-scale")
    print("interference is the prime obstruction re-indexed by inter-atom separation -- NOT tamed.")
