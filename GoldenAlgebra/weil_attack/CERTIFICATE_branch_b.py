"""
=============================================================================================
CERTIFICATE (branch b): natural constrained expansions of the Yoshida cone past log2 DIE.
The n=2 negative mode cannot be neutralized while keeping the arithmetic coupling alive.
=============================================================================================
This consolidates the decisive experiments (all in weil_attack/, all UNCONDITIONAL: Q built
from ARCH+POLE-PRIME directly, NEVER the zero-sum). Engine verified: matrix Q matches the
zero-sum identity to ~1e-16 (numpy Gaussian) / explicit formula to ~1e-29 (calibrate.py),
with the CORRECT cosh-POLE bilinear phihat(i/2)*conj(phihat(-i/2)).

THE THREE FACTS:

(A) KNIFE-EDGE IN PRIME-SCALE (global_scale_gaussian.py, 1e-16 accurate engine, T=1.0 & 1.5
    > log2). min-eig of  Q_alpha = ARCH+POLE - alpha*PRIME  vs alpha:
        alpha:    0.0    0.5    0.8    0.9    1.0(ZETA)   1.1     1.2    1.5
        T=1.0:  -1.40  -0.69  -0.27  -0.13   +6.7e-17   -0.16   -0.33  -0.86
        T=1.5:  -2.06  -1.03  -0.41  -0.20   -3.7e-14   -0.31   -0.61  -1.54
    => PSD at EXACTLY alpha=1 (true zeta prime data), min-eig=0 (tangent), STRICTLY NEGATIVE
       for any other alpha. No positive margin: the form is on the knife edge precisely at the
       arithmetic value. Past log2 the prime sum is genuinely active; positivity holds at
       alpha=1 only.

(B) SAME KNIFE-EDGE IN THE n=2 COEFFICIENT (c2_sweep_dh.py, exact single-prime regime,
    log2<T<log3, compact basis so prime cutoff EXACT). min-eig of
        Q_{c2} = ARCH+POLE - 2*(c2/sqrt2)*g(log2)   vs c2:
        c2:     -1.0    0.0    0.4   0.693=Lambda(2)   0.8    1.0    2.0
        mineig: -0.74  -0.19  -0.03    +1.3e-5        -0.02  -0.15  -0.84
    => PSD only at c2 = Lambda(2)=log2. The ZETA value sits at the unique tipping point;
       peak->0 under refinement (knife_edge.py: argmax_c2 -> log2, peak_mineig -> 0).
    DH-DISTINCTION: the Davenport-Heilbronn n=2 coefficient is c(2) = -1.386 (dh_contrast.py),
       NEGATIVE (no Lambda>=0, no Euler product). At c2=-1.386 the form min-eig ~ -1.0 (deep
       negative). So DH FAILS the n=2 positivity that zeta passes at the knife edge. The
       positivity is bought EXACTLY by c2=Lambda(2) = the prime-power coefficient.

(C) CONSTRAINTS DO NOT NEUTRALIZE THE n=2 MODE -- they only generically regularize
    (constrained_c2_window.py + constraint_reality_check.py). PSD c2-window widths at T=0.95,
    n=21 (window = {c2: min-eig_constrained(c2)>=0}):
        UNCONSTRAINED                     width 0.05  (knife edge)
        perp cos(x log2)  [2-adic mode]   width 0.275
        perp cos & sin(x log2)            width 0.60
        int g = 0                         width 0.275
        CONTROL perp cos(x*0.5)  [non-arith] width 0.275  <-- IDENTICAL to 2-adic
        CONTROL perp cos(x*1.7)  [non-arith] width 0.275  <-- IDENTICAL
        CONTROL random direction             width 0.275  <-- IDENTICAL
    => Removing ANY one basis direction (arithmetic or not) widens the window by the SAME
       amount. The 'expansion' is pure dimension-reduction of a near-singular form, NOT a
       2-adic-specific neutralization. The min-eigenvector under 'perp cos(x log2)' still has
       g(log2) = -0.108*g(0) != 0 (coupling NOT deleted) -- and the IDENTICAL vector arises
       from the non-arithmetic control. There is no constraint that targets and kills the n=2
       negative direction; it reappears for every c2 != Lambda(2).

VERDICT (branch b): The Yoshida cone {supp g subset (-log2,log2)} is sharp. Past log2 the form
ARCH+POLE-PRIME is positive-SEMIdefinite with min-eig EXACTLY 0 at the true zeta prime data and
INDEFINITE under any perturbation of that data. No natural constraint (2-adic orthogonality,
vanishing moment, even/odd, prime-mode orthogonality) opens a genuine unconditional margin:
each only regularizes generically, and the n=2 negative direction is structurally inseparable
from keeping the arithmetic coupling. Equivalently, Q>=0 just past log2 is exactly the
zero-sum being >=0 -- i.e. the statement that the low zeros are on-line -- which is conditional
(or numerical), not an unconditional structural certificate. This matches Bombieri (negative
eigenvalues track off-line zeros once support resolves them) and Connes-Consani (prolate scale
L=2log S). No new unconditional cone past log2 exists by these natural expansions.

Run the pieces:  python3 global_scale_gaussian.py ; python3 c2_sweep_dh.py ;
                 python3 knife_edge.py ; python3 constrained_c2_window.py ;
                 python3 constraint_reality_check.py ; python3 dh_contrast.py
"""
print(__doc__)
