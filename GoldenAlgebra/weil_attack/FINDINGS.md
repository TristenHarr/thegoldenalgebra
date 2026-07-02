# Arithmetic Transfer Principle for RH — Weil Positivity Cone: Findings

Goal: find the largest test-function cone C on which Λ(n)≥0 + multiplicativity (Euler
product) UNCONDITIONALLY force the Weil quadratic form Q(g) ≥ 0, and pinpoint where C stops.

All scripts in this directory. Explicit formula verified to 28 digits (`calibrate.py`),
zero-sum cross-check matches matrix form to ~1e-21 for symmetric test functions.

## 1. The decomposition Q(g) = ARCH(g) + POLE(g) − PRIME(g)

For g = φ⋆φ̃ (positive type), h(r)=|φ̂(r)|² ≥ 0, g(u)=(1/2π)∫h(r)e^{iru}dr:

  ARCH(g)  = (1/2π) ∫ h(r) [ Re ψ(1/4 + ir/2) − log π ] dr        (archimedean place)
  POLE(g)  = h_c(i/2) + h_c(−i/2),  h_c(i/2)=φ̂(i/2)·\overline{φ̂(−i/2)}   (poles s=0,1)
  PRIME(g) = 2 Σ_{n≥2} Λ(n) n^{−1/2} g(log n)                       (finite places)

  Q(g) = Σ_ρ h(γ_ρ),   γ_ρ = (ρ−1/2)/i.   Q ≥ 0 ∀ pos-type g  ⟺  RH (Weil/Bombieri).

CRITICAL NORMALIZATION FIX (vs prior weil_attack scripts): the pole term is
h_c(i/2)=φ̂(i/2)·\overline{φ̂(−i/2)} (a PRODUCT / cosh bilinear), NOT |φ̂(i/2)|². Using the
square form gives a SPURIOUS +1.068 mismatch with the zero-sum for non-even φ; the cosh
form closes the identity to 1e-21. (See pole_matrix_check.py, full_Q_fixed.py.)

## 2. ARCH ≥ 0 is NOT pointwise; it is a Sonin-space property

Ω(r)=Re ψ(1/4+ir/2) − log π is NEGATIVE for small r (Ω(0)=−5.37, <0 until r≈7.6) — so the
archimedean kernel is pointwise indefinite. ARCH+POLE alone is also NOT ≥0 (sonin_pole.py).
Connes 2020 (arXiv:2006.13771): the archimedean Weil distribution is ≥0 exactly on the
SONIN SPACE — the orthogonal complement of the range of the phase-space cutoff projections
(prolate spheroidal), cutoff parameter 1. It is a GLOBAL quadratic-form positivity, not a
pointwise-kernel statement. Naive "total kernel K(r)≥0" arguments (prior total_kernel.py)
are the WRONG object — K(r)≡0 there is just the functional equation, hiding the zero sum.

## 3. Per-prime LOCAL factors are INDEFINITE — multiplicativity is ADDITIVE not factorized

The local factor at p: W_p(φ) = −((log p)/π) ∫ |φ̂(r)|² B_p(r) dr,
  B_p(r) = Re( z/(1−z) ),  z = p^{−1/2} e^{i r log p}.
B_p ranges from MIN = −p^{−1/2}/(1+p^{−1/2}) at r·log p=π  to  MAX = +p^{−1/2}/(1−p^{−1/2})
at r·log p=0. SIGN-CHANGING at EVERY prime (local_factors.py). So:
  - There is NO per-place positivity to multiply. The Euler product enters Q ADDITIVELY:
    Q = W_∞ + Σ_p W_p (sum of indefinite local forms), not a product of ≥0 factors.
  - The role of the Euler product is NOT factorized positivity. It is: (a) Λ(n) ≥ 0
    (one sign), and (b) Λ supported only on prime powers ⟹ first contribution at n=2.

## 4. THE CONE C — and where it stops

PRIME(g) = 2 Σ_{n≥2} Λ(n) n^{−1/2} g(log n) sees only n ≤ e^T for supp(g) ⊂ [−T,T].
  - T < log 2 (≈0.6931): the prime sum is EMPTY. Q = ARCH+POLE, and Q ≥ 0 UNCONDITIONALLY.
    This is YOSHIDA's theorem (positivity for support in the multiplicative interval (1/2,2),
    = additive (−log2, log2)). = the "Connes short-support" regime. PROVEN, classical.

  C = { g = φ⋆φ̃ : supp(g) ⊆ (−log 2, log 2) }  is the RIGOROUS unconditional cone.

  - PAST log 2: as soon as T>log2 the n=2 term Λ(2)2^{−1/2} g(log2) = (log2/√2) g(log2)
    enters. Because g(log2)=⟨φ,S_{log2}φ⟩ is sign-INDEFINITE (positive-type does NOT force
    g(a)≥0 for a≠0), PRIME has no sign. The prime form's indefiniteness (B_p sign-change,
    §3; D(ξ)=−2Re ζ'/ζ(1/2+iξ) sign-changes at ξ≈7.6, prime_indef.py) means there is NO
    unconditional certificate that ARCH+POLE dominates PRIME for general φ.

  WHERE C STOPS: at the FIRST PRIME, T = log 2. Beyond it, positivity of Q is no longer
  forced by Λ(n)≥0 alone; it becomes a statement about the actual LOCATION of zeros.

## 5. Is "Q≥0 on C" ⟹ RH, or PARTIAL?  → PROVABLY PARTIAL.

Bombieri ("Remarks on Weil's quadratic functional I"): the number of NEGATIVE eigenvalues
of the Weil form restricted to support [−t,t] equals (#off-line zeros)/2 — but ONLY once t
is large enough ("truncation big enough"). An off-line zero ρ=1/2+δ+iγ₀ injects a negative
eigenvalue only when the support can RESOLVE the displacement δ at height γ₀ (uncertainty:
t ≳ 1/δ). For bounded support, off-line zeros are INVISIBLE. Therefore:
  - Q ≥ 0 on the FULL space (all support) ⟺ RH.
  - Q ≥ 0 on the bounded-support cone C ⟹  NOTHING about RH (partial, RH-incomplete).
The cone C is a genuine PARTIAL unconditional theorem (Yoshida), NOT RH-equivalent.

## 6. Davenport–Heilbronn contrast — the EXACT failing step

DH function = combination of Dirichlet L-functions: SAME functional equation as ζ, NO Euler
product. Has zeros off the critical line. Its "−f'/f" Dirichlet coefficients c(n)
(dh_contrast.py):
  ζ:  a(n)=Λ(n) ≥ 0, supported ONLY on prime powers, first at n=2 ⟹ gap (−log2,log2).
  DH: c(n) SIGN-CHANGING, supported on ALL n, c(2)≠0 ⟹ NO gap, NO empty-prime cone.

FAILING STEP (in the chain of §1–§5): step 4. For DH there is no Λ(n)≥0 and no prime-power
support ⟹ the PRIME term has indefinite sign on EVERY support, including the shortest ⟹
the unconditional cone C = {supp ⊂ (−log2,log2)} does NOT EXIST. The archimedean place
(§2, Connes) is IDENTICAL for DH (same Γ-factor), so ARCH≥0 still holds; what DH loses is
precisely the arithmetic input that creates the cone. This is the meta-clue made exact:
the functional equation alone (shared by DH) gives the archimedean positivity but NOT the
cone; the cone is bought entirely by Λ(n)≥0 + prime-power support, i.e. the Euler product.

## VERDICT

- Largest UNCONDITIONAL cone found/confirmed: C = {g=φ⋆φ̃ : supp ⊆ (−log2, log2)} (Yoshida).
  Boundary: the first prime, T=log 2. We did NOT find a cone strictly larger than this on
  which Q≥0 is UNCONDITIONAL — past log2 the n=2 term is indefinite and ARCH+POLE does not
  provably dominate it (no certificate; true positivity there is equivalent to knowing the
  low zeros are on-line, which is conditional/numerical, not unconditional).
- The transfer is PARTIAL-UNCONDITIONAL, not RH-equivalent: bounded support cannot detect
  off-line zeros (resolution t≳1/δ), so positivity on C says nothing about RH.
- DH-failing step: step 4 — no Euler product ⟹ no Λ(n)≥0 and no prime-power gap ⟹ PRIME
  indefinite on all supports ⟹ no cone.

## 7. PRIME OBSTRUCTION SPECTRUM — diagonalizing Q_T (prime_obstruction_spectrum.py,
##    fast_spectrum.py, positivity_subspace.py, prime_mode_gram, floor_probe.py)

Built Q_T = ARCH + POLE − PRIME (validated cosh-POLE assembly, matched zero-sum to ~3e-8 on
ASYMMETRIC configs in floor_probe/cross-checks) as a generalized symmetric eigenproblem
Q v = λ G v in a Gaussian-bump basis, λ = Q(φ)/‖φ‖². Built from primes ONLY; zero-sum used
ONLY as an independent arithmetic check, never to define Q. No RH assumed.

(a) SUPPORT DISCIPLINE / YOSHIDA: with bump tails kept inside [−T/2,T/2], Q_T ≥ 0 for ALL
    T < log2 (min eig > 0), and min eig → 0⁺ monotonically as T → log2⁻ (0.11→3e-3→2e-4→1e-5).
    The sub-log2 "negatives" seen with fat bumps are pure tail leakage (||PRIME||→0 as s→0).

(b) SPECTRUM vs T (crossings log2,log3,log4=2log2,log5,log7,log8,log9,log11,…,log31):
    min eig decays MONOTONICALLY from 2e-5 (at log2) → 3e-7 (log3–log5) → ~1e-9 FLOOR band
    (log7 onward). NO retreat window; no second eigenvalue ever lifts off zero. Past ~log7 the
    min eig sits in the ±1e-9 numerical-floor band (G-conditioning × ARCH-quadrature).

(c) FLOOR PROBE (dps=40, well-conditioned bases, condG~10–18): at every "negative" T point
    (2.7–3.4) matrix_min ∈ [−2e-11,−4e-12] but the TRUE zero-sum on the exact min-eigenvector
    is POSITIVE (5e-15…1e-12). VERDICT: the negatives are the numerical FLOOR, not a genuine
    Q<0 direction. Q_T is PSD with its minimum eigenvalue pressed against zero — the RH-true
    signature (Q_T = Σ_ρ|φ̂(γ_ρ)|², lowest zeros give the smallest but POSITIVE Rayleigh value).

(d) PRIME-MODE GRAM (G_{p,q}=⟨mode_p,mode_q⟩, mode_n = most-negative eigvec of the single-n
    shift+reflect form; 12 prime powers in supp, T=3): single-mode depths all O(1) negative
    (−0.47…−2.15; higher p^k shallower since weight Λ/√n = log p/√(p^k) decays). The Gram has
    EFFECTIVE RANK 1.17 — 92.3% of its mass in ONE eigenvalue (11.07/12); every prime mode
    loads on the SAME common direction with magnitude ≈1/√12 and a per-prime SIGN (phase ~log p).
    ⟹ the negative directions are NOT prime-localized/independent. Each prime power adds its
    negative weight ALONG THE SAME bulk packet; what changes with the prime is only the SIGN.
    There is NO fixed subspace orthogonal to all prime modes simultaneously, because the active
    sign pattern Σ_p ±Λ(p)/√p changes as T admits new primes. The collinearity is exactly why
    "cone expansion" past log2 cannot be bought by projecting out a finite set of bad directions:
    the obstruction is one moving direction, balanced (under RH) by the zeros — not removable.

(e) ζ vs DH SIGNATURE (positivity_subspace.py, same ARCH+POLE, DH coeffs c(n) of −g₀'/g₀,
    g₀=1−2·2^{−s}+3^{−s}): at T=0.65 (BELOW log2) ζ has min eig +3.6e-5 (Yoshida cone intact)
    while DH has min eig −0.76 with TWO negative eigenvalues — O(1) deep, far above any floor.
    DH's first mode is at log2 (c(2)=−1.386≠0) and modes sit at EVERY log n, both signs ⟹ no
    empty-prime gap, negatives appear EARLIER (below log2) and DENSER. The invariant separating
    ζ from DH is precisely §7(d): ζ's prime-mode Gram is the collinear, one-sign-per-prime-power
    structure with the (−log2,log2) gap; DH has no gap and indefinite modes everywhere.

VERDICT (this diagnostic): NO positivity-preserving subspace strictly larger than the Yoshida
cone exists. The prime-side negative directions are ROBUST in the sense that they are present
(each prime adds one), but they are COLLINEAR — a single moving bulk direction whose sign flips
per prime — so they cannot be deflated away by a fixed subspace. This is the concrete mechanism
explaining why cone expansion fails: past log2 positivity is no longer a subspace property; it
is the explicit-formula balance between the (collinear) prime direction and the zeros, i.e. RH.

## 8. KNIFE-EDGE + CONSTRAINT CONTROLS — branch (b) certificate (independent route)

Scripts: `global_scale_gaussian.py`, `c2_sweep_dh.py`, `single_prime_exact.py`, `knife_edge.py`,
`constrained_c2_window.py`, `constraint_reality_check.py`, `CERTIFICATE_branch_b.py`. Engine
re-validated: numpy Gaussian Q matches the zero-sum to ~1e-16 INCLUDING the antisymmetric test
that exposed the old |φ̂(i/2)|² bug — confirms the cosh-POLE entry 2π s² e^{s²/4}(e^{d/2}+e^{−d/2}).
All Q built from ARCH+POLE−PRIME directly (unconditional); zero-sum only as an independent check.

(A) KNIFE-EDGE IN PRIME SCALE (accurate Gaussian engine, T=1.0 & 1.5 > log2, ALL primes):
    min-eig of Q_α = ARCH+POLE − α·PRIME vs α (α=1 = zeta):
      α       0.0   0.5   0.8   0.9    1.0(ζ)     1.1   1.2   1.5   2.0
      T=1.0: −1.40 −0.69 −0.27 −0.13  +6.7e-17  −0.16 −0.33 −0.86 −1.74
      T=1.5: −2.06 −1.03 −0.41 −0.20  −3.7e-14  −0.31 −0.61 −1.54 −3.08
    ⟹ PSD at EXACTLY α=1 (true ζ prime data); min-eig = 0 (tangent), STRICTLY NEGATIVE for
    every α≠1. Zero positive margin: the form sits on the knife edge precisely at α=1, past log2.

(B) KNIFE-EDGE IN THE n=2 COEFFICIENT (exact single-prime regime log2<T<log3, compact triangle
    basis so the prime cutoff is EXACT, only n=2 active). min-eig of
    Q_{c2}=ARCH+POLE − 2(c2/√2)g(log2) vs c2 (T=0.95, n=21):
      c2:     −1.0  0.0  0.4   0.693=Λ(2)   0.8   1.0   2.0
      mineig: −0.74 −0.19 −0.03  +1.3e-5    −0.02 −0.15 −0.84
    PSD ONLY at c2=Λ(2)=log2. knife_edge.py: as n→25 argmax→log2 (argmax−log2→−0.003 at T=1.05)
    and peak_mineig→0⁺ (2.1e-4→3.8e-5). DH-DISTINCTION: DH's n=2 coeff is c(2)=−1.386
    (sign-changing, no Λ≥0); at c2=−1.386 the same form has min-eig ≈ −0.9 (deep negative) ⟹ DH
    FAILS the n=2 positivity ζ passes at the edge. Positivity is bought EXACTLY by c2=Λ(2).

(C) CONSTRAINTS ONLY REGULARIZE (decisive control). PSD c2-window widths (= {c2: min-eig
    constrained ≥0}), T=0.95, n=21:
      UNCONSTRAINED ........................ 0.05  (knife edge)
      perp cos(x·log2) [2-adic mode] ....... 0.275
      perp cos & sin(x·log2) ............... 0.60
      ∫g = 0 .............................. 0.275
      CONTROL perp cos(x·0.5) [non-arith] .. 0.275  ← IDENTICAL to 2-adic constraint
      CONTROL perp cos(x·1.7) [non-arith] .. 0.275  ← IDENTICAL
      CONTROL random direction ............. 0.275  ← IDENTICAL
    Removing ANY one of 21 basis directions widens the window by the SAME amount ⟹ the
    "expansion" is generic dimension-reduction of a near-singular form, NOT a 2-adic-specific
    neutralization. The min-eigenvector under perp cos(x·log2) still has g(log2)=−0.108·g(0)≠0
    (coupling NOT deleted) and is BYTE-IDENTICAL to the non-arithmetic control vector. The n=2
    negative direction is inseparable from keeping the arithmetic coupling — it reappears for
    every c2≠Λ(2). (Same conclusion as §7(d) via collinearity, reached here via the c2 knife edge.)

VERDICT (branch b, banked): No new unconditional cone past log2 exists by natural constrained
expansion. Just past log2, ARCH+POLE−PRIME is positive-SEMIdefinite with min-eig EXACTLY 0 at
the true ζ prime data and INDEFINITE under any perturbation; positivity there IS the zero-sum
being ≥0 (low zeros on-line) = conditional, not structural. The Yoshida cone is SHARP. NOTE:
the old cone_past_log2.py "min-eig ≈ −18" was a TRUNCATION ARTIFACT (prime sum cut at n=2 with
wide Gaussians whose tails reach n=3,4); with the full prime sum the true form is ≈0, as it must
be (=zero-sum). Consistent with Bombieri (Mem. Lincei 2001) and Connes–Consani (prolate scale
L=2 log S).

## 9. RANK + COLLECTIVE COORDINATE of Q_prime,T — "rank-1" is ILLUSORY; v_T MOVES (the honest wall)
##    (prime_rank_collective.py, prime_rank_decisive.py, prime_cone_and_gate.py, prime_gate_clean.py)

The prior §7(d) "effective rank 1.17 / 92% mass in one eigenvalue" was the Gram of NORMALIZED
single-prime mode eigenvectors — magnitude AND sign stripped, keeping only the shared SHAPE. It
is NOT the rank of the actual obstruction. Computing the TRUE weighted form
  Q_prime,T = Σ_{n=p^k≤e^T} (Λ(n)/√n)·R_{log n},   R_u: g↦⟨g,(S_u+S_{−u})g⟩  (rank-2 shift+reflect)
as a matrix in a FIXED Gaussian-bump basis (centers/width independent of T, so v_T lives in one
coordinate space ∀T) and diagonalizing in the G-metric (Q_prime v = μ G v) gives:

(a) NOT RANK-ONE. Effective rank (participation ratio of |eigenvalues|) of Q_prime,T is
    ~9–13 (NB=15/21 bases), rank-1 Frobenius error 0.83–0.95, |λ2/λ1| ≈ 0.70–1.00. A single
    scalar λ1·⟨g,v1⟩² captures only ~48–52% of ‖Q_prime,T‖²_F. RECONCILIATION (prime_rank_decisive
    Part 2): redoing the OLD normalized-mode Gram in the fixed basis reproduces the collinear
    picture (one dominant Gram eig), but the SAME modes summed WITH their weights/signs give the
    weighted form whose effective rank is ~13. The 1.17 measured "all primes lean on one common
    packet SHAPE"; it did NOT measure rank, because (i) each prime's R_u is rank-TWO (a ± pair,
    not one direction) and (ii) the per-prime magnitudes Λ/√n and the alternating phase were
    deleted by normalization. The Euler obstruction is NOT one scalar pressure.

(b) v_T MOVES — decisively, in the early regime. G-overlap of the dominant eigvec across each
    crossing (3 independent bases, prime_gate_clean.py):
        crossing   |⟨v(T−),v(T+)⟩_G|   (NB=15 / NB=19 / NB=25)
        log2          0.28 / 0.052 / 0.044     ← v_T flips to a ~ORTHOGONAL direction
        log3          0.86 / 0.044 / 0.041     ← flips again
        log4          0.999/ 0.998 / 0.997     ← settles
        log5,log7     ~0.99 each               ← stable thereafter
        v(0.8) vs v(1.95):  0.84 / 0.003 / 0.013  (well-resolved bases: ≈ORTHOGONAL)
    MECHANISM: the top-2 eigenvalues of Q_prime,T are NEAR-DEGENERATE for T<log4 (T=0.80:
    |λ1|=0.831,|λ2|=0.829, rel-gap 0.003; T=1.10: rel-gap 0.10). Each new early prime rotates
    the dominant vector arbitrarily within the near-degenerate top block — so v_T is ill-defined /
    moving exactly while only a few primes are active. It STABILIZES (rel-gap→0.34 by log7) once
    several primes share the bulk packet. So: rank-1-BUT-MOVING in the regime that matters
    (just past log2), then a settled but still multi-dimensional (rank ~13) packet.

(c) THE CONE TEST — settled (prime_cone_and_gate.py, support-disciplined Weil engine matching the
    zero-sum to ~1e-15). At fixed T>log2, impose ⟨g,v_T⟩_G=0 on the POSITIVE-TYPE Q=ARCH+POLE−PRIME:
        T      Qmin uncon     perp v_T      perp random    perp cos(x·log2)
        0.95   −6.6e-16       +2.3e-16      +2.2e-16        +2.0e-16
        1.40   −1.6e-15       −1.2e-15      −1.6e-15        −1.5e-15
        1.95   −2.2e-12       −2.0e-12      −2.2e-12        −2.2e-12
    perp v_T ≡ perp random ≡ perp cos(x·log2) (all at the ~0 knife-edge floor). Removing the prime
    collective coordinate buys NO cone beyond what removing a RANDOM direction buys (Yoshida-agent
    control confirmed). RECONCILED with the rank-1 expectation: if Q_prime were rank-1 with a FIXED
    v_T, ⟨g,v_T⟩=0 WOULD give a cone. It does NOT — therefore v_T must move, exactly as (b) shows.
    rank-1-but-moving ⟹ no fixed orthogonal subspace ⟹ no cone. This is the honest structural
    explanation of the wall: there is no finite set of bad directions to project out.

(d) δT~1 GATE (prime_gate_clean.py, prime_cone_and_gate.py). An off-line zero ρ=1/2+δ+iγ enters the
    zero-sum at COMPLEX height γ_ρ=γ−iδ; for g of support [−T,T], h=ĝ is entire of exponential type
    T, so the zero's contribution is scaled by ≈e^{Tδ}. Detectability margin |e^{Tδ}−1|: <<1 for
    Tδ<<1, O(1) at Tδ≈1 (e^1−1=1.72). The prime channel matches this: Q_prime,T reaches separations
    u=log n only up to T (max log n in support = T), so it cannot resolve structure finer than 1/T;
    a displacement δ produces a feature at scale 1/δ, resolved only when T≳1/δ. Both give the SAME
    line δ=1/T. The prime-pressure scalar P_T(g)=λ_T·⟨g,v_T⟩² is the leading detector channel, but
    (per (a)) it is only ~50% of the obstruction — the off-line zero is detected when T crosses 1/δ,
    i.e. when the (moving, multi-mode) prime packet finally has the bandwidth to feel the displacement.

VERDICT (§9): The "rank-one prime obstruction" is ILLUSORY as a rank statement (true eff-rank ~13);
it was a rank-one SHAPE collinearity of normalized modes. The dominant collective coordinate v_T is
NOT fixed — it is near-degenerate and MOVES (≈orthogonal flips) as T crosses log2 and log3, settling
only after ~4 primes. Because v_T moves, ⟨g,v_T⟩=0 gives NO fixed cone (perp-v_T = perp-random,
confirmed on the positive-type form) — this is the clean, honest mechanism of the wall: the
obstruction is a single MOVING (and multi-mode) packet, not a removable fixed direction. The single
prime-pressure scalar λ_T⟨g,v_T⟩² is band-limited at scale ~T, reproducing the δ·T~1 detection gate;
but it carries only ~half the obstruction, so RH-positivity past log2 is the full (moving, high-rank)
explicit-formula balance — exactly as Bombieri/Connes–Consani predict, not a one-scalar simplification.

## 10. MULTISCALE / WAVELET ROUTE — cross-scale interference RECONSTRUCTS the obstruction
##     (multiscale_weil.py, multiscale_wavelet.py, multiscale_saturate.py, multiscale_crossterm.py,
##      multiscale_theta.py, multiscale_verdict.py, multiscale_moving_mode.py, multiscale_dh.py,
##      CERTIFICATE_multiscale.py)

NEW ROUTE: replace the single sharp Yoshida window by a Calderón/wavelet decomposition.
Write φ = Σ_j φ_j into ATOMS (translated+dilated signed wavelets) each SELF-SAFE: g_j=φ_j⋆φ̃_j
supported in (−log2,log2) ⟹ D_jj=Q(g_j)≥0 (Yoshida diagonal). Bilinearity (the Q matrix IS the
polarized Weil form on bumps): Q(Σφ_j)=Σ_j D_jj + 2Σ_{j<k} C_jk, C_jk=Q(φ_j,φ_k). All difficulty
is the cross-scale interference C; atoms tile total support PAST log2. Built ENTIRELY from the
validated ARCH+POLE−PRIME engine; NO RH; zero-sum only as an independent witness check.

(a) LOW-DIM SAFE FAMILIES are trivially PSD — but it's RESOLUTION, not the cone. A 9-atom safe
    family has Q|_V PSD past log2; so does an UNSAFE control of equal dim (multiscale_saturate.py).
    The obstruction captured by the atom span grows 0.03→0.79 as dim V grows.

(b) ENRICHED SAFE FAMILY GOES NEGATIVE. A 75-atom safe family (3 scales × 25 translations, EVERY
    D_jj ≥ +0.13) has min-eig Q|_V = −8.25e-3 < 0. The witness is GENUINE: its matrix Q value equals
    the direct ARCH+POLE−PRIME computation to full precision, prime part = explicit 2Σ Λ(n)/√n g(log n)
    = +1.4896 exactly (multiscale_verdict.py II). A real Weil-negative test function made of safe atoms.

(c) MECHANISM: cross terms ARE the prime obstruction re-indexed by SEPARATION (multiscale_crossterm.py).
    C_jk involves φ_j⋆φ̃_k near separation |c_k−c_j|; its prime part activates exactly when that
    separation crosses log2. Min-eig leaves the 0⁺ floor precisely as the cross reach passes log2.

(d) NO DIAGONALIZATION OF THE MOVING MODE (multiscale_moving_mode.py). Q_prime restricted to the
    multiscale span has eff-rank 14.09 (cf §9 ~13); its dominant obstruction eigenvector spreads over
    17.9 of 23 atoms. Multiscale does NOT localize one prime per scale — cross terms RE-ASSEMBLE the
    full high-rank moving packet across scales. The §9 wall is reconstructed, not tamed.

(e) THE EXACT INEQUALITY — θ<1 is NECESSARY-LOOKING but NOT SUFFICIENT (multiscale_theta.py). The
    asked-for bound Σ_{j<k}C_jk ≥ −θ Σ_j D_jj is a SCALAR (trace) statement; the controlling object
    is the MATRIX inequality C ⪰ −D ⟺ λ_min(D^{−1/2} C D^{−1/2}) ≥ −1:
        family                  θ        λ_min(C|D)   min-eig Q|V
        [0.3]×9                 0.4347    −0.9387      +8.42e-2  (PSD)
        [0.3]×17                0.3088    −0.9890      +3.42e-3  (PSD, edge)
        [0.2,0.3]×17            0.3395    −1.0005      −4.37e-4  (NEG)
        [0.12,0.22,0.3]×25      0.3535    −1.0013      −8.25e-3  (NEG)
        [0.1..0.32]×21          0.4257    −1.0016      −1.27e+0  (NEG)
    θ stays ~0.2–0.43 < 1 THROUGHOUT, while λ_min(C|D) crosses −1 EXACTLY when min-eig crosses 0. The
    cross matrix C is INDEFINITE (the rank-~13 moving obstruction), NOT a scalar fraction of D; it
    SATURATES C ⪰ −D (λ_min→−1.00…) and breaks it once the family resolves the obstruction.

(f) ζ vs DH (multiscale_dh.py). The route rests on the SAFE DIAGONAL D_jj≥0 = the empty (−log2,log2)
    prime gap. For Davenport–Heilbronn (real c(n) of −g₀'/g₀, g₀=1−2·2^{−s}+3^{−s}; c(2)=−1.386,
    sign-changing, all n) an atom whose self-correlation reaches log2 has D_jj(DH)=−0.217<0 vs
    D_jj(ζ)=+0.57. The multiscale diagonal — the FOUNDATION of the decomposition — exists for ζ and
    evaporates for DH. It is itself the Euler-product distinction.

VERDICT (§10): The wavelet/Calderón decomposition does NOT beat the Yoshida cone. The diagonal D is
safe by construction, but the cross-scale interference C is the SAME moving, high-rank (~13) prime
obstruction re-indexed by inter-atom separation. It saturates the MATRIX bound C ⪰ −D exactly
(λ_min→−1) and breaks it as soon as the multiscale family resolves the obstruction, driving Q<0 on
genuine safe-diagonal test functions. NO partial-positivity theorem past log2 follows from a scalar
θ<1 bound: the controlling object is a matrix, not a scalar. This is a clean CERTIFICATE that
cross-scale interference is uncontrollable, with the precise reason (C indefinite, saturates C⪰−D).
The Yoshida cone is SHARP against multiscale decomposition. Consistent with §9, Bombieri, Connes–Consani.
