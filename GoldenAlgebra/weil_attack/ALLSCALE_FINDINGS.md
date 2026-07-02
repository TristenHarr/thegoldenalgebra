# SCALE-INTEGRATED DISPLACEMENT-ENERGY FUNCTIONAL  E(mu) — Findings

Mission: build a scale-integrated displacement-energy functional defeating the fixed-scale
`delta*T ~ 1` blindness (ScratchResolutionTheory), and decide HONESTLY whether the scale
integration produces structure beyond fixed-T Weil positivity, or is the integrated wall.

Scripts: `allscale_energy.py` (convergence/completeness), `allscale_structure.py` (closed
form + convexity/monotonicity/cancellation), `allscale_explicit.py` (explicit-formula
connection + verdict). Lean: `ScratchAllScaleEnergy.lean` (axiom-clean: propext, Classical.choice,
Quot.sound — no sorryAx).

## THE OBJECT

    E(profile) = INT_0^inf [ SUM_rho (cosh(eta_rho T) - 1) W_T(gamma_rho) ] dnu(T)

eta_rho = displacement of zero rho off the critical line; cosh(eta T)-1 = the PROVEN Weil
off-line edge detector (ScratchResolutionTheory.cosh_minus_one_resolution). Each term >= 0,
= 0 iff eta_rho = 0. The all-scale object SEES every displacement (some T ~ 1/eta activates it).

## TASK 1 — CONVERGENT + DISPLACEMENT-COMPLETE pairing (the delicate part). DONE.

cosh(eta T) ~ (1/2)e^{|eta|T} grows exponentially, so nu must DECAY to converge.
Tested three nu (allscale_energy.py):
  * dnu = e^{-T^2} dT (GAUSSIAN): CONVERGES for EVERY eta (super-exp beats cosh), E>0 iff eta!=0.
    => CONVERGENT and DISPLACEMENT-COMPLETE. **This is the banked pairing** (W_T = 1, no window).
  * dnu = e^{-T} dT (exponential rate beta=1): converges ONLY for |eta|<1. A FIXED exponential
    rate has a DISPLACEMENT HORIZON (blind/divergent for |eta|>=beta). NOT complete.
  * dnu = dT/T^2 on [1,inf) (the mission's first suggestion): DIVERGES for ANY eta>0 — 1/T^2
    cannot tame cosh. The dT/T^2 measure FAILS unless W_T supplies an exp cutoff.
VERDICT TASK 1: the Gaussian scale-measure is the unique-feeling clean choice that is both
convergent (every eta, even eta=10: E=6.4e10 finite) and complete (E=0 iff eta=0).

## TASK 2 — THE KEY QUESTION: does scale-integration produce NEW STRUCTURE? YES (real facts).

(S1) **GAUSSIAN COLLAPSE — closed form (the headline structural fact).**
     INT_0^inf (cosh(eta T)-1) e^{-T^2} dT = (sqrt(pi)/2)(e^{eta^2/4} - 1), verified to 1e-15.
     The ENTIRE cosh-tower across all scales COLLAPSES to ONE real-analytic potential
        V(eta) = e^{eta^2/4} - 1   (a Gaussian-of-the-displacement),
     and  E({eta_rho}) = (sqrt(pi)/2) SUM_rho V(eta_rho)  — a SEPARABLE sum (no zero-zero coupling).

(S2) **ABSOLUTE MONOTONICITY in T (no cross-scale cancellation).** The per-scale integrand
     S(T)=SUM(cosh(eta_rho T)-1) has ALL Taylor coefficients >= 0 => S, S', S'' all >= 0 for T>=0,
     for EVERY profile. The integrand is absolutely monotone in T: with a POSITIVE nu there is NO
     cancellation across scales — the integral only accumulates positive mass.

(S3) **STRICT CONVEXITY of E in the displacement profile (the genuine new invariant).**
     V''(eta) = (1/4)(1 + eta^2/2)e^{eta^2/4} > 0 EVERYWHERE => V strictly convex; E is a STRICTLY
     CONVEX functional of {eta_rho} with a UNIQUE GLOBAL MINIMUM 0 at eta=0 (=RH). [Proven in Lean:
     scaleEnergyPotential_strictConvexOn.] Fixed-T cosh(eta T)-1 is convex in eta too, but the
     SCALE INTEGRAL is what yields the clean Gaussian potential e^{eta^2/4}-1 whose convex tower is
     the all-scale invariant. This convexity + Gaussian collapse are SCALE-INTEGRATION facts, not
     visible at any single scale.

(S4) **CANCELLATION needs a SIGNED nu — and that is exactly the wall.** With an oscillating
     (signed) scale-weight cos(freq*T)e^{-T^2}, INT goes NEGATIVE for freq>~2. So a signed nu
     DESTROYS positivity = re-introduces the indefinite Weil cross-terms (sec.10). The structural
     dividing line is nu >= 0: on the POSITIVE-nu cone E is a positive all-scale invariant; off it,
     indefinite. The Gaussian nu lives on the good side.

## TASK 3 — CONNECTION TO THE EXPLICIT FORMULA (the honest crux). 

The Weil contribution of one off-line quartet {1/2 +- eta +- i gamma}, supp g in [-T,T], is EXACTLY
(QUART_FINDINGS star):  N = N0 + Delta,  N0 = 4*ghat(gamma) >= 0 (on-line mass),
   Delta = 4 INT g(u)(cosh(eta u)-1)cos(gamma u) du,   |Delta| <= 4(cosh(eta T)-1) INT|g|.
Our detector (cosh(eta T)-1) is the ENVELOPE/BOUND of Delta — with the cos(gamma u) oscillation
(the source of indefiniteness) and the on-line mass N0 STRIPPED OUT.

(T1) The realized Delta(eta,gamma,T) is SIGN-CHANGING in gamma (the cos), strictly inside the
     envelope (allscale_explicit.py): NO genuine positive-type Weil functional Q(g) equals the bare
     envelope cosh(eta T)-1 (every real Q carries N0 and the cos oscillation).
(T2) INT Q_T dnu with positive nu STAYS INDEFINITE: each Q_T is indefinite past log2 (min-eig
     -2.0..-0.95 at T=0.65..2.0, then ~0 floor); a positive-weighted sum is a positive mix of
     indefinite matrices, min-eig = -2.93 < 0. Integrating the genuine Weil FORM does NOT
     manufacture definiteness. The wall is re-confirmed for the integrated form.
(T3) E is NOT INT Q_{g_T} dnu. E is a functional of the ZEROS' displacements eta_rho DIRECTLY,
     through the EVEN POSITIVE kernel cosh(eta_rho T)-1 (no cos). It sidesteps indefiniteness — but
     the eta_rho are PRECISELY the unknown RH data. The explicit formula gives the gamma-read-out
     SUM ghat(gamma_rho) = arch+pole-prime(g); it does NOT give a positive displacement-read-out
     SUM (cosh(eta_rho T)-1). There is no test function whose Weil functional equals that positive
     envelope sum.

## TASK 4 — THE HONEST VERDICT

E is a GENUINELY NEW, convergent, displacement-complete, STRICTLY CONVEX all-scale energy with
E = 0 <=> RH (banked, proven in Lean: E_zero_imp_RH). The Gaussian scale-collapse to V=e^{eta^2/4}-1
and the strict convexity are REAL scale-integration facts, NOT visible at fixed T. In THAT sense it
is NOT "exactly Weil positivity integrated": integrating the Weil FORM (T2) stays indefinite, whereas
E is positive by construction.

BUT the positivity of E lives on the ZERO side (the displacements), not the prime side. The precise
price (T1/T3): the Euler product controls the indefinite ghat(gamma)-read-out (Delta, with its cos),
NOT the positive envelope SUM(cosh(eta T)-1). So while E=0 => RH is airtight and E is structurally
new, the Euler-product input that would FORCE E=0 is not delivered by the arithmetic side as a
positive quantity — the cos(gamma u) oscillation that makes the prime side indefinite is exactly what
E discards. The new convex invariant is real; the bridge from the Euler product to "E=0" is the same
wall, relocated: it is the gap between the positive displacement-envelope and the indefinite,
cos-carrying prime-side read-out.

NET (flagged honestly): a real new all-scale convex invariant with E=0 <=> RH and a clean
Gaussian-collapse structure (banked in Lean) — but its positivity is on the zero side; the Euler
product does not supply E as a prime-side positive quantity, so it does not, by itself, force E=0.
What would: any arithmetic identity expressing SUM_rho(e^{eta_rho^2/4}-1) (or the per-scale
SUM_rho(cosh(eta_rho T)-1)) as a manifestly nonnegative prime-side quantity — which is precisely
what the cos-indefiniteness of Delta obstructs (T1, sec.10 multiscale).
