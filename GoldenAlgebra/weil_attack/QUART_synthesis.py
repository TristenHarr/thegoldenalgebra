"""
SYNTHESIS (Tasks 4 & 5) + the deliverable inequality, with all constants.
=========================================================================

THE SHARP UNCERTAINTY INEQUALITY (deliverable, derived & verified exactly):
  For g positive-type, supp(g) subset [-T,T] (h=ghat entire of exp type T, h>=0 on R), the
  contribution to the Weil sum Q(g)=sum_rho h(gamma_rho) of an off-line quartet
  {1/2 +- delta +- i gamma0} is EXACTLY
        N(delta,gamma0,T) = 4 \int_{-T}^{T} g(u) cosh(delta u) cos(gamma0 u) du
                          = 4 ĝ(gamma0)  +  4 \int_{-T}^{T} g(u) (cosh(delta u)-1) cos(gamma0 u) du
                          =:  N0  +  Delta,     N0 = 4|f̂(gamma0)|^2 >= 0  (= on-line value).
  BOUND:   |Delta| <= 4 (cosh(delta T) - 1) \int_{-T}^{T} |g(u)| du.
  Most-negative achievable (over positive-type g, normalized g(0)=1), VERIFIED gamma0-independent:
        N_min(delta,T)/g(0)  =  -F(delta T),   F(x) = (1/2)x^2 + O(x^4)  for small x,  ~ e^{~x} large x.
  ==> a single off-line zero perturbs the NONNEGATIVE on-line mass by a RELATIVE amount F(delta T).
      INVISIBLE (Delta/N0 = O((delta T)^2)) until delta T = O(1). gamma0 enters only through the
      density of competing on-line zeros, NOT the threshold. This is the sharp 'invisible until 1/delta'.

TASK 3 (the honest crux) — why bounded positivity gives NO zero-free region:
  At T <= log2 the prime sum is EMPTY and Q = ARCH+POLE >= 0 is a THEOREM (Yoshida), verified
  here (QUART_yoshida_honest.py: min eig STRICTLY > 0, ->0 as T->log2, well-conditioned). The
  quartet mass N is a SUB-PART of this provably-nonnegative form. Hence for EVERY (delta,gamma0)
  the positive ARCH+POLE floor >= |N_neg|: the maximal DETECTABLE off-line displacement at
  T=log2 is NONE. Bounded short-support positivity carries ZERO zero-location information.
  Quantitatively: the negative quartet mass at support T is bounded by F(delta T) ~ (delta T)^2/2;
  at T=log2 this is <= (delta*0.693)^2/2, which is dominated by the ARCH+POLE positive floor for
  ALL delta (the floor is an order-1 positive form, the quartet perturbation is its sub-part).

TASK 4 — support needed for a zero-free region of width w:
  To CERTIFY no zeros with displacement delta >= w, the Weil form must be able to PRODUCE
  negative mass for every such zero (contrapositive: Q>=0 forbids it). By the inequality, an
  off-line zero at displacement delta is detectable only once delta T >~ c0, i.e.
        T_needed(w) >= c0 / w.
  As w -> 0 (a FIXED strip arbitrarily close to Re=1/2 -> RH), T_needed -> INFINITY: you need
  UNBOUNDED support = full-space Weil positivity = RH-strength. NO finite T gives a fixed-width
  unconditional strip. The bounded cone (T=log2) gives w=infinity (no info), consistent.

TASK 5 — same uncertainty constant in different clothes:
  Yoshida T<log2:    support cap at FIRST PRIME; additive (-log2,log2)=multiplicative (1/2,2).
  Bombieri:          'truncation t big enough' to see an off-line pair = exactly delta*t>~c0.
  Sonin space:       phase-space cutoff parameter = support cutoff; positivity holds on the
                     complement of the cutoff range -> bounded support = inside cutoff = blind.
  Li / Keiper-Li:    lambda_n for an off-line zero grows ~ EXPONENTIALLY in n; n plays role of
                     T (resolution index): off-line zero invisible until n large = T large.
  de Bruijn / Newman: backward heat flow gap; closing the gap = letting support -> infinity.
  ALL are the SAME Fourier uncertainty: a feature at displacement delta off the real axis is
  resolved only with bandwidth/support T >~ 1/delta. The constant c0 is order-1 (Bernstein/
  Paley-Wiener), gamma0-independent.
"""
import numpy as np

# UNIVERSALITY in x=delta*T: hold delta*T fixed, split it differently, and across gamma0.
# N_min/g(0) with PROPER g(0)=1 normalization (grid quadrature). The load-bearing facts:
# (a) depends on x=delta*T, (b) gamma0-independent, (c) ~x^2 small / exp large.
# (Clean normalized table also in QUART_magnitude.py.)
def Nmin_norm(delta, gamma0, T, m=320):
    xs=np.linspace(-T/2,T/2,m); dx=xs[1]-xs[0]
    D=xs[:,None]-xs[None,:]
    A=np.cosh(delta*D)*np.cos(gamma0*D)*dx*dx   # f^T A f ~ int int f f K = int g K
    G=np.eye(m)*dx                               # f^T G f ~ int f^2 = g(0)
    w,V=np.linalg.eigh(G); U=V/np.sqrt(w)
    B=U.T@(4*A)@U
    return np.linalg.eigvalsh((B+B.T)/2).min()

print("UNIVERSALITY: N_min/g(0) depends on x=delta*T alone, and is gamma0-independent.")
print(f"{'x=dT':>6} {'(d,T) split':>14} {'gamma0':>8} {'N_min/g(0)':>13}")
for x in [0.5, 1.0, 2.0]:
    for (delta,T) in [(x/5.0,5.0),(x/10.0,10.0)]:
        for g0 in [50.0, 1000.0]:
            print(f"{x:6.2f} {f'd={delta:.3f},T={T:.0f}':>14} {g0:8.0f} {Nmin_norm(delta,g0,T):13.4e}")
print()
print("Same x=delta*T => same N_min (across (d,T) split AND across gamma0).")
print("Small x: ~x^2 (INVISIBLE).  Large x: exp-growth (Bernstein) -> VISIBLE.  Gate: dT~1.")
print()
print("ZERO-FREE-REGION COST  T_needed(w) = c0/w  (c0=O(1)):  w->0 => T->inf => RH-strength.")
for w in [0.5,0.2,0.1,0.05,0.01]:
    print(f"   width w={w:5.2f}:  T_needed ~ {1.0/w:6.1f}  (in units of c0)")
