"""
mollifier_vs_density_moment.py
==============================

TASK 3: Can MOLLIFIER methods (Levinson/Conrey/PRZ) BEAT the density-derived
displacement 2nd-moment bound  Sum eta^2 << 64 T/log T  (Selberg layer-cake)?

PRECISE ANALYSIS.
-----------------
Mollifier theorems are PROPORTION theorems: a proportion theta of zeros up to T
have eta = 0 EXACTLY (Levinson theta>=1/3, Conrey 2/5, Pratt-Robles-Zaharescu-
Zeindler 2018 theta>5/12=0.4167). They identify on-line zeros; they say NOTHING
quantitative about HOW FAR the remaining (1-theta) fraction sit from the line.

So the BEST a bare proportion theorem can give for the moment is to bound the
off-line zeros' eta^2 by the trivial cap |eta| <= 1/2 (or the zero-free-region
cap |eta| <= 1/2 - c/log gamma):

    Sum eta^2  =  Sum_{off-line} eta^2
              <=  (1-theta) * N(T) * (1/2)^2          [trivial cap]
              ~   (1-theta) * (T log T / 2pi) * 1/4
              =   (1-theta)/(8 pi) * T log T.

This GROWS like T log T -- a factor log^2 T WORSE than the Selberg layer-cake
T/log T.  CONCLUSION: a bare proportion theorem does NOT beat the density moment
bound; it is quadratically (in log T) worse, because it has no decay-in-displacement.

The density estimate N(1/2+u,T) is exactly the missing ingredient: it weights the
off-line zeros by how far out they are (T^{-u/4}), which the proportion theorem
discards.  The layer-cake CONVERTS the density's u-decay into the eta^2 moment.

WHAT WOULD A MOLLIFIER NEED to beat T/log T?  A mollified second moment of the
form  Int_0^T |zeta'(1/2+it) M(1/2+it)|^2 dt  controls zeros NEAR the line at the
1/log T resolution, but the published outputs are PROPORTIONS (counts), not
displacement moments.  To extract a moment one still needs a density/N(sigma,T)
input.  Mollifiers improve the PROPORTION constant (1/3 -> 5/12), which improves
the COEFFICIENT in the trivial-cap budget (1-theta: 2/3 -> 7/12), but NOT the
T log T order.  They do not change the moment EXPONENT.

=> REPORTED VERDICT: mollifiers do NOT sharpen the moment exponent.  The Selberg
   layer-cake bound  Sum eta^2 << T/log T  is the sharper unconditional moment
   bound.  Mollifiers sharpen the *proportion* (the count of exactly-on-line
   zeros), which is a DIFFERENT, weaker-for-the-moment statistic.

This script quantifies the comparison.
"""

import mpmath as mp
mp.mp.dps = 30

def N_total(Tval):
    Tm = mp.mpf(Tval)
    return Tm/(2*mp.pi)*mp.log(Tm/(2*mp.pi)) - Tm/(2*mp.pi)

def selberg_moment(Tval):
    """Sum eta^2 <= 4 T logT Int_0^{1/2} u T^{-u/4} du."""
    Tm = mp.mpf(Tval); Lm = mp.log(Tm); c = Lm/4
    I = (1 - mp.e**(-c/2)*(1+c/2))/c**2
    return 4*Tm*Lm*I

def mollifier_trivial_moment(Tval, theta):
    """(1-theta) N(T) * (1/2)^2  -- proportion theorem + trivial |eta|<=1/2 cap."""
    return (1-theta)*N_total(Tval)*mp.mpf(1)/4

def mollifier_zfr_moment(Tval, theta):
    """(1-theta) N(T) * (1/2 - c/log T)^2 with c=1 de la Vallee-Poussin-ish.
       Still ~ (1-theta) N(T)/4, the log correction is lower order."""
    Tm = mp.mpf(Tval); Lm = mp.log(Tm)
    cap = (mp.mpf(1)/2 - 1/Lm)**2
    return (1-theta)*N_total(Tval)*cap

thetas = {"Levinson 1/3":mp.mpf(1)/3, "Conrey 2/5":mp.mpf(2)/5, "PRZZ 5/12":mp.mpf(5)/12}

print("="*92)
print(" DISPLACEMENT 2nd-MOMENT  Sum_{gamma<=T} eta^2  :  density layer-cake  vs  mollifier-proportion")
print("="*92)
print(f"{'T':>7} | {'Selberg LC (dens)':>18} | {'Levinson trivial':>17} | {'Conrey trivial':>15} | {'PRZZ trivial':>13}")
print("-"*92)
for k in [6, 9, 12, 15]:
    Tval = mp.mpf(10)**k
    s = selberg_moment(Tval)
    mL = mollifier_trivial_moment(Tval, mp.mpf(1)/3)
    mC = mollifier_trivial_moment(Tval, mp.mpf(2)/5)
    mP = mollifier_trivial_moment(Tval, mp.mpf(5)/12)
    print(f"10^{k:<4} | {mp.nstr(s,5):>18} | {mp.nstr(mL,5):>17} | {mp.nstr(mC,5):>15} | {mp.nstr(mP,5):>13}")

print()
print(" RATIO mollifier/Selberg (how much WORSE the proportion-based budget is):")
print(f"{'T':>7} | {'Levinson/Selb':>14} | {'Conrey/Selb':>12} | {'PRZZ/Selb':>11} | {'~log^2 T':>9}")
print("-"*64)
for k in [6, 9, 12, 15]:
    Tval = mp.mpf(10)**k
    s = selberg_moment(Tval)
    Lm = mp.log(Tval)
    print(f"10^{k:<4} | {mp.nstr(mollifier_trivial_moment(Tval,mp.mpf(1)/3)/s,5):>14} | "
          f"{mp.nstr(mollifier_trivial_moment(Tval,mp.mpf(2)/5)/s,5):>12} | "
          f"{mp.nstr(mollifier_trivial_moment(Tval,mp.mpf(5)/12)/s,5):>11} | {mp.nstr(Lm**2,4):>9}")

print()
print(" ORDER comparison (asymptotic, the load-bearing statement):")
print("   Selberg LC ~ 64 T / log T ;  mollifier-trivial ~ (1-theta) T log T / (8 pi).")
print("   RATIO mollifier/Selberg ~ [(1-theta)/(8 pi)] * log^2 T / 64  ->  +infinity.")
print("   So ASYMPTOTICALLY the Selberg density bound is a factor ~log^2 T SHARPER.")
print()
print(" HONEST finite-T caveat: the Selberg LC carries the implied constant ~64, so the")
print(" numerical crossover (where Selberg actually drops below the mollifier budget) is")
print(" LATE -- around T ~ 10^24 (Conrey 2/5).  Below that the small mollifier coefficient")
print(" (1-theta)/4 wins on raw size.  The EXPONENT claim (T/log T vs T log T) is what is")
print(" unconditional and load-bearing; the constant is not optimized here.")
print()
print(" => Mollifiers do NOT beat the moment EXPONENT.  They sharpen the PROPORTION")
print("    constant (1-theta: 2/3->7/12) but keep the T log T order.  The density")
print("    layer-cake is the sharper moment bound exponent-wise (T/log T).")
print()
print(" HONEST SUMMARY of the comparison (moment exponent in T):")
print("   trivial cap            :  T log T            (no displacement info)")
print("   mollifier proportion   :  (1-theta) T log T  (removes a CONSTANT fraction)")
print("   Selberg layer-cake     :  64 T / log T       (uses density u-decay)  <-- BEST")
print("   kernel-weighted (g^-4) :  O(1)               (T-uniform)             <-- BEST avg")
print("   RH                     :  0")
