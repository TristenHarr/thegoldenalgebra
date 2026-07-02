"""
modern_displacement_energy.py

Displacement-coordinate translation + layer-cake energy budget, comparing the
CLASSICAL Ingham baseline A=3 against the MODERN current-best A(sigma):
  - Ingham refined  A(s)=3/(2-s)    on s in [1/2, 7/10]      (continuous, A(7/10)=30/13)
  - Guth-Maynard 24 A(s)=15/(3+5s)  on s in [7/10, 19/25]    (arXiv:2405.20552)

Displacement coords: a zero beta+i gamma has eta=beta-1/2, sigma=1/2+eta.
  #{ eta>=eps, |gamma|<=T } = N(1/2+eps, T) << T^{ A(1/2+eps)*(1/2-eps) + o(1) }.

Truncated displacement energy (layer-cake, reuse ScratchPositionEnvelope identity):
  E_{>=eps}(T) = int_eps^{1/2} 2u * N(1/2+u, T) du
             << int_eps^{1/2} 2u * T^{ A(1/2+u)*(1/2-u) } du   (exponents drive the budget)

We compare the *energy exponent* e(u)=A(1/2+u)*(1/2-u):
classical Ingham A=3 gives e_Ing(u)=3*(1/2-u); modern gives strictly smaller e(u).
Smaller exponent => exponentially smaller energy budget at every fixed eps.
"""
from fractions import Fraction as F
import mpmath as mp
mp.mp.dps = 40

def A_modern(s):
    s = F(s)
    if F(1,2) <= s <= F(7,10):   return F(3)/(2-s)          # Ingham refined
    if F(7,10) < s <= F(19,25):  return F(15)/(3+5*s)       # Guth-Maynard 2024
    # beyond 19/25 use the GM curve value frozen (conservative) - only used for s up to 19/25 here
    return F(15)/(3+5*s)

A_classical = lambda s: F(3)   # Ingham classical headline A=3

def energy_exp(Afun, eps):
    s = F(1,2)+F(eps) if not isinstance(eps,F) else F(1,2)+eps
    return Afun(s) * (F(1,2)-(s-F(1,2)))   # A(1/2+eps)*(1/2-eps)

print("=== Energy exponent e(eps)=A(1/2+eps)*(1/2-eps): classical A=3 vs modern ===")
print(f"{'eps':>7}{'sigma':>8}{'A_class':>9}{'A_mod':>10}{'e_class':>10}{'e_mod':>10}{'saving':>10}")
for k in range(1,26):
    eps=F(k,100); s=F(1,2)+eps
    Ac=A_classical(s); Am=A_modern(s)
    ec=float(Ac*(F(1,2)-eps)); em=float(Am*(F(1,2)-eps))
    print(f"{float(eps):7.3f}{float(s):8.3f}{float(Ac):9.3f}{float(Am):10.5f}{ec:10.5f}{em:10.5f}{ec-em:10.5f}")

# Numerically verify the layer-cake energy budget integral at a concrete T,
# eps range [eps0, 1/2], using the upper-bound integrand 2u*T^{e(u)}.
print("\n=== Layer-cake energy budget int_eps0^{1/2} 2u*T^{e(u)} du  (T=10^6) ===")
T = mp.mpf(10)**6
for eps0 in [F(1,5), F(21,100), F(11,50), F(23,100), F(1,4)]:
    lo=float(eps0); hi=0.5
    def integrand(Afun):
        def f(u):
            uu=F(u).limit_denominator(10**6) if False else None
            # use float A via piecewise on float
            su=0.5+u
            if su<=0.7: Av=3.0/(2.0-su)
            else:       Av=15.0/(3.0+5.0*su)
            ec=3.0*(0.5-u)
            return u, Av, ec
        return f
    # modern budget
    fm = lambda u: 2.0*u*float(T**( (3.0/(2.0-(0.5+u)) if (0.5+u)<=0.7 else 15.0/(3.0+5.0*(0.5+u)))*(0.5-u) ))
    fc = lambda u: 2.0*u*float(T**(3.0*(0.5-u)))
    Em = mp.quad(fm, [lo, min(0.7-0.5,hi) if lo<0.2 else lo, hi]) if lo<0.2 else mp.quad(fm,[lo,hi])
    Ec = mp.quad(fc, [lo, hi])
    print(f" eps0={lo:.2f}: E_modern={mp.nstr(Em,4):>12}  E_classical={mp.nstr(Ec,4):>12}  ratio mod/class={mp.nstr(Em/Ec,4)}")
