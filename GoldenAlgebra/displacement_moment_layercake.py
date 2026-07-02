"""
displacement_moment_layercake.py
================================

THE CLEAN DISPLACEMENT 2nd-MOMENT BOUND via layer-cake on a zero-density estimate.

Identity (Cavalieri / layer-cake, the SAME one proven in ScratchPositionEnvelope as
`displacementMoment_layerCake`, here truncated to the strip [0, 1/2] where |eta|<=1/2
always):

    Sum_{0<gamma<=T} eta_rho^2  =  2 * Integral_{0}^{1/2} u * N_off(u, T) du

where N_off(u,T) = #{rho : |beta - 1/2| >= u, 0 < gamma <= T}  <= 2 * N(1/2 + u, T).
(The factor 2 is the FE symmetry beta <-> 1-beta pairing both sides; we keep it explicit.)

Plug the UNCONDITIONAL zero-density estimate. The right density for the WHOLE
near-line range u in (0,1/2] is **Selberg (1946)**:

    N(1/2 + u, T)  <<  T^{1 - u/4} * log T          (Selberg, exponent factor 1/4)

(Ingham A=3 / Guth-Maynard A(sigma) are sharper near sigma=3/4 i.e. u~1/4, but Selberg
gives clean exponential-in-u decay valid for ALL u in (0,1/2], which is exactly what the
layer-cake u-integral needs.)

So the displacement second moment is bounded, UNCONDITIONALLY, by

    M2(T) := Sum eta^2  <=  4 * log T * Integral_{0}^{1/2} u * T^{1 - u/4} du
                        =  4 * T * log T * Integral_{0}^{1/2} u * T^{-u/4} du.

Let L = log T. Then T^{-u/4} = exp(-u L /4). With c = L/4:

    Integral_{0}^{1/2} u e^{-c u} du = [1 - e^{-c/2}(1 + c/2)] / c^2.

For large T, c = L/4 -> infinity, so the bracket -> 1 and the integral -> 1/c^2 = 16/L^2.
Hence the LEADING behaviour:

    M2(T)  <=  4 T L * (16 / L^2) * (1 + o(1))  =  64 * T / log T * (1 + o(1)).

==> UNCONDITIONAL DISPLACEMENT 2nd-MOMENT BOUND:

        Sum_{0<gamma<=T} (beta - 1/2)^2   <<   T / log T.

Compare: total zero count N(T) ~ (T/2pi) log T. So the AVERAGE square displacement is

        (1/N(T)) Sum eta^2  <<  (T/log T) / (T log T)  =  1 / (log T)^2  -> 0.

i.e. the mean-square displacement of a zero is  O(1/log^2 T), the resolution scale
1/log T squared.  This is the honest unconditional statement: zeros sit, on average,
within O(1/log T) of the line (NOT on it -- that's RH).

This script:
 (1) verifies the closed form of the u-integral symbolically;
 (2) tabulates M2(T) and the per-zero mean-square for T = 10^k;
 (3) compares the Selberg-density layer-cake budget to the Ingham A=3 one;
 (4) records the kernel-weighted (gamma^-4) version -> T-UNIFORM (bounded in T).
"""

import sympy as sp
import mpmath as mp

mp.mp.dps = 40

print("=" * 78)
print(" 1. SYMBOLIC closed form of the layer-cake u-integral")
print("=" * 78)

u, c, L, T = sp.symbols('u c L T', positive=True)

# Integral_0^{1/2} u e^{-c u} du
I = sp.integrate(u * sp.exp(-c*u), (u, 0, sp.Rational(1,2)))
I = sp.simplify(I)
print("Integral_0^{1/2} u e^{-c u} du =")
sp.pprint(I)

# closed form claim: [1 - e^{-c/2}(1 + c/2)] / c^2
claim = (1 - sp.exp(-c/2)*(1 + c/2)) / c**2
print("\nClaim  [1 - e^{-c/2}(1 + c/2)]/c^2 matches:",
      sp.simplify(I - claim) == 0)

# large-c limit of c^2 * I  -> 1
lim = sp.limit(c**2 * I, c, sp.oo)
print("lim_{c->oo} c^2 * I =", lim, "  (so I ~ 1/c^2)")

print()
print("=" * 78)
print(" 2. Full M2(T) bound with Selberg density  N(1/2+u,T) << T^{1-u/4} log T")
print("=" * 78)
print("   M2(T) <= 4 T log T * Integral_0^{1/2} u T^{-u/4} du,   c = (log T)/4")
print()

def M2_bound(Tval):
    """Explicit upper bound 4 T logT * I(c), c = logT/4 (implied const = 1)."""
    Tm = mp.mpf(Tval)
    Lm = mp.log(Tm)
    cm = Lm / 4
    Im = (1 - mp.e**(-cm/2) * (1 + cm/2)) / cm**2
    return 4 * Tm * Lm * Im, Lm

def N_total(Tval):
    """Riemann-von Mangoldt main term N(T) ~ (T/2pi) log(T/2pi) - T/2pi."""
    Tm = mp.mpf(Tval)
    return Tm/(2*mp.pi) * mp.log(Tm/(2*mp.pi)) - Tm/(2*mp.pi)

print(f"{'T':>8} | {'M2 bound (Sum eta^2)':>22} | {'N(T)~':>16} | {'mean eta^2':>14} | {'1/log^2T':>10}")
print("-"*86)
for k in range(3, 13):
    Tval = mp.mpf(10)**k
    M2, Lm = M2_bound(Tval)
    NT = N_total(Tval)
    mean = M2 / NT
    inv = 1/Lm**2
    print(f"10^{k:<5} | {mp.nstr(M2,6):>22} | {mp.nstr(NT,6):>16} | {mp.nstr(mean,5):>14} | {mp.nstr(inv,4):>10}")

print()
print("  -> M2(T) grows ~ 64 T/log T ; mean-square eta ~ const/log^2 T -> 0.")
print("  -> M2(T)/(T/log T) tends to the constant 64:")
for k in [6, 9, 12, 18, 30]:
    Tval = mp.mpf(10)**k
    M2,Lm = M2_bound(Tval)
    ratio = M2 / (Tval/Lm)
    print(f"       T=10^{k:<3}: M2 / (T/log T) = {mp.nstr(ratio,6)}")

print()
print("=" * 78)
print(" 3. Layer-cake budget: Selberg vs Ingham(A=3) density")
print("=" * 78)
print("   Ingham:  N(1/2+u,T) << T^{3u} log T  is USELESS in layer-cake for u>1/6")
print("   (exponent 3u exceeds 1, integral dominated by u=1/2 -> T^{3/2}).")
print("   Selberg's T^{1-u/4} is the correct decaying density for the full strip.")
print()

def ingham_layercake(Tval, A=3.0):
    """2 logT * Int_0^{1/2} 2u * T^{A u} du  (N_off<=2N, N<=T^{A u} logT, with
       sigma=1/2+u so a(1/2-sigma)... here using crude N(1/2+u,T)<<T^{A u} logT shape).
       Wait: Ingham is N(sigma,T)<<T^{a(1-sigma)}; with sigma=1/2+u, 1-sigma=1/2-u,
       so exponent a(1/2-u). That DECREASES in u. Use that honest form."""
    Tm = mp.mpf(Tval); Lm = mp.log(Tm)
    f = lambda uu: 4*Lm*uu*Tm**(A*(mp.mpf(1)/2 - uu))
    return mp.quad(f, [0, mp.mpf(1)/2])

def selberg_layercake(Tval):
    Tm = mp.mpf(Tval); Lm = mp.log(Tm)
    f = lambda uu: 4*Lm*uu*Tm**(1 - uu/4)
    return mp.quad(f, [0, mp.mpf(1)/2])

print(f"{'T':>8} | {'Selberg LC':>16} | {'Ingham A=3 LC':>16} | {'ratio Selb/Ing':>14}")
print("-"*64)
for k in [6, 9, 12]:
    Tval = mp.mpf(10)**k
    s = selberg_layercake(Tval)
    i = ingham_layercake(Tval, 3.0)
    print(f"10^{k:<5} | {mp.nstr(s,5):>16} | {mp.nstr(i,5):>16} | {mp.nstr(s/i,5):>14}")
print()
print("   NOTE: Ingham's a(1/2-u) exponent is DOMINATED by the u->0 endpoint where")
print("   it -> a/2 = 3/2, i.e. Ingham layer-cake ~ T^{3/2} -- MUCH WORSE than Selberg's")
print("   T/logT.  The exponential-in-u Selberg density is essential; near u=0 BOTH")
print("   give T^{(exponent at 0)}: Selberg 1, Ingham 3/2.  Selberg wins for the MOMENT.")

print()
print("=" * 78)
print(" 4. KERNEL-WEIGHTED moment (gamma^-4 weight)  ->  T-UNIFORM")
print("=" * 78)
print("   Phi_K = Sum |K_z(eta,gamma)| <= 12 y * Sum eta^2 / (gamma^2+y^2)^2.")
print("   The height weight 1/(gamma^2+y^2)^2 is summable: with zero density")
print("   dN ~ (1/2pi) log(gamma) dgamma,")
print("        Sum_gamma 1/(gamma^2+y^2)^2  <=  Int_1^oo (log g/2pi)/(g^2+y^2)^2 dg  < oo,")
print("   INDEPENDENT of T.  So weighting eta^2 by the kernel's gamma^-4 gives a")
print("   T-UNIFORM displacement-energy functional (bounded as T->oo), whereas the")
print("   bare M2(T) ~ 64 T/log T grows.  Quantify the height integral at y=1:")

def height_integral(y):
    f = lambda g: (mp.log(g)/(2*mp.pi)) / (g**2 + y**2)**2
    return mp.quad(f, [mp.e, mp.inf])   # from g=e where log g >=1

for yv in [1, 5, 14.1347]:   # y=14.13 ~ first zero ordinate
    H = height_integral(yv)
    print(f"     y={yv:<8}:  Int_e^oo (log g/2pi)/(g^2+y^2)^2 dg = {mp.nstr(H,6)}  (T-uniform)")

print()
print("   COMBINED kernel-weighted second moment bound (T-uniform):")
print("     Phi_K(iy) <= 12 y * (max eta^2=1/4) * Sum 1/(gamma^2+y^2)^2")
print("               <= 3 y * [const independent of T].")
for yv in [1, 5, 14.1347]:
    H = height_integral(yv)
    print(f"     y={yv:<8}:  Phi_K <= 3*{yv}*{mp.nstr(H,4)} = {mp.nstr(3*yv*H,5)}  (bounded in T)")
print()
print("   This is the genuine averaged anti-Herglotz error: a T-UNIFORM bound on the")
print("   off-line population's signed contribution to G(iy), unconditional.")
