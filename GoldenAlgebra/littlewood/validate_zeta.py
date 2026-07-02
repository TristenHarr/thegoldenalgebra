"""
TEST B: Littlewood's lemma for the genuine Riemann xi on a rectangle with
left edge sigma_0 = 1/2.

We use the completed zeta (Riemann xi):
    xi(s) = (1/2) s (s-1) pi^{-s/2} Gamma(s/2) zeta(s)
which is ENTIRE, has zeros exactly at the nontrivial zeros of zeta, and
satisfies the functional equation xi(s) = xi(1-s). On the critical line
s = 1/2 + it, xi is REAL (this is the standard Z-like normalization up to the
real factor), so log|xi(1/2+it)| is well-defined and the displacement sum
  sum_{0<gamma<T}(beta - 1/2)
is ZERO whenever all zeros up to height T lie on beta = 1/2 (verified numerics
of RH up to enormous heights).

Littlewood (left edge sigma0 = 1/2, right edge sigma1, height T):
  2 pi sum_{rho, 1/2<beta, 0<gamma<T}(beta - 1/2)
     = INT_0^T log|xi(1/2+it)|dt - INT_0^T log|xi(sigma1+it)|dt
       + INT_{1/2}^{sigma1} arg xi(sigma+iT) dsigma
       - INT_{1/2}^{sigma1} arg xi(sigma) dsigma.

NOTE the FE asymmetry: Littlewood applied with left edge sigma0=1/2 counts ONLY
zeros with beta>1/2 (the right half of the strip). The boundary RHS therefore
equals sum_{beta>1/2}(beta-1/2). If all zeros are ON the line this is 0, so the
RHS must vanish -> on-line consistency check.

We verify: boundary RHS = (numerically) 0 for xi with sigma0 = 1/2.

Then we ALSO realize the headline identity used in the analysis: take sigma0 = 1/2
but split log|xi| = log|zeta| + archimedean. We compute
  INT_0^T log|zeta(1/2+it)| dt
directly and compare its size against T (Selberg: this integral is o(T), in fact
O(sqrt(T log log T)) fluctuations around 0) -- demonstrating the first-moment
bound.
"""
import mpmath as mp

mp.mp.dps = 25


def xi(s):
    # Riemann xi (entire), symmetric xi(s)=xi(1-s). mpmath provides it directly.
    return mp.siegelz  # placeholder, replaced below


def Xi(s):
    s = mp.mpc(s)
    # (s-1)*zeta(s) is entire; near s=1 use the Laurent expansion to avoid the pole.
    if abs(s - 1) < mp.mpf('1e-12'):
        s = 1 + mp.mpf('1e-12')
    return mp.mpf('0.5') * s * (s - 1) * mp.power(mp.pi, -s/2) * mp.gamma(s/2) * mp.zeta(s)


def littlewood_rhs_xi(sigma0, sigma1, T, n_arg=2000):
    f = Xi
    left = mp.quad(lambda t: mp.log(abs(f(mp.mpf(sigma0) + 1j*t))), [0, T])
    right = mp.quad(lambda t: mp.log(abs(f(mp.mpf(sigma1) + 1j*t))), [0, T])

    def arg_integral(t_fixed):
        sigmas = [sigma0 + (sigma1 - sigma0)*k/n_arg for k in range(n_arg+1)]
        vals = []
        prev = None
        offset = mp.mpf(0)
        for s in sigmas:
            a = mp.arg(f(mp.mpf(s) + 1j*t_fixed))
            if prev is not None:
                d = a - prev
                while d > mp.pi:
                    offset -= 2*mp.pi
                    d -= 2*mp.pi
                while d < -mp.pi:
                    offset += 2*mp.pi
                    d += 2*mp.pi
            vals.append(a + offset)
            prev = a
        h = (sigma1 - sigma0)/n_arg
        return h*((vals[0] + vals[-1])/2 + sum(vals[1:-1]))

    top = arg_integral(T)
    bottom = arg_integral(0)
    return (left - right + top - bottom)/(2*mp.pi)


def test_B_onLine():
    print("="*70)
    print("TEST B: Littlewood for genuine Riemann Xi, left edge sigma0 = 1/2")
    print("="*70)
    sigma1 = 3.0
    # First few zeros are at gamma ~ 14.13, 21.02, 25.01, 30.42, 32.93, ...
    for T in [20.0, 27.0, 35.0]:
        rhs = littlewood_rhs_xi(0.5, sigma1, T)
        # number of zeros below T (all on line):
        n_below = mp.nstr(rhs, 6)
        print(f"  T={T}: sum_(beta>1/2)(beta-1/2) via Littlewood RHS = {n_below}")
    print("  (All zeros below these T are ON the line, so the true value is 0.")
    print("   The RHS should be ~0 up to numerical/arg-sampling error.)")


def test_B_logzeta_integral():
    print("="*70)
    print("TEST B': size of INT_0^T log|zeta(1/2+it)| dt  vs  T")
    print("="*70)
    print("  Selberg: mean of log|zeta(1/2+it)| is 0, fluctuations O(sqrt(T loglogT)).")
    print("  So this integral should be o(T) -- tiny compared to T.")
    for T in [50.0, 100.0, 200.0, 500.0]:
        # integrate, avoiding exact zeros on the line (integrable log singularities;
        # mpmath quad handles them via subdivision).
        I = mp.quad(lambda t: mp.log(abs(mp.zeta(mp.mpf('0.5') + 1j*t))),
                    [0, T])
        print(f"  T={T:6.0f}:  INT log|zeta(1/2+it)|dt = {mp.nstr(I, 8):>14}"
              f"   (I/T = {mp.nstr(I/T, 5)})")


if __name__ == "__main__":
    test_B_onLine()
    print()
    test_B_logzeta_integral()
