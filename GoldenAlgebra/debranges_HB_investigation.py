"""
de Branges / Hermite-Biehler investigation for the Riemann xi pullback.

Riemann's Xi:  Xi(z) = 2 * integral_0^inf Phi(u) cos(z u) du
with Phi(u) = sum_{n>=1} (2 pi^2 n^4 e^{9u} - 3 pi n^2 e^{5u}) exp(-pi n^2 e^{4u}).
This is the standard Riemann Phi (super-exponentially decaying, even extension symmetric).

Xi(z) = xi(1/2 + i z) (up to normalization). Xi(z) is real for real z, even.

de Branges structure function (one-sided):
   E_Phi(z) = 2 * integral_0^inf Phi(u) e^{-i z u} du
so that  Xi(z) = (E_Phi(z) + E_Phi^#(z))/2  where E^#(z) = conj(E(conj z)).
Check: E(z) + E#(z) = 2 Re-extension = 2 * 2 integral Phi cos = 2 Xi. Good.

Hermite-Biehler:  |E#(z)| < |E(z)|  for Im z > 0.
Equivalently  |E(x+iy)|^2 - |E#(x+iy)|^2 > 0  for y>0.

We test this numerically with mpmath using the *true* Phi.
"""
import mpmath as mp
mp.mp.dps = 30

def Phi(u):
    # Riemann's Phi, the integrand kernel. u real.
    s = mp.mpf(0)
    n = 1
    while True:
        npi = mp.pi * n*n
        term = (2*npi*npi*mp.e**(9*u) - 3*npi*mp.e**(5*u)) * mp.e**(-npi*mp.e**(4*u))
        s += term
        if abs(term) < mp.mpf(10)**(-mp.mp.dps-5) and n > 3:
            break
        n += 1
        if n > 200:
            break
    return s

# Xi(z) = 2 * int_0^inf Phi(u) cos(z u) du  (complex z)
def Xi(z):
    f = lambda u: Phi(u) * mp.cos(z*u)
    return 2*mp.quad(f, [0, mp.inf])

# One-sided structure function E(z) = 2 int_0^inf Phi(u) e^{-i z u} du
def E(z):
    f = lambda u: Phi(u) * mp.e**(-1j*z*u)
    return 2*mp.quad(f, [0, mp.inf])

def Esharp(z):
    return mp.conj(E(mp.conj(z)))

# Sanity: Xi vs (E+E#)/2
print("=== Sanity: Xi(z) == (E(z)+E#(z))/2 ? ===")
for z in [mp.mpf(0), mp.mpf(5), mp.mpf(14.13), mp.mpc(2,1), mp.mpc(0,1)]:
    xi = Xi(z)
    eav = (E(z)+Esharp(z))/2
    print(f"z={z}:  Xi={mp.nstr(xi,8)}  (E+E#)/2={mp.nstr(eav,8)}  diff={mp.nstr(abs(xi-eav),4)}")

print()
print("=== Compare E(z) to e^{theta} forms; check Xi(0) normalization ===")
print("Xi(0) =", mp.nstr(Xi(0),10), " (should be 2*int Phi = xi(1/2)>0)")
print()

print("=== HERMITE-BIEHLER TEST: |E(x+iy)|^2 - |E#(x+iy)|^2 for y>0 ===")
print("(HB requires this > 0 everywhere in UHP)")
fails = 0
tests = 0
import itertools
xs = [0, 1, 5, 10, 14.134725, 20, 21.022, 25, 30]
ys = [0.05, 0.2, 0.5, 1.0, 2.0, 5.0]
for x,y in itertools.product(xs, ys):
    z = mp.mpc(x,y)
    e = E(z); es = Esharp(z)
    d = abs(e)**2 - abs(es)**2
    tests += 1
    flag = "" if d > 0 else "  <<< HB FAIL"
    if d <= 0: fails += 1
    print(f"x={x:>10}  y={y:>5}:  |E|^2-|E#|^2 = {mp.nstr(d,6)}{flag}")
print(f"\nTotal tests {tests}, HB failures {fails}")

print()
print("=== Relate to energy monotonicity ===")
# energy monotone: d/dy ||Xi(x+iy)||^2 >= 0.
# Claim: |E|^2-|E#|^2 relates to it. With Xi=(E+E#)/2,
# ||Xi||^2 vs |E|^2-|E#|^2.  Let's also directly compute d/dy ||Xi||^2.
print("Direct d/dy ||Xi(x+iy)||^2 (should be >=0 if energy-monotone target true):")
for x in [0, 5, 14.134725, 20]:
    g = lambda y: abs(Xi(mp.mpc(x,y)))**2
    for y in [0.3, 1.0, 2.0]:
        dd = mp.diff(g, y)
        z = mp.mpc(x,y)
        hbq = abs(E(z))**2 - abs(Esharp(z))**2
        print(f"x={x:>10} y={y}:  d/dy||Xi||^2={mp.nstr(dd,6)}   |E|^2-|E#|^2={mp.nstr(hbq,6)}")
