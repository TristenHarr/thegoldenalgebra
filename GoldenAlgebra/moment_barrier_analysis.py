"""
Is T/log T a barrier from the FORM of the near-line density, or only the constant?

The near-line density has the universal shape (Selberg/Jutila/Conrey):
   N(1/2+u, T) << T^{1 - 2*theta*u} * (log T)^k,   k=1 classically.
Layer-cake:  M2(T) <= 4 (log T)^k * int_0^{1/2} u T^{1-2 theta u} du
                    = 4 T (log T)^k * int_0^{1/2} u e^{-(2 theta log T) u} du.
With c = 2 theta log T, int_0^{1/2} u e^{-c u} du ~ 1/c^2 = 1/(4 theta^2 log^2 T).
=>  M2(T) <~ T (log T)^k / (theta^2 log^2 T) = T (log T)^{k-2} / theta^2.

So the LOG-POWER of the moment is (k-2):
  - k=1 (standard density, factor log T): moment ~ T/log T.        <-- current
  - k=0 (LOG-FREE near-line density):      moment ~ T/(log T)^2.   <-- would be a WIN
  - any power saving in the EXPONENT (theta -> larger) only changes the CONSTANT 1/theta^2.

CONCLUSION: To beat T/log T in ORDER you must REMOVE the log T factor from the
near-line density (k: 1 -> 0), i.e. a LOG-FREE estimate valid near sigma=1/2.
A larger theta (Jutila/Conrey) only shrinks the constant 64 -> ~3.06.
"""
import sympy as sp
L, T, theta, k = sp.symbols('L T theta k', positive=True)
c = 2*theta*L
inner = (1 - sp.exp(-c/2)*(1+c/2))/c**2   # <= 1/c^2
M2 = 4*T*L**k*inner
# leading behavior: replace inner ~ 1/c^2
M2_lead = sp.simplify(4*T*L**k/c**2)
print("M2(T) leading ~", M2_lead, "  => log-power = k-2")
for kk in [0,1,2]:
    print(f"  k={kk}: moment order ~ T * (log T)^{kk-2}")

print("""
WHY the log T factor is structurally present near sigma=1/2:
 The near-line density is proved via a mean-value/Selberg-moment of log|zeta|
 on a vertical segment; the count of zeros in a box of height H>>1 carries an
 unavoidable factor ~ log T (the local zero density N'(t) ~ log t / 2pi). The
 log-free machinery (large-sieve / Halasz-Montgomery + reflection) that removes
 it is only known to close for sigma bounded away from 1/2 (currently sigma >~ 0.985,
 Bellotti 2024). Near sigma=1/2 the reflection argument loses, so k=1 stands.
""")
