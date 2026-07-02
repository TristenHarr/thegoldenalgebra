"""
SAVED SCRIPT: displacement second-moment under the general near-line density
   N(1/2+u,T) << T^{1 - 2 theta u} (log T)^k,  Conrey: any theta < 4/7, k=1.
Computes the closed-form envelope constant 1/theta^2 and the log-power k-2.
Tabulates M2(T)/(T/log T) at finite T for theta in {1/8 (Selberg), 4/7 (Conrey)}.
"""
import sympy as sp, math

theta_sym, L, T = sp.symbols('theta L T', positive=True)
c = 2*theta_sym*L
inner = (1 - sp.exp(-c/2)*(1+c/2))/c**2
M2 = 4*T*L*inner          # k=1
print("Exact envelope (k=1):", sp.simplify(M2))
print("Leading const (coeff of T/log T):", sp.limit(M2*L/T, L, sp.oo), "= 1/theta^2\n")

def ratio_at(theta, T):
    L = math.log(T); c = 2*theta*L
    inner = (1 - math.exp(-c/2)*(1+c/2))/c**2
    M2 = 4*T*L*inner
    return M2/(T/L)   # ratio to T/log T

print(f"{'T':>8} | M2/(T/logT) Selberg(1/8) | Conrey(4/7) | ratio improve")
for Texp in [6,12,30,100,1000]:
    T = 10.0**Texp
    rS = ratio_at(0.125, T); rC = ratio_at(4/7, T)
    print(f"10^{Texp:<4} | {rS:>20.3f}    | {rC:>9.4f}  | {rS/rC:>6.2f}x")
print("\nAsymptotic: Selberg const 64, Conrey const (7/4)^2 = 49/16 = %.5f, ratio 64/(49/16)=%.2fx"
      % (49/16, 64/(49/16)))
