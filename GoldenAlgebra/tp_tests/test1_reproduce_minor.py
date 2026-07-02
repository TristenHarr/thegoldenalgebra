"""
TEST 1: Independently reproduce the paper's certified-negative 5x5 Toeplitz minor
at (u0=0.01, h=0.05), and confirm orders 2,3,4 are strictly positive.

Paper (arXiv 2602.20313) claims:
  D_5(0.01,0.05) = det(M) in [-1.8472496e-9, -1.8472225e-9]  (NEGATIVE)
  D_2,D_3,D_4 strictly positive.
"""
import mpmath as mp
from phi_kernel import K_paper, toeplitz_det, Phi_paper

mp.mp.dps = 80

print("=== Sanity: a few Phi_paper values ===")
for u in ['0.0','0.01','0.05','0.1']:
    print(f"  Phi_paper({u}) = {mp.nstr(Phi_paper(u), 15)}")

print("\n=== Toeplitz determinants at u0=0.01, h=0.05 ===")
u0, h = '0.01', '0.05'
for r in range(2, 8):
    D = toeplitz_det(K_paper, u0, h, r)
    sign = '+' if D > 0 else ('-' if D < 0 else '0')
    print(f"  D_{r}(0.01,0.05) = {mp.nstr(D, 12)}   sign={sign}")

print("\n=== Focus: D_5 vs paper interval [-1.8472496e-9, -1.8472225e-9] ===")
D5 = toeplitz_det(K_paper, u0, h, 5)
print(f"  D_5 = {mp.nstr(D5, 20)}")
lo = mp.mpf('-1.8472496e-9'); hi = mp.mpf('-1.8472225e-9')
print(f"  in paper interval? {lo <= D5 <= hi}")
print(f"  D_5 negative?      {D5 < 0}")
