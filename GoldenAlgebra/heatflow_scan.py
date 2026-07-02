#!/usr/bin/env python3
"""
heatflow_scan.py  -- the decisive scan.

Step 1: confirm U_t >= 0 broadly on the UHP at t=0 (Schur boundary intact = RH energy positivity).
Step 2: scan (x, y, t), record U and dU/dt; locate NEAR-CONTACT points (U smallest).
Step 3: KEY DIAGNOSTIC: at U~0, is dU/dt > 0 (PROTECTIVE) or sign-changing/0 (MARGINAL)?
Step 4: forward (t up) vs backward (t down) orientation explicitly.
"""
import mpmath as mp
from heatflow_firstcontact import quantities, Phi

mp.mp.dps = 30
A = mp.mpf('1.05')   # cutoff; Phi negligible beyond ~0.7, but keep margin

def fmt(z, n=6):
    return mp.nstr(z, n)

print("="*78)
print("STEP 1: U_t at t=0 over a UHP grid  (U = log||A||^2 - log||B||^2)")
print("Expect U >= 0 (Schur contractivity at base point).")
print("="*78)
print(f"{'x':>6} {'y':>6} {'U(t=0)':>16} {'dU/dt':>16}")
minU = None
for xi in [0.5, 1.0, 2.0, 3.0, 5.0, 8.0, 12.0]:
    for yi in [0.1, 0.3, 0.6, 1.0, 1.5]:
        q = quantities(0.0, A, xi, yi)
        U = q['U']; dU = q['dUdt']
        print(f"{xi:>6} {yi:>6} {fmt(U):>16} {fmt(dU):>16}")
        if minU is None or U < minU[0]:
            minU = (U, xi, yi, dU)
print(f"\nSmallest U at t=0: U={fmt(minU[0])} at (x={minU[1]}, y={minU[2]}), dU/dt={fmt(minU[3])}")
