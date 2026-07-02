#!/usr/bin/env python3
"""
heatflow_diagnostic.py -- STEP 2,3,4: near-contact diagnostic + orientation + threshold probe.

Findings to nail down:
 (A) y->0 boundary behavior of U and sign of dU/dt there (true near-contact of the Schur disk).
 (B) t-dependence: forward (t increasing) vs backward (t decreasing). Sign convention:
     zeros of H_t move toward real axis as t INCREASES (de Bruijn monotonicity, t>=Lambda => all real).
     So 'protective' = the flow that restores RH = INCREASING t should push U UP (dU/dt>0).
 (C) Artificial near-threshold: drive Phi-weight to create a small-U extended region by using
     a LARGE NEGATIVE t (backward heat, t<Lambda regime would create complex zeros). Watch whether
     dU/dt stays > 0 (robust protective) or loses sign (marginal = dBN wall).
"""
import mpmath as mp
from heatflow_firstcontact import quantities

mp.mp.dps = 30
A = mp.mpf('1.05')
def fmt(z, n=6): return mp.nstr(z, n)

# ---------------------------------------------------------------------------
print("="*78)
print("(A) y -> 0 near-contact: U and dU/dt as the Schur disk boundary is approached")
print("="*78)
print(f"{'x':>5} {'y':>10} {'U':>16} {'dU/dt':>16} {'sign dU/dt':>11}")
for xi in [1.0, 5.0, 12.0]:
    for yi in ['0.05','0.02','0.01','0.004','0.001']:
        q = quantities(0.0, A, xi, mp.mpf(yi))
        U=q['U']; dU=q['dUdt']
        print(f"{xi:>5} {yi:>10} {fmt(U):>16} {fmt(dU):>16} {('+' if dU>0 else ('-' if dU<0 else '0')):>11}")

# ---------------------------------------------------------------------------
print()
print("="*78)
print("(B) t-sweep at a fixed UHP probe: is U increasing in t? where is U smallest in t?")
print("="*78)
xi, yi = mp.mpf('5.0'), mp.mpf('0.3')
print(f"probe x={xi}, y={yi}")
print(f"{'t':>8} {'U':>16} {'dU/dt':>16}")
for ti in ['-0.5','-0.25','-0.1','-0.02','0.0','0.02','0.1','0.25','0.5']:
    q = quantities(mp.mpf(ti), A, xi, yi)
    print(f"{ti:>8} {fmt(q['U']):>16} {fmt(q['dUdt']):>16}")

# ---------------------------------------------------------------------------
print()
print("="*78)
print("(C) Backward-heat near-threshold probe: large NEGATIVE t pushes toward the dBN wall.")
print("    Watch the smallest-U region and whether dU/dt keeps its (protective) sign.")
print("="*78)
print(f"{'t':>8} {'x':>5} {'y':>8} {'U':>16} {'dU/dt':>16} {'sgn':>4}")
for ti in ['-1.0','-2.0','-3.0','-5.0']:
    # find smallest U over a small (x,y) grid at this t
    best=None
    for xi in [0.5,1.0,2.0,4.0,8.0]:
        for yi in ['0.02','0.1','0.3','0.6']:
            q=quantities(mp.mpf(ti),A,mp.mpf(xi),mp.mpf(yi))
            if best is None or q['U']<best[0]:
                best=(q['U'],xi,yi,q['dUdt'])
    U,xb,yb,dU=best
    print(f"{ti:>8} {xb:>5} {yb:>8} {fmt(U):>16} {fmt(dU):>16} {('+' if dU>0 else ('-' if dU<0 else '0')):>4}")
