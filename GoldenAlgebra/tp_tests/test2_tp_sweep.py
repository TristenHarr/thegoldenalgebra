"""
TEST 2: Determine the EXACT total-positivity level.

(a) Search for a NEGATIVE minor of order 2,3,4 over many node/spacing configs
    (Toeplitz AND general non-equispaced).  If none found at order<=4 but order 5
    fails => the kernel is exactly PF_4 (TP_4) and NOT PF_5.
(b) Confirm order-5 failure is robust (many (u0,h)).
(c) Locate the C_5 sign-change threshold u0* ~ 0.0311398.
"""
import mpmath as mp
import random
from phi_kernel import K_paper, toeplitz_det, general_minor_det

mp.mp.dps = 60

print("=== (a) Hunt for negative minors at orders 2,3,4 ===")
random.seed(12345)
neg_found = {2: None, 3: None, 4: None}
n_configs = 0

# Toeplitz sweep over a grid of (u0,h)
u0_grid = [mp.mpf(x)/1000 for x in range(0, 400, 7)]   # 0 .. 0.4
h_grid  = [mp.mpf(x)/1000 for x in range(2, 300, 11)]   # 0.002 .. 0.3
for r in (2,3,4):
    minD = mp.inf
    for u0 in u0_grid:
        for h in h_grid:
            D = toeplitz_det(K_paper, u0, h, r)
            n_configs += 1
            if D < minD: minD = D
            if D < 0 and neg_found[r] is None:
                neg_found[r] = (float(u0), float(h), D)
    print(f"  order {r}: min Toeplitz det over grid = {mp.nstr(minD,8)}  neg_found={neg_found[r]}")

print(f"  (scanned {n_configs} Toeplitz configs)")

print("\n=== (a2) Random GENERAL (non-equispaced) ordered minors, orders 2,3,4 ===")
for r in (2,3,4):
    minD = mp.inf
    worst = None
    for _ in range(4000):
        # random ordered nodes in [-0.5, 0.5]
        xs = sorted(mp.mpf(random.uniform(-0.5,0.5)) for _ in range(r))
        ys = sorted(mp.mpf(random.uniform(-0.5,0.5)) for _ in range(r))
        # require strictly increasing
        if any(xs[i+1]-xs[i] < mp.mpf('1e-6') for i in range(r-1)): continue
        if any(ys[i+1]-ys[i] < mp.mpf('1e-6') for i in range(r-1)): continue
        D = general_minor_det(K_paper, xs, ys)
        if D < minD:
            minD = D; worst = (xs, ys)
    print(f"  order {r}: min general det over 4000 random = {mp.nstr(minD,8)}",
          "<-- NEGATIVE!" if minD < 0 else "(all >= 0)")

print("\n=== (b) Robustness of order-5 failure across many (u0,h) ===")
neg5 = 0; tot5 = 0; pos5 = 0
for u0 in [mp.mpf(x)/1000 for x in range(0, 60, 5)]:
    for h in [mp.mpf(x)/1000 for x in range(20, 120, 10)]:
        D5 = toeplitz_det(K_paper, u0, h, 5)
        tot5 += 1
        if D5 < 0: neg5 += 1
        else: pos5 += 1
print(f"  D_5 over {tot5} configs (small u0): negative={neg5}, nonneg={pos5}")

print("\n=== (c) C_5 sign-change threshold u0* (via small-h D_5/h^20) ===")
def C5_approx(u0, h):
    return toeplitz_det(K_paper, u0, h, 5) / mp.mpf(h)**(5*4)
# bisection on sign of C5_approx with tiny h
h = mp.mpf('0.01')
lo, hi = mp.mpf('0.0'), mp.mpf('0.06')
# verify bracket
clo = C5_approx(lo, h); chi = C5_approx(hi, h)
print(f"  C5~(u0=0, h={float(h)}) = {mp.nstr(clo,8)};  C5~(u0=0.06) = {mp.nstr(chi,8)}")
if clo*chi < 0:
    for _ in range(60):
        mid = (lo+hi)/2
        cm = C5_approx(mid, h)
        if cm*clo <= 0: hi = mid
        else: lo = mid; clo = cm
    print(f"  threshold u0* ~ {mp.nstr((lo+hi)/2, 12)}  (paper: 0.031139763615...)")
else:
    print("  no sign change in bracket at this h; (C5 limit needs smaller h)")
