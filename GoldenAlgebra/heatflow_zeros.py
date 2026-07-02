#!/usr/bin/env python3
"""
heatflow_zeros.py -- the HONEST threshold test.

The finite-cutoff Schur quantity U_t is structurally robust (U>0, dU/dt>0 always) because
the finite cosine transform of a fixed amplitude is HB-stable; it does NOT resolve the dBN
threshold. The genuine threshold lives in the ZEROS of H_t themselves.

Here we:
 1. Check Phi sign structure (it is NOT one-signed: the -3 pi n^2 e^{5u} term).
 2. Compute complex zeros of the finite H_t(z) = int_0^A e^{t u^2} Phi(u) cos(z u) du as a
    function of t, near a real double-zero / conjugate-pair pitchfork, to SEE the threshold.
 3. At a near-pitchfork (two zeros approaching the real axis / each other), evaluate U_t and
    dU/dt at the midpoint just above the axis -> is the Schur derivative protective or marginal
    EXACTLY where the zeros are about to collide and leave the line?

This is the maximum-principle 'first contact' in its true form: U_t(z*) -> 0 in the INTERIOR
(not just y->0) precisely when a zero of A_t (equivalently a zero of H_t) approaches z*.
"""
import mpmath as mp
from heatflow_firstcontact import Phi, quantities

mp.mp.dps = 30
A = mp.mpf('1.05')
def fmt(z,n=6): return mp.nstr(z,n)

# 1. Phi sign structure
print("="*78); print("(1) Phi(u) sign structure (u^2-weighted is what d/dt sees)"); print("="*78)
for u in ['0.0','0.05','0.1','0.15','0.2','0.25','0.3','0.4']:
    print(f"Phi({u}) = {fmt(Phi(mp.mpf(u)),8)}")
print("=> Phi is positive near 0, decays super-fast; the integrand is effectively one-signed")
print("   on the support, which is WHY the finite model is HB-robust (Polya-type).")

# 2. H_t and its complex zeros.
def Ht(t, z):
    t=mp.mpf(t)
    return mp.quad(lambda u: mp.e**(t*u*u)*Phi(u)*mp.cos(z*u), [0, A])

print()
print("="*78)
print("(2) Lowest zeros of finite H_t(z) as t varies. Are they real? (HB => yes)")
print("    For a Polya/HB function ALL zeros are real for ALL t >= some Lambda_model.")
print("="*78)
print(f"{'t':>7}  {'first zeros of H_t (Im should be ~0 if all-real)':>50}")
for ti in ['-3.0','-1.0','0.0','1.0','3.0']:
    t=mp.mpf(ti)
    zs=[]
    # scan real axis for sign changes of real H_t (H_t is real on R since Phi,cos real)
    prev=None; xs=mp.linspace(0.5, 40, 400)
    for x in xs:
        v=Ht(t, x).real
        if prev is not None and prev*v<0:
            try:
                r=mp.findroot(lambda z: Ht(t,z), mp.mpf(x))
                zs.append(r)
            except Exception:
                pass
        prev=v
        if len(zs)>=4: break
    maxim=max((abs(z.imag) for z in zs), default=mp.mpf(0))
    print(f"{ti:>7}  zeros~{[fmt(z.real,7) for z in zs]}  max|Im|={fmt(maxim,3)}")

# 3. Interior near-contact: pick a point just above a real zero of H_t (where A_t ~ B_t in modulus?).
# A_t has the SAME zeros as the structure function E_Phi; U_t = log|A|^2-log|B|^2.
# As z-> a real zero of A_t from UHP, |A_t|->0 so U_t -> -inf, NOT 0. The Schur 'contact' U=0
# is |A_t|=|B_t|, i.e. |Theta_t|=1, which on the boundary R is automatic. Map U near a real zero:
print()
print("="*78)
print("(3) U_t and dU/dt approaching a real zero x0 of A_t from the UHP (interior contact test)")
print("="*78)
t=mp.mpf('0.0')
# find a real zero of Re/structure via A_transform real part ~ first zero around x~ root of H
# Just scan x for where U dips (||A|| smallest relative to ||B||)
print(f"{'x':>8} {'y':>8} {'U':>16} {'dU/dt':>16} {'||A||^2':>14} {'||B||^2':>14}")
for xi in ['6.0','7.0','7.5','8.0','9.0','10.0']:
    for yi in ['0.05']:
        q=quantities(t,A,mp.mpf(xi),mp.mpf(yi))
        print(f"{xi:>8} {yi:>8} {fmt(q['U']):>16} {fmt(q['dUdt']):>16} {fmt(q['nA']):>14} {fmt(q['nB']):>14}")
