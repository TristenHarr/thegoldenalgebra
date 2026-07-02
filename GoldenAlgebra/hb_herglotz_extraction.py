"""
DECISIVE TEST 1 + 3 for the HB-dominance program of ScratchHBDominance.lean.

Conventions (EXACT match to ScratchHBDominance.lean):
  a(w)=cos(xw)cosh(yw)   a_y(w)=w cos(xw)sinh(yw)
  b(w)=sin(xw)sinh(yw)   b_y(w)=w sin(xw)cosh(yw)
  L1=int Phi(a+a_y) L2=int Phi(a-a_y) L3=int Phi(b+b_y) L4=int Phi(b-b_y)
  A=L1+iL3   B=L2+iL4
  R = |A|^2-|B|^2 = L1^2+L3^2-L2^2-L4^2   (target: R>=0 for y>0  <=>  RH)
  Theta = B/A   (de Branges structure ratio)
  H = (1+Theta)/(1-Theta)   (Cayley/Herglotz transform)

Phi = true Riemann Phi.  Xi(x)=2 int Phi cos(xw) dw  has zeros at x=2*gamma_n.

KEY ANALYTIC IDENTITY (already established, re-verified here):
  A+B = 2 Ia + 2i Ib ,   A-B = 2 Iay + 2i Iby
  A real part on y=0:  Ib=Iby=0  =>  A=2Ia=Xi(x) real, B=A-2Iay... actually
  At y=0:  cosh=1, sinh=0 => a=cos(xw), a_y=0, b=0, b_y=w sin(xw).
    L1=L2=Ia=int Phi cos(xw)=Xi(x)/2,  L3= Iby, L4=-Iby.
    => A = Xi/2 + i*Iby,  B = Xi/2 - i*Iby.   |A|=|B| EXACTLY on the real axis!
  So Theta has |Theta|=1 on the WHOLE real axis (boundary), and R=0 there identically.

This file:
  (1) extracts the Herglotz measure of H on the UHP and asks if its density has a
      closed theta form or encodes the zeros (=> RH-equivalent spectral data).
  (2) maps the margin R and 1-|Theta| as y->0 and as a function of dist to zeros.
"""
import mpmath as mp
import numpy as np
mp.mp.dps = 22

def phi_term(u, n):
    npi = mp.pi*n*n
    return (2*npi*npi*mp.e**(9*u) - 3*npi*mp.e**(5*u))*mp.e**(-npi*mp.e**(4*u))
def Phi(u, N=24):
    return mp.fsum(phi_term(u, n) for n in range(1, N+1))

UP = 6.0
def Ls(x, y):
    Ia  = mp.quad(lambda u: Phi(u)*mp.cos(x*u)*mp.cosh(y*u), [0, UP])
    Iay = mp.quad(lambda u: Phi(u)*u*mp.cos(x*u)*mp.sinh(y*u), [0, UP])
    Ib  = mp.quad(lambda u: Phi(u)*mp.sin(x*u)*mp.sinh(y*u), [0, UP])
    Iby = mp.quad(lambda u: Phi(u)*u*mp.sin(x*u)*mp.cosh(y*u), [0, UP])
    return (Ia+Iay, Ia-Iay, Ib+Iby, Ib-Iby)
def AB(x, y):
    L1,L2,L3,L4 = Ls(x,y)
    return mp.mpc(L1,L3), mp.mpc(L2,L4)

print("="*78)
print("STEP 0 — verify |A|=|B| identically on the real axis (boundary saturation)")
print("="*78)
for x in [0.0, 5.0, 14.134725, 28.26945, 42.0]:
    A,B = AB(x, 1e-9)
    print(f"  x={x:>10}: |A|={mp.nstr(abs(A),8):<13} |B|={mp.nstr(abs(B),8):<13} "
          f"|A|-|B|={mp.nstr(abs(A)-abs(B),4)}  R={mp.nstr(abs(A)**2-abs(B)**2,4)}")
print("  => On y->0, |A|=|B| EXACTLY (Theta is unimodular on the entire real axis).")
print("     The whole real axis is the boundary; Theta is an INNER-type boundary.")

print()
print("="*78)
print("STEP 1 — HERGLOTZ TRANSFORM H=(1+Theta)/(1-Theta); is Re H >=0, and the measure?")
print("="*78)
# H = (1+Theta)/(1-Theta), Theta=B/A.  H = (A+B)/(A-B).
# A+B = 2Ia+2i Ib,  A-B = 2Iay+2i Iby  => H = (Ia + i Ib)/(Iay + i Iby).
def H_of(x, y):
    A,B = AB(x,y)
    if abs(A-B)==0: return None
    return (A+B)/(A-B)
print("Re H and Im H sampled in the interior (y>0):")
for y in [1.0, 0.5, 0.2]:
    row=[]
    for x in [0.0, 5.0, 14.134725, 28.26945]:
        H=H_of(x,y)
        row.append((x, mp.nstr(H.real,5), mp.nstr(H.imag,5)))
    print(f"  y={y}: "+"  ".join(f"x={r[0]}:ReH={r[1]},ImH={r[2]}" for r in row))

print()
print("Boundary density via Re H(x+iy) as y->0  (Herglotz: dmu = (1/pi) ReH dx):")
print("  (if H Herglotz with Im s>0 mapping, the boundary Re H is the abs-cont density)")
for x in [0.0, 3.0, 7.0, 14.134725, 20.0, 28.26945]:
    vals=[]
    for y in [0.2,0.1,0.05,0.02,0.01]:
        H=H_of(x,y)
        vals.append(H.real if H else float('nan'))
    print(f"  x={x:>10}: ReH(y=.2..01)= "+"  ".join(mp.nstr(v,5) for v in vals))

print()
print("="*78)
print("STEP 2 — MARGIN MAP:  R(x,y) and 1-|Theta| vs distance to nearest zero x0=2gamma")
print("="*78)
zeros_x = [2*g for g in [14.134725,21.022040,25.010858,30.424876,32.935062]]
def nearest_zero_dist(x):
    return min(abs(x-z) for z in zeros_x)
print("Interior margin R=|A|^2-|B|^2  (should be >0 in interior if positivity holds):")
print(f"{'x':>10} {'y':>7} {'R':>15} {'1-|Theta|':>14} {'dist0':>9}")
import random
random.seed(1)
anyneg=False
samples=[]
for x in [0.5, 7.0, 14.134725, 28.26945, 28.0, 28.5, 42.044]:
    for y in [1.0, 0.5, 0.2, 0.08, 0.03]:
        A,B=AB(x,y)
        R=abs(A)**2-abs(B)**2
        th=abs(B)/abs(A) if abs(A)>0 else float('nan')
        if R<0: anyneg=True
        print(f"{x:10.4f} {y:7.3f} {mp.nstr(R,6):>15} {mp.nstr(1-th,6):>14} {nearest_zero_dist(x):9.3f}")
print("ANY NEGATIVE R IN INTERIOR:", anyneg)

print()
print("STEP 2b — APPROACH TO A ZERO along the real axis from inside (x=2gamma, y->0):")
print("  Does the margin R/y (the y-derivative density) DEGRADE/vanish at the zero?")
print(f"{'x':>12} {'y':>8} {'R':>15} {'R/y':>15}")
x0=28.26945028  # first zero
for x in [x0, x0+0.5, x0+2.0]:
    for y in [0.2,0.1,0.05,0.02,0.01,0.005]:
        A,B=AB(x,y)
        R=abs(A)**2-abs(B)**2
        print(f"{x:12.5f} {y:8.4f} {mp.nstr(R,6):>15} {mp.nstr(R/y,6):>15}")
    print()
