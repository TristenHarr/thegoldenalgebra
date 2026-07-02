#!/usr/bin/env python3
"""
signed_kernel_FINAL.py — consolidated off-axis signed-kernel result.

MAIN THEOREM (symbolically proven, see identities below):
  The per-zero net contribution of an off-line zero (gamma, eta) to the sign field
  G(z) = -Im(Xi'/Xi)(z) at a probe z = x + i y (y>0) is EXACTLY

     net(x,y,gamma,eta) = R(x,y,gamma) + K_z(eta,gamma)
                        = m(y,eta,gamma+x) + m(y,eta,gamma-x),

  with the CLEAN per-mirror closed form

     m(y,eta,a) = 2 y (a^2 + y^2 - eta^2) / [ ((y-eta)^2+a^2) ((y+eta)^2+a^2) ].

  SIGN:  m(y,eta,a) >= 0  <=>  a^2 + y^2 >= eta^2  <=>  (y>=|eta|, any a)  OR (|a| large).
  In particular  m >= 0  for EVERY a whenever  y >= |eta|.

  REGION  R = { z = x+iy : y >= 1/2 }.  Since every off-line zero has |eta| < 1/2 <= y,
  every per-mirror net is >= 0 on R, hence net >= 0 for EVERY off-line zero, EVERY x.
  => the off-line population can NEVER force G < 0 on R: R is an UNCONDITIONAL
  anti-Herglotz region OFF the imaginary axis.

HELP/HURT SIGN-MAP (the part the |K| bound of the prior agent threw away):
  near the off-line pole w = gamma + i eta, the singular part of K is +(y-eta)/|z-w|^2:
     y > eta (probe ABOVE the zero)  => K -> +inf  : the off-line zero HELPS G>=0
     y < eta (probe BELOW the zero)  => K -> -inf  : the off-line zero HURTS  (net<0)
  The HURT region is the thin sliver { y < eta <= 1/2, x ~ gamma } BELOW each off-line
  zero. R = {y>=1/2} sits entirely ABOVE every off-line zero => only the HELP sign.

TRIVIALITY VERDICT: NONTRIVIAL. R reaches Euclidean distance -> 0 of an off-line zero
  (x=gamma, y=1/2, eta->1/2), yet nets >= 0 — "safe by SIGN" (above the zero), NOT
  "safe by distance" (the prior axis x=0 was always >= 14.13 from every zero).
"""
import sympy as sp, mpmath as mp
mp.mp.dps = 30

# ---- symbolic confirmation of the two identities ----
y,e,a,x,g = sp.symbols('y e a x g', real=True)
ImDquad = ( 2*y/(y**2+(g+x)**2) + 2*y/(y**2+(g-x)**2)
   + (e-y)/((e-y)**2+(g+x)**2) + (e-y)/((e-y)**2+(g-x)**2)
   - (e+y)/((e+y)**2+(g+x)**2) - (e+y)/((e+y)**2+(g-x)**2) )
Kfull = -ImDquad
Rref  = 2*y/(y**2+(g+x)**2)+2*y/(y**2+(g-x)**2)
mclean = lambda aa: 2*y*(aa**2+y**2-e**2)/(((y-e)**2+aa**2)*((y+e)**2+aa**2))
print("IDENTITY 1  net(x,y,g,e) = R+K == m(g+x)+m(g-x):",
      sp.simplify((Rref+Kfull) - (mclean(g+x)+mclean(g-x))) == 0)
# per-mirror net numerator sign
mnum = sp.numer(sp.together(mclean(a)))
print("IDENTITY 2  m(y,e,a) numerator = 2y(a^2+y^2-e^2):",
      sp.simplify(mnum - 2*y*(a**2+y**2-e**2)) == 0)
print("            denominator = ((y-e)^2+a^2)((y+e)^2+a^2) > 0 for y>0.")
print()

# ---- numeric: net >= 0 everywhere on R = {y>=1/2}, REACHING the zeros ----
def mclean_n(yy,ee,aa):
    yy,ee,aa=mp.mpf(yy),mp.mpf(ee),mp.mpf(aa)
    d=((yy-ee)**2+aa**2)*((yy+ee)**2+aa**2)
    return 2*yy*(aa**2+yy**2-ee**2)/d if d!=0 else mp.mpf('nan')
def net_n(xx,yy,gg,ee): return mclean_n(yy,ee,gg+xx)+mclean_n(yy,ee,gg-xx)

print("=== net >= 0 on R = {y>=1/2}, including probes that TOUCH the zeros ===")
import random; random.seed(0)
mn=None
for _ in range(1000000):
    gg=random.uniform(14,5000); ee=random.uniform(-0.5,0.5)
    yy=random.uniform(0.5, 5000); xx=random.uniform(-2*gg,2*gg)
    v=net_n(xx,yy,gg,ee)
    if mp.isnan(v): continue
    if mn is None or v<mn[0]: mn=(float(v),xx,yy,gg,ee)
print(f"  min per-zero net over 1e6 R-probes: {mn[0]:.6g} >= 0 ? {mn[0]>=0}")
print(f"     at x={mn[1]:.2f}, y={mn[2]:.3f}, gamma={mn[3]:.2f}, eta={mn[4]:.3f}")
print()

print("=== HELP/HURT confirmation: below an off-line zero (y<eta) net goes NEGATIVE ===")
g0,e0=mp.mpf('14.1347'),mp.mpf('0.4')
for yy in [0.5,0.45,0.41,0.4001,0.39,0.3,0.2]:
    v=net_n(g0,yy,g0,e0)
    tag = "HELP(>=0)" if v>=0 else "HURT(<0)"
    print(f"  x=gamma, y={yy:>6.4f} (eta={float(e0)}): net={mp.nstr(v,5):>14}  {tag}")
print("  => the boundary is exactly y = eta; R={y>=1/2} clears all off-line zeros (|eta|<1/2).")
print()

print("=== signed vs |K|: the improvement ===")
print("Prior |K| axis bound needed gamma>=14 (FAR-from-zeros) and only x=0.")
print("Signed per-mirror net m(y,e,a)>=0 holds for ALL a (incl a=0, x=gamma, AT the zero")
print("abscissa) and ALL gamma down to the first zero, requiring ONLY y>=|eta|.")
print("The |K| majorant 6y e^2/(a^2+y^2)^2 is LOSSY by ratio -> inf near the pole;")
print("the signed (exact) net m is bounded BELOW by 0 there because the pole HELPS.")
print()
print("BANKABLE: R = {y>=1/2} is an UNCONDITIONAL off-axis anti-Herglotz region,")
print("NONTRIVIAL (reaches dist->0 of zeros), proven by the per-mirror SIGN, no RH,")
print("no density needed for the per-zero statement (density only bounds tail SUMMABILITY).")
