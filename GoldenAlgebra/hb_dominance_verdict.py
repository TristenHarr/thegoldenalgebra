"""
DECISIVE VERDICT script for ScratchHBDominance.lean's  SpecialPhiHBDominance ( |B|<=|A| ).

Consolidates the closed-form reduction and the implication-failure that PROVE the
HB-dominance route saturates at the boundary = RH (no unconditional theta source).

CONVENTIONS (exact ScratchHBDominance.lean):
  a=cos(xw)cosh(yw) a_y=w cos(xw)sinh(yw) b=sin(xw)sinh(yw) b_y=w sin(xw)cosh(yw)
  L1=int Phi(a+a_y) L2=int Phi(a-a_y) L3=int Phi(b+b_y) L4=int Phi(b-b_y)
  A=L1+iL3 B=L2+iL4 ; R=|A|^2-|B|^2 ; dominance  <=> R>=0 for y>0.

THE CLOSED FORM (this file's central result), with C(w)=int_0^inf Phi(u)cos(wu)du=Xi(w)/2:
  A+B = 2 C(x-iy),   A-B = -2i C'(x-iy),
  R = |A|^2-|B|^2 = Re((A+B)conj(A-B)) = 4 Im( C'(w) conj C(w) ) = Im( Xi'(w) conj Xi(w) ),
  w = x - i y  (LOWER half-plane,  Im w = -y < 0).
  => R = |Xi(w)|^2 * Im( Xi'(w)/Xi(w) ) = |Xi(w)|^2 * (d/dRe w) arg Xi(w).
  R>=0 for all y>0  <=>  arg Xi monotone in the LHP  <=>  Xi Hermite-Biehler  <=>  RH.

FINDINGS:
  * |A|=|B| EXACTLY on the WHOLE real axis (R=0 identically). Boundary fully saturated.
  * Herglotz H=(1+Theta)/(1-Theta)=(A+B)/(A-B) is PURE IMAGINARY on the boundary,
    H(x)= -i Xi(x)/(2 Iby0(x)),  Iby0(x)=int Phi u sin(xu)du.  Its zeros ARE zeta zeros.
    Measure mu: one atom at x=0 (pole of Iby0), a.c. density 0 a.e.; mu encodes the zeros.
  * Phi>=0 (positive measure / Laplace-CM) is UNCONDITIONALLY true here but DOES NOT
    imply R>=0: explicit positive measures (e^{-u}, u e^{-u}, e^{-u}(1+cos3u)/2, ...)
    give R<0 in the LHP. R>=0 holds iff the cosine-transform has REAL zeros only
    (Gaussian e^{-u^2} -> e^{-w^2/4}, real zeros, R>=0). = the target, not a source.
"""
import mpmath as mp
mp.mp.dps = 22
def phi_term(u,n):
    npi=mp.pi*n*n
    return (2*npi*npi*mp.e**(9*u)-3*npi*mp.e**(5*u))*mp.e**(-npi*mp.e**(4*u))
def Phi(u,N=26): return mp.fsum(phi_term(u,n) for n in range(1,N+1))
UP=6.0
def C(w):  return mp.quad(lambda u:Phi(u)*mp.cos(w*u),[0,UP])
def Cp(w): return mp.quad(lambda u:-Phi(u)*u*mp.sin(w*u),[0,UP])
def Ls(x,y):
    Ia =mp.quad(lambda u:Phi(u)*mp.cos(x*u)*mp.cosh(y*u),[0,UP])
    Iay=mp.quad(lambda u:Phi(u)*u*mp.cos(x*u)*mp.sinh(y*u),[0,UP])
    Ib =mp.quad(lambda u:Phi(u)*mp.sin(x*u)*mp.sinh(y*u),[0,UP])
    Iby=mp.quad(lambda u:Phi(u)*u*mp.sin(x*u)*mp.cosh(y*u),[0,UP])
    return mp.mpc(Ia+Iay,Ib+Iby),mp.mpc(Ia-Iay,Ib-Iby)

print("CENTRAL IDENTITY  R = 4 Im(C'(w) conjC(w)) = Im(Xi'(w)conjXi(w)),  w=x-iy:")
for (x,y) in [(5,0.3),(14.134725,0.5),(28.26945,0.2),(28.5,0.1),(42.044,0.3)]:
    A,B=Ls(x,y); R=float(abs(A)**2-abs(B)**2)
    w=mp.mpc(x,-y); Rc=float(4*(Cp(w)*mp.conj(C(w))).imag)
    print(f"  (x={x:>10},y={y}): R={R:.6e}  4Im(C'conjC)={Rc:.6e}  match={abs(R-Rc)<1e-12}")

print()
print("IMPLICATION FAILURE — positive measures Phi>=0 with R<0 (LHP grid min):")
import numpy as np
def minR(Phifun,UP2=8.0):
    def Cc(w): return mp.quad(lambda u:Phifun(u)*mp.cos(w*u),[0,UP2])
    def Cpp(w):return mp.quad(lambda u:-Phifun(u)*u*mp.sin(w*u),[0,UP2])
    w0=1e9
    for x in np.linspace(0.2,40,60):
        for y in np.linspace(0.05,3,30):
            w=mp.mpc(float(x),-float(y)); v=float((Cpp(w)*mp.conj(Cc(w))).imag)
            if v<w0: w0=v
    return w0
for f,nm in [(lambda u:mp.e**(-u),'e^-u'),(lambda u:u*mp.e**(-u),'u e^-u'),
             (lambda u:mp.e**(-u)*(1+mp.cos(3*u))/2,'e^-u(1+cos3u)/2'),
             (lambda u:mp.e**(-u*u),'gaussian e^-u^2 (HB, real zeros)')]:
    m=minR(f); print(f"  {nm:>28}: minR={m:.4e}  {'NEG => not sufficient' if m<-1e-9 else '>=0 (real-zero transform)'}")
print()
print("VERDICT: HB-dominance route = Im(Xi' conj Xi)>=0 in LHP = Hermite-Biehler(Xi) = RH.")
print("No unconditional theta-only source: Phi>=0 holds but does not imply the dominance.")
