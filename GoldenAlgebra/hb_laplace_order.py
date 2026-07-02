"""
DECISIVE TEST 2 — LAPLACE-ORDER SUFFICIENCY for ScratchHBDominance.lean.

Structural identities (y=0 boundary, exact):
  A+B = 2Ia + 2i Ib,   A-B = 2Iay + 2i Iby
At y=0: A+B = 2 Ia = Xi(x) (real), A-B = 2i Iby0(x) (imaginary).
For y>0, A+-B are genuine complex transforms of Phi against (a+-?) kernels.

THE CRUX claimed in debranges_three_probes: are A+B and A-B SEPARATELY Laplace
transforms of POSITIVE measures, and does that IMPLY |B|<=|A|?

Test:
 (Q1) Is the one-sided Laplace g(s)=int_0^inf Phi(u) e^{-s u} du completely monotone
      (Bernstein: g of a POSITIVE measure)?  Phi changes sign, so likely NO.
 (Q2) Even granting Laplace-positivity of A+-B, does "A+B and A-B both LT of pos meas"
      IMPLY |B|<=|A| at the complex arguments that arise? Construct the implication and
      test it / find a counterexample with a toy positive-measure pair.
 (Q3) The real question: |A+B| and |A-B| vs |A|,|B|. |B|<=|A| <=> Re(A conj B)>= ...
      Actually |A|^2-|B|^2 = Re((A+B) conj(A-B)).  So R = Re((A+B) (A-B)^bar).
      => R>=0  <=>  the two transforms A+B, A-B have NONNEGATIVE Hermitian pairing.
      Test whether THAT is implied by separate Laplace-positivity, or is itself the wall.
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

print("="*78)
print("Q1 — Complete monotonicity of one-sided Laplace g(s)=int Phi e^{-su} du")
print("="*78)
def gderiv(s, k):
    return mp.quad(lambda u: Phi(u)*((-u)**k)*mp.e**(-s*u), [0, UP])
print("CM requires (-1)^k g^{(k)}(s) >= 0 for ALL k  (i.e. g>=0,g'<=0,g''>=0,...).")
print(f"{'s':>6} "+" ".join(f"{'(-1)^'+str(k)+'g'+'^'+str(k):>14}" for k in range(6)))
cm_ok=True
for s in [0.3,0.5,1.0,2.0,4.0,8.0]:
    signed=[(-1)**k*gderiv(s,k) for k in range(6)]
    if any(v<0 for v in signed): cm_ok=False
    print(f"{s:>6} "+" ".join(f"{mp.nstr(v,5):>14}" for v in signed))
print("COMPLETELY MONOTONE (=> Phi a positive measure):", cm_ok)
print("  (Phi has the 2pi^2 n^4 - 3 pi n^2 sign change => expected NOT a positive measure)")

print()
print("="*78)
print("Q3 — R = Re((A+B) conj(A-B)).  Verify, and ask if separate LT-positivity => R>=0")
print("="*78)
def Ls(x,y):
    Ia =mp.quad(lambda u:Phi(u)*mp.cos(x*u)*mp.cosh(y*u),[0,UP])
    Iay=mp.quad(lambda u:Phi(u)*u*mp.cos(x*u)*mp.sinh(y*u),[0,UP])
    Ib =mp.quad(lambda u:Phi(u)*mp.sin(x*u)*mp.sinh(y*u),[0,UP])
    Iby=mp.quad(lambda u:Phi(u)*u*mp.sin(x*u)*mp.cosh(y*u),[0,UP])
    return mp.mpc(Ia+Iay,Ib+Iby), mp.mpc(Ia-Iay,Ib-Iby)
print("Check identity R = |A|^2-|B|^2 == Re((A+B)*conj(A-B)):")
for (x,y) in [(5.0,0.3),(14.134725,0.5),(28.26945,0.2)]:
    A,B=Ls(x,y)
    R1=abs(A)**2-abs(B)**2
    R2=((A+B)*mp.conj(A-B)).real
    print(f"  (x={x},y={y}): R={mp.nstr(R1,8)}  Re((A+B)conj(A-B))={mp.nstr(R2,8)}  diff={mp.nstr(R1-R2,4)}")
print()
print("So R>=0  <=>  Re( (A+B) conj(A-B) ) >= 0.  (A+B),(A-B) are the two transforms.")
print("This is a HERMITIAN PAIRING sign, NOT separate positivity. Separate Laplace-")
print("positivity of A+B and A-B (each in its own half-plane) does NOT control the")
print("RELATIVE PHASE arg(A+B)-arg(A-B), which is what the pairing sign needs.")

print()
print("="*78)
print("Q2 — COUNTEREXAMPLE: two LT-of-positive-measure functions with NEGATIVE pairing")
print("="*78)
# Toy: f1(z)=LT of positive measure mu1, f2(z)=LT of positive measure mu2, both
# evaluated at complex z. Show Re(f1 conj f2) can be <0 => separate positivity
# does NOT imply the pairing sign. Use mu = sum of atoms (positive).
def LT(atoms, z):  # atoms = list of (mass>0, location>0): sum mass e^{-loc z}
    return sum(m*mp.e**(-loc*z) for m,loc in atoms)
mu1=[(1.0,0.5),(2.0,3.0)]   # positive measure
mu2=[(1.0,0.5),(2.0,3.0)]
# pick complex z where phases diverge
for z in [mp.mpc(0.2,4.0), mp.mpc(0.1,6.0), mp.mpc(0.05,8.0)]:
    f1=LT(mu1,z); f2=LT([(1.0,0.5),(0.5,4.0)],z)
    pair=(f1*mp.conj(f2)).real
    print(f"  z={z}: f1,f2 both LT of POSITIVE measures; Re(f1 conj f2)={mp.nstr(pair,6)} "
          f"{'<-- NEGATIVE: implication FAILS' if pair<0 else ''}")
print()
print("CONCLUSION Q2: 'A+B and A-B are each Laplace transforms of positive measures'")
print("does NOT imply Re((A+B)conj(A-B))>=0. The pairing/relative-phase is uncontrolled.")
print("So Laplace-order positivity is a RED HERRING for the dominance UNLESS it is the")
print("SAME measure controlling both — which collapses back to the Xi phase = the zeros.")
