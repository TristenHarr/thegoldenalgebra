"""
SHARPER use of Phi's SPECIFIC theta structure for the contractivity R>=0.

Prior finding: generic Phi>=0 does NOT imply R = Im(Xi'(w)conjXi(w))>=0 in LHP;
counterexamples e^{-u}, u e^{-u}, e^{-u}(1+cos3u)/2 are positive measures with R<0.

What do those counterexamples LACK that the Riemann Phi HAS?  The Riemann Phi
satisfies the THETA FUNCTIONAL EQUATION reflected as the self-duality
    Phi(u) = Phi(-u)   (the even theta kernel)  AND the deeper
    Phi(u) ~ even, with cosine transform Xi(t) satisfying Xi(t)=Xi(-t) and the
    Riemann functional equation Xi(t)=Xi(\bar t)... i.e. Xi is REAL ENTIRE of ORDER 1.

The decisive SHARP structural property the toy examples fail:
  (S1) Xi is an entire function of ORDER 1 (genus 1), REAL on R, EVEN.
  (S2) Phi(u) = 4 sum (2 pi^2 n^4 e^{9u/2}-3 pi n^2 e^{5u/2}) e^{-pi n^2 e^{2u}} and
       crucially Phi(u)=Phi(-u): the theta functional equation theta(1/t)=sqrt t theta(t).

TEST: does the theta SELF-DUALITY Phi(u)=Phi(-u) (which the toy positive measures
violate -- they live on [0,inf) only) by itself force R>=0?  I.e. is
'positive measure SYMMETRIC about 0 with order-1 cosine transform' enough?

We test SYMMETRIC positive measures and see if R>=0 is forced, or if even symmetry
+ positivity still fails (isolating that ORDER-1 / real-zeros is the real content).
"""
import mpmath as mp
import numpy as np
mp.mp.dps = 20

# R(w) = Im(Cp(w) conj C(w)) with C(w)=int_{-inf}^{inf} Phi(u) e^{i w u} du /?
# For an EVEN measure mu (symmetric about 0), C(w)=int Phi(u)cos(wu)du is its FT.
# We test min over LHP of R = Im(C'(w) conj C(w)).
def minR(Phifun, supp, UP2=8.0):
    if supp=='half':
        def Cc(w): return mp.quad(lambda u:Phifun(u)*mp.cos(w*u),[0,UP2])
        def Cpp(w):return mp.quad(lambda u:-Phifun(u)*u*mp.sin(w*u),[0,UP2])
    else: # symmetric: integrate -UP2..UP2, Phifun even
        def Cc(w): return mp.quad(lambda u:Phifun(u)*mp.cos(w*u),[-UP2,UP2])
        def Cpp(w):return mp.quad(lambda u:-Phifun(u)*u*mp.sin(w*u),[-UP2,UP2])
    m=1e18; arg=None
    for x in np.linspace(0.2,40,50):
        for y in np.linspace(0.05,3,25):
            w=mp.mpc(float(x),-float(y)); v=float((Cpp(w)*mp.conj(Cc(w))).imag)
            if v<m: m=v; arg=(x,y)
    return m,arg

print("="*80)
print("Does EVEN (symmetric-about-0) positivity force R>=0?  Toy SYMMETRIC pos measures:")
print("="*80)
tests = [
    (lambda u: mp.e**(-u*u),       'sym', 'gaussian e^-u^2 (order2, real zeros)'),
    (lambda u: mp.e**(-abs(u)),    'sym', 'sym Laplace e^-|u| (order1, FT=2/(1+w^2) real zeros? )'),
    (lambda u: 1/mp.cosh(u),       'sym', 'sech u (FT = sech, real zeros)'),
    (lambda u: mp.e**(-u*u)*(1+0.5*mp.cos(3*u)), 'sym', 'sym gaussian*(1+.5cos3u) pos? order2'),
    (lambda u: mp.e**(-u*u)*(2+mp.cos(5*u)),     'sym', 'sym gaussian*(2+cos5u) POS, may have complex zeros'),
]
for f,supp,nm in tests:
    m,arg=minR(f,supp)
    verdict = 'R>=0 (consistent w/ real zeros)' if m>-1e-7 else f'R<0 at {arg} => NOT forced'
    print(f"  {nm:>42}: minR={m:.4e}  {verdict}")

print()
print("="*80)
print("KEY: even-symmetry+positivity does NOT force R>=0 either (if the FT acquires")
print("complex zeros). The ONLY thing forcing R>=0 is the cosine transform having")
print("REAL zeros = Laguerre-Polya membership. Phi's theta structure gives order 1 and")
print("the FE, but NOT real zeros without RH. We now check: is Phi's COSINE TRANSFORM")
print("forced into Laguerre-Polya by any FINITE theta data? (the moment/Hamburger test)")
print("="*80)
print("Laguerre-Polya <=> the Hankel matrices of the TAYLOR coeffs of Xi at 0 obey the")
print("Hamburger/Hurwitz sign pattern (Newton inequalities a_k^2>=a_{k-1}a_{k+1}*r).")
print("Test Newton inequalities on Xi(t)=sum b_k t^{2k} (real-zero NECESSARY conditions):")

def phi_term(u,n):
    npi=mp.pi*n*n
    return (2*npi*npi*mp.e**(9*u)-3*npi*mp.e**(5*u))*mp.e**(-npi*mp.e**(4*u))
def Phi(u,N=26): return mp.fsum(phi_term(u,n) for n in range(1,N+1))
# Xi(t)=2 int_0^inf Phi(u) cos(tu) du. Taylor: Xi(t)=sum (-1)^k m_{2k}/(2k)! t^{2k},
# m_{2k}=2 int Phi(u) u^{2k} du.
def moment(k): return 2*mp.quad(lambda u:Phi(u)*u**(2*k),[0,6.0])
b=[(-1)**k*moment(k)/mp.factorial(2*k) for k in range(0,8)]
print("\nXi Taylor coeffs b_k (Xi=sum b_k t^{2k}):")
for k,bb in enumerate(b): print(f"  b[{k}]={mp.nstr(bb,8)}")
print("\nLaguerre-Polya NECESSARY (Newton/Turan) for an EVEN real-zero entire fn g(t)=Xi:")
print("write g(t)=sum a_k t^k with a_{2k}=b_k, a_odd=0; LP needs a_k^2 >= a_{k-1}a_{k+1}*(...)")
print("For even fn, the relevant test is on the b_k via the LP closure (all b_k same-ish")
print("sign with log-concavity).  Turan: b_k^2 - b_{k-1}b_{k+1} >= 0  (necessary for LP):")
for k in range(1,len(b)-1):
    t=b[k]**2-b[k-1]*b[k+1]
    print(f"  k={k}: b_k^2-b_(k-1)b_(k+1) = {mp.nstr(t,6)}  {'>=0 ok' if t>=-1e-12 else '<0 VIOLATES LP-necessary'}")
print("\n(If these hold it's NECESSARY-only; they DON'T certify LP/real-zeros -- a")
print(" function can pass all finite Turan/Newton tests and still have complex zeros.")
print(" That gap is exactly the unconditional wall.)")
