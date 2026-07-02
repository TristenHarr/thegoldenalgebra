"""
Three "hidden structure" probes for the HB dominance  ‖B_Φ‖ ≤ ‖A_Φ‖
matched to ScratchHBDominance.lean:
  a(w)=cos(xw)cosh(yw)   a_y(w)=w cos(xw)sinh(yw)
  b(w)=sin(xw)sinh(yw)   b_y(w)=w sin(xw)cosh(yw)
  L1=∫Φ(a+a_y) L2=∫Φ(a-a_y) L3=∫Φ(b+b_y) L4=∫Φ(b-b_y)
  A=L1+iL3   B=L2+iL4
  R = |A|²-|B|² = L1²+L3²-L2²-L4²   (energy positivity target; want R>=0 for y>0)

Probe 1 SCHUR:  Theta = B/A; test |Theta|<=1 and 1-|Theta| behavior near zero ordinates.
Probe 2 THETA-SOS:  Phi=sum_n phi_n; R = sum_{m,n} c_m c_n K_mn; is K_mn PSD on the
   theta coefficient structure (all c_n=1) / after n<->1/n pairing?  Eigenvalues of K.
Probe 3 LAPLACE-ORDER: are A+B and A-B completely monotone / Laplace transforms of
   positive measures (substitution r=e^{2t})? Test sign of derivatives.
"""
import mpmath as mp
mp.mp.dps = 18

# Riemann Phi and its per-n term phi_n (the theta summand)
def phi_term(u, n):
    npi = mp.pi * n*n
    return (2*npi*npi*mp.e**(9*u) - 3*npi*mp.e**(5*u)) * mp.e**(-npi*mp.e**(4*u))

def Phi(u, N=12):
    return mp.fsum(phi_term(u, n) for n in range(1, N+1))

# moment integrands
def a_(x,y,w):  return mp.cos(x*w)*mp.cosh(y*w)
def ay_(x,y,w): return w*mp.cos(x*w)*mp.sinh(y*w)
def b_(x,y,w):  return mp.sin(x*w)*mp.sinh(y*w)
def by_(x,y,w): return w*mp.sin(x*w)*mp.cosh(y*w)

UP = 6.0  # integration cutoff in u (Phi decays super-exponentially; tiny beyond ~3)

def Ls(x,y,phifun=Phi):
    Ia  = mp.quad(lambda u: phifun(u)*a_(x,y,u),  [0,UP])
    Iay = mp.quad(lambda u: phifun(u)*ay_(x,y,u), [0,UP])
    Ib  = mp.quad(lambda u: phifun(u)*b_(x,y,u),  [0,UP])
    Iby = mp.quad(lambda u: phifun(u)*by_(x,y,u), [0,UP])
    L1=Ia+Iay; L2=Ia-Iay; L3=Ib+Iby; L4=Ib-Iby
    return L1,L2,L3,L4

def AB(x,y,phifun=Phi):
    L1,L2,L3,L4 = Ls(x,y,phifun)
    A = mp.mpc(L1,L3); B = mp.mpc(L2,L4)
    return A,B,(L1,L2,L3,L4)

print("="*70)
print("PROBE 1 — SCHUR:  Theta=B/A,  test |Theta|<=1 and margin 1-|Theta|")
print("="*70)
# first zero ordinate of Xi is t1=14.1347; off-line probes (x near 0) approaching real axis
print("Approach to REAL AXIS at fixed x (small y -> 0):")
for x in [0.0, 14.134725, 21.022040]:
    print(f"  x={x}:")
    for y in [2.0, 1.0, 0.5, 0.2, 0.05, 0.01]:
        A,B,_ = AB(x,y)
        if abs(A)==0:
            print(f"    y={y}: A=0"); continue
        th = abs(B/A)
        print(f"    y={y:<5}: |Theta|={mp.nstr(th,8):<12} margin 1-|Theta|={mp.nstr(1-th,6)}")
print()
print("NOTE: B/A is the de Branges Theta-like ratio. If |Theta|->1 only AT zero")
print("ordinates as y->0 (margin->0 there, >0 elsewhere) it's boundary-Schur = RH-tight.")

print()
print("="*70)
print("PROBE 2 — THETA-SOS:  R=|A|²-|B|² = sum_{m,n} c_m c_n K_mn ; PSD of K_mn?")
print("="*70)
# R is BILINEAR in Phi (since L's are linear in Phi). With Phi=sum phi_n,
# R(x,y) = sum_{m,n} K_mn(x,y) where K_mn uses phi_m in one L-factor, phi_n in other.
# Build K_mn = (1/?) symmetric form: R = L1²+L3²-L2²-L4², each L = sum_n L^{(n)}.
# So R = sum_{m,n} [ L1^m L1^n + L3^m L3^n - L2^m L2^n - L4^m L4^n ] =: sum K_mn.
def Lvec_n(x,y,n):
    pf = lambda u: phi_term(u,n)
    return Ls(x,y,pf)  # (L1,L2,L3,L4) contributed by phi_n alone

import numpy as np
for (x,y) in [(0.0,1.0),(0.0,0.3),(14.134725,0.3)]:
    N=6
    Ln = [Lvec_n(x,y,n) for n in range(1,N+1)]  # list of (L1,L2,L3,L4)
    K = np.zeros((N,N))
    for i in range(N):
        for j in range(N):
            L1i,L2i,L3i,L4i = Ln[i]; L1j,L2j,L3j,L4j = Ln[j]
            K[i,j] = float(L1i*L1j + L3i*L3j - L2i*L2j - L4i*L4j)
    Ks = 0.5*(K+K.T)
    ev = np.linalg.eigvalsh(Ks)
    ones = np.ones(N)
    Rtot = ones@Ks@ones   # R with all coeffs =1 (true Phi truncated)
    print(f"  (x={x}, y={y}): R(all c=1)={Rtot:.6e}  K eigenvalues={np.array2string(ev, precision=3)}")
    print(f"       #pos={sum(ev>1e-12)}, #neg={sum(ev<-1e-12)}  => {'PSD' if all(ev>-1e-9) else 'INDEFINITE'}")
print()
print("NOTE: continuous kernel was signature ++-- (indefinite). Question: is the")
print("theta-DISCRETIZED K_mn PSD (then R>=0 free), or still indefinite (RH wall)?")

print()
print("="*70)
print("PROBE 3 — LAPLACE-ORDER: are A+B, A-B Laplace transforms of POSITIVE measures?")
print("="*70)
# A+B = (L1+L2)+i(L3+L4) = 2Ia + i 2Ib ; A-B = 2Iay + i 2Iby.
# Real-axis (y=0): Ib=Iby=0, so A,B real. A+B|_{y=0}=2Ia=2∫Φcos(xw)=Xi(x), A-B=2Iay=0.
# The 'order' question: treat t with r=e^{2t}; test complete monotonicity of
# g(s)=∫Φ(u)e^{-s u}du in s>0 (one-sided Laplace of Phi). CM <=> all (-1)^k g^{(k)}>=0.
def gLap(s):  # ∫_0^UP Phi(u) e^{-s u} du
    return mp.quad(lambda u: Phi(u)*mp.e**(-s*u), [0,UP])
# g^{(k)}(s) = ∫ Φ(u) (-u)^k e^{-su} du  (differentiate under integral, exact, no finite diff)
def gLapDeriv(s,k):
    return mp.quad(lambda u: Phi(u)*((-u)**k)*mp.e**(-s*u), [0,UP])
print("One-sided Laplace g(s)=∫Φ e^{-su}du and signs of derivatives (CM test):")
for s in [0.5,1.0,2.0,4.0]:
    g0=gLapDeriv(s,0); g1=gLapDeriv(s,1); g2=gLapDeriv(s,2); g3=gLapDeriv(s,3)
    print(f"  s={s}: g={mp.nstr(g0,5)} g'={mp.nstr(g1,5)} g''={mp.nstr(g2,5)} g'''={mp.nstr(g3,5)}")
print("CM requires (-1)^k g^{(k)} >= 0 for all k (i.e. g,g'',..>=0 and g',g'''<=0).")
print("Phi itself changes sign (theta has the 2π²n⁴ - 3πn² structure), so the")
print("amplitude is NOT a positive measure; report whether g is still CM (Bernstein).")
