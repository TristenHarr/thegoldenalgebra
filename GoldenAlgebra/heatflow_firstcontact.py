#!/usr/bin/env python3
"""
heatflow_firstcontact.py
========================
DECISIVE NUMERICAL EXPERIMENT for the heat-flow first-failure / Schur-contractivity
route to RH via the de Bruijn-Newman (dBN) flow.

Setup (matching ScratchHBDominance.lean and ScratchDeBranges.lean):

  Riemann Phi:   Phi(u) = sum_{n>=1} (2 pi^2 n^4 e^{9u} - 3 pi n^2 e^{5u}) exp(-pi n^2 e^{4u})
  Heat deform:   Phi_t(u) = e^{t u^2} Phi(u)      (t = heat time; t>=Lambda => all zeros real)

  Moment building blocks (from ScratchHBDominance, evaluated at probe (x,y), y>0):
     a(u)   = cos(x u) cosh(y u)        a_y(u) = u cos(x u) sinh(y u)   ( = d/dy a )
     b(u)   = sin(x u) sinh(y u)        b_y(u) = u sin(x u) cosh(y u)   ( = d/dy b )

  Phi_t-weighted moments (cutoff A):
     Ia  = int_0^A Phi_t a       Iay = int_0^A Phi_t a_y
     Ib  = int_0^A Phi_t b       Iby = int_0^A Phi_t b_y

  L1=Ia+Iay  L2=Ia-Iay  L3=Ib+Iby  L4=Ib-Iby
  A_t = L1 + i L3 ,  B_t = L2 + i L4
  ||A_t||^2 = L1^2+L3^2 ,  ||B_t||^2 = L2^2+L4^2

  U_t(x,y) = log ||A_t||^2 - log ||B_t||^2    ( >= 0  <=>  Schur contractivity |Theta_t|<=1 )

  d/dt of the weight e^{t u^2} pulls down a factor u^2:
     d/dt Phi_t = u^2 Phi_t,  so  d/dt Ia = (same moment with extra u^2 weight), etc.
  Hence dU/dt = (d/dt ||A||^2)/||A||^2 - (d/dt ||B||^2)/||B||^2 with
     d/dt ||A||^2 = 2 L1 (dL1) + 2 L3 (dL3),  dL1 = dIa+dIay, dL1 uses u^2-weighted moments.

THE DIAGNOSTIC: at near-contact points (U_t ~ 0, Schur boundary nearly touched),
is dU/dt > 0 (PROTECTIVE: flow pushes contractivity back inside) or sign-changing/0
(MARGINAL: the dBN Lambda<=0 wall)?

We also test forward (t up) vs backward (t down) orientation and probe an artificial
near-threshold extended region.
"""

import mpmath as mp

mp.mp.dps = 40   # high precision; Phi is super-exponentially decaying so integrals are tame

# ----------------------------------------------------------------------------
# Riemann Phi(u) and its u^2-weighted partner.
# Phi(u) = sum (2 pi^2 n^4 e^{9u} - 3 pi n^2 e^{5u}) exp(-pi n^2 e^{4u})
# super-exponential decay => few terms suffice; we sum until terms underflow.
# ----------------------------------------------------------------------------
def Phi(u):
    u = mp.mpf(u)
    e4u = mp.e**(4*u)
    e9u = mp.e**(9*u)
    e5u = mp.e**(5*u)
    total = mp.mpf(0)
    n = 1
    while True:
        n2 = mp.mpf(n*n)
        n4 = n2*n2
        term = (2*mp.pi**2*n4*e9u - 3*mp.pi*n2*e5u) * mp.e**(-mp.pi*n2*e4u)
        total += term
        # stop when the exponential damping has killed the term
        if mp.pi*n2*e4u > mp.mpf(80) and abs(term) < mp.mpf(10)**(-mp.mpf(45)):
            break
        n += 1
        if n > 2000:
            break
    return total

# ----------------------------------------------------------------------------
# Generic moment integral:  int_0^A  weight(u)*Phi(u)*g(x,y,u) du
# weight(u) = exp(t u^2) * u^(2k)   (k=0 for value, k=1 for d/dt).
# We integrate the FOUR building blocks together in one pass for efficiency.
# Returns (Ia, Iay, Ib, Iby) for a given extra power 2k of u.
# ----------------------------------------------------------------------------
def moments(t, A, x, y, kpow):
    """kpow = 0 -> value moments; kpow = 1 -> d/dt moments (extra u^2)."""
    t = mp.mpf(t); A = mp.mpf(A); x = mp.mpf(x); y = mp.mpf(y)
    def integrand(u):
        u = mp.mpf(u)
        w = mp.e**(t*u*u) * Phi(u)
        if kpow == 1:
            w = w * u * u
        cu = mp.cos(x*u); su = mp.sin(x*u)
        chu = mp.cosh(y*u); shu = mp.sinh(y*u)
        a   = cu*chu
        ay  = u*cu*shu
        b   = su*shu
        by  = u*su*chu
        return mp.matrix([w*a, w*ay, w*b, w*by])
    # mpmath quad over vector-valued: do componentwise (cheap, Phi computed 4x; acceptable)
    Ia  = mp.quad(lambda u: (mp.e**(t*u*u)*Phi(u)*(u*u if kpow else 1))*mp.cos(x*u)*mp.cosh(y*u), [0, A])
    Iay = mp.quad(lambda u: (mp.e**(t*u*u)*Phi(u)*(u*u if kpow else 1))*u*mp.cos(x*u)*mp.sinh(y*u), [0, A])
    Ib  = mp.quad(lambda u: (mp.e**(t*u*u)*Phi(u)*(u*u if kpow else 1))*mp.sin(x*u)*mp.sinh(y*u), [0, A])
    Iby = mp.quad(lambda u: (mp.e**(t*u*u)*Phi(u)*(u*u if kpow else 1))*u*mp.sin(x*u)*mp.cosh(y*u), [0, A])
    return Ia, Iay, Ib, Iby

def Ls(Ia, Iay, Ib, Iby):
    return (Ia+Iay, Ia-Iay, Ib+Iby, Ib-Iby)

def quantities(t, A, x, y):
    """Return dict with normsqA, normsqB, U, dUdt (analytic via u^2-weighted moments)."""
    Ia, Iay, Ib, Iby = moments(t, A, x, y, 0)
    L1, L2, L3, L4 = Ls(Ia, Iay, Ib, Iby)
    nA = L1*L1 + L3*L3
    nB = L2*L2 + L4*L4
    # d/dt moments
    dIa, dIay, dIb, dIby = moments(t, A, x, y, 1)
    dL1, dL2, dL3, dL4 = Ls(dIa, dIay, dIb, dIby)
    dnA = 2*L1*dL1 + 2*L3*dL3
    dnB = 2*L2*dL2 + 2*L4*dL4
    U = mp.log(nA) - mp.log(nB)
    dUdt = dnA/nA - dnB/nB
    return {
        'nA': nA, 'nB': nB, 'U': U, 'dUdt': dUdt,
        'L': (L1, L2, L3, L4), 'dnA': dnA, 'dnB': dnB,
    }

if __name__ == '__main__':
    print("# quick sanity: Phi sample values")
    for u in [0.0, 0.2, 0.5, 1.0, 1.5, 2.0]:
        print(f"Phi({u}) = {mp.nstr(Phi(u), 10)}")
