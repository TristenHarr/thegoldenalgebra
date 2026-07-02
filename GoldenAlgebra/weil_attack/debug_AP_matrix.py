"""
Debug: does the matrix ARCH+POLE form agree with the VALIDATED single-vector computation?
Take phi = c1 phi_1 + c2 phi_2, gaussians at x1,x2. Compute (ARCH+POLE)(phi):
 (a) via matrix: c^T (A+POLE) c with my closed forms.
 (b) via direct single-vector (the form validated to 1e-21 against zero-sum in pole_fix logic
     EXCEPT pole_fix used the SQUARE pole; here use the CORRECT continuation product pole).
Then check which POLE bilinear actually reproduces the zero-sum for a 2-term vector.
"""
import numpy as np, mpmath as mp
mp.mp.dps=28
SQ2PI=mp.sqrt(2*mp.pi)
def Omega(r): return mp.re(mp.digamma(mp.mpf(1)/4+1j*r/2))-mp.log(mp.pi)
s=mp.mpf('0.30'); s2=s*s
x=[mp.mpf('0.2'),mp.mpf('-0.15')]; c=[mp.mpf('1.0'),mp.mpf('0.7')]
def phihat(w):
    return sum(ck*SQ2PI*s*mp.e**(-s2*w*w/2)*mp.e**(-1j*w*xk) for ck,xk in zip(c,x))
def h(r): return phihat(r)*mp.conj(phihat(r))   # |phihat|^2 on real axis
# direct ARCH
ARCH_direct=mp.quad(lambda r: mp.re(h(r))*Omega(r),[-mp.inf,0,mp.inf])/(2*mp.pi)
# direct POLE = h_c(i/2)+h_c(-i/2), h_c(w)=phihat(w)*overline{phihat(overline w)}
def conjbar_phihat(w): return mp.conj(phihat(mp.conj(w)))
def hc(w): return phihat(w)*conjbar_phihat(w)
POLE_direct=mp.re(hc(1j*mp.mpf(1)/2)+hc(-1j*mp.mpf(1)/2))
# matrix forms
def Dij(i,j): return x[i]-x[j]
A_mat=mp.mpf(0); POLE_mat_cosh=mp.mpf(0); POLE_mat_sq=mp.mpf(0)
for i in range(2):
    for j in range(2):
        d=Dij(i,j)
        Aij=s2*mp.quad(lambda r: mp.e**(-s2*r*r)*mp.cos(r*d)*Omega(r),[-mp.inf,0,mp.inf])
        A_mat+=c[i]*c[j]*Aij
        POLE_mat_cosh+=c[i]*c[j]*2*mp.pi*s2*mp.e**(s2/4)*(mp.e**(d/2)+mp.e**(-d/2))
        # square form bilinear: pe_i pe_j + pem_i pem_j
        pei=SQ2PI*s*mp.e**(s2/8)*mp.e**(x[i]/2); pej=SQ2PI*s*mp.e**(s2/8)*mp.e**(x[j]/2)
        pemi=SQ2PI*s*mp.e**(s2/8)*mp.e**(-x[i]/2); pemj=SQ2PI*s*mp.e**(s2/8)*mp.e**(-x[j]/2)
        POLE_mat_sq+=c[i]*c[j]*(pei*pej+pemi*pemj)
print("ARCH direct  =",mp.nstr(ARCH_direct,12),"  ARCH matrix =",mp.nstr(A_mat,12))
print("POLE direct  =",mp.nstr(POLE_direct,12))
print("POLE cosh-mat=",mp.nstr(POLE_mat_cosh,12))
print("POLE sq-mat  =",mp.nstr(POLE_mat_sq,12))
print()
# which matches direct?
print("cosh matches direct?", mp.nstr(POLE_mat_cosh-POLE_direct,6))
print("sq matches direct?  ", mp.nstr(POLE_mat_sq-POLE_direct,6))
