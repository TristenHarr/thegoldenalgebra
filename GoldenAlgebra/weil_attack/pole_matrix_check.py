"""
Check: the MATRIX pole form POLE_kl = phihat_k(i/2)conj(phihat_l(i/2))? or 
phihat_k(i/2)*phihat_l(-i/2)? The correct bilinear from h_c(i/2)=phihat(i/2)conj_phihat(i/2):
For phi=sum c_k phi_k, phihat=sum c_k phihat_k. 
h_c(i/2)=(sum c_k phihat_k(i/2))(sum c_l conj_phihat_l(i/2)).
conj_phihat_l(i/2)=overline{phihat_l(-i/2)} = phihat_l(-i/2) for REAL coeffs basis (real).
So POLE bilinear M^P_kl = phihat_k(i/2)phihat_l(-i/2) + phihat_k(-i/2)phihat_l(i/2).
This is SYMMETRIC and = (e^{x_k/2}e^{-x_l/2}+e^{-x_k/2}e^{x_l/2}) * (2pi s^2 e^{s2/4})
= 2pi s^2 e^{s2/4}(e^{(x_k-x_l)/2}+e^{-(x_k-x_l)/2}) = 2pi s^2 e^{s2/4}*2cosh((x_k-x_l)/2).
THIS MATCHES my earlier matrix POLE (e^{d/2}+e^{-d/2}) form! So the MATRIX was RIGHT.
The single-vector full_Q_fixed used POLE=pe^2+pem^2 (=phihat(i/2)^2+phihat(-i/2)^2) which is
the DIAGONAL k=l of a DIFFERENT (wrong) form. For c=(1,-1): correct gives
 (phihat_1(i/2)-phihat_2(i/2))(phihat_1(-i/2)-phihat_2(-i/2))*2... let me just confirm
the MATRIX threshold form is the correct one by re-validating it on the antisym vector.
"""
import numpy as np
s=0.4; s2=s*s; SQ2PI=np.sqrt(2*np.pi)
centers=[0.5,-0.5]; C=np.array(centers); coeffs=np.array([1.0,-1.0])
# phihat_k(i/2)=SQ2PI s e^{s2/8} e^{x_k/2}
pe=SQ2PI*s*np.exp(s2/8)*np.exp(C/2)
pem=SQ2PI*s*np.exp(s2/8)*np.exp(-C/2)
# CORRECT bilinear: POLE_kl=pe_k pem_l + pem_k pe_l
POLE_correct=np.outer(pe,pem)+np.outer(pem,pe)
# WRONG (what full_Q used as diagonal): outer(pe,pe)+outer(pem,pem)
POLE_wrong=np.outer(pe,pe)+np.outer(pem,pem)
print("antisym c=(1,-1):")
print("  POLE correct (cosh form):", coeffs@POLE_correct@coeffs)
print("  POLE wrong (square form): ", coeffs@POLE_wrong@coeffs)
print("  => full_Q_fixed/single-vec used the WRONG square form, giving spurious +1.068.")
print("     The MATRIX scan (cone_threshold2) used cosh form = CORRECT.")
