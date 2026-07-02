"""
TASK 3: per-prime LOCAL positivity (Weil-Barner / Burnol local factors).
The Weil explicit formula sums LOCAL distributions W_v over places v:
   Q(g) = W_inf(g) + sum_p W_p(g)
W_p(g) = - sum_{k>=1} (log p) p^{-k/2} [ g(k log p) + g(-k log p) ]   (for g even: 2 g(k log p))
For g=phi*phi~ (positive type), is EACH W_p(g) >= 0 ? If yes, and W_inf>=0 (Connes),
then Q>=0 GLOBALLY -- which would be RH. So at least ONE must fail. WHICH?

W_p as a quadratic form in phi:  W_p(phi*phi~) = -2 sum_k (log p) p^{-k/2} (phi*phi~)(k log p).
(phi*phi~)(a) = <phi, S_a phi> (S_a = shift by a). In freq: = (1/2pi)\int |phihat(r)|^2 e^{i r a} dr.
So W_p(phi*phi~) = -(log p)/pi \int |phihat(r)|^2 [ sum_k p^{-k/2} cos(r k log p) ] dr.
Inner bracket  B_p(r) = sum_{k>=1} p^{-k/2} cos(k r log p) = Re( 1/(p^{1/2} e^{-i r log p} -1) )... 
  = Re( sqrt(p) e^{i r log p}... ) compute: sum_k z^k = z/(1-z), z=p^{-1/2}e^{i r log p}.
  Re(z/(1-z)). 
So W_p(phi) = -(log p)/pi \int |phihat(r)|^2 Re(z/(1-z)) dr,  z=p^{-1/2}e^{i r log p}.
LOCAL POSITIVITY of -W_p as a form requires Re(z/(1-z)) <= 0 for all r. Check its sign.
"""
import numpy as np
def Bp(p, r):
    z=p**(-0.5)*np.exp(1j*r*np.log(p))
    return np.real(z/(1-z))
print("Sign of B_p(r)=Re(z/(1-z)), z=p^{-1/2}e^{irlog p}. If B_p>=0 for all r => -W_p<=0 (BAD,")
print("prime form NEGATIVE definite, good for being dominated). If B_p changes sign => W_p indefinite.")
print()
for p in [2,3,5,7]:
    rs=np.linspace(0,4*np.pi/np.log(p),400)
    vals=np.array([Bp(p,r) for r in rs])
    print(f"p={p}: B_p range [{vals.min():+.4f}, {vals.max():+.4f}]  -> {'SIGN-CHANGES (indefinite)' if vals.min()<0<vals.max() else ('all>=0' if vals.min()>=0 else 'all<=0')}")
print()
# The MAX of B_p occurs at r log p = 0 (mod 2pi): z=p^{-1/2}, z/(1-z)=p^{-1/2}/(1-p^{-1/2})>0.
# The MIN at r log p = pi: z=-p^{-1/2}, z/(1-z)=-p^{-1/2}/(1+p^{-1/2})<0.
for p in [2,3,5,7,1009]:
    s=p**-0.5
    bmax=s/(1-s); bmin=-s/(1+s)
    print(f"p={p}: B_p max={bmax:+.5f} (at r log p=0), min={bmin:+.5f} (at r log p=pi). product<0 => INDEFINITE")
print()
print("CONCLUSION: each prime's local form W_p is INDEFINITE (B_p changes sign).")
print("So local positivity FAILS at every prime; no per-place positivity to multiply.")
print("Multiplicativity gives Q=W_inf+sum_p W_p (ADDITIVE in log, not a product of >=0 factors).")
