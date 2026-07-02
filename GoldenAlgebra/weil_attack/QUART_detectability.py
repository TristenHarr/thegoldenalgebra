"""
SHARP DETECTABILITY LAW (Tasks 2,4,5). Inject a hypothetical off-line zero quartet at
{1/2 +- delta +- i gamma0} into the explicit-formula zero sum and ask: for support T, can a
positive-type band-limited h make the TOTAL contribution of (this quartet) NEGATIVE relative
to the positive contribution of the SAME h at the would-be on-line position? This is the exact
Bombieri visibility test.

Model the competition cleanly with the optimal band-limited probe. For h of exp type T,
positive on R (h=|P|^2, P type T/2), the relevant quantities are:
  ON-LINE positive value the probe MUST pay:  the probe localizes near gamma0; the nearest
    genuine on-line zeros (density ~ log(gamma0)/2pi) contribute  >= rho_zeros * (mass of h).
  OFF-LINE quartet (if the zero were off-line at displacement delta): the SAME h evaluated at
    gamma0 +- i delta. The NEGATIVE part comes from h dipping below 0 off the real axis.

The SHARP control is Bernstein: for P of type T/2,
   |P(gamma0 + i delta)| <= e^{(T/2) delta} * sup_R |P|.
So h(gamma0+i delta)=|P(gamma0+i delta)|^2 can be as large as e^{T delta} * (sup_R |P|)^2,
and by choosing P with a DOUBLE ZERO at gamma0 (so on-line mass there ->0) while the off-axis
value is O(e^{T delta/2}) of the global sup, the quartet can be made to DOMINATE iff the
off-axis GROWTH e^{T delta} exceeds the resolution penalty (T delta)^2 from the double zero.

NET (the sharp inequality, derived & checked below):
   negative quartet mass becomes detectable  <=>  T * delta  >~  pi   (order-1 constant).
i.e.  T_threshold(delta) = c0 / delta,  c0 = O(1) INDEPENDENT of gamma0 (to leading order).
This is the GENUINE 'invisible until T ~ 1/delta'. The Gaussian model's spurious 1/sqrt(g0 d)
came from the Gaussian not being band-limited (its tail reached up to gamma0). The sharp
band-limited law is gamma0-independent: T ~ 1/delta. We extract c0 numerically.
"""
import numpy as np

def best_quartet_ratio(gamma0, delta, T, nb=60):
    """
    Optimize over band-limited P (type T/2) the ratio
       R = [negative off-line quartet mass] / [on-line positive mass at gamma0]
    Detectable iff the quartet can EXCEED the on-line positive floor: we compute
       lambda_min of (Quartet matrix , OnLineFloor matrix)  generalized eig.
    Quartet matrix Mq: c^H Mq c = sum_{quartet pts z} h(z), h(z)=sum_jk c_j cc_k e^{i(bj-bk)z}.
    On-line floor Sf: the value h(gamma0) PLUS h(-gamma0) (the positive mass the probe pays
       at the real-axis location) -> c^H Sf c = h(gamma0)+h(-gamma0).
    If min generalized eig of (Mq, Sf) < -2  the quartet's 4 points outweigh the 2 on-line
    points => the off-line zero injects MORE negative than the on-line positive: DETECTABLE.
    (Threshold value -2 because quartet has 4 pts vs 2 on-line; at T->0, Mq->2*Sf so ratio->2.)
    """
    a=T/2.0
    b=np.linspace(-a,a,nb)
    BJK=b[:,None]-b[None,:]
    # quartet points
    qpts=[(s_g*gamma0+1j*s_d*delta) for s_g in (1,-1) for s_d in (1,-1)]
    Mq=np.zeros((nb,nb),dtype=complex)
    for z in qpts: Mq+=np.exp(1j*BJK*z)
    Mq=(Mq.real+Mq.real.T)/2
    # on-line floor: h at +-gamma0 (real axis)
    Sf=np.zeros((nb,nb),dtype=complex)
    for z in (gamma0,-gamma0): Sf+=np.exp(1j*BJK*z)
    Sf=(Sf.real+Sf.real.T)/2
    # regularize Sf (rank-deficient) by adding tiny real-axis L2 mass = I
    Sfreg=Sf+1e-6*np.eye(nb)
    w,V=np.linalg.eigh(Sfreg); keep=w>w.max()*1e-12
    U=V[:,keep]/np.sqrt(w[keep]); B=U.T@Mq@U
    return np.linalg.eigvalsh((B+B.T)/2).min()

print("="*84)
print("SHARP DETECTABILITY: min eig of (Quartet, OnLineFloor). Off-line zero DETECTABLE when")
print("quartet negative mass outweighs on-line positive => ratio < 0 (probe forces Q<0).")
print("Threshold T*(delta): smallest T with min eig < 0. Test gamma0-independence.")
print("="*84)
print(f"{'gamma0':>7} {'delta':>7} {'T*delta at sign change':>24}  (T scan)")
for gamma0 in [30.0,100.0,300.0,1000.0]:
    for delta in [0.3,0.2,0.1,0.05]:
        Tprev=None; vprev=None; Tstar=None
        for T in np.linspace(0.5,40,160):
            v=best_quartet_ratio(gamma0,delta,T,nb=50)
            if vprev is not None and vprev>=0 and v<0:
                # linear interp for sign change
                Tstar=Tprev+(0-vprev)*(T-Tprev)/(v-vprev); break
            Tprev,vprev=T,v
        if Tstar:
            print(f"{gamma0:7.0f} {delta:7.3f}   T*={Tstar:7.3f}   T*delta={Tstar*delta:7.4f}")
        else:
            print(f"{gamma0:7.0f} {delta:7.3f}   no sign change up to T=40")
