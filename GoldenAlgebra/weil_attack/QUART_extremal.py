"""
THE SHARP THRESHOLD via the Bernstein extremal problem.
=======================================================
We want: among positive-type h of exponential type T (h>=0 on R, h=|phihat|^2 with phihat
of type T/2), how NEGATIVE can the quartet mass
   N(h) = h(gamma0+i d)+h(gamma0-i d)+h(-gamma0+i d)+h(-gamma0-i d)
be, RELATIVE to the total Q-budget the rest of the form provides? The honest comparison
(Bombieri): an off-line zero is "visible" iff there is a positive-type h of type T with
   N(h) < 0   while keeping h>=0 on R and h normalized.
Because h>=0 on R, write phihat(r)=P(r) (type T/2), h=|P|^2. Then
   h(gamma0 + i d) = P(gamma0+i d) * conj(P(gamma0 - i d))   [since conj(P)(z)=conj(P(conj z)) for
   real-coeff P].  Re of the quartet =  2 Re[ P(gamma0+id) conj(P(gamma0-id)) ]
                                       + 2 Re[ P(-gamma0+id) conj(P(-gamma0-id)) ].
Let P be type T/2 (so a=T/2). Parametrize P(r) = sum_k c_k e^{i b_k r}, |b_k|<=T/2 (exp type),
real c_k for real-on-R-... actually P need not be real; |P|^2>=0 automatically. We optimize
the RATIO  N(P) / ||P||_R^2  (Rayleigh) where ||P||_R^2 ~ on-line positive contribution scale.

DISCRETE realization: P(r)=sum_k c_k e^{i b_k r} with b_k uniformly in [-T/2,T/2]. Then
   h(z)=|P|^2 -> h(z)=P(z) Pbar(z), Pbar(z)=sum_k conj(c_k) e^{-i b_k z} (the function whose
   values on R are conj). h(gamma0+id)=P(gamma0+id) Pbar(gamma0+id).
We MINIMIZE  Re N(c) subject to ||c||=1 weighting (proxy for real-axis mass). This is a
generalized eigenvalue problem  min_c  c^H M c / c^H S c, M from quartet, S=real-axis Gram.
The MIN eigenvalue's sign tells us whether a NEGATIVE-mass band-limited h exists at type T.
Threshold T*(delta,gamma0) = smallest T with min eigenvalue < 0.
"""
import numpy as np

def threshold_for(gamma0, delta, T, nb=40):
    a = T/2.0
    b = np.linspace(-a, a, nb)            # frequencies (type a = T/2)
    # h(z) = sum_{j,k} c_j conj(c_k) e^{i(b_j) z} e^{-i b_k * z}? careful:
    # P(z)=sum_j c_j e^{i b_j z};  Pbar(z)=sum_k conj(c_k) e^{-i b_k z}
    # h(z)=P(z)Pbar(z)=sum_{j,k} c_j conj(c_k) e^{i(b_j-b_k) z}
    # quartet pts z in {sg*gamma0 + i*sd*delta}, sg,sd in {+,-}
    pts = [(s_g*gamma0 + 1j*s_d*delta) for s_g in (1,-1) for s_d in (1,-1)]
    # M[j,k] = sum_pts e^{i(b_j-b_k) z}   (so N = c^H? we want sum_{j,k} c_j conj(c_k) M_jk
    #   = c^H M c with M_jk = sum_pts e^{i(b_j-b_k)z}, and we take Re)
    BJK = b[:,None]-b[None,:]
    M = np.zeros((nb,nb), dtype=complex)
    for z in pts:
        M += np.exp(1j*BJK*z)
    M = M.real  # quartet is symmetric in +-delta and +-gamma0 -> real
    M = (M+M.T)/2
    # real-axis Gram S: ||h||? We normalize by the ON-LINE positive contribution.
    # Use S_jk = integral over real-axis "near gamma0" of e^{i(b_j-b_k)r}? Simplest:
    # use the L2(R) inner product weight = the on-line zero contribution proxy = value of h
    # AT the would-be on-line position h(gamma0). h(gamma0)=sum c_j conj(c_k) e^{i(b_j-b_k)gamma0}.
    # That is rank-1; instead use total real-axis mass ||P||_{L2}^2 = sum|c_j|^2 (orthonormal-ish
    # exponentials) -> S = I.  Then min eigenvalue of M = most negative quartet mass at unit norm.
    ev = np.linalg.eigvalsh(M)
    return ev.min()

print("="*86)
print("MIN quartet mass min_{||P||=1} Re N over band-limited P of type T/2.")
print("Negative => a positive-type test fn of support T CAN give the off-line zero negative")
print("mass in Q (i.e. the zero is 'visible'). Threshold T*: smallest T with min<0.")
print("="*86)
print(f"{'gamma0':>7} {'delta':>7} | min quartet mass at T = ...")
header = "      ".join(f"{T:.2f}" for T in [0.693,1,2,3,4,6,8,12,16,24])
print(f"{'':>16}   {header}")
for gamma0 in [10.0, 50.0, 100.0, 1000.0]:
    for delta in [0.2, 0.1, 0.05, 0.01]:
        row=[]
        for T in [0.693,1,2,3,4,6,8,12,16,24]:
            nb=max(8,int(6*T)+4)
            row.append(threshold_for(gamma0,delta,T,nb))
        s="  ".join(f"{v:+8.3f}" for v in row)
        print(f"{gamma0:7.0f} {delta:7.3f} | {s}")
