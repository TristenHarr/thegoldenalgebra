"""
CONSTRAINED YOSHIDA CONE ENGINE.

Goal: enlarge the unconditional Weil-positive cone past support radius log2 by
NEUTRALIZING the n=2 negative mode with linear constraints (NOT by deleting support).

The Weil quadratic form on positive-type g=phi*phi~, basis phi=sum c_k G_s(.-x_k):
  Q = ARCH + POLE - PRIME   (=sum_rho |phihat(gamma)|^2; Q>=0 forall pos-type g <=> RH)

VERIFIED kernel (matches zero-sum to ~1e-21, explicit formula to ~1e-29; see
full_Q_fixed.py / pole_fix.py / calibrate.py). Basis Gaussian width s, center x_k:
  phihat_k(r) = sqrt(2pi) s e^{-s^2 r^2/2} e^{-i r x_k}.
With d = x_i - x_j:
  ARCH_ij = (1/2pi) * 2pi s^2 e^{...}  -> we use the validated assembled entry:
            ARCH_ij = s^2 * integral_R e^{-s^2 r^2} cos(r d) Omega(r) dr           (Omega=Re psi(1/4+ir/2)-log pi)
            (this equals (1/2pi)int h Omega with h=phihat_i conj phihat_j, the cross term)
  POLE_ij = 2pi s^2 e^{s^2/4} (e^{d/2}+e^{-d/2})
  PRIME_ij= 2 sum_{n>=2} Lambda(n) n^{-1/2} * s^2 (sqrt(pi)/(2s)) (e^{-(d-u)^2/4s^2}+e^{-(d+u)^2/4s^2}),  u=log n
  G_ij    = sqrt(pi) s e^{-d^2/4s^2}                                              (Gram = <phi_i,phi_j>=g_ij(0))

A constraint "L(phi)=0" is linear in coeffs c: L = sum_k c_k l_k = l . c = 0.
The constrained cone is {c : A c = 0} intersect basis-span. We project Q,G onto ker(A)
and compute the minimal GENERALIZED eigenvalue min_c (c'Q c)/(c'G c) over that subspace.
If >=0 for all T in (log2,log3) (and beyond), the cone is UNCONDITIONALLY positive past log2.

CRUCIAL: Q here is built from ARCH+POLE-PRIME DIRECTLY (the arithmetic side), never the
zero-sum. So a >=0 result is genuinely unconditional, not circular.
"""
import numpy as np, mpmath as mp

# ---- Omega table (archimedean kernel) ----
def Omega(r): return float(mp.re(mp.digamma(0.25 + 1j*r/2)) - mp.log(mp.pi))
RG = np.linspace(-400, 400, 200001)
DR = RG[1]-RG[0]
OM = np.array([Omega(r) for r in RG])

def vonmangoldt(N):
    out = {}
    for n in range(2, N+1):
        mm=n; fac={}; d=2
        while d*d<=mm:
            while mm%d==0: fac[d]=fac.get(d,0)+1; mm//=d
            d+=1
        if mm>1: fac[mm]=fac.get(mm,0)+1
        if len(fac)==1: out[n]=np.log(list(fac.keys())[0])
    return out
PL = vonmangoldt(200000)

def build_QG(centers, s, prime_cap=None):
    """Return (Q, G) matrices. prime_cap: only include primes n<=prime_cap (None=all up to support)."""
    C = np.asarray(centers, float); n=len(C); s2=s*s
    D = C[:,None]-C[None,:]
    # ARCH
    A = np.zeros((n,n)); base = s2*np.exp(-s2*RG**2)*OM
    for i in range(n):
        for j in range(i,n):
            v = np.trapz(base*np.cos(RG*D[i,j]), RG)
            A[i,j]=v; A[j,i]=v
    # POLE (cosh bilinear)
    POLE = 2*np.pi*s2*np.exp(s2/4)*(np.exp(D/2)+np.exp(-D/2))
    # PRIME
    PRIME = np.zeros((n,n))
    Tsup = C.max()-C.min(); emax = np.exp(Tsup + 12*s)
    for nn,lam in PL.items():
        if prime_cap is not None and nn>prime_cap: break
        if nn>emax: break
        u=np.log(nn)
        gkl = s2*(np.sqrt(np.pi)/(2*s))*(np.exp(-(D-u)**2/(4*s2))+np.exp(-(D+u)**2/(4*s2)))
        PRIME += 2*lam/np.sqrt(nn)*gkl
    Q = A+POLE-PRIME
    G = np.sqrt(np.pi)*s*np.exp(-D**2/(4*s2))
    return (Q+Q.T)/2, (G+G.T)/2

# ---- constraint functionals as vectors in coeff space ----
# For g=phi*phi~ with phi=sum c_k G_s(.-x_k), various linear functionals of phi:
def func_eval_phihat_real(centers, s, x):
    """phihat at imaginary or real arg used for moments. Here: l_k for a cosine-mode projection.
       Projection of g onto cos(x log p) is more natural on g; but constraints on phi (the cone is
       on phi). We implement the constraint <g, cos(omega .)> via g's even spectrum = h(omega).
       Simpler: constraints directly on phi as linear functionals l.c."""
    raise NotImplementedError

def constraint_integral(centers, s):
    """ l_k = integral phi_k dx = integral G_s(x-x_k) dx = 1 (normalized Gaussian area).
        Our basis G_s(x)= (we use h=|phihat|^2 normalization). integral phi_k = phihat_k(0)
        = sqrt(2pi) s. constant across k -> constraint int phi=0 is sum c_k=0. """
    return np.ones(len(centers))

def constraint_logn_moment(centers, s):
    """ l_k = integral phi_k(x) * x dx  (first moment); = derivative of phihat at 0 ~ x_k * area.
        integral x G_s(x-x_k) dx = x_k * sqrt(2pi) s. -> l_k proportional to x_k."""
    return np.asarray(centers, float)

def constraint_cos_mode(centers, s, omega):
    """ Project phi onto the oscillatory mode cos(omega x): l_k = integral phi_k(x) cos(omega x) dx
        = Re phihat_k(omega) = sqrt(2pi) s e^{-s^2 omega^2/2} cos(omega x_k)."""
    C=np.asarray(centers,float); s2=s*s
    return np.sqrt(2*np.pi)*s*np.exp(-s2*omega*omega/2)*np.cos(omega*C)

def constraint_sin_mode(centers, s, omega):
    C=np.asarray(centers,float); s2=s*s
    return -np.sqrt(2*np.pi)*s*np.exp(-s2*omega*omega/2)*np.sin(omega*C)

def project_mineig(Q, G, constraints):
    """min generalized eigenvalue of Q rel G on {c: a.c=0 for a in constraints}."""
    n=Q.shape[0]
    if constraints:
        Acon=np.array(constraints)            # m x n
        # basis of kernel of Acon
        u,sv,vt = np.linalg.svd(Acon)
        rank=int((sv>1e-10*sv.max()).sum()) if sv.size else 0
        Kbasis = vt[rank:].T                   # n x (n-rank): orthonormal kernel
        if Kbasis.shape[1]==0: return None,0
    else:
        Kbasis=np.eye(n)
    Qk = Kbasis.T@Q@Kbasis; Gk = Kbasis.T@G@Kbasis
    # whiten G
    w,V = np.linalg.eigh((Gk+Gk.T)/2); keep=w>w.max()*1e-9
    if keep.sum()==0: return None,0
    U = V[:,keep]/np.sqrt(w[keep])
    B = U.T@Qk@U; ev = np.linalg.eigvalsh((B+B.T)/2)
    return ev.min(), keep.sum()

if __name__=="__main__":
    print("Sanity: unconstrained min-eig should reproduce cone_past_log2 (negative past log2).")
    print(f"{'T':>6} {'s':>5} {'dim':>4} {'unconstrained_mineig':>22}")
    for T in [0.6, 0.69, 0.8, 1.0]:
        s=0.30; nb=8
        centers=np.linspace(-T/2,T/2,nb)
        Q,G=build_QG(centers,s)
        me,d=project_mineig(Q,G,[])
        print(f"{T:6.3f} {s:5.2f} {d:4d} {me:22.6e}")
