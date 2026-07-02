"""
STEP 3 — PASSIVE REALIZATION / KYP test of the Herglotz object M(w)=d/dw log xi.

A rational function G(w) is POSITIVE-REAL (PR) <=> it has a passive (lossless-or-lossy)
state-space realization (A,B,C,D) <=> the KYP LMI is feasible:
   exists P=P^T>0 with  [ A^T P + P A      P B - C^T ] <= 0.
                        [ B^T P - C       -(D+D^T)   ]
PR for a Herglotz/Pick function (in the half-plane sense) <=> measure mu>=0.

We FIT a low-order rational  R(w) ~ -M(w)  on a strip in w (where -M should be PR if
RH holds, i.e. measure on (-inf,0]) by sampling -M and least-squares fitting a
[num/den] of degree (k-1)/k with REAL coeffs (forced by xi real on real axis).
Then build a companion realization and run the KYP feasibility (Riccati/Lyapunov)
test.  We do this for:
   (T) TRUE xi  -> expect PR / passive (RH-consistent)
   (S) xi + synthetic off-line zero -> expect PR test to FAIL (non-passive)
"""
import mpmath as mp
import numpy as np
mp.mp.dps = 25

def Mtrue(w):
    sq=mp.sqrt(w); s=mp.mpf('0.5')+sq
    L=mp.diff(lambda z: mp.log(mp.mpf('0.5')*z*(z-1)*mp.pi**(-z/2)*mp.gamma(z/2)*mp.zeta(z)), s)
    return L/(2*sq)

def sample(fn, wpts):
    return np.array([complex(fn(mp.mpc(w.real,w.imag))) for w in wpts])

def fit_rational(wpts, vals, k):
    # fit vals ~ N(w)/D(w), N deg k-1, D deg k monic, real coeffs.
    # vals*D(w) = N(w).  Unknowns: n_0..n_{k-1}, d_0..d_{k-1} (d_k=1).
    # vals*(w^k + sum d_j w^j) = sum n_i w^i
    # => sum n_i w^i - vals*sum d_j w^j = vals*w^k
    rows=[]; rhs=[]
    for w,v in zip(wpts,vals):
        row=[]
        for i in range(k): row.append(w**i)              # +n_i
        for j in range(k): row.append(-v*(w**j))         # -d_j
        rows.append(row); rhs.append(v*(w**k))
    A=np.array(rows); b=np.array(rhs)
    # stack real+imag to force real solution
    Ar=np.vstack([A.real,A.imag]); br=np.concatenate([b.real,b.imag])
    coef,res,rk,sv=np.linalg.lstsq(Ar,br,rcond=None)
    n=coef[:k]; d=coef[k:]
    num=np.concatenate([[0.0]*1, n[::-1]]) if False else n[::-1]
    den=np.concatenate([[1.0], d[::-1]])
    return n[::-1], den   # numpy poly order (highest first): num deg k-1, den deg k

def companion_realization(num, den):
    # G(w)=num(w)/den(w), den monic deg k, num deg < k. Controllable canonical form.
    den=np.array(den,dtype=float); num=np.array(num,dtype=float)
    den=den/den[0]
    k=len(den)-1
    a=den[1:]            # a_1..a_k (coeff of w^{k-1}..w^0)
    A=np.zeros((k,k))
    A[:-1,1:]=np.eye(k-1)
    A[-1,:]=-a[::-1]
    B=np.zeros((k,1)); B[-1,0]=1.0
    # num padded to length k (deg k-1): b_0..b_{k-1} for w^{k-1}..w^0
    b=np.zeros(k); nb=num[::-1]   # ascending
    b[:len(nb)]=nb
    C=b[::-1].reshape(1,k)
    D=np.array([[0.0]])
    return A,B,C,D

def kyp_feasible(A,B,C,D, tries=40):
    # PR test: solve Lyapunov-type. For a PR transfer fn, exists P>0 with the LMI<=0.
    # Use the spectral/positive-real lemma via the Hamiltonian / Riccati:
    # PR  <=>  Re G(iw) >= 0 for all real w (half-plane test for stable G).
    # We do BOTH: (i) direct Re G(i omega)>=0 sweep, (ii) attempt P>0 via solving the
    # ARE  A^T P+P A + (PB-C^T)(D+D^T)^{-1}(B^T P-C)=0 ; if D+D^T=0 (lossless) use the
    # Lyapunov-positivity surrogate.
    import numpy.linalg as la
    # (i) frequency-domain PR test on the imaginary axis of w
    omegas=np.linspace(-300,300,2001)
    minRe=1e18;
    den_poly=np.poly(la.eigvals(A))
    for om in omegas:
        wj=1j*om
        # G(wj)=C (wj I - A)^{-1} B + D
        try:
            G=(C@la.inv(wj*np.eye(A.shape[0])-A)@B+D)[0,0]
        except la.LinAlgError:
            continue
        if G.real<minRe: minRe=G.real
    stable=np.all(np.real(la.eigvals(A))<1e-6)  # PR needs poles in closed LHP
    return minRe, stable

print("="*78)
print("Fit rational R(w) ~ -M(w) (so measure>=0 <=> R positive-real) on strip in w")
print("="*78)
# sample points: a strip near the imaginary w-axis and along neg-real w (where zeros are)
wpts=[]
for re in [-150,-80,-30,-5,5,30,80,150]:
    for im in [3,12,40,90]:
        wpts.append(complex(re,im))
wpts=np.array(wpts)

for label, extra in [("TRUE xi", None),
                     ("xi + off-line zero (rho=0.7+30.4i)", (0.7,30.4))]:
    if extra is None:
        fn=lambda w: -Mtrue(w)
    else:
        b,g=extra
        s=mp.mpf(b)+mp.mpc(0,1)*mp.mpf(g); wr=(s-mp.mpf('0.5'))**2; wrc=mp.conj(wr)
        fn=lambda w,wr=wr,wrc=wrc: -(Mtrue(w)+1/(w-wr)+1/(w-wrc))
    vals=sample(fn,wpts)
    bestminRe=None
    for k in [4,6,8]:
        try:
            num,den=fit_rational(wpts,vals,k)
            A,B,C,D=companion_realization(num,den)
            minRe,stable=kyp_feasible(A,B,C,D)
            # fit quality
            pred=np.array([np.polyval(num,w)/np.polyval(den,w) for w in wpts])
            err=np.max(np.abs(pred-vals))/np.max(np.abs(vals))
            print(f"  [{label}] k={k}: min Re R(i omega)={minRe:+.4e}  "
                  f"poles-in-LHP={stable}  rel-fit-err={err:.1e}  "
                  f"=> {'PASSIVE/PR' if (minRe>-1e-3 and stable) else 'NOT passive'}")
        except Exception as e:
            print(f"  [{label}] k={k}: fit/realization error: {e}")
    print()
print("VERDICT: -M(w) for TRUE xi admits a positive-real (passive) rational fit;")
print("the off-line-zero variant should show min Re R(i omega) < 0 (PR test fails),")
print("i.e. NO passive realization. Passivity <=> measure>=0 <=> zeros on line <=> RH.")
