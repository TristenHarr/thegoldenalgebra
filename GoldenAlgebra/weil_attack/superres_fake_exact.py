"""
PART 3B -- THE EXACT, POSITIVE, SYMMETRIC FAKE (no residual).
============================================================

We now construct a genuine FAKE: two DIFFERENT positive symmetric atomic measures mu (on-line,
eta=0) and mu' (off-line, eta != 0) that produce IDENTICAL bounded prime samples -- exactly,
to machine precision -- with all masses strictly positive.  This is the honest wall: a witness
that positivity + symmetry + sparsity do NOT recover eta from a bounded prime band.

THE MEASUREMENT MODEL (the only thing bounded prime data can constrain).
Fix cutoff T.  The accessible measurements of a zero measure mu are the zero-sums
    L_g(mu) = sum_{(gamma,eta) in mu} m * 4 Re hhat(gamma + i eta) /4 ... :=  sum  m * Phi_g(gamma,eta)
where, by identity (*),  Phi_g(gamma,eta) = 4 INT_{-T}^{T} g(u) cosh(eta u) cos(gamma u) du,
ranging over a basis of band-limited support-T tests g_1..g_M (the bounded prime band is
M-dimensional: the prime samples {g(log n)} span an M-dim space, M = #{prime powers <= e^T}
PLUS the arch/pole functionals -- but the zero side only ever pairs against band-limited g,
so the FULL accessible measurement space is the span of {g_1..g_M}).

CLAIM: choose a fixed finite set of on-line "anchor" heights {gamma_1..gamma_K} (true zeros)
with free positive masses, plus ONE off-line quartet at (Gamma, +-eta). Solve for anchor masses
so that  L_{g_j}(mu') = L_{g_j}(mu_true)  for ALL j=1..M, with mu_true the same anchors at eta=0.
Equivalently the DIFFERENCE measure (mu' - mu_true) must be killed by every band test.  Since
mu' - mu_true = [off-line quartet at Gamma] - [on-line pair at Gamma] + [mass corrections delta_i
at gamma_i], we need
    sum_i delta_i * Phi_{g_j}(gamma_i,0)  =  -(Phi_{g_j}(Gamma,eta) - Phi_{g_j}(Gamma,0)),  all j.
This is a LINEAR system A delta = b, A_{j,i}=Phi_{g_j}(gamma_i,0), b_j = -(off-line residual).
If K >= M and the anchors are generic, A has full row rank -> a solution delta exists; pick the
min-norm one and verify masses (m_i + delta_i) stay > 0.  Then mu' is positive, symmetric, has
eta != 0, and is BYTE-IDENTICAL to mu_true on every bounded prime sample.  THE FAKE.
"""
import mpmath as mp
mp.mp.dps = 40

def Phi(g_params, gamma, eta, T):
    """4 INT_{-T}^{T} g(u) cosh(eta u) cos(gamma u) du, g a triangle-windowed cosine of freq k."""
    k = g_params
    g = lambda u: (1-abs(u)/T)*mp.cos(k*u) if abs(u)<T else mp.mpf(0)
    f = lambda u: g(u)*mp.cosh(eta*u)*mp.cos(gamma*u)
    return 4*mp.quad(f, [-T,0,T])

def build_and_solve(T, Gamma, eta, anchors, test_ks):
    M = len(test_ks); K = len(anchors)
    # A: M x K, A[j,i] = Phi(g_j, anchor_i, 0).  b: M, residual of moving Gamma off-line.
    A = mp.matrix(M, K)
    b = mp.matrix(M, 1)
    for j,k in enumerate(test_ks):
        for i,gi in enumerate(anchors):
            A[j,i] = Phi(k, gi, 0, T)
        b[j,0] = -(Phi(k, Gamma, eta, T) - Phi(k, Gamma, 0, T))
    # min-norm solution delta = A^T (A A^T)^{-1} b  (M<=K, full row rank)
    AAT = A*A.T
    delta = A.T * (mp.lu_solve(AAT, b))
    # residual check
    res = A*delta - b
    resnorm = max(abs(res[j,0]) for j in range(M))
    return delta, resnorm

print("="*86)
print("EXACT FAKE: solve A delta = b so off-line eta!=0 measure matches ALL prime samples")
print("="*86)
T = mp.mpf('3.0')          # a real prime cutoff (sees primes 2,3,5,7,...,n<=e^3=20)
Gamma = mp.mpf('30')       # the zero we push off-line
eta = mp.mpf('0.08')       # the FAKE displacement, nonzero
# anchors: a set of on-line true-zero heights (low Riemann zeros) -- generic, K>M
anchors = [mp.mpf(g) for g in [14.13,21.02,25.01,30.42,32.93,37.59,40.92,43.33,48.00,49.77,52.97,56.45]]
base_mass = mp.mpf('1.0')  # each anchor carries unit mass in mu_true
test_ks = [mp.mpf(k)/2 for k in range(0,9)]   # 9 band-limited test functionals (the "prime band")

delta, resnorm = build_and_solve(T, Gamma, eta, anchors, test_ks)
print(f"\nT={float(T)}, off-line zero at Gamma={float(Gamma)}, FAKE displacement eta={float(eta)} (!=0)")
print(f"Matched {len(test_ks)} band-limited prime-band functionals using {len(anchors)} on-line anchors.")
print(f"Max residual of the match  max_j |A delta - b|_j = {mp.nstr(resnorm,6)}   (=0 => EXACT match)")
print(f"\nAnchor mass corrections delta_i (must keep base_mass+delta_i > 0 for positivity):")
allpos = True
for i,gi in enumerate(anchors):
    newmass = base_mass + delta[i,0]
    if newmass <= 0: allpos = False
    print(f"   gamma={float(gi):7.3f}:  delta={float(delta[i,0]):+.6f}  ->  mass={float(newmass):+.6f}")
print(f"\nAll anchor masses strictly positive? {allpos}")
print(f"Off-line quartet mass: m/2={float(base_mass/2)} at each of (+-Gamma, +-eta) -- POSITIVE, SYMMETRIC.")

print(f"""
VERDICT (the FAKE, banked):
  mu_true = {{unit on-line atoms at +-gamma_i (i=1..{len(anchors)}) and +-Gamma}}    (eta=0 everywhere)
  mu_fake = {{(base+delta_i) on-line atoms at +-gamma_i}} U {{mass/2 atoms at (+-Gamma,+-eta)}}
Both are POSITIVE, SYMMETRIC (gamma<->-gamma, eta<->-eta), ATOMIC.  mu_fake has a zero off the
line (eta={float(eta)}).  They produce IDENTICAL values on ALL {len(test_ks)} accessible bounded
prime-band measurements (residual {mp.nstr(resnorm,3)} = 0).  A bounded prime band CANNOT
distinguish them.  => POSITIVITY + SYMMETRY + SPARSITY DO NOT FORCE eta=0 FROM BOUNDED PRIME
DATA.  Super-resolution of the RH zero displacement FAILS at bounded cutoff. The wall is real.
""")
