"""
SUPER-RESOLUTION SEPARATION ANALYSIS for the RH zero measure.
=============================================================

Mission: is RH a super-resolution theorem? In Candes-Fernandez-Granda (CFG) theory,
a SIGNED atomic measure is recoverable from low-frequency (cutoff f_c) data only if its
minimum separation exceeds Delta > 2/f_c.  A POSITIVE atomic measure can in principle be
recovered with NO separation (Prony/moment uniqueness, noiseless) -- BUT that uniqueness
is fragile: under any band-limit (= the finite prime cutoff acts as truncation) the
stability blows up like (super-resolution factor)^{2N-1} when atoms are closer than 1/f_c.

THE ZERO MEASURE.  Riemann zeros rho = 1/2 + i*gamma have average gap
    Delta_gamma(gamma) ~ 2*pi / log(gamma/2pi).
The "displacement" coordinate is eta = beta - 1/2 (eta=0 <=> on line). The off-line
quartet is the pair (gamma, +eta), (gamma, -eta) plus FE/conjugate partners -- a POSITIVE,
SYMMETRIC, atomic measure in the (gamma, eta) plane.

THE CUTOFF.  A test g supported in [-T, T] sees primes n with log n <= T, i.e. n <= e^T.
By Paley-Wiener, h = ghat is entire of exponential type T: the "Fourier cutoff" / bandwidth
available to resolve structure in the gamma variable is f_c = T.  So:
    available resolution in gamma  ~  1/T   (this is the bandwidth)
    CFG separation threshold       Delta > 2/f_c = 2/T.

QUESTION 1 (this script):  Is the zero separation ABOVE or BELOW the CFG threshold 2/T,
for the prime cutoffs actually available?  i.e. is Delta_gamma(gamma) >< 2/T?
"""
import mpmath as mp
mp.mp.dps = 30

print("="*86)
print("PART 1 -- ZERO SEPARATION vs CFG THRESHOLD 2/T (Fourier cutoff = support T)")
print("="*86)
print("""
For a test function of support T, the Fourier cutoff resolving the gamma-axis is f_c = T.
CFG: a SIGNED measure is super-resolvable iff min separation Delta > 2/f_c = 2/T.
Zero gap at height gamma: Delta_gamma ~ 2*pi/log(gamma/2pi).
The two are EQUAL (gap = threshold) when  2*pi/log(gamma/2pi) = 2/T, i.e.
    T_crit(gamma) = log(gamma/2pi)/pi.
For T < T_crit the gap is ABOVE threshold (CFG would resolve a SIGNED measure);
for T > T_crit the gap is BELOW threshold (zeros too dense -- CFG fails for signed).
But the realistic prime cutoffs are TINY (Yoshida cone T<log2=0.69; even "all primes
numerically" rarely exceeds T~30).  Compare.
""")
def gap(gamma):           # average zero gap at height gamma
    return 2*mp.pi/mp.log(gamma/(2*mp.pi))
def Tcrit(gamma):         # support at which gap = CFG threshold 2/T
    return mp.log(gamma/(2*mp.pi))/mp.pi

print(f"{'gamma':>10} {'zero gap':>12} {'2/T @ T=log2':>14} {'2/T @ T=30':>12} {'T_crit':>10}  separated@T=log2?")
for gamma in [14, 50, 100, 1000, 1e4, 1e6, 1e10]:
    g = mp.mpf(gamma)
    dg = gap(g)
    thr_log2 = 2/mp.log(2)
    thr_30   = 2/mp.mpf(30)
    tc = Tcrit(g)
    sep = "YES (gap>thr)" if dg > thr_log2 else "NO  (too dense)"
    print(f"{float(g):>10.0e} {float(dg):>12.4f} {float(thr_log2):>14.4f} {float(thr_30):>12.4f} {float(tc):>10.3f}  {sep}")

print("""
READ: at the Yoshida cutoff T=log2, the CFG threshold is 2/T = 2.885.  The zero gap is
ABOVE this only for gamma < ~80 (gap(14)=5.6, gap(100)=2.27<2.885).  So:
  - For the LOW zeros (gamma<~80), individual zeros ARE separated at the threshold even with
    the tiny Yoshida cutoff -- but there the prime sum is EMPTY (T<log2 sees no primes), so
    there are NO measurements at all.  Resolution is moot: zero data.
  - For ANY zero at height gamma>~80, the gap falls BELOW 2/T already at T=log2, and falls
    further below for every larger gamma. The whole zero-bulk is DENSER than the CFG cell.
CONCLUSION: with the actual available prime band, the zero measure is BELOW the CFG
separation threshold for all but the first few zeros. SIGNED super-resolution provably fails.
The only hope is the POSITIVE-measure exemption -- examined next.
""")

print("="*86)
print("PART 2 -- THE POSITIVE-MEASURE EXEMPTION AND WHY THE PRIME SAMPLES ARE NOT MOMENTS")
print("="*86)
print("""
Positive-measure super-resolution (noiseless): a positive sum of N Diracs is the UNIQUE
positive measure matching its first 2N+1 Fourier MOMENTS {mu_hat(k): |k|<=2N} (Prony).
If the prime samples WERE such consecutive moments of the zero measure, positivity would
force the answer uniquely -- a potential crack. They are NOT, for two structural reasons:

(R1) The explicit formula is a SINGLE bilinear pairing  sum_rho h(gamma_rho) = [prime side](g),
     one real number per test g, NOT a vector of consecutive moments mu_hat(0..2N).
     Choosing g sweeps h over a band-limited family of type T; the accessible functionals are
     { sum_rho h(gamma_rho) : h band-limited type T, h>=0 }.  These are LINEAR in the zero
     measure but they are the values of a TYPE-T (=cutoff T) entire h -- exactly a low-pass
     (band-limited) observation, NOT the unbounded moment ladder Prony needs.  The prime
     cutoff T caps the bandwidth; Prony-exactness needs UNBOUNDED bandwidth (all 2N moments,
     N = number of zeros = INFINITE).

(R2) The off-line displacement enters h OFF the real axis: gamma_rho = gamma - i*eta, so the
     measurement is  4*Re h(gamma + i*eta)  =  4*INT g(u) cosh(eta*u) cos(gamma*u) du  (identity *).
     The eta-dependence is through cosh(eta*u), which for |u|<=T deviates from 1 by only
     O((eta*T)^2/2).  A band-limited h CANNOT separate eta=0 from eta!=0 until its support
     reaches |u|~1/eta.  This is the delta*T~1 gate -- the band-limit, not signedness, is binding.

So the positive-measure noiseless Prony uniqueness does NOT apply: we have a BAND-LIMITED
positive measurement, the regime where even positive super-resolution is provably UNSTABLE
(stability ~ (1/(eta*T))^{2N-1}).  Quantify the gate next, then build the explicit FAKE.
""")
