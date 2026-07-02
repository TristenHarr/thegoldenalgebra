"""
THE CONE THRESHOLD COMPUTATION.
================================
Weil explicit formula (even real test function g, support [-T,T]; F = Fourier
transform of g, h(r)=|F(r)|^2 form is NOT what we use here -- we use the
*linear* explicit formula in g and build the quadratic form Q(g)=W(g*g~)).

Standard Weil form for g even, compactly supported in [-T,T]:

  Q(g) = ARCH(g) + POLE(g) - PRIME(g)

  POLE(g)  = 2 * ghat(i/2) + 2*ghat(-i/2)  (the s=0,1 poles of xi)  [main term]
             For g even real: contributes  2*\int g(u) cosh(u/2) du  (pole pair)
  ARCH(g)  = (1/2pi) \int_{-inf}^{inf} ghat(r) * Omega(r) dr,
             Omega(r) = Re psi(1/4 + i r/2) - log pi    (archimedean kernel)
  PRIME(g) = 2 * sum_{n>=2} Lambda(n) n^{-1/2} g(log n)   (FINITE: only n<=e^T)

We work with the quadratic form by taking g = phi * phi~ (autocorrelation),
phi supported in [-T/2,T/2], so g supported in [-T,T], ghat = |phihat|^2 >= 0.
Then ARCH(g) = (1/2pi)\int |phihat(r)|^2 Omega(r) dr  (Connes' archimedean form),
and the WHOLE thing is a quadratic form in phi.

We discretize phi as a real vector on a grid in [-T/2,T/2] and assemble the
real-symmetric matrix  M(T)  with  phi^T M(T) phi = Q(phi*phi~).
min eigenvalue of M(T) >= 0  <=>  Q >= 0 on ALL g=autocorr supported in [-T,T]
(positive-type g). We find T* = sup{ T : min eig M(T) >= 0 } UNCONDITIONALLY
(prime sum finite, archimedean kernel explicit, NO use of RH / zeros).
"""
import numpy as np
from sympy import isprime
import mpmath as mp
mp.mp.dps = 20

def vonMangoldt_list(Nmax):
    out = {}
    n = 2
    while n <= Nmax:
        # prime power?
        m = n; p = 2; found = None
        # factor
        mm = n; fac = {}
        d = 2
        while d*d <= mm:
            while mm % d == 0:
                fac[d] = fac.get(d,0)+1; mm//=d
            d+=1
        if mm>1: fac[mm]=fac.get(mm,0)+1
        if len(fac)==1:
            p = list(fac.keys())[0]
            out[n] = np.log(p)
        n+=1
    return out

def Omega(r):
    # archimedean kernel Re psi(1/4 + i r/2) - log pi
    return float(mp.re(mp.digamma(mp.mpf(1)/4 + 1j*mp.mpf(r)/2)) - mp.log(mp.pi))

# Precompute Omega on a fine r-grid for the archimedean integral
RGRID = np.linspace(-200, 200, 40001)
DR = RGRID[1]-RGRID[0]
OMEGA = np.array([Omega(r) for r in RGRID])

def build_M(T, Npts):
    """Discretize phi on grid in [-T/2, T/2], Npts points.
    Q(phi) = sum over basis contributions. We assemble M so phi^T M phi = Q.
    """
    xs = np.linspace(-T/2, T/2, Npts)
    dx = xs[1]-xs[0] if Npts>1 else 1.0
    # phi(x) = sum_i c_i delta-bump at xs[i] (we treat c_i as nodal values * dx weight)
    # phihat(r) = sum_i c_i e^{-i r x_i} dx   (real part for even... but phi need not be even)
    # |phihat(r)|^2 = sum_{i,j} c_i c_j cos(r(x_i-x_j)) dx^2
    # ARCH = (1/2pi)\int |phihat|^2 Omega dr
    #      = (dx^2/2pi) sum_{ij} c_i c_j \int Omega(r) cos(r (x_i-x_j)) dr
    # Let Ahat(delta) = (1/2pi)\int Omega(r) cos(r*delta) dr   (Omega even in r)
    # PRIME = 2 sum_n Lambda(n)/sqrt(n) g(log n), g=phi*phi~ :
    #   g(u) = \int phi(x) phi(x-u) dx = sum_{ij} c_i c_j dx^2 [x_i - x_j = u]? 
    #   discretely g(u)= sum_{ij} c_i c_j dx * tri/delta(u-(x_i-x_j)). For nodal we use
    #   g(log n) approximated by sum_{ij} c_i c_j * dx * K_window(x_i - x_j - log n).
    # To stay clean & EXACT-as-quadratic-form we instead use a SMOOTH basis below.
    raise NotImplementedError

# --- Cleaner: use smooth Gaussian bump basis, exact analytic Q entries. ---
# Basis: phi_k(x) = exp(-(x-x_k)^2/(2 s^2)), centers x_k in [-T/2,T/2].
# phihat_k(r) = s sqrt(2pi) exp(-s^2 r^2/2) exp(-i r x_k)   (up to const; real conv ok)
# g_{kl}(u) = (phi_k * phi_l~)(u) = \int phi_k(x) phi_l(x-u) dx
#           = sqrt(pi) s exp(-(u-(x_k-x_l))^2/(4 s^2))   [autocorr of gaussians]
# ARCH entry: (1/2pi)\int phihat_k conj(phihat_l) Omega dr  with phihat_k phihat_l*
#   = 2pi s^2 exp(-s^2 r^2) exp(-i r (x_k - x_l)); times Omega, integrate /2pi:
#   A_{kl} = s^2 \int exp(-s^2 r^2) cos(r (x_k-x_l)) Omega(r) dr
# POLE entry: pole term = 2*(ghat_{kl}(i/2)+ghat_{kl}(-i/2)). ghat=|.|? 
#   Actually POLE term in Weil = ghat(1/2)+ghat(-1/2) in s-var = \int g(u) e^{u/2}du + e^{-u/2}.
#   = \int g_{kl}(u) (e^{u/2}+e^{-u/2}) du = \int g_{kl}(u) 2 cosh(u/2) du.
# PRIME entry: P_{kl} = 2 sum_{n} Lambda(n)/sqrt(n) g_{kl}(log n).
# Q matrix M = A + POLE - PRIME (real symmetric).

def assemble(T, centers, s, primes_Lambda):
    n = len(centers)
    A = np.zeros((n,n)); POLE=np.zeros((n,n)); PRIME=np.zeros((n,n))
    s2 = s*s
    # archimedean integrand uses precomputed OMEGA grid
    for i in range(n):
        for j in range(n):
            d = centers[i]-centers[j]
            # A_{ij}
            integ = s2 * np.exp(-s2*RGRID**2) * np.cos(RGRID*d) * OMEGA
            A[i,j] = np.trapezoid(integ, RGRID)
            # POLE: \int g(u) 2cosh(u/2) du, g(u)=sqrt(pi) s exp(-(u-d)^2/(4 s^2))
            # = sqrt(pi)s * 2 * \int exp(-(u-d)^2/4s^2) cosh(u/2) du
            # \int exp(-(u-d)^2/(4s^2)) e^{u/2} du = 2 s sqrt(pi) e^{d/2 + s^2/4}
            # so POLE = sqrt(pi)s * [2 s sqrt(pi)(e^{d/2}+e^{-d/2}) e^{s^2/4}]
            POLE[i,j] = np.sqrt(np.pi)*s * 2*s*np.sqrt(np.pi)*(np.exp(d/2)+np.exp(-d/2))*np.exp(s2/4)
            # PRIME
            tot = 0.0
            for nn,(lam, sqrtn) in primes_Lambda.items():
                u = np.log(nn)
                g = np.sqrt(np.pi)*s*np.exp(-(u-d)**2/(4*s2))
                tot += lam/sqrtn * g
            PRIME[i,j] = 2*tot
    M = A + POLE - PRIME
    return M, A, POLE, PRIME

# primes up to large bound (finite sum truncates by gaussian tail anyway)
NMAX = 100000
vm = vonMangoldt_list(NMAX)
primes_Lambda = {nn:(lam, np.sqrt(nn)) for nn,lam in vm.items()}

print("T*-search: smooth Gaussian basis, centers spanning [-T/2,T/2], width s tuned small.")
print("min-eig of Weil matrix M(T) (UNCONDITIONAL: prime sum finite, no zeros used)")
print()
print(f"{'T':>6} {'s':>6} {'mineig':>14} {'Adiag~':>12} {'POLEdiag':>12} {'PRIMEdiag':>12}")
for T in [0.5,1.0,1.386,2.0,2.5,3.0,3.5,4.0,5.0,6.0]:
    nb = max(2, int(T/0.25)+1)
    centers = np.linspace(-T/2, T/2, nb)
    s = 0.18
    M,A,POLE,PRIME = assemble(T, centers, s, primes_Lambda)
    ev = np.linalg.eigvalsh((M+M.T)/2)
    print(f"{T:6.3f} {s:6.2f} {ev.min():14.6e} {A[0,0]:12.4e} {POLE[0,0]:12.4e} {PRIME[0,0]:12.4e}")
