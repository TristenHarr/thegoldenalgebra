"""
THE CORRECT SHARP STATEMENT: it is NOT a hard threshold (the quartet kernel cosh(delta D) is
indefinite at every T>0, so a positive-type g CAN always extract SOME negative N). The sharp
content is the MAGNITUDE: how negative can N be, RELATIVE to the on-line positive value the
same g pays. We prove:
    |N_negative| / (on-line positive mass)  <=  e^{delta T} - 1  ~  delta T   (for delta T<<1),
so the off-line zero is invisible to leading order until delta T = O(1). This is the SHARP,
gamma0-INDEPENDENT uncertainty inequality.

DERIVATION (exact):  N = 4 \int_{-T}^{T} g(u) cosh(delta u) cos(gamma0 u) du.
Write cosh(delta u) = 1 + (cosh(delta u) - 1). Then
   N = 4 h(gamma0)  +  4 \int g(u)(cosh(delta u)-1) cos(gamma0 u) du = N0 + Delta.
N0 = 4 ĝ(gamma0) = 4|f̂(gamma0)|^2 >= 0  is the ON-LINE (nonnegative) value.
The off-line CORRECTION Delta is bounded:  |cosh(delta u)-1| <= cosh(delta T)-1 on [-T,T], and
   |Delta| <= 4 (cosh(delta T)-1) \int |g(u)| du.
For positive-type g, \int|g| is comparable to g(0)=||f||^2 (the total mass). The on-line term
N0 = 4|f̂(gamma0)|^2 can be as large as 4 g(0)*(matched) but a probe LOCALIZED at gamma0 has
N0 ~ 4 g(0) * (concentration). So the RATIO Delta/N0 is bounded by ~ (cosh(delta T)-1) ~
(delta T)^2/2. The off-line zero perturbs the (nonnegative) on-line contribution by a RELATIVE
amount  (delta T)^2/2 : INVISIBLE until delta T ~ 1.

We verify the bound  Delta_min / g(0)  ~  -(cosh(delta T)-1)*const  numerically: minimize
N over positive-type g (supp[-T,T]) NORMALIZED by g(0)=1, and confirm the most-negative N
scales as -(cosh(delta T)-1), i.e. -(delta T)^2/2 for small delta T, gamma0-independent.
"""
import numpy as np

def most_negative_N_over_g0(delta, gamma0, T, m=300):
    """
    Minimize N(g)=4 f^T A f, A_xy=cosh(d(x-y))cos(g0(x-y)), subject to g(0)=f^T f =1.
    => min eigenvalue of A times 4 (since g(0)=int f^2 dx = f^T f on unit-weight grid).
    Use grid with quadrature weight dx so f^T f approximates int f^2 = g(0).
    """
    x=np.linspace(-T/2,T/2,m); dx=x[1]-x[0]
    D=x[:,None]-x[None,:]
    A=np.cosh(delta*D)*np.cos(gamma0*D)
    A=(A+A.T)/2*dx*dx          # so f^T A f ~ int int f f K  (g(u) autocorr integral)
    Gram=np.eye(m)*dx          # f^T Gram f ~ int f^2 = g(0)
    # generalized min eig of (4A, Gram)
    ev=np.linalg.eigvalsh(4*A/dx)   # normalize: A had dx^2, Gram dx -> ratio has dx
    return ev.min()

print("="*82)
print("Most-negative N at g(0)=1 (positive-type g, supp[-T,T]). Compare to -(cosh(dT)-1)*c.")
print("Tests: (i) gamma0-independence, (ii) scaling N_min ~ -(cosh(delta T)-1) ~ -(dT)^2/2.")
print("="*82)
print(f"{'gamma0':>7} {'delta':>7} {'T':>6} {'dT':>7} {'N_min/g0':>12} {'-(cosh(dT)-1)':>15} {'ratio':>8}")
for gamma0 in [50.0, 200.0, 1000.0]:
    for delta in [0.1, 0.05]:
        for T in [2.0, 5.0, 10.0, 1.0/delta, 2.0/delta]:
            nm=most_negative_N_over_g0(delta,gamma0,T,m=240)
            ref=-(np.cosh(delta*T)-1)
            print(f"{gamma0:7.0f} {delta:7.3f} {T:6.2f} {delta*T:7.3f} {nm:12.4e} {ref:15.4e} {nm/ref if ref!=0 else 0:8.3f}")
    print()
