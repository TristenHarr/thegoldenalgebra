"""
Riemann / de Bruijn-Newman Phi kernel and total-positivity (Polya-frequency) machinery.

Two conventions for the Riemann Phi:

 CLASSICAL (Riemann/Polya):
   Phi_c(u) = sum_{n>=1} (2 pi^2 n^4 e^{9u/2} - 3 pi n^2 e^{5u/2}) exp(-pi n^2 e^{2u})
   It is even: Phi_c(-u) = Phi_c(u).  Xi(z) = 2 int_0^inf Phi_c(u) cos(z u) du.

 PAPER 2602.20313 convention (substitution u -> 2u, i.e. faster):
   Phi_p(u) = sum_{n>=1} (2 pi^2 n^4 e^{9u} - 3 pi n^2 e^{5u}) exp(-pi n^2 e^{4u})
   (Same function evaluated at 2u.)  K(u) = Phi_p(|u|).

A Toeplitz/translation kernel K(x-y) is "Polya frequency of order r" (PF_r) iff
every k x k minor det[K(x_i - y_j)] with x_1<...<x_k and y_1<...<y_k ordered
nodes is >= 0, for all k <= r.  For a *translation* kernel with equally spaced
nodes this reduces to nonnegativity of the Toeplitz determinants
   D_r(u0,h) = det[ K(u0 + (i-j) h) ]_{i,j=0}^{r-1}.
"""
import mpmath as mp

mp.mp.dps = 80  # 80 decimal digits, matching the paper's certified precision

def Phi_paper(u):
    """Paper-convention kernel Phi_p(u), u real. Even-extend via |u| outside."""
    u = mp.mpf(u)
    e9 = mp.e**(9*u)
    e5 = mp.e**(5*u)
    e4 = mp.e**(4*u)
    s = mp.mpf(0)
    n = 1
    pi = mp.pi
    while True:
        n2 = mp.mpf(n)**2
        n4 = n2*n2
        term = (2*pi**2*n4*e9 - 3*pi*n2*e5) * mp.e**(-pi*n2*e4)
        s += term
        # stop when the exponential damping makes terms negligible
        if abs(term) < mp.mpf(10)**(-mp.mp.dps-10) and n > 3:
            break
        n += 1
        if n > 2000:
            break
    return s

def Phi_classical(u):
    """Classical Riemann Phi_c(u). Even function."""
    u = mp.mpf(u)
    e9 = mp.e**(mp.mpf(9)*u/2)
    e5 = mp.e**(mp.mpf(5)*u/2)
    e2 = mp.e**(2*u)
    s = mp.mpf(0)
    n = 1
    pi = mp.pi
    while True:
        n2 = mp.mpf(n)**2
        n4 = n2*n2
        term = (2*pi**2*n4*e9 - 3*pi*n2*e5) * mp.e**(-pi*n2*e2)
        s += term
        if abs(term) < mp.mpf(10)**(-mp.mp.dps-10) and n > 3:
            break
        n += 1
        if n > 2000:
            break
    return s

def K_paper(u):
    return Phi_paper(abs(mp.mpf(u)))

def K_classical(u):
    return Phi_classical(mp.mpf(u))  # already even

def toeplitz_det(Kfun, u0, h, r):
    """D_r(u0,h) = det[ K(u0 + (i-j) h) ]_{i,j=0..r-1}."""
    M = mp.matrix(r, r)
    for i in range(r):
        for j in range(r):
            M[i, j] = Kfun(mp.mpf(u0) + (i - j) * mp.mpf(h))
    return mp.det(M)

def general_minor_det(Kfun, xs, ys):
    """det[ K(x_i - y_j) ] for arbitrary ordered node lists xs, ys (same length)."""
    r = len(xs)
    assert len(ys) == r
    M = mp.matrix(r, r)
    for i in range(r):
        for j in range(r):
            M[i, j] = Kfun(mp.mpf(xs[i]) - mp.mpf(ys[j]))
    return mp.det(M)
