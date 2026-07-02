"""
OPTIMAL T*(delta,gamma0): smallest support at which a POSITIVE-TYPE g (supp[-T,T]) makes the
quartet mass  N = 4 int_{-T}^{T} g(u) cosh(delta u) cos(gamma0 u) du  NEGATIVE.
This is a clean extremal problem. g positive-type, supp[-T,T]  <=>  g(u)=(f * f~)(u) with
supp(f) subset [-T/2,T/2]. Discretize f on a grid in [-T/2,T/2]; g=autocorrelation; then
   N(f) = 4 int g(u) K(u) du,  K(u)=cosh(delta u) cos(gamma0 u),
        = 4 int int f(x) f(y) K(x-y) dx dy   (since g(u)=int f(x)f(x-u)dx => int g K = int int f(x)f(y)K(x-y))
   = 4 f^T A f,  A_xy = K(x-y).
Minimize Rayleigh f^T A f / f^T f  => min eigenvalue of the kernel matrix A_xy=K(x-y),
x,y in [-T/2,T/2]. NEGATIVE min eig  <=>  exists positive-type g of support T with N<0
<=> the off-line zero at (delta,gamma0) is 'visible' to support T. Threshold T*: min eig = 0.

This is RIGOROUS and gives the SHARP constant. Run scan; extract T*(delta) and test the
law T* = c0/delta and its gamma0-dependence.
"""
import numpy as np

def min_eig_kernel(delta, gamma0, T, m=400):
    x=np.linspace(-T/2,T/2,m)
    D=x[:,None]-x[None,:]
    A=np.cosh(delta*D)*np.cos(gamma0*D)
    A=(A+A.T)/2
    ev=np.linalg.eigvalsh(A)
    return ev.min()

print("="*80)
print("RIGOROUS threshold: min eig of kernel A_xy=cosh(delta(x-y))cos(gamma0(x-y)),")
print("x,y in [-T/2,T/2]. <0  <=>  positive-type g of support T can make quartet mass N<0.")
print("Threshold T*(delta,gamma0): smallest T with min eig = 0.")
print("="*80)
def find_Tstar(delta,gamma0):
    lo,hi=0.05, 60.0
    # ensure sign change
    if min_eig_kernel(delta,gamma0,hi)>=0: return None
    for _ in range(40):
        mid=(lo+hi)/2
        if min_eig_kernel(delta,gamma0,mid)<0: hi=mid
        else: lo=mid
    return (lo+hi)/2

print(f"{'gamma0':>8} {'delta':>8} {'T*':>10} {'T*·delta':>10} {'T*·delta/pi':>12}")
for gamma0 in [10.0,30.0,100.0,300.0,1000.0]:
    for delta in [0.5,0.3,0.2,0.1,0.05]:
        Ts=find_Tstar(delta,gamma0)
        if Ts: print(f"{gamma0:8.0f} {delta:8.3f} {Ts:10.4f} {Ts*delta:10.4f} {Ts*delta/np.pi:12.4f}")
        else:  print(f"{gamma0:8.0f} {delta:8.3f}   (no visible threshold)")
