"""
RH-equivalent energy positivity test for rh.lean's IntegratedDoubleKernelPositivity.

Target object (rh.lean:1890):
    P(x,y) := int_0^inf int_0^inf Phi(u) Phi(v) K(u,v;x,y) du dv  >= 0   for y>0,
with the file's kernel  K = d/dy cosKer,  cosKer = Re(cos(zu) conj(cos(zv))), z=x+iy.

Verified-symbolic structural facts:
    cos(zu) = a(u) - i b(u),  a(u)=cos(xu)cosh(yu),  b(u)=sin(xu)sinh(yu).
    cosKer(u,v) = a(u)a(v) + b(u)b(v).
    K(u,v) = ay(u)a(v)+a(u)ay(v) + by(u)b(v)+b(u)by(v),
      ay(u)=u cos(xu) sinh(yu),  by(u)=u sin(xu) cosh(yu).
    => P(x,y) = 2[ (int Phi a)(int Phi ay) + (int Phi b)(int Phi by) ]
              = d/dy [ (int Phi a)^2 + (int Phi b)^2 ]   = (1/4) d/dy |Xi(x+iy)|^2.
We report  S(x,y) := (int Phi a)(int Phi ay) + (int Phi b)(int Phi by) = P/2.
(P>=0  <=>  S>=0.)  Phi is the TRUE Riemann Phi.
"""
import numpy as np

def Phi_vec(u, Nmax=60):
    u = np.asarray(u, dtype=np.float64)
    e2u = np.exp(2.0*u)
    e9 = np.exp(4.5*u); e5 = np.exp(2.5*u)
    s = np.zeros_like(u)
    for n in range(1, Nmax+1):
        n2 = n*n
        s += (2*np.pi**2*n2*n2*e9 - 3*np.pi*n2*e5) * np.exp(-np.pi*n2*e2u)
    return s

def grids(Lneg=12.0, Upos=3.2, N=300001):
    u = np.linspace(-Lneg, Upos, N)
    return u, Phi_vec(u)

U, PHI = grids()

def integ(y, x):
    return np.trapz(y, x)

def S_of(x, y):
    cu = np.cos(x*U); su = np.sin(x*U)
    chu = np.cosh(y*U); shu = np.sinh(y*U)
    a = cu*chu; b = su*shu
    ay = U*cu*shu; by = U*su*chu
    Ea  = integ(PHI*a,  U); Eb  = integ(PHI*b,  U)
    Eay = integ(PHI*ay, U); Eby = integ(PHI*by, U)
    return Ea*Eay + Eb*Eby, Ea, Eb, Eay, Eby

if __name__ == "__main__":
    print("S(x,y) = (intPhi a)(intPhi ay)+(intPhi b)(intPhi by) = P/2,  P=d/dy|Xi|^2 (RH: S>=0 for y>0)")
    print(f"{'x':>9} {'y':>6} {'S=P/2':>16} {'Ea':>14} {'Eb':>14}")
    xs = [0.0, 0.5, 1.0, 3.0, 6.0, 10.0, 14.134725, 15.0, 21.022, 25.0]
    anyneg = False
    for x in xs:
        for y in [0.02, 0.1, 0.3, 0.6, 1.0]:
            S, Ea, Eb, Eay, Eby = S_of(x, y)
            flag = "   <== NEGATIVE" if S < 0 else ""
            if S < 0: anyneg = True
            print(f"{x:9.4f} {y:6.2f} {S:16.6e} {Ea:14.6e} {Eb:14.6e}{flag}")
    print("\nANY NEGATIVE S FOUND:", anyneg)
    print()
    print("PSD test of K(u,v;x,y) as a kernel (eigenvalues of quadrature matrix):")
    for (x0,y0) in [(0.5,0.3),(3.0,0.5),(14.13,0.2)]:
        ug = np.linspace(0.01, 6.0, 300)
        a = np.cos(x0*ug)*np.cosh(y0*ug); b = np.sin(x0*ug)*np.sinh(y0*ug)
        ay = ug*np.cos(x0*ug)*np.sinh(y0*ug); by = ug*np.sin(x0*ug)*np.cosh(y0*ug)
        M = np.outer(ay,a)+np.outer(a,ay)+np.outer(by,b)+np.outer(b,by)
        M = 0.5*(M+M.T)
        w = np.linalg.eigvalsh(M)
        print(f"  x={x0:6.2f} y={y0:4.2f}: min eig={w.min():12.4e}  max eig={w.max():12.4e}  rank>=2 indefinite")
