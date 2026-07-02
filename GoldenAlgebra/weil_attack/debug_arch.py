import mpmath as mp
mp.mp.dps=25
def dig(z): return mp.digamma(z)
sig=mp.mpf('1.0');C=2*mp.pi*sig*sig
vec=[mp.mpf(x) for x in ['-0.69254','-0.17057','-0.1291','-0.21003','-0.33588','-0.37533','0.42051']]
us=[mp.mpf(n) for n in range(7)]
def h(r):
    S=sum(c*mp.e**(-1j*r*u) for c,u in zip(vec,us))
    return (C*mp.e**(-(sig*sig)*r*r)*abs(S)**2).real
W=lambda r: mp.re(dig(mp.mpf(1)/4+1j*r/2))-mp.log(mp.pi)
# integrate with many subdivisions to resolve oscillation (period ~ 2pi/6 ~1)
pts=[-mp.inf]+[mp.mpf(t)/2 for t in range(-40,41)]+[mp.inf]
A=mp.quad(lambda r:h(r)*W(r),pts)/(2*mp.pi)
print("ARCH refined=",mp.nstr(A,12))
# Even simpler: expand |S|^2 = sum_{j,k} c_j c_k e^{-i r (u_j-u_k)}. Each term arch integral
# I_{jk} = (1/2pi) int C e^{-sig^2 r^2} e^{-i r d} W(r) dr, d=u_j-u_k. Real part since symmetric sum.
def arch_pair(d):
    f=lambda r: C*mp.e**(-(sig*sig)*r*r)*mp.cos(r*d)*W(r)
    return mp.quad(f,[-mp.inf,0,mp.inf])/(2*mp.pi)
A2=mp.mpf(0)
for cj,uj in zip(vec,us):
    for ck,uk in zip(vec,us):
        A2+=cj*ck*arch_pair(uj-uk)
print("ARCH by pairs=",mp.nstr(A2,12))
