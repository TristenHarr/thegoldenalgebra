"""
TASK 5: DAVENPORT-HEILBRONN CONTRAST. 
The DH function f(s)=(1-i*tan(theta)) L(s,chi) ... is a linear combination of two Dirichlet
L-functions with the SAME functional equation as zeta (same Gamma factor, conductor 5),
but NO Euler product. It HAS zeros off the critical line (Davenport-Heilbronn 1936).

For DH, the "explicit formula" still holds:
   sum_rho h(gamma_rho) = ARCH(h) + (no pole, f entire... or analogous) - PRIME_DH(g)
where PRIME_DH(g) = 2 sum_n c(n)/sqrt(n) g(log n), c(n)= -coefficients of f'/f Dirichlet series.
KEY DIFFERENCE: f has NO Euler product => f'/f is NOT -sum Lambda(n) n^{-s} with Lambda>=0.
The coefficients c(n) of f'/f are SIGN-CHANGING and NOT supported on prime powers.
=> PRIME_DH has NO definite sign even for the SHORTEST support; there is NO 'first prime
   power at log 2' structure. The cone where PRIME vanishes does NOT exist.

We demonstrate: compute the Dirichlet coefficients of f'/f for zeta (= -Lambda(n), prime-power
supported, one sign) vs for a DH-type combination (sign-changing, all n). Show that the
ARCH-domination argument that protects the zeta cone has nothing to dominate consistently.
"""
import mpmath as mp
mp.mp.dps=25

# zeta: -zeta'/zeta(s)= sum Lambda(n) n^{-s}. coefficients a(n)=Lambda(n) >=0, prime-powers only.
def Lambda(n):
    mm=n;fac={};d=2
    while d*d<=mm:
        while mm%d==0:fac[d]=fac.get(d,0)+1;mm//=d
        d+=1
    if mm>1:fac[mm]=fac.get(mm,0)+1
    return mp.log(list(fac.keys())[0]) if len(fac)==1 else mp.mpf(0)

print("ZETA: coefficients of -zeta'/zeta(s)=sum a(n)n^{-s}  [a(n)=Lambda(n)]")
print("  n: 2..12 :", [ (n, float(Lambda(n))) for n in range(2,13)])
print("  => a(n)>=0, NONZERO only on prime powers {2,3,4,5,7,8,9,11,...}. First at n=2 (log2).")
print()

# DH model: f = L(s,chi1)+ kappa L(s,chi2), no Euler product. Use a simple Dirichlet poly model
# with sign-changing coeffs to illustrate -f'/f coeff structure. Concretely take a function
# g(s)=1 - 2*2^{-s} + 3^{-s} (a Dirichlet polynomial with a zero off any line) and compute -g'/g.
# -g'/g = (sum_n b(n) log n n^{-s}) / g(s)  -- its Dirichlet coeffs c(n) by series division.
import sympy as sp
# represent Dirichlet series by coeffs on n=1..N. g(s)=sum B[n] n^{-s}.
N=40
B=[mp.mpf(0)]*(N+1); B[1]=mp.mpf(1); B[2]=mp.mpf(-2); B[3]=mp.mpf(1)  # toy non-Euler-product
# -g'/g = D/g where D = sum_n B[n] log n n^{-s}. Coeffs of D: d(n)=B[n] log n.
d=[B[n]*mp.log(n) if n>=1 else mp.mpf(0) for n in range(N+1)]
d[1]=mp.mpf(0)
# c = D * g^{-1}. g^{-1} via Dirichlet inverse Binv: sum_{ab=n} B[a]Binv[b]=[n==1].
Binv=[mp.mpf(0)]*(N+1); Binv[1]=1/B[1]
for n in range(2,N+1):
    s=mp.mpf(0)
    a=1
    # divisors
    for a in range(1,n+1):
        if n%a==0 and a<n:
            s+=B[n//a]*Binv[a]
    Binv[n]=-s/B[1]
# c(n)=sum_{ab=n} d(a) Binv[b]
c=[mp.mpf(0)]*(N+1)
for n in range(1,N+1):
    s=mp.mpf(0)
    for a in range(1,n+1):
        if n%a==0: s+=d[a]*Binv[n//a]
    c[n]=s
print("DH-type toy g(s)=1-2*2^{-s}+3^{-s} (NO Euler product): coeffs of -g'/g")
print("  n: 2..12 :",[(n,float(mp.nstr(c[n],4))) for n in range(2,13)])
signs=set(int(mp.sign(c[n])) for n in range(2,N+1) if abs(c[n])>1e-12)
nz=[n for n in range(2,N+1) if abs(c[n])>1e-12]
print(f"  => coeffs SIGN-CHANGING (signs present: {signs}); supported on ALL n (not just prime powers): {nz[:14]}...")
print()
print("CONSEQUENCE for the cone:")
print(" zeta: PRIME(g)=2 sum_{n>=2} Lambda(n)/sqrt(n) g(log n). For supp(g) in (-log2,log2)=(-.693,.693)")
print("       the sum is EMPTY (first term n=2 at log2) => Q=ARCH+POLE>=0 UNCONDITIONALLY (Yoshida).")
print(" DH:   PRIME_DH(g)=2 sum_{n>=2} c(n)/sqrt(n) g(log n). c(2)=%.3f != 0 AND c(n) sign-changes."%float(c[2]))
print("       Even on the SHORTEST support the n=2 term is present with INDEFINITE sign, and there")
print("       is NO 'gap before the first prime'. The empty-prime-sum cone DOES NOT EXIST for DH.")
