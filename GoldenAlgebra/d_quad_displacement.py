import sympy as sp

# ---------------------------------------------------------------
# Symbols
# ---------------------------------------------------------------
x, y, gamma, eta = sp.symbols('x y gamma eta', real=True)
z = x + sp.I*y                      # general point, y>0 (UHP)
g, h = sp.symbols('gamma eta', real=True, positive=True)  # for sign work

# Paired-Cauchy kernel at base u : 1/(z-u) + 1/(z+u)
def K(zz, u):
    return 1/(zz - u) + 1/(zz + u)

# ---------------------------------------------------------------
# TASK 1: Bookkeeping
#
# Four pullback points: {gamma - i*eta, -gamma + i*eta, -gamma - i*eta, gamma + i*eta}
# A paired atom K_u covers {+u, -u}.
#   u1 = gamma + i*eta  covers { gamma+i*eta , -gamma-i*eta }
#   u2 = gamma - i*eta  covers { gamma-i*eta , -gamma+i*eta }
# Together u1,u2 cover ALL FOUR points exactly once.  -> TRUE = K(z,u1)+K(z,u2)
#
# Height model: ONE paired atom at u=gamma covers {+gamma,-gamma}.
# But the quadruple is ONE zero rho giving 4 xi-zeros = effectively TWO paired atoms.
# The honest height representation of the SAME mass is TWO copies of the real atom?
# No: the height model collapses the quadruple onto the real axis. The quadruple
# carries the same total "atom count" as two paired real atoms at gamma (since u1,u2
# both -> gamma as eta->0). So height = 2 * K(z,gamma)? Let's test eta=0 consistency.
# ---------------------------------------------------------------

u1 = gamma + sp.I*eta
u2 = gamma - sp.I*eta

true_sum   = K(z, u1) + K(z, u2)
height_rep = K(z, gamma) + K(z, gamma)   # two real-height atoms (u1,u2 both -> gamma)

Dq = true_sum - height_rep

# Check eta=0 => 0 exactly
print("=== TASK 1: eta=0 collapse ===")
print("D_quad at eta=0 :", sp.simplify(Dq.subs(eta,0)))

print("\n=== Alternative: single height atom convention ===")
# If height used ONE atom K(z,gamma), then at eta=0 true_sum = 2K(z,gamma), mismatch.
Dq_single = true_sum - K(z, gamma)
print("D (single-atom) at eta=0 :", sp.simplify(Dq_single.subs(eta,0)))
# -> nonzero (= K(z,gamma)), so the correct matching MUST use 2 height atoms.
# CONCLUSION: quadruple = 2 paired pullback atoms (u1,u2); height = 2 paired atoms at gamma.

# ---------------------------------------------------------------
# TASK 2: Im D_quad(x+iy) symbolic
# ---------------------------------------------------------------
print("\n=== TASK 2: Im D_quad symbolic ===")
ImD = sp.im(Dq)
ImD = sp.simplify(ImD)
print("Im D_quad =")
sp.pprint(ImD)

# Factor / put over common form
ImD_t = sp.together(ImD)
print("\nTogether form:")
sp.pprint(ImD_t)

# ---------------------------------------------------------------
# Clean decomposition. Define a single-zero displacement at a + i*b
# vs real height a, then symmetrize x -> -x.
# Im[ 1/(z-w) ] = -(y - Im w)/|z-w|^2.
# Build Im D as sum of single Cauchy imaginary parts.
# ---------------------------------------------------------------
def im_cauchy(zz, w):
    # Im 1/(zz - w)
    return sp.im(1/(zz - w))

# true atoms at the 4 pullback points
pts_true = [gamma - sp.I*eta, -gamma + sp.I*eta, -gamma - sp.I*eta, gamma + sp.I*eta]
# height: 2 atoms at gamma, 2 at -gamma (paired => +-gamma, two copies)
pts_height = [gamma, gamma, -gamma, -gamma]

ImD2 = sum(im_cauchy(z, w) for w in pts_true) - sum(im_cauchy(z, w) for w in pts_height)
ImD2 = sp.simplify(ImD2)
print("\n=== cross-check Im D via explicit atoms ===")
print("Im D matches:", sp.simplify(ImD2 - ImD) == 0)

# ---------------------------------------------------------------
# TASK 3: small-eta expansion
# ---------------------------------------------------------------
print("\n=== TASK 3: small-eta expansion of Im D_quad ===")
ser = sp.series(ImD, eta, 0, 4).removeO()
ser = sp.simplify(ser)
print("Series to O(eta^4):")
sp.pprint(ser)

# coefficient of eta^1 and eta^2
c1 = sp.simplify(ImD.diff(eta).subs(eta,0))
c2 = sp.simplify(ImD.diff(eta,2).subs(eta,0)/2)
print("\nLinear coeff (d/deta at 0):", sp.simplify(c1))
print("\nQuadratic coeff (1/2 d2/deta2 at 0):")
sp.pprint(sp.simplify(c2))

# ---------------------------------------------------------------
# TASK 3 (cont): sign of the eta^2 coefficient C2(x,y,gamma)
# ImD ~ C2 * eta^2 + O(eta^4).  Leading sign for small eta>0 = sign(C2).
# C2 = 2y [ (3(g-x)^2 - y^2)(y^2+(g+x)^2)^3 + (3(g+x)^2 - y^2)(y^2+(g-x)^2)^3 ]
#      / [ (y^2+(g-x)^2)^3 (y^2+(g+x)^2)^3 ]
# Denominator > 0, factor 2y>0 in UHP. Sign governed by numerator bracket N(x,y,g).
# ---------------------------------------------------------------
a = (gamma - x)**2
b = (gamma + x)**2
N = (3*a - y**2)*(y**2 + b)**3 + (3*b - y**2)*(y**2 + a)**3
N = sp.expand(N)
print("\n=== TASK 3 sign: numerator N of C2 (drop positive 2y/denominator) ===")
sp.pprint(sp.collect(N, y))

# Is N sign-definite? Test: small y (near real axis) vs large y.
# small y -> leading 3a*b^3 + 3b*a^3 = 3ab(a^2+b^2) >0  => C2>0 near axis
# large y -> -y^2*(y^6)-y^2*(y^6) ~ -2 y^8 <0           => C2<0 high up
print("\nN as y->0+ (leading):", sp.simplify(N.subs(y,0)))
print("N leading term in y (large y):", sp.LT(sp.Poly(N, y)))

# Near-axis numerator P(x) := 6g^8+24g^6x^2-60g^4x^4+24g^2x^6+6x^8 (set y=0).
# Factor / find where positive.
P = 6*gamma**8 + 24*gamma**6*x**2 - 60*gamma**4*x**4 + 24*gamma**2*x**6 + 6*x**8
print("\n=== near-axis numerator P(x) at y->0 ===")
print("P(x=0):", P.subs(x,0), " (=6 g^8 >0  => C2>0 at x=0, small y)")
# So directly above the origin (x=0, small y>0), small eta>0 => Im D_quad > 0.
# Check P sign over x: roots
Pp = sp.Poly(P, x)
print("P roots (x^2 = t):")
t = sp.symbols('t', positive=True)
Pt = 6*gamma**8 + 24*gamma**6*t - 60*gamma**4*t**2 + 24*gamma**2*t**3 + 6*t**4
rts = sp.nroots(sp.Poly(Pt.subs(gamma,1), t))
print("  (gamma=1) t-roots:", rts)

# ---------------------------------------------------------------
# TASK 4: blow-up near off-line true pullback pole gamma + i*eta (UHP), eta>0
# approach from below: z = gamma + i*(eta - s), s->0+ . True atom 1/(z-(gamma+i eta))
# = 1/(-i s) -> Im = 1/s -> +infinity.
# ---------------------------------------------------------------
print("\n=== TASK 4: blow-up near gamma + i*eta ===")
s = sp.symbols('s', positive=True)
zb = gamma + sp.I*(eta - s)
ImD_pole = sp.im(true_sum.subs({x: sp.re(zb)})) # safer: substitute numerically
# do numeric
import mpmath as mp
def ImDq_num(xv, yv, gv, hv):
    zz = mp.mpf(xv) + 1j*mp.mpf(yv)
    pts_t = [gv-1j*hv, -gv+1j*hv, -gv-1j*hv, gv+1j*hv]
    pts_h = [gv, gv, -gv, -gv]
    val = sum(1/(zz-w) for w in pts_t) - sum(1/(zz-w) for w in pts_h)
    return float(val.imag)

gv, hv = 1.0, 0.3
print("approach gamma+i*eta = 1+0.3i from below (y = eta - s):")
for sv in [0.1,0.01,1e-3,1e-4,1e-5]:
    print(f"  s={sv:8.0e}  Im D_quad = {ImDq_num(gv, hv-sv, gv, hv):+.4e}   (~1/s={1/sv:.2e})")

# ---------------------------------------------------------------
# TASK 5: decisive verdict. Is Im D_quad <= 0 on all UHP? Scan for positive values.
# ---------------------------------------------------------------
print("\n=== TASK 5: scan sign of Im D_quad over UHP ===")
import random
gv, hv = 1.0, 0.2
pos_witness = None; neg_witness=None
maxpos=-1e9; minneg=1e9
random.seed(0)
for _ in range(200000):
    xv = random.uniform(-3,3); yv=random.uniform(1e-3,3)
    v = ImDq_num(xv,yv,gv,hv)
    if v>maxpos: maxpos=v; pos_witness=(xv,yv)
    if v<minneg: minneg=v; neg_witness=(xv,yv)
print(f"gamma={gv}, eta={hv}")
print(f"  MAX Im D_quad = {maxpos:+.4f} at (x,y)={pos_witness}")
print(f"  MIN Im D_quad = {minneg:+.4f} at (x,y)={neg_witness}")

# clean small-eta witness above origin
print("\nClean small-eta witness (x=0, small y, eta=0.05, gamma=1):")
for yv in [0.05,0.1,0.2]:
    print(f"  x=0,y={yv}: Im D_quad = {ImDq_num(0.0,yv,1.0,0.05):+.4e}  (predict +6 eta^2 g^8/...)")

# negative-region witness (high up)
print("\nNegative-region witness (x=0, large y):")
for yv in [2.0,3.0,5.0]:
    print(f"  x=0,y={yv}: Im D_quad = {ImDq_num(0.0,yv,1.0,0.3):+.4e}")
print("\nVERDICT: Im D_quad takes POSITIVE values in UHP  =>  D_off carries RH-strength.")

# ---------------------------------------------------------------
# Verify eta^2 coefficient at x=0 against numerics
# C2(x=0): N(0,y,g) = 6 g^8 - 2 y^8 + 12 g^4 y^4 + 16 g^6 y^2 ... evaluate
# Use full C2 expression.
# ---------------------------------------------------------------
print("\n=== eta^2 coeff check at x=0, gamma=1 ===")
C2_expr = sp.simplify(c2)  # 1/2 d2/deta2 Im D at eta=0
C2_x0 = sp.simplify(C2_expr.subs({x:0, gamma:1}))
print("C2(x=0,g=1,y) =", C2_x0)
for yv in [0.05,0.1,0.2,2.0,3.0]:
    pred = float(C2_x0.subs(y,yv))* (0.05**2 if yv<1 else 0.3**2)
    hh = 0.05 if yv<1 else 0.3
    num = ImDq_num(0.0,yv,1.0,hh)
    print(f"  y={yv}: C2*eta^2={float(C2_x0.subs(y,yv))*hh**2:+.4e}  numeric={num:+.4e}")
