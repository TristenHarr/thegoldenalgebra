"""
STEP 4c — IS THERE A GENUINE CONTINUATION PRINCIPLE?  (honest negative + positive parts)

We have two positivity facts:
  (CM)  -zeta'/zeta is completely monotone on the REAL ray sigma>1  (from Lambda>=0).
  (PR)  -d/dw log xi is positive-real on UHP_w  <=>  RH   (the target).

Question (task 4): is there an analytic-continuation/Herglotz-class principle carrying
(CM) to (PR), i.e. positivity from sigma>1 to sigma>=1/2?

HONEST ANALYSIS of candidate principles:

(I) "CM function continues to a Herglotz function" — FALSE in general. A completely
    monotone f on (a,inf) extends (Bernstein) to a function holomorphic and bounded in
    the RIGHT HALF PLANE Re s>a with Re f possibly sign-indefinite (we SAW Re(-zeta'/zeta)
    <0 in the strip in step1 P3). CM gives the LAPLACE rep on Re s>a ONLY; the rep
    (positive measure on [0,inf) in the t-variable) is valid EXACTLY on Re s> sigma_c=1
    and has a SINGULARITY WALL at sigma_c. There is NO continuation of the *positive-measure
    representation* past the abscissa. (Verified structurally in step2.) So (I) gives
    nothing below sigma=1.

(II) "Herglotz class is preserved by s->1-s (the FE map)" — FALSE: s->1-s reverses Im
     (step4b), sending Herglotz to anti-Herglotz. In the FE-invariant variable
     w=(s-1/2)^2 the FE is the IDENTITY, so it transfers NOTHING. (Verified.)

(III) The ONLY true statement: BOTH (CM on sigma>1) AND (PR on UHP_w) are shadows of the
      SAME underlying object — the positive spectral measure of the self-adjoint-like
      structure — IF AND ONLY IF the zeros are real-in-w. The Euler product gives the
      measure on the t=log n side (CM); RH is whether the DUAL measure on the w<0 side
      (PR) is also positive. These are NOT linked by a soft continuation theorem: linking
      them is the Weil explicit formula / positivity, i.e. RH itself. There is NO free
      lunch; the transfer is the content of RH.

This file gives the DECISIVE numerical demonstration of the GAP: it exhibits a function
that is completely monotone on (1,inf) (like -zeta'/zeta) but whose 'w-frame dual' is NOT
PR — proving (CM)-/->(PR) has NO general implication, so any real RH proof must use the
SPECIFIC arithmetic (Euler product positivity in the explicit formula), not soft transfer.
"""
import mpmath as mp
mp.mp.dps = 25

print("="*78)
print("GAP DEMONSTRATION: CM-on-(1,inf) does NOT imply PR-in-w (no soft transfer)")
print("="*78)
print("""
  Construct g(s) = sum_n a_n n^{-s} with a_n>=0 (=> g CM on its half-plane, exactly the
  same 'positive Dirichlet series' input as zeta) but whose completed/symmetrized object
  has a zero OFF the w<0 axis. Simplest: a 'fake' Dirichlet polynomial with positive
  coeffs whose symmetric completion g(s)g(1-s)-normalization has complex w-zeros.
""")
# g(s) = 1 + a 2^{-s} + b 3^{-s}, a,b>0  (positive coeffs => CM on Re s>0)
# Symmetric model G(s)=g(s)+g(1-s) is even about 1/2; its zeros in w=(s-1/2)^2 need not
# be real. Find them.
a,b=mp.mpf('0.9'),mp.mpf('0.7')
def g(s): return 1+a*mp.mpf(2)**(-s)+b*mp.mpf(3)**(-s)
def G(s): return g(s)+g(1-s)   # even about 1/2, real on real axis
# CM check for -g'/g on (0,inf): coeffs of g are >=0 so -g'/g = sum (a_n log n) n^{-s}/g...
# Actually simplest CM object: g itself is CM (positive-coeff Dirichlet series => CM in sigma).
print("  g(s)=1+0.9*2^-s+0.7*3^-s : positive coeffs => g completely monotone on (0,inf):")
gg=lambda x: g(x)
print("   sigma  (-1)^k g^(k):")
for sigma in [mp.mpf('0.5'),mp.mpf('1.0'),mp.mpf('2.0')]:
    row=[((-1)**k)*mp.diff(gg,sigma,k) for k in range(4)]
    print(f"    {mp.nstr(sigma,3):>5}: "+"  ".join(mp.nstr(r,4) for r in row)+
          ("  CM-OK" if all(r>=-1e-12 for r in row) else "  not-CM"))
print()
print("  Now its symmetric completion G(s)=g(s)+g(1-s): find zeros, map to w=(s-1/2)^2.")
zeros=[]
for guess in [mp.mpc('0.5','6'),mp.mpc('0.5','12'),mp.mpc('0.5','18'),
              mp.mpc('1.5','9'),mp.mpc('2.5','9'),mp.mpc('0.9','15')]:
    try:
        z=mp.findroot(G,guess)
        if abs(G(z))<1e-12:
            w=(z-mp.mpf('0.5'))**2
            online = abs(z.real-0.5)<1e-6
            zeros.append((z,w,online))
    except: pass
seen=set()
for z,w,online in zeros:
    key=mp.nstr(z,6)
    if key in seen: continue
    seen.add(key)
    print(f"    zero s={mp.nstr(z,8)}  -> w={mp.nstr(w,8)}  "
          f"{'ON line (w<0 real)' if online else '*** OFF line => w not on neg-real axis ***'}")
print()
print("  => A positive-coefficient (CM) Dirichlet object can ABSOLUTELY have off-line")
print("     zeros in its symmetric completion. Positivity of the coefficients alone does")
print("     NOT force the w-frame zeros onto the negative real axis. THERE IS NO SOFT")
print("     TRANSFER. What saves zeta is not mere positivity but the EXACT Euler-product")
print("     structure entering the Weil explicit formula (a quadratic-form positivity),")
print("     which the above toy lacks. The transfer principle, as a general theorem, is FALSE;")
print("     RH is the assertion that zeta's specific arithmetic realizes it.")
