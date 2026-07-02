"""
ARITHMETIC TRANSFER PRINCIPLE — STEP 4 (the transfer question)
================================================================
Does the FE map  s |-> 1-s  preserve the relevant positivity class, structurally?

SETUP.  Let  L(s) = xi'/xi(s).  FE  xi(s)=xi(1-s)  =>  L(s) = -L(1-s).   (ODD about 1/2)
On Re s>1, write  L(s) = ARCH(s) - PRIME(s) + POLEpart, where
   PRIME(s) = sum Lambda(n) n^{-s}   (positive measure, CM in sigma>1),
and ARCH(s) = (1/2)log pi part + (1/2) psi(s/2) part + s(s-1) logarithmic-derivative part.

The completed object is, by Hadamard,
   xi'/xi(s) = sum_rho 1/(s-rho)   (symmetric-summed; rho and 1-rho paired),  + const.
This is a sum of  1/(s-rho).  Each term 1/(s-rho) is a HERGLOTZ-type kernel:
   Im( -1/(s-rho) ) for Im s>0 has a definite sign ONLY if rho is real.
   For rho on the critical line (rho=1/2+i gamma), the pair  1/(s-rho)+1/(s-(1-rho))
   = 1/(s-1/2-i gamma)+1/(s-1/2+i gamma)  is REAL & even in gamma.

THE PRECISE TRANSFER STATEMENT we test:
   Consider  G(s) := (s-1/2) * xi'/xi(s)... no. Better: the object whose positivity
   is EQUIVALENT to RH is the de Branges / Herglotz function built from xi. We test the
   cleanest one:

   PHI(s) := xi'/xi(s) / (s-1/2)       [removes the odd symmetry; even about 1/2]
   By FE, PHI(s)=PHI(1-s) is EVEN about 1/2.  We ask whether PHI maps the right
   half-plane Re s>1/2 into a half-plane (Herglotz w.r.t. the variable (s-1/2)^2).

CHANGE OF VARIABLE  w = (s-1/2)^2.  FE s<->1-s becomes w<->w (FIXED). So functions
even about 1/2 are single-valued in w.  Re s>1/2  <=>  w in C \ (-inf,0]  roughly.
A zero rho=1/2+i gamma  <=>  w = -gamma^2 < 0  (NEGATIVE REAL AXIS in w).
A zero OFF the line, rho=beta+i gamma (beta>1/2) <=> w=(beta-1/2+i gamma)^2 OFF the
neg-real axis.

CLAIM TO TEST (the would-be transfer principle):
   "xi, as a function of w=(s-1/2)^2, is in the Laguerre-Polya / Hermite-Biehler class
    => all its zeros (in w) lie on the NEGATIVE real w-axis => all rho on the line."
   The HERGLOTZ object is  M(w) := d/dw log xi  =  xi'/xi(s) * 1/(2(s-1/2)) = PHI(s)/2.
   RH  <=>  M(w) is a Herglotz (Pick) function of w mapping UHP_w -> LHP_w (or the sign
   convention giving a positive measure on (-inf,0]):  M(w)= c + integral dmu(t)/(t-w),
   mu>=0 supported on (-inf,0]  <=>  all zeros at w<0  <=>  RH.

   This M(w) Herglotz-ness is the ARITHMETIC TRANSFER TARGET. We test whether the
   PRIME-side positivity (Lambda>=0) feeds Herglotz-positivity of M(w), and whether
   the archimedean part is the OBSTRUCTION or the HELP.
"""
import mpmath as mp
mp.mp.dps = 30

def xi(s):
    return mp.mpf('0.5')*s*(s-1)*mp.pi**(-s/2)*mp.gamma(s/2)*mp.zeta(s)

def xilog_deriv(s, h=mp.mpf('1e-12')):
    # xi'/xi via log-derivative; use mpmath diff of log xi
    return mp.diff(lambda z: mp.log(xi(z)), s)

def M_of_w(w):
    # w=(s-1/2)^2 ; pick s=1/2+sqrt(w). M(w)=d/dw log xi = (xi'/xi)(s) / (2(s-1/2))
    sq = mp.sqrt(w)
    s = mp.mpf('0.5') + sq
    L = xilog_deriv(s)
    return L/(2*sq)

print("="*78)
print("STEP 4a — M(w)=d/dw log xi, w=(s-1/2)^2.  RH <=> M Herglotz on UHP_w with")
print("           measure on (-inf,0].  TEST: Im M(w) sign for Im w>0.")
print("="*78)
print("  Herglotz (this orientation): for Im w>0, a function with positive measure")
print("  mu>=0,  M(w)=integral dmu(t)/(t-w)  has  Im M(w) = integral Im 1/(t-w) dmu")
print("        = integral (Im w)/|t-w|^2 dmu  > 0.  So RH => Im M(w)>0 for Im w>0.")
print()
print(f"{'Re w':>10} {'Im w':>8} {'Re M':>16} {'Im M':>16}  {'ImM sign'}")
allpos=True
for rw in [mp.mpf('-50'), mp.mpf('-200'), mp.mpf('0'), mp.mpf('50'), mp.mpf('200')]:
    for iw in [mp.mpf('1'), mp.mpf('10'), mp.mpf('50')]:
        w=mp.mpc(rw,iw)
        try:
            M=M_of_w(w)
        except Exception as e:
            print(f"{mp.nstr(rw,4):>10} {mp.nstr(iw,3):>8}  err {e}"); continue
        if M.imag<=0: allpos=False
        print(f"{mp.nstr(rw,4):>10} {mp.nstr(iw,3):>8} {mp.nstr(M.real,8):>16} "
              f"{mp.nstr(M.imag,8):>16}  {'+' if M.imag>0 else '-'}")
print(f"\n  Im M(w)>0 throughout sampled UHP_w: {allpos}")
print("  => consistent with M Herglotz in w  <=>  RH (numerically, not assuming RH).")

print()
print("="*78)
print("STEP 4b — DOES THE FE MAP PRESERVE THE HERGLOTZ CLASS *STRUCTURALLY*?")
print("="*78)
print("""
  The FE s<->1-s in the w-variable is the IDENTITY (w=(s-1/2)^2 invariant). So the
  question 'does FE preserve Herglotz-in-s' is the WRONG question: in s, the map
  s->1-s sends UHP_s to UHP_s (it's z->1-z, fixing the real axis orientation...
  actually 1-s reflects Re but PRESERVES Im sign: Im(1-s)=-Im s, it FLIPS Im).
  So s->1-s maps UHP_s -> LHP_s.  A Herglotz function (UHP->UHP) composed with an
  Im-flipping involution becomes UHP->LHP, i.e. an ANTI-Herglotz. Hence:

    *** The FE map s->1-s is Im-sign-REVERSING; it sends the Herglotz class to its
        NEGATIVE.  It does NOT preserve Herglotz-in-s. ***

  This is exactly why -zeta'/zeta being CM-in-sigma (a half-line, Im-blind statement)
  is the structure that the FE *can* interact with, while Herglotz-in-s is destroyed.
  The ONLY frame in which the FE acts trivially (preserving a positivity class) is the
  w=(s-1/2)^2 frame, where FE=identity. In THAT frame the target is 'M(w) Herglotz',
  and the FE gives NOTHING for free (it's the identity) — so there is NO structural
  transfer from the FE alone.  The content must come from the actual location of
  zeros, i.e. RH is not a corollary of FE+positivity.
""")

print("="*78)
print("STEP 4c — Quantify: split M(w) = ARCH-part + ZEROS-part and see which carries")
print("           the Herglotz positivity, and whether ARCH alone is already Herglotz.")
print("="*78)
# d/ds log( pi^{-s/2} Gamma(s/2) * (1/2) s(s-1) ) = arch + poly part; subtract to get
# the pure zeta zeros contribution.  arch L_arch(s):
def L_arch(s):
    g = lambda z: mp.log(mp.pi**(-z/2)*mp.gamma(z/2)*mp.mpf('0.5')*z*(z-1))
    return mp.diff(g, s)
def M_arch(w):
    sq=mp.sqrt(w); s=mp.mpf('0.5')+sq
    return L_arch(s)/(2*sq)
def M_zeros(w):
    return M_of_w(w)-M_arch(w)   # = d/dw log zeta-part... (xi/arch = zeta basically)
print(f"{'Re w':>10} {'Im w':>8} {'Im M_arch':>16} {'Im M_zeros':>16}")
for rw in [mp.mpf('-200'), mp.mpf('0'), mp.mpf('200')]:
    for iw in [mp.mpf('10'), mp.mpf('50')]:
        w=mp.mpc(rw,iw)
        ma=M_arch(w); mz=M_zeros(w)
        print(f"{mp.nstr(rw,4):>10} {mp.nstr(iw,3):>8} {mp.nstr(ma.imag,8):>16} "
              f"{mp.nstr(mz.imag,8):>16}")
print("""
  If Im M_arch>0 AND Im M_zeros>0 separately, BOTH pieces are Herglotz and the sum is
  trivially Herglotz -> RH would be 'easy'. If one piece has WRONG sign, Herglotz-ness
  of the total is a delicate cancellation = the real content of RH.
""")
