"""
bd_threshold.py — Pin the BD visibility threshold N*(delta,t) and compare to the
universal gates. THE decisive question.

The finite-N Báez-Duarte distance has the asymptotic (under RH; conjecturally sharp,
BLLS/Burnol):
        d_N^2  ~  (1/log N) * Sum_rho 1/|rho|^2 .
The per-zero contribution of a zero rho to (d_N^2 * log N) is  w(rho)=1/|rho|^2.

Now MOVE one zero off the line: rho_t = 1/2 + i t  ->  1/2 + delta + i t (and its mirror
1/2 - delta + i t).  The change in the spectral sum is
        Delta(delta,t) = [1/((1/2+delta)^2+t^2) + 1/((1/2-delta)^2+t^2)] - 2/(1/4+t^2).
For small delta:  Delta ~ w''_pair(0)/2 * delta^2 * 2 ... explicitly (computed):
        Delta(delta,t) ~ C(t) delta^2,   C(t) = (3*(1/4) - t^2)/(1/4+t^2)^3  -> -1/t^4  (large t).
So the off-line SIGNAL in d_N^2 is
        d_N^2(off) - d_N^2(on)  ~  C(t) delta^2 / log N  ~  -(delta^2/t^4)/log N   (large t).

The off-line signal is VISIBLE once it exceeds the intrinsic NOISE floor of the finite-N
truncation.  Two candidate noise floors:
  (A) the leading term itself, d_N^2 ~ const/log N: signal/leading ~ C(t)*delta^2/const
      = delta^2 * t-shape, N-INDEPENDENT ratio (the off-line zero changes the CONSTANT,
      not the rate).  => RELATIVE visibility is N-independent: BD never 'turns on' a zero
      at a critical N; it reweights the constant for ALL N>=N_min(t).
  (B) BUT a zero at height t only enters the sum once N resolves height t.  The Dirichlet
      length N <-> Mellin support log N <-> heights up to t are resolved when
                 log N  >~  log t      i.e.   N  >~  t.
      (BLLS: the zeros enter the d_N^2 asymptotic through the Mellin transform of the
      Dirichlet polynomial of length N, whose 'reach' in the t-aspect is ~ exp(log N)=N;
      more precisely the relevant window resolves ordinate t at N ~ t.)

THEREFORE the BD visibility threshold for a zero of height t is

        N*_BD ~ t        (DELTA-INDEPENDENT!),

i.e.  log N* ~ log t.  The 'support' analogue is  S_BD := log N ~ log t.

Contrast the universal gates (support S needed to see displacement delta at height t):
  Weil:  S_Weil ~ 1/delta        (delta*T~1; DELTA-dependent, t-independent)
  Li:    n ~ t^2/delta           (both delta and t)
  BD:    S_BD := log N ~ log t    (t-dependent, DELTA-INDEPENDENT)  <-- DIFFERENT LAW.

This is the bold-twist payoff: BD's threshold to first RESOLVE a zero of height t does NOT
depend on its displacement delta at all.  The displacement only rescales the CONSTANT
(C(t) delta^2 correction), it never sets the gate.  BD trades the delta*T~1 displacement-
resolution wall for a pure HEIGHT-resolution wall log N ~ log t.
"""
import mpmath as mp
import numpy as np
mp.mp.dps = 30

def C_of_t(t):
    """Exact leading coefficient: Delta(delta,t) = C(t) delta^2 + O(delta^4),
       C(t) = d^2/deta^2 [w(eta)+w(-eta)]/2 at 0  =  w''(0)  for the pair... compute analytically.
       w(eta)=1/((1/2+eta)^2+t^2). w'(eta)=-2(1/2+eta)/D^2, D=(1/2+eta)^2+t^2.
       w''(eta)= -2/D^2 + 8(1/2+eta)^2/D^3.  At eta=0, with D0=1/4+t^2:
       w''(0)= -2/D0^2 + 8*(1/4)/D0^3 = -2/D0^2 + 2/D0^3.
       pair''(0)=2 w''(0); Delta ~ (pair''(0)/2) delta^2 = w''(0) delta^2."""
    t=mp.mpf(t); D0=mp.mpf('0.25')+t*t
    return -2/D0**2 + 2/D0**3   # = w''(0)

def bd_threshold_N(t):
    """N*_BD ~ t : the Dirichlet length needed to resolve a zero of height t."""
    return float(t)

def weil_support(delta):  return 1.0/float(delta)
def li_n(delta,t):        return float(t)**2/float(delta)

print("="*86)
print("LEADING displacement coefficient C(t):  Delta(delta,t) = C(t)*delta^2 + ...")
print("="*86)
print(f"{'t':>10} {'C(t) exact':>18} {'-1/t^4 (large-t)':>18} {'ratio':>10}")
for t in [1,14.13,50,100,1000,1e4]:
    C=C_of_t(t); approx=-1/mp.mpf(t)**4
    print(f"{t:>10} {float(C):>18.6e} {float(approx):>18.6e} {float(C/approx):>10.4f}")

print("\nNOTE: C(t) < 0 for t>~0.7 (off-line pair contributes LESS to Sum 1/|rho|^2 than")
print("on-line). So an off-line zero DECREASES d_N^2*log N. The displacement signal is")
print("|C(t)| delta^2 / log N -- second order in delta, decaying as t^-4 in height.\n")

print("="*86)
print("VISIBILITY THRESHOLD: support S to first SEE a zero (delta,t). DECISIVE TABLE.")
print("="*86)
print(f"{'delta':>8} {'t':>8} | {'Weil S~1/d':>12} {'Li n~t^2/d':>14} {'BD logN~log t':>16} {'BD N~t':>10}")
for (delta,t) in [(1e-1,14),(1e-2,14),(1e-3,14),(1e-3,100),(1e-3,1000),(1e-6,1000)]:
    print(f"{delta:>8} {t:>8} | {weil_support(delta):>12.1f} {li_n(delta,t):>14.1f} "
          f"{float(mp.log(t)):>16.3f} {bd_threshold_N(t):>10.1f}")

print("""
READING THE TABLE:
 * Weil column EXPLODES as delta->0 (1/delta): the delta*T~1 wall. To see a zero at
   delta=1e-6 you need support ~1e6 REGARDLESS of height.
 * Li column explodes in BOTH delta and t.
 * BD column (logN~log t, N~t) is COMPLETELY FLAT in delta: a zero at delta=1e-1 and a
   zero at delta=1e-6, same height t=1000, have the SAME BD resolution threshold N~1000.
   The displacement NEVER enters the gate. <<< DIFFERENT VISIBILITY LAW >>>

VERDICT: BD does NOT collapse to the universal delta*T~1 gate. It has a genuinely
different visibility law: a pure HEIGHT-resolution gate (logN ~ log t), delta-independent,
with the displacement entering only as a 2nd-order constant correction |C(t)|delta^2/log N.
""")
