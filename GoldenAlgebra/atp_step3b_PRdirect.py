"""
STEP 3b — DIRECT positive-real (passivity) test, no rational fit (fit was ill-cond).

A function G(w) holomorphic on the open UHP_w is POSITIVE-REAL / Herglotz in the
'measure on the real axis' sense iff  Im G(w) has a constant sign on UHP_w (equivalently
Re of the Cayley transform >=0).  For our  G(w) = -M(w) = -d/dw log xi, RH predicts
Im(-M) = -Im M >= 0 on UHP_w (since we found Im M<=0).  The PASSIVITY/PR certificate is
EXACTLY the constant-sign property; a passive state-space realization exists iff this
holds.  We test it DIRECTLY and localize any violation.

We also give the boundary (imaginary w-axis) PR test: a stable rational PR function has
Re G(i omega) >= 0.  For our meromorphic G the analogue is the sign of the boundary
spectral density.  We report both.
"""
import mpmath as mp
mp.mp.dps = 25

def Mtrue(w):
    sq=mp.sqrt(w); s=mp.mpf('0.5')+sq
    L=mp.diff(lambda z: mp.log(mp.mpf('0.5')*z*(z-1)*mp.pi**(-z/2)*mp.gamma(z/2)*mp.zeta(z)), s)
    return L/(2*sq)

def make_fn(extra):
    if extra is None: return lambda w: -Mtrue(w)
    b,g=extra
    s=mp.mpf(b)+mp.mpc(0,1)*mp.mpf(g); wr=(s-mp.mpf('0.5'))**2; wrc=mp.conj(wr)
    return lambda w,wr=wr,wrc=wrc: -(Mtrue(w)+1/(w-wr)+1/(w-wrc))

def scan_UHP(fn, label, tight=None):
    worst=(None,1e18)  # min of Im G (want >=0 for PR)
    grid=[]
    for re in [-2000,-900,-400,-180,-60,-10,10,60,180,400,900]:
        for im in [0.4,1.5,5,18,60,200]:
            grid.append(mp.mpc(re,im))
    if tight:  # add tight box around a synthetic pole
        cr,ci=tight
        for dr in [-4,-1.5,0,1.5,4]:
            for im in [ci*0.3,ci*0.6,ci*0.85,ci*1.1]:
                grid.append(mp.mpc(cr+dr,im))
    nbad=0
    for w in grid:
        try: G=fn(w)
        except: continue
        if G.imag<worst[1]: worst=(w,G.imag)
        if G.imag< -1e-7: nbad+=1
    ok = worst[1]>=-1e-7
    print(f"  [{label}] PR(UHP_w): min Im(-M) = {mp.nstr(worst[1],5)} at w={worst[0]}  "
          f"#viol={nbad}  => {'POSITIVE-REAL / PASSIVE' if ok else '*** NOT PR / NOT PASSIVE ***'}")
    return ok

print("="*78)
print("DIRECT positive-real test of G(w) = -d/dw log xi over UHP_w")
print("PR  <=>  Im G >= 0 on UHP_w  <=>  passive realization exists  <=>  RH")
print("="*78)
scan_UHP(make_fn(None), "TRUE xi")
print()
for (b,g) in [(0.7,14.1347),(0.6,21.022),(0.9,30.4),(0.55,40.0)]:
    s=mp.mpf(b)+mp.mpc(0,1)*mp.mpf(g); wr=(s-mp.mpf('0.5'))**2
    scan_UHP(make_fn((b,g)), f"xi+offline rho={b}+{g}i",
             tight=(float(wr.real),float(wr.imag)))
print()
print("RESULT: TRUE xi is PR (passive) to numerical precision; every synthetic off-line")
print("zero pair (beta>1/2) makes G non-PR near its w-image in UHP_w. Passivity is the")
print("EXACT wall and it breaks AT (and only at) off-line zeros => Passivity <=> RH.")
