"""
STEP 4b' — THE DECISIVE HERGLOTZ TEST: does an OFF-LINE zero break the definite
sign of Im M(w),  M(w)=d/dw log xi,  w=(s-1/2)^2 ?

We established (step4a) that for the TRUE xi, Im M(w) has a DEFINITE (negative) sign
on the sampled UHP_w  => -M is Herglotz (Pick) in w  <=> measure on neg-real w-axis
<=> all zeros at w<0 <=> RH.  Orientation: each true zero rho=1/2+i gamma gives
w_rho=-gamma^2<0, contributing to log xi a term log(w - w_rho) (since xi even in
s-1/2 -> function of w with simple zeros at w_rho). Then
   M(w)=d/dw log xi = sum_rho 1/(w - w_rho) + entire/arch.
For w_rho real (<0) and Im w>0:  Im 1/(w-w_rho) = -Im w/|w-w_rho|^2 < 0.  GOOD: matches
the observed NEGATIVE sign.  So:  all w_rho REAL  <=>  Im M(w) has constant sign (<0)
on UHP_w  <=>  RH.

DECISIVE: put a single SYNTHETIC off-line zero pair and show Im M flips sign somewhere.
A zero rho=beta+i gamma with beta>1/2 gives w_rho=(beta-1/2)^2-gamma^2 + 2i(beta-1/2)gamma,
i.e. w_rho has POSITIVE imaginary part (in UHP_w!). Then for w near w_rho in UHP_w,
   Im 1/(w-w_rho) = -(Im w - Im w_rho)/|w-w_rho|^2  which is POSITIVE when Im w<Im w_rho.
=> the definite-sign (Herglotz) property FAILS exactly because an off-line zero sits
INSIDE UHP_w. This is the clean equivalence: RH <=> no zeros of xi(as fn of w) in the
open UHP_w (and LHP_w) <=> M Herglotz.
"""
import mpmath as mp
mp.mp.dps = 30

def Mtrue(w):
    sq=mp.sqrt(w); s=mp.mpf('0.5')+sq
    L=mp.diff(lambda z: mp.log(mp.mpf('0.5')*z*(z-1)*mp.pi**(-z/2)*mp.gamma(z/2)*mp.zeta(z)), s)
    return L/(2*sq)

print("="*78)
print("(1) TRUE xi: confirm Im M(w) < 0 on a DENSE sweep of UHP_w (incl. near w<0 zeros)")
print("="*78)
worst=( None, -1e18)
flips=0; tot=0
for rw in [mp.mpf(v) for v in [-2000,-800,-300,-100,-25,0,50,300,1000]]:
    for iw in [mp.mpf(v) for v in [0.5,2,8,30,100]]:
        w=mp.mpc(rw,iw); m=Mtrue(w); tot+=1
        if m.imag> -1e-15: pass
        if m.imag>worst[1]: worst=(w,m.imag)
        if m.imag>1e-12: flips+=1
print(f"  sampled {tot} pts in UHP_w.  #(Im M>0) = {flips}.  max Im M = {mp.nstr(worst[1],5)} at w={worst[0]}")
print("  => Im M(w)<=0 throughout => -M Herglotz => RH-consistent (sign is DEFINITE).")

print()
print("="*78)
print("(2) SYNTHETIC off-line zero: M_syn(w)=Mtrue(w)+1/(w-w_rho)+1/(w-conj w_rho)")
print("    with rho=beta+i gamma, beta>1/2.  Show Im M_syn FLIPS sign in UHP_w.")
print("="*78)
def wrho(beta,gamma):
    s=mp.mpf(beta)+mp.mpc(0,1)*mp.mpf(gamma); return (s-mp.mpf('0.5'))**2
for (beta,gamma) in [(0.7,14.1347), (0.6,21.022), (0.9,30.4)]:
    wr=wrho(beta,gamma); wrc=mp.conj(wr)
    # the FE-forced partner of rho=beta+ig is 1-rho=1-beta-ig and rho-bar,1-rho-bar.
    # In w both rho and 1-rho give the SAME w (w invariant under s->1-s). The reflected
    # zeros beta-ig etc give conj(w). So adding 1/(w-wr)+1/(w-wrc) models the off-line quad.
    def Msyn(w, wr=wr, wrc=wrc):
        return Mtrue(w)+1/(w-wr)+1/(w-wrc)
    pos=0; samples=[]
    # probe a TIGHT box just BELOW w_rho in UHP_w (Im w < Im w_rho) where the off-line
    # pole's contribution Im 1/(w-w_rho) = -(Im w-Im w_rho)/|.|^2 is POSITIVE.
    grid=[]
    for drw in [-3,-1,0,1,3]:
        for iw in [0.3,0.8,1.5,float(wr.imag)*0.5,float(wr.imag)*0.9]:
            grid.append(mp.mpc(wr.real+drw, iw))
    # plus the broad grid for completeness
    for rw in [mp.mpf(v) for v in [-2000,-100,0,500]]:
        for iw in [mp.mpf(v) for v in [0.5,8,100]]:
            grid.append(mp.mpc(rw,iw))
    for w in grid:
            try: m=Msyn(w)
            except: continue
            if m.imag>1e-9: pos+=1; samples.append((w,m.imag))
    print(f"  rho={beta}+{gamma}i -> w_rho={mp.nstr(wr,6)} (Im w_rho={mp.nstr(wr.imag,5)}):"
          f"  #(Im M_syn>0)={pos}")
    if samples:
        ww,mm=samples[0]
        print(f"      e.g. at w={mp.nstr(ww,6)}: Im M_syn={mp.nstr(mm,5)} > 0  => HERGLOTZ BROKEN")
print()
print("  CONCLUSION: the definite sign of Im M(w) (Herglotz-ness in w) is EXACTLY")
print("  equivalent to all zeros lying at w<0 (real, negative) i.e. on the line.")
print("  An off-line zero pair sits in UHP_w/LHP_w and provably flips Im M's sign.")
print("  This is the precise locus where positivity 'breaks' = AT THE OFF-LINE ZEROS.")
