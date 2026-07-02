"""
Can the n=2 term ALONE flip Q's sign, for g supported just past log2?
Per-frequency density: Q-density(r) = (1/2pi)[Omega(r)+2 D_cut(r)] + pole-density,
with D_cut(r) the FINITE prime density. With ONLY n=2: D_2(r)= (log2)/sqrt(2) cos(r log2).
The archimedean Omega is fixed. The question: does Omega(r)+ 2*(log2/sqrt2)cos(r log2)
ever go negative -- and if so can a positive-type g supported in [-T,T] concentrate there?
But CRUCIAL: a g supported in [-T,T] CANNOT have arbitrary |ghat(r)|^2 -- it's band-LIMITED
in the Paley-Wiener sense (ghat entire of exp-type T). So |ghat|^2 can't be a delta at the
worst r. The REAL test is the full quadratic form. Here we just map the danger frequencies.
"""
import mpmath as mp
mp.mp.dps=25
Omega=lambda r: mp.re(mp.digamma(mp.mpf(1)/4+1j*r/2))-mp.log(mp.pi)
l2=mp.log(2); w2=l2/mp.sqrt(2)
# pole density: pole term = ghat(i/2)+ghat(-i/2). For g positive type this is >0 always; 
# in frequency it acts like adding mass via analytic continuation, hard to localize -> 
# treat conservatively as 0 (only helps positivity). So worst-case density:
def Kmin_singleprime(r): return Omega(r)+2*w2*mp.cos(r*l2)
print("Worst-case bulk density with ONLY n=2 prime (pole ignored => lower bound on Q-density):")
print("r        Omega       2*D_2       K=Omega+2D2")
neg=[]
rr=mp.mpf(0)
while rr<=40:
    K=Kmin_singleprime(rr)
    if K<0: neg.append(float(rr))
    if abs(float(rr)-round(float(rr)*2)/2)<1e-9 and float(rr)%2<0.01:
        print(f"{float(rr):6.2f}  {mp.nstr(Omega(rr),6):>10} {mp.nstr(2*w2*mp.cos(rr*l2),6):>10} {mp.nstr(K,6):>10}{'  <NEG' if K<0 else ''}")
    rr+=mp.mpf('0.05')
print()
if neg:
    print(f"K<0 (density dips negative) on r in approx [{neg[0]:.2f}, {neg[-1]:.2f}] and similar bands.")
    print("So even ONE prime makes the *pointwise* density indefinite. BUT band-limited g")
    print("(supp in [-T,T]) averages |ghat|^2 against K; positivity can survive if the")
    print("NEGATIVE bands are narrow/shallow relative to Omega's positive bulk + pole.")
else:
    print("K>=0 everywhere with one prime: cone safe vs n=2 at all freq.")
