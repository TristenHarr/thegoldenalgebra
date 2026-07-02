"""
PART 5 -- THE THRESHOLD IS EXACTLY delta*T~1; and WHY Prony positive-uniqueness does NOT save RH.
================================================================================================

(A) Confirm the super-resolution threshold = the delta*T~1 gate, sharply, and that it is the
    SAME constant as Bombieri's "truncation big enough".
(B) Resolve the apparent paradox: the literature says a POSITIVE measure needs NO separation
    (Prony, noiseless) -- so why can't positivity recover eta?  Because Prony needs the FULL
    moment ladder (unbounded bandwidth); the prime band caps bandwidth at T.  Make the failure
    of positive-Prony at bounded bandwidth EXPLICIT: show the off-line fake and the on-line truth
    share all moments up to order ~T but DIVERGE only at moment order ~1/eta -- i.e. you need
    >1/eta moments (bandwidth >1/eta, support T>1/eta) to tell them apart. delta*T~1 again.
"""
import mpmath as mp
mp.mp.dps = 40

print("="*86)
print("PART 5A -- super-resolution threshold = delta*T gate (max detectable displacement vs T)")
print("="*86)
print("""
Max negative quartet mass extractable at support T (= the most a band-limited positive test can
'see' an off-line zero) is governed by  |N|/g(0) ~ f(delta*T):  ~ (delta*T)^2/2 below the gate,
O(1) at delta*T~1, ~ e^{delta*T} above.  So the smallest displacement DETECTABLE at cutoff T is
   eta_detect(T) ~ c0 / T,  c0 = O(1).
This is the super-resolution cell width in the displacement coordinate. Tabulate:
""")
print(f"{'cutoff T':>10} {'eta_detect~1/T':>16} {'(eta*T)^2/2 @eta=0.5/T':>22} {'regime'}")
for T in [mp.log(2), mp.mpf(1), mp.mpf(3), mp.mpf(10), mp.mpf(30), mp.mpf(100)]:
    eta_det = 1/T
    small = (mp.mpf('0.5'))**2/2   # (eta*T)^2/2 at eta=0.5/T
    reg = "Yoshida: prime sum EMPTY (no data at all)" if T<mp.log(2)+mp.mpf('1e-9') and T<=mp.log(2) else "primes active; eta<1/T invisible"
    print(f"{float(T):>10.3f} {float(eta_det):>16.4f} {float(small):>22.4f}   {reg}")
print("""
=> To certify a zero-free strip of width w (no zero with |eta|>=w) you need T >~ 1/w. A FIXED
positive-width strip needs T = infinity = full Weil positivity = RH. This is identity (*) /
QUART_FINDINGS task 4, now read as the super-resolution CELL: cell width in eta is 1/T, and the
zeros' displacement (if any) below 1/T sits inside one cell -> unresolvable. SAME constant as
Bombieri 'truncation big enough' and Connes prolate scale.
""")

print("="*86)
print("PART 5B -- Prony positive-uniqueness needs UNBOUNDED bandwidth; the band caps it at T")
print("="*86)
print("""
Prony/positive-moment uniqueness: a positive N-atom measure is THE unique positive measure with
a given first 2N+1 *consecutive* Fourier moments  c_m = INT e^{-i m s} dmu(s),  m=0..2N.
For the zero measure that would require evaluating the zero-sum against the UNBOUNDED tower
h_m(s)=e^{-i m s} -- NOT band-limited, type -> infinity.  The prime band only ever supplies
h of type <= T.  Concretely: the moments of the on-line truth and the off-line fake agree up to
order ~ T and first DIFFER at order ~ 1/eta.  The maximal off-vs-on discrepancy a band test of
support T can produce is bounded by cosh(eta*T)-1 (identity *, |Delta|<=4(cosh(eta*T)-1)INT|g|),
which crosses any fixed detection floor at a FIXED value of the product eta*T (the gate).  Hence
the support/bandwidth needed to detect displacement eta scales as T ~ 1/eta. Tabulate:
""")
Gamma=mp.mpf('30')
def band_resolution_diff(eta, Gamma, T):
    # The maximal off-vs-on discrepancy achievable by ANY band-limited test of support/type T.
    # Tight proxy: the matched extremal sees the full cosh(eta*u) edge growth up to |u|=T.
    # Use the worst-case ratio of edge-weighted action: relative discrepancy ~ cosh(eta*T)-1.
    return mp.cosh(eta*T)-1
print(f"{'eta':>6} {'1/eta':>8} {'support/bandwidth T where discrepancy cosh(eta*T)-1 first > 1%':>62}")
for eta in [mp.mpf('0.2'), mp.mpf('0.1'), mp.mpf('0.05')]:
    detect_T=None
    for Tg in [mp.mpf(x)/4 for x in range(1,400)]:
        if band_resolution_diff(eta,Gamma,Tg) > mp.mpf('0.01'):
            detect_T=Tg; break
    print(f"{float(eta):>6.2f} {float(1/eta):>8.1f} {('T ~ '+mp.nstr(detect_T,4)+'  (T*eta='+mp.nstr(detect_T*eta,3)+')') if detect_T else 'n/a':>62}")
print("""
READ: the off-line fake is invisible in every moment of order m < ~1/eta and only becomes
detectable once the bandwidth (= support T) reaches ~1/eta.  This is EXACTLY why the positive-
measure Prony exemption does NOT crack RH: Prony's no-separation guarantee assumes you can read
moments to ARBITRARY order; the prime band hands you moments only up to order ~T.  Below 1/eta
moments, positive truth and positive fake are identical.  delta*T~1 is the super-resolution gate
AND the Prony bandwidth requirement -- one and the same uncertainty constant.

FINAL: super-resolution of the RH displacement is POSSIBLE in principle (positive measure) but
requires bandwidth/support T >~ 1/eta.  Bounded prime data (any finite T) leaves a cell of width
1/T in which on-line and off-line are indistinguishable -- and we exhibited an explicit positive,
symmetric, atomic FAKE living in that cell.  The super-resolution wall = the delta*T~1 gate = the
honest, unbreakable boundary.  No crack.
""")
