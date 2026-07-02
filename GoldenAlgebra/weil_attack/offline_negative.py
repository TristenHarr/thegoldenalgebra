import mpmath as mp
mp.mp.dps=25
def T(a,gamma0,delta):
    return 4*mp.e**(-a*(gamma0*gamma0-delta*delta))*mp.cos(2*a*gamma0*delta)
# need 2 a gamma0 delta > pi/2. With gamma0=14, delta=0.45:
for a in [mp.mpf(x)/100 for x in [10,15,20,25,30]]:
    g0=14;d=mp.mpf('0.45')
    print(f"a={float(a):.2f}: 2ag0d={float(2*a*g0*d):.3f}  T={mp.nstr(T(a,g0,d),8)}")
print()
# Optimize: maximize |negative| / structure. The key qualitative fact:
# T<0 achievable => for a test function concentrated to "see" the off-line zero,
# the zero-sum (=Q) gets a negative contribution that the on-line zeros & main
# terms do NOT automatically cancel.
g0=14;d=mp.mpf('0.49')
a=mp.mpf('0.5')
print(f"strong: a={float(a)}, g0={g0}, d={float(d)}: T={mp.nstr(T(a,g0,d),8)}")
