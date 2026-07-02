"""
Verify the detection-scale scaling M(rho)-1 ~ delta/t^2 *2t... let's get exact.
For rho=1/2+delta + i t, mirror gives M = sqrt((beta^2+t^2)/((1-beta)^2+t^2)),
beta=1/2+delta. beta^2-(1-beta)^2 = (2beta-1) = 2delta. So
 M^2 = 1 + 2delta/((1-beta)^2+t^2) ~ 1 + 2delta/t^2  for large t.
 log M ~ delta/t^2.  n to reach O(1): n ~ t^2/delta.  (Voros: t~1e9 => n~1e18.)
"""
import math
for delta,t in [(0.1,1e3),(1e-3,1e3),(0.1,1e9),(1e-3,1e9)]:
    beta=0.5+delta
    M=math.sqrt((beta*beta+t*t)/((1-beta)**2+t*t))
    approx=math.exp(delta/t**2)
    n_detect = t*t/delta
    print(f"delta={delta:.0e} t={t:.0e}: M={M:.15f}  ~exp(delta/t^2)={approx:.15f}  n_detect~t^2/delta={n_detect:.2e}")
