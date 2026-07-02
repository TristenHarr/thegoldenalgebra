"""
Sanity check: is the layer-cake LOSSY, and does the FIRST moment beat density?

FIRST moment (Littlewood, unconditional, classical):
   Sum_{0<gamma<=T} (beta - 1/2) = (1/(2 pi)) * int_0^T log|zeta(1/2+it)| ... 
   Actually the exact identity (Littlewood's lemma applied to zeta on [1/2,1]x[0,T]):
        2 pi * sum_{rho:0<gamma<=T} (beta - 1/2)
           = int_{1/2}^{1}  [something]   = O(log T)   unconditionally.
   The first absolute moment sum_{gamma<=T}|beta-1/2| is NOT known to be O(log T)
   unconditionally without sign cancellation; the SIGNED sum is O(log T).

   Layer-cake for SIGNED would need signed N; the ENERGY (second moment) is what
   density controls because eta^2 = |eta|^2 has no sign cancellation.

SECOND moment via layer-cake is EXACT (no loss in the identity):
   Sum eta^2 = 2 int_0^{1/2} u * N_off(u,T) du     (Cavalieri, exact).
The ONLY inequality is N_off(u,T) <= 2 N(1/2+u,T) <= 2 T^{1-2 theta u} log T.
So ALL the slack is in the density estimate, none in the layer-cake.

Therefore: improving Sum eta^2 below T/log T <=> improving the near-line density
below T^{1-2 theta u} log T in LOG-POWER (k=1 -> k=0) for u ~ 1/log T.

The signed first moment being O(log T) does NOT bound the energy: the energy is a
sum of squares (all positive), genuinely of size ~ (number of zeros within 1/log T)
* (1/log T)^2 ~ (T log T * fraction) / log^2 T. Even if ALL T log T /(2pi) zeros sat
at distance exactly ~1/log T, energy ~ T log T /log^2 T = T/log T. That is the
heuristic floor matching the rigorous density bound: T/log T is the size you get
if a positive proportion of zeros sit at the natural resolution 1/log T off the line.
"""
print(__doc__)
# Heuristic floor: all N(T) zeros at distance ~ a/log T
import math
for a in [1.0]:
    print(f"If every zero sits at |eta| = {a}/log T: energy = N(T)*(a/logT)^2 "
          f"= (T logT/2pi)*(a^2/log^2 T) = a^2 T/(2pi log T).")
print("=> T/log T is the HEURISTIC FLOOR, not just an artifact: it is what the")
print("   energy WOULD be if zeros clustered at the natural 1/log T resolution.")
print("   Density k=1 log-power exactly reproduces this floor; k=0 (log-free) would")
print("   push it to T/log^2 T, which is BELOW the clustering floor => would need")
print("   the EXTRA input that zeros do NOT cluster at 1/log T (a near-line repulsion).")
