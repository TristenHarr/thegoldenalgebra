"""
Numerically corroborate Selberg's moments of log|zeta(1/2+it)|:
  - signed mean  (1/T) INT log|zeta|        -> 0  (slowly)
  - 2nd moment   (1/T) INT (log|zeta|)^2     -> ~ 1/2 log log T
These are the 'known inputs' for the Littlewood first-moment bound (FM).
We sample on a high window [T0, T0+L] to see log log T behavior (it grows
painfully slowly, so we just check order of magnitude and positivity).
"""
import mpmath as mp
mp.mp.dps = 20


def moments(T0, L, npts):
    h = mp.mpf(L)/npts
    s1 = mp.mpf(0); s2 = mp.mpf(0); sa = mp.mpf(0)
    for k in range(npts):
        t = T0 + (k + mp.mpf('0.5'))*h
        v = mp.log(abs(mp.zeta(mp.mpf('0.5') + 1j*t)))
        s1 += v
        s2 += v*v
        sa += abs(v)
    return s1/npts, s2/npts, sa/npts


if __name__ == "__main__":
    print("window         mean      2nd-moment   pred(1/2 loglogT)   |.|-moment")
    for T0 in [1e3, 1e4, 1e5, 1e6]:
        m1, m2, ma = moments(T0, 200.0, 4000)
        pred = mp.mpf('0.5')*mp.log(mp.log(T0))
        print(f"T~{T0:8.0e}:  {float(m1):+8.4f}   {float(m2):8.4f}     "
              f"{float(pred):8.4f}           {float(ma):7.4f}")
    print("\n(2nd moment should track ~1/2 loglogT; mean should hover near 0.")
    print(" Sampling is coarse and the window short, so expect order-of-magnitude")
    print(" agreement, not high precision. loglogT grows extremely slowly.)")
