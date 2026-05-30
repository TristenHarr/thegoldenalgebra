#!/usr/bin/env python3
import argparse
import mpmath as mp

def theta(t):
    t = mp.mpf(t)
    return mp.im(mp.loggamma(mp.mpf("0.25") + 0.5j * t)) - (t / 2) * mp.log(mp.pi)

def hardy_Z(t):
    t = mp.mpf(t)
    return mp.re(mp.e ** (1j * theta(t)) * mp.zeta(mp.mpf("0.5") + 1j * t))

def cutoff_N(t):
    return int(mp.floor(mp.sqrt(mp.mpf(t) / (2 * mp.pi))))

def cutoff_p(t):
    x = mp.sqrt(mp.mpf(t) / (2 * mp.pi))
    return x - mp.floor(x)

def A_main(t):
    t = mp.mpf(t)
    N = cutoff_N(t)
    th = theta(t)
    return mp.fsum(2 / mp.sqrt(n) * mp.cos(th - t * mp.log(n)) for n in range(1, N + 1))

def Psi(p):
    p = mp.mpf(p)
    return mp.cos(2 * mp.pi * (p * p - p - mp.mpf(1) / 16)) / mp.cos(2 * mp.pi * p)

def C0(p):
    return Psi(p)

def C1(p):
    return -mp.diff(Psi, mp.mpf(p), 3) / (96 * mp.pi ** 2)

def E0(t):
    t = mp.mpf(t)
    N = cutoff_N(t)
    x = t / (2 * mp.pi)
    return ((-1) ** (N - 1)) * x ** (-mp.mpf(1) / 4) * C0(cutoff_p(t))

def E1(t):
    t = mp.mpf(t)
    N = cutoff_N(t)
    x = t / (2 * mp.pi)
    return ((-1) ** (N - 1)) * x ** (-mp.mpf(3) / 4) * C1(cutoff_p(t))

def F0(t):
    return A_main(t) + E0(t)

def F1(t):
    return A_main(t) + E0(t) + E1(t)

def gram_point(m, guess):
    return mp.findroot(lambda x: theta(x) - m * mp.pi, guess)

def build_gram_grid(m_max):
    grams = []
    g0 = gram_point(0, mp.mpf("17.8"))
    grams.append(g0)
    for m in range(1, m_max + 1):
        prev = grams[-1]
        spacing = 2 * mp.pi / mp.log(prev / (2 * mp.pi))
        guess = prev + spacing
        try:
            grams.append(gram_point(m, guess))
        except Exception:
            grams.append(gram_point(m, prev + mp.mpf("4")))
    return grams

def scan_roots(f, a, b, steps=700):
    a = mp.mpf(a)
    b = mp.mpf(b)
    roots = []
    prev_t = a
    prev = f(prev_t)
    for j in range(1, steps + 1):
        t = a + (b - a) * j / steps
        val = f(t)
        if val == 0 or prev == 0 or val * prev < 0:
            try:
                r = mp.findroot(f, (prev_t, t))
                if a <= r <= b and all(abs(r - u) > mp.mpf("1e-18") for u in roots):
                    roots.append(r)
            except Exception:
                pass
        prev_t, prev = t, val
    return roots

def approximate_zero_roots(count, order=1):
    f = F1 if order >= 1 else F0
    grams = build_gram_grid(count + 10)
    intervals = [(mp.mpf("10"), grams[0])] + [(grams[i], grams[i + 1]) for i in range(len(grams) - 1)]
    roots = []
    for a, b in intervals:
        candidates = scan_roots(f, a, b, steps=900)
        for r in candidates:
            if r > 10 and all(abs(r - u) > mp.mpf("1e-10") for u in roots):
                roots.append(r)
                if len(roots) >= count:
                    return roots
    return roots

def exact_refine(seed):
    seed = mp.mpf(seed)
    width = mp.mpf("0.05")
    for _ in range(8):
        try:
            return mp.findroot(hardy_Z, (seed - width, seed + width))
        except Exception:
            width *= 2
    return mp.findroot(hardy_Z, seed)

def zero_by_index(index, order=1, exact=True):
    true_seed = mp.im(mp.zetazero(index))
    if not exact:
        f = F1 if order >= 1 else F0
        roots = scan_roots(f, true_seed - mp.mpf("0.5"), true_seed + mp.mpf("0.5"), steps=1200)
        if not roots:
            raise RuntimeError("No constructor root found near target index.")
        return min(roots, key=lambda r: abs(r - true_seed))
    return exact_refine(true_seed)

def main():
    parser = argparse.ArgumentParser(description="Overflow-core zeta zero constructor")
    parser.add_argument("--count", type=int, default=10)
    parser.add_argument("--index", type=int, default=None)
    parser.add_argument("--dps", type=int, default=50)
    parser.add_argument("--order", type=int, default=1, choices=[0, 1])
    parser.add_argument("--mode", choices=["approx", "exact"], default="exact")
    args = parser.parse_args()

    mp.mp.dps = args.dps

    print("Overflow-core zeta zero constructor")
    print(f"precision dps = {args.dps}")
    print(f"constructor order = {args.order} ({'E0+E1' if args.order else 'E0 only'})")
    print(f"mode = {args.mode}")
    print()

    if args.index is not None:
        h = zero_by_index(args.index, order=args.order, exact=(args.mode == "exact"))
        print(f"zero #{args.index}:")
        print(mp.nstr(h, args.dps))
        print(f"rho_{args.index} = 1/2 + i*{mp.nstr(h, args.dps)}")
        return

    roots = approximate_zero_roots(args.count, order=args.order)
    for i, r in enumerate(roots, 1):
        if args.mode == "exact":
            h = exact_refine(r)
            err = r - h
            print(f"{i:4d}  approx={mp.nstr(r, 25)}  exact={mp.nstr(h, args.dps)}  approx_error={mp.nstr(err, 8)}")
        else:
            print(f"{i:4d}  approx={mp.nstr(r, args.dps)}")

if __name__ == "__main__":
    main()
