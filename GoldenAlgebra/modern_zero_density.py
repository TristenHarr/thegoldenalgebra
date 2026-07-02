"""
modern_zero_density.py
Current-best (2024-2025) unconditional zero-density exponent A(sigma) in
    N(sigma,T) << T^{A(sigma)(1-sigma)+o(1)},  sigma in [1/2,1).

Sources:
  - Ingham 1940 (refined form 3/(2-sigma)); classical headline A<=3.
  - Guth-Maynard 2024, arXiv:2405.20552: near sigma=3/4, A=30/13 (headline);
    refined ANTEDB piece A(sigma)=15/(3+5 sigma) on [7/10,19/25].
  - Ivic 1984, Bourgain 2000, Heath-Brown 1979 pieces (ANTEDB Table 11.1).
  - Tao-Trudgian-Yang 2025, arXiv:2501.16779 (ANTEDB systematization /
    Corollary 11.25 near sigma=1).
"""
from fractions import Fraction as F

# ANTEDB Table 11.1 piecewise A(sigma), each entry (lo, hi, A_func, source)
PIECES = [
    (F(1,2),  F(7,10),    lambda s: F(3)/(2-s),       "Ingham 1940 (3/(2-sigma))"),
    (F(7,10), F(19,25),   lambda s: F(15)/(3+5*s),    "Guth-Maynard 2024 (15/(3+5s))"),
    (F(19,25),F(127,167), lambda s: F(9)/(8*s-2),     "Ivic 1984"),
    (F(127,167),F(13,17), lambda s: F(15)/(13*s-3),   "Ivic 1984"),
    (F(13,17),F(17,22),   lambda s: F(6)/(5*s-1),     "Ivic 1984"),
    (F(17,22),F(41,53),   lambda s: F(2)/(9*s-6),     "Bourgain (improved)"),
    (F(41,53),F(7,9),     lambda s: F(9)/(7*s-1),     "Ivic 1984"),
    (F(7,9),F(1867,2347), lambda s: F(9)/(8*(2*s-1)), "Bourgain (improved)"),
    (F(1867,2347),F(4,5), lambda s: F(3)/(2*s),       "Bourgain 2000"),
    (F(4,5),F(7,8),       lambda s: F(3)/(2*s),       "Ivic 1984"),
    (F(7,8),F(31,34),     lambda s: F(3)/(10*s-7),    "Heath-Brown 1979"),
    # near 1: ANTEDB Cor 11.25 optimized; use Huxley-type 12/5 cap as safe bound
    (F(31,34),F(1),       lambda s: F(12,5),          "TTY 2025 / cap A<=12/5"),
]

def A(sigma):
    s = F(sigma)
    for lo, hi, f, src in PIECES:
        if lo <= s <= hi:
            return f(s), src
    raise ValueError(sigma)

if __name__ == "__main__":
    print("=== Continuity check at breakpoints ===")
    for i in range(len(PIECES)-1):
        b = PIECES[i][1]
        left  = PIECES[i][2](b)
        right = PIECES[i+1][2](b)
        flag = "OK" if left==right else "JUMP %.5f->%.5f"%(float(left),float(right))
        print(f" sigma={float(b):.5f}: {flag}")
    print("\n=== A(sigma) table; displacement eps=sigma-1/2 ===")
    print(f"{'sigma':>8}{'eps':>8}{'A(sigma)':>12}{'A*(1-s)':>12}{'source':>32}")
    for k in range(0,51):
        s = F(1,2)+F(k,100)
        if s>=1: continue
        a,src=A(s)
        print(f"{float(s):8.3f}{float(s-F(1,2)):8.3f}{float(a):12.5f}{float(a*(1-s)):12.5f}  {src}")
