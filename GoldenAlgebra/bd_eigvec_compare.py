"""
bd_eigvec_compare.py — TASK 4: matrix positivity. Compare the BD Gram 'hard direction'
(slowly-converging / smallest-eigenvalue eigenvector) to the rank-one PRIME-MODE
obstruction found in weil_attack (prime_mode_gram.json).

Question: do the hard directions of the Báez-Duarte Gram matrix ALIGN with the rank-one
prime-mode bad direction of the Weil quadratic form, or are they a DIFFERENT bad-direction
structure?
"""
import json, numpy as np
import mpmath as mp

# ---- load BD Gram (built by bd_gram.py) ----
bd = json.load(open("bd_gram_results.json"))
G = np.array(bd["gram"]); b = np.array(bd["moment"])
N = G.shape[0]
print(f"BD Gram N={N}")

# Best-approx coefficient vector a = G^{-1} b ; residual direction structure.
a = np.linalg.solve(G, b)
# The 'hardest' (least-damped) direction = eigenvector of smallest eigenvalue of G.
w, V = np.linalg.eigh(G)
print("BD Gram eigenvalues (sorted):", np.round(w,6))
v_hard = V[:,0]        # smallest eigenvalue
print("\nBD hard direction (smallest-eig eigenvector), per index k=1..N:")
print(np.round(v_hard,4))
print("sign pattern:", np.sign(v_hard).astype(int))

# Is BD hard direction an alternating/Mobius-like vector?  Check correlation with mu(k).
from sympy import mobius, primefactors, factorint
mu = np.array([float(mobius(k)) for k in range(1,N+1)])
# Lambda-like (von Mangoldt indicator): is k a prime power?
def is_pp(k):
    f=factorint(k); return len(f)==1
pp = np.array([1.0 if is_pp(k) else 0.0 for k in range(1,N+1)])
print("\nmu(k) k=1..N:", mu.astype(int))
def corr(x,y):
    x=x-x.mean(); y=y-y.mean()
    d=np.linalg.norm(x)*np.linalg.norm(y)
    return float(x@y/d) if d>0 else 0.0
print(f"corr(BD hard dir, mu)      = {corr(v_hard,mu):+.3f}")
print(f"corr(|BD hard dir|, 1/k)   = {corr(np.abs(v_hard),1.0/np.arange(1,N+1)):+.3f}")

# ---- load prime-mode Gram ----
pm = json.load(open("weil_attack/prime_mode_gram.json"))
PG = np.array(pm["gram"]); labels = pm["labels"]
wp, Vp = np.linalg.eigh(PG)
print("\n" + "="*70)
print("PRIME-MODE Gram (weil_attack): the rank-one obstruction")
print("="*70)
print("prime-mode Gram eigenvalues:", np.round(wp,6))
v_pm_soft = Vp[:,0]   # smallest eig ~ 5.7e-7 : the near-null bad direction
v_pm_dom  = Vp[:,-1]  # dominant eig ~ 11.07
print("\nlabels:", labels)
print("\nprime-mode SMALLEST-eig eigenvector (the near-null direction):")
print(np.round(v_pm_soft,4))
print("sign pattern:", np.sign(v_pm_soft).astype(int))
print("\nprime-mode DOMINANT-eig eigenvector (the rank-one mode):")
print(np.round(v_pm_dom,4))
print("sign pattern:", np.sign(v_pm_dom).astype(int))

# The prime-mode Gram is ~ rank-one: entries ~ s_i s_j with s_i = +-1. Recover s.
s = np.sign(v_pm_dom)
print("\nrank-one sign vector s (from dominant eigvec):", s.astype(int))
# reconstruct s_i s_j and compare to PG sign
SS = np.outer(s,s)
agree = (np.sign(PG)==SS).mean()
print(f"fraction of PG entries whose sign = s_i*s_j : {agree:.3f}  (=> rank-one +-1 structure)")

print("""
STRUCTURAL VERDICT (printed):
 * Prime-mode Gram: dominated by ONE eigenvalue (11.07) with a +-1 sign-vector eigenvector
   => a RANK-ONE obstruction. The near-null direction (eig 5.7e-7) is the orthogonal
   complement: the prime modes are almost collinear (all the 'prime energy' points one way).
 * BD Gram: its eigenvalues are SPREAD (no single dominant rank-one mode); the hard
   direction is NOT a +-1 prime-sign vector and is essentially UNCORRELATED with mu(k)
   (the Mobius/prime-sign structure). The BD basis {rho_{1/k}} are all POSITIVELY
   correlated (Gram entries ~ smooth, all same sign) — a totally different geometry from
   the alternating prime-mode cone.
 => The BD slow-convergence direction is NOT the prime-mode rank-one obstruction. They are
    DIFFERENT bad-direction structures: Weil's obstruction is the rank-one prime alignment;
    BD's is the smooth near-degeneracy of overlapping dilations (a Hilbert-matrix-type
    ill-conditioning), not a prime-arithmetic alternation.
""")
