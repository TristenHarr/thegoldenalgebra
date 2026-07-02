"""
THE CORE OBSTRUCTION, sharpened:  the Weil displacement functional is UNBOUNDED BELOW
in the displacement η, hence NOT convex and has NO minimizer (least of all the axis).

B(γ,η) = 4 e^{-a γ^2} · e^{+a η^2} · cos(2 a γ η).

As η → ∞ along η_n = (2n+1)π/(2aγ) (where cos(2aγη) = -1... actually cos = 0 there;
the troughs cos=-1 are at 2aγη = (2k+1)π), B = -4 e^{-aγ^2} e^{aη^2} → -∞.

So for ANY fixed test scale a>0 and any zero γ≠0, sup_η B = +∞ and inf_η B = -∞.
The functional F_Q(η) = Σ_k B(γ_k,η_k) is unbounded below: there is NO global minimizer,
convex or otherwise. The axis η=0 is a SADDLE (Hessian neg-def at axis, but the function
also goes to +∞ along cos=+1 directions). Adding any POLYNOMIAL penalty λ‖η‖^2 cannot
restore boundedness because e^{aη^2} dominates every polynomial.

We show the troughs explicitly with high precision (no e^{-aγ^2} underflow): use the
NORMALIZED block  b(γ,η) := B(γ,η)/(4 e^{-aγ^2}) = e^{aη^2} cos(2aγη), and add penalty.
"""
import numpy as np

def b_norm(gamma, eta, a):
    return np.exp(a*eta**2)*np.cos(2*a*gamma*eta)

def b_norm_plus_pen(gamma, eta, a, lam_over_pref):
    # F/pref = e^{aη^2}cos(2aγη) + (λ/pref) η^2   -- penalty also scaled by pref.
    return b_norm(gamma, eta, a) + lam_over_pref*eta**2

if __name__ == "__main__":
    a = 0.02; gamma = 14.135
    print(f"NORMALIZED Weil block b(γ,η)=e^(aη^2)cos(2aγη), γ={gamma}, a={a}")
    print("Troughs at 2aγη=(2k+1)π  =>  η_k=(2k+1)π/(2aγ):")
    print(f"   {'η':>10} {'b(γ,η)':>16} {'b+10η^2':>16} {'b+1000η^2':>18}")
    for k in range(0, 14):
        eta = (2*k+1)*np.pi/(2*a*gamma)
        b = b_norm(gamma, eta, a)
        print(f"   {eta:10.3f} {b:16.4e} {b+10*eta**2:16.4e} {b+1000*eta**2:18.4e}")
    print("\n=> b plunges to -e^{aη^2} -> -infinity along the troughs; ANY λη^2 (polynomial)")
    print("   is eventually swamped by the exponential. The axis is NOT a global minimum,")
    print("   and NO convex functional agrees with F_Q because F_Q is unbounded below.")

    print("\n--- restated as the exact non-convexity certificate ---")
    print("d2B/dη2|_{η=0} = 4 e^{-aγ^2}(2a - 4a^2 γ^2) < 0 for a γ^2 > 1/2  (CONCAVE at axis).")
    print("With first zeta zero γ1=14.13, this requires a > 1/(2·14.13^2) = "
          f"{1/(2*14.135**2):.5e}: ANY test scale wider than σ≈14 (a above that) is concave")
    print("at the axis at γ1; for the BULK of zeros (large γ) the concavity threshold a is")
    print("microscopic, so for every realistic test scale the Weil block is concave at the axis.")

    # Conclusion table over scales: is axis a local min, local max, or saddle?
    print("\n--- axis classification per scale a (sign of axis Hessian summed) ---")
    import mpmath as mp; mp.mp.dps=20
    gammas=[float(mp.im(mp.zetazero(k))) for k in range(1,21)]
    for a in [1e-4,1e-3,1e-2,1e-1]:
        diag=[4*np.exp(-a*g*g)*(2*a-4*a*a*g*g) for g in gammas]
        npos=sum(1 for d in diag if d>0); nneg=sum(1 for d in diag if d<0)
        cls = "axis = SADDLE (mixed)" if (npos and nneg) else ("axis = local MIN" if nneg==0 else "axis = local MAX")
        print(f"  a={a:.0e}: {npos} convex dir, {nneg} concave dir over 20 zeros -> {cls}")
