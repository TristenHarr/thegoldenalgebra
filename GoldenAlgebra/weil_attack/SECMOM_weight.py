"""
SECMOM_weight.py — the per-zero weight W(γ,T) = lim_{η→0} Δ_ρ(g)²/η⁴, its decay in γ,
and whether it ever vanishes (faithfulness of M2_diag).

W(γ,T) = ( 4 ∫_{-T}^{T} g(u) (u²/2) cos(γu) du )²   [leading η² coefficient of Δ, squared]
       = ( 2 ∫ g(u) u² cos(γu) du )².
For g = triangle on [-T,T], this is an explicit band-limited function of γ that DOES have
real zeros (the cos-cancellation): so a SINGLE γ can give W(γ)=0.  The honest faithfulness
statement for the DIAGONAL second moment is therefore COLLECTIVE, not per-zero.
"""
import mpmath as mp
mp.mp.dps = 30
def g_tri(T): return lambda u: max(mp.mpf(0),1-abs(u)/T)

def W(gamma, T, g):
    # leading-order weight: Δ ≈ 4∫ g (η²u²/2) cos(γu) = 2η²∫ g u² cos(γu); W = (2∫g u²cos)²
    I = mp.quad(lambda u: g(u)*u**2*mp.cos(gamma*u), [-T,0,T])
    return (2*I)**2

T = mp.mpf('0.6'); g = g_tri(T)
print("W(γ,T) = (2∫g u²cos(γu))²  for g=triangle, T=0.6 — per-zero η⁴ weight")
print(f"{'gamma':>8} {'W(gamma)':>16}")
zeros = [14.134725,21.022040,25.010858,30.424876,32.935062,37.586178,40.918719,43.327073]
for gm in zeros:
    print(f"{gm:>8} {float(W(mp.mpf(str(gm)),T,g)):>16.6e}")
print()
print("W DECAYS like 1/γ⁴ (two integrations by parts of band-limited g): high zeros are")
print("nearly INVISIBLE to a fixed short support.  And W has genuine ZEROS in γ:")
# find zeros of W (= zeros of ∫ g u² cos(γu))
prev=None; zs=[]
gg=mp.mpf('0.5')
while gg<45:
    I=mp.quad(lambda u: g(u)*u**2*mp.cos(gg*u),[-T,0,T])
    if prev is not None and mp.sign(I)!=mp.sign(prev[1]):
        a,b=prev[0],gg
        for _ in range(50):
            m=(a+b)/2; Im=mp.quad(lambda u:g(u)*u**2*mp.cos(m*u),[-T,0,T])
            if mp.sign(Im)==mp.sign(prev[1]): a=m
            else: b=m
        zs.append(float((a+b)/2))
    prev=(gg,I); gg+=mp.mpf('0.2')
print("  W(γ)=0 at γ ≈", [round(z,3) for z in zs])
print()
print("VERDICT on faithfulness:")
print(" - M2_diag = Σ_ρ |Δ_ρ|² ≥ 0, = (Σ_ρ W(γ_ρ)) η_typ⁴-scale.  Each term ≥ 0 (squared).")
print(" - It is COLLECTIVELY faithful: M2_diag=0 forces Δ_ρ=0 for EVERY ρ.  But because W has")
print("   zeros in γ, a configuration where every off-line zero sits exactly on a W-zero would")
print("   give M2_diag=0 with η≠0 — a measure-zero coincidence, not generic, and avoidable by")
print("   varying g (the W-zeros MOVE with T).  So: M2_diag detects displacement, but the SAME")
print("   band-limitation that caps the first moment caps it: W(γ,T) ~ small for γ T ≳ O(1).")
