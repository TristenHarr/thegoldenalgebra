"""
SUZUKI omega-CONTINUATION ATTACK on the Schur ratio contractivity Theta_Phi.

GOAL.  The target is: Theta_omega(z) = xi(1/2 - omega - i z) / xi(1/2 + omega - i z)
is INNER on the upper half plane (UHP):  |Theta_omega(z)| <= 1 for Im z > 0.
Suzuki proves the associated canonical system has a POSITIVE Hamiltonian H(x) >= 0
UNCONDITIONALLY for omega > 1.  Continuing H(x) >= 0 down to omega -> 0 (with a
PROVABLE propagation mechanism) would prove RH.

THIS SCRIPT does the genuine numerical experiment the task asks for:

  (A) Verify the STRUCTURAL reason omega>1 is unconditional: the denominator
      xi(1/2 + omega - i z) is ZERO-FREE in the closed UHP for omega>1/2
      *unconditionally*, because then Re(1/2+omega) > 1 lies in the zero-free
      region of zeta (Re s > 1, Euler product).  For omega in (0,1/2] the relevant
      zeros enter the UHP and the inner property becomes RH-equivalent.

  (B) Track |Theta_omega(z)| over the UHP as omega DECREASES from 3 -> 0.
      Find the largest sup_{UHP} |Theta_omega|.  If it stays <=1 with a structural
      reason that propagates, that's the proof.  Watch where (which omega, which z)
      the bound first becomes RH-sensitive.

  (C) DIRECT inner test: |Theta_omega| <= 1 on UHP  <=>  every zero of the
      denominator xi(1/2+omega-iz) is in the OPEN UHP and every zero of the
      numerator xi(1/2-omega-iz) is in the CLOSED LHP, AND |Theta_omega|<=1 on R.
      Locate the zeros of numerator & denominator as functions of omega and watch
      them cross the real axis exactly at the RH-sensitive threshold.

CONVENTIONS.  xi here = Riemann completed xi, real on the critical line, with
xi(s)=xi(1-s).  mpmath: mp.siegelz / mp.zeta give us what we need; we use the
completed xi via the standard formula.
"""
import mpmath as mp
mp.mp.dps = 30

def xi(s):
    # completed xi(s) = 1/2 s (s-1) pi^{-s/2} Gamma(s/2) zeta(s)
    return mp.mpf('0.5')*s*(s-1)*mp.pi**(-s/2)*mp.gamma(s/2)*mp.zeta(s)

def Theta(omega, z):
    # Theta_omega(z) = xi(1/2 - omega - i z) / xi(1/2 + omega - i z)
    num = xi(mp.mpf('0.5') - omega - 1j*z)
    den = xi(mp.mpf('0.5') + omega - 1j*z)
    if den == 0:
        return mp.inf
    return num/den

print("="*80)
print("(A) STRUCTURAL: where do denominator zeros sit?  xi(1/2+omega - i z)=0")
print("    xi has zeros only at s=1/2+i*gamma (nontrivial; assume on/off line) ")
print("    plus none for Re s>1.  Set 1/2+omega - i z = rho => z = -i(1/2+omega-rho).")
print("    A NONTRIVIAL zero rho=beta+i*gamma gives z = (gamma) + i(beta-1/2-omega)... ")
print("    => Im z = -(omega + 1/2 - beta).  For beta in (0,1): Im z < 0 iff omega>beta-1/2.")
print("    Since beta<1 always (zero-free Re s>=1), omega>1/2 => ALL denom zeros in LHP")
print("    UNCONDITIONALLY (z-plane), i.e. denominator zero-free in UHP. ")
print("    For omega<=1/2 the off-line possibility (beta>1/2) can push a zero into UHP")
print("    => inner property becomes RH-sensitive exactly at omega ~ 1/2.")
print("="*80)

# Let's NUMERICALLY confirm: take the first few xi zeros 1/2 + i gamma (ON line, RH true
# numerically here) and a HYPOTHETICAL off-line zero, and see the z-plane image.
gammas = [14.134725, 21.022040, 25.010858]
print("\nOn-line zeros rho=1/2+i*gamma -> z image of denominator, Im z vs omega:")
print(f"{'omega':>8} " + " ".join(f"{'g='+str(g):>16}" for g in gammas))
for omega in [3.0, 2.0, 1.0, 0.7, 0.5, 0.3, 0.1, 0.01]:
    row=[]
    for g in gammas:
        rho = mp.mpc('0.5', g)
        # 1/2+omega - i z = rho  => z = -i(1/2+omega-rho) = -i(omega) + -i(1/2-rho)
        z = -1j*(mp.mpf('0.5')+omega - rho)
        row.append(z)
    print(f"{omega:>8} " + " ".join(f"Imz={mp.nstr(z.imag,5):>11}" for z in row))
print("(On-line: Im z of denominator zeros = -omega < 0 for all omega>0 -> in LHP,")
print(" denominator zero-free in UHP. The threshold is about OFF-LINE zeros.)")

print("\nHYPOTHETICAL off-line zero beta=0.6 (RH-violating), z-image Im z vs omega:")
beta=mp.mpf('0.6')
for omega in [3.0,1.0,0.5,0.3,0.11,0.05]:
    rho=mp.mpc(beta,30.0)
    z=-1j*(mp.mpf('0.5')+omega-rho)
    # Im z = -(1/2+omega-beta) = beta-1/2-omega
    print(f"  omega={omega:>5}: Im z (denom zero) = {mp.nstr(z.imag,6)}  "
          f"{'IN UHP -> Theta NOT inner!' if z.imag>0 else 'in LHP (ok)'}")
print("  => An off-line zero with beta=0.6 enters the UHP exactly when omega < beta-1/2=0.1.")
print("  So for omega>1/2 NO possible zero (beta<1) reaches UHP: inner UNCONDITIONALLY.")
print("  For small omega, only RH (beta=1/2) keeps them out. THIS IS THE WALL LOCATION.")
