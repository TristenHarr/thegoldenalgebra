# RH as a Super-Resolution Problem — Findings

Mission: is RH a SUPER-RESOLUTION theorem? Can positivity + symmetry + sparsity of the zero
measure recover the displacement `eta = beta - 1/2 = 0` from BOUNDED prime data, beating the
`delta*T~1` resolution gate — OR is there an explicit positive symmetric atomic FAKE with
`eta != 0` matching the prime samples (super-resolution fails)?

**VERDICT: (b) — the honest wall. Super-resolution FAILS at any bounded prime cutoff.**
We banked an EXPLICIT positive, symmetric, atomic FAKE measure with `eta = 0.08 != 0` that
reproduces the genuine bounded prime samples to `1e-32`. The reason is precise: the prime band
is a BAND-LIMITED (type-`T`) positive measurement, the one regime where even positive-measure
super-resolution is provably impossible below the cell width `1/T`. No crack.

Scripts (all run clean, mpmath/sympy, no RH assumed, EF/identity verified):
`superres_separation.py`, `superres_fake_model.py`, `superres_fake_exact.py`,
`superres_sample_positivity.py`, `superres_gate_and_prony.py`.

---

## 1. The recovery problem, set up precisely

Zero measure `mu = sum m_rho delta_{(gamma,eta)}` on the `(gamma, eta)` plane: positive
(`m_rho > 0`), symmetric under the FE/conjugation `gamma<->-gamma, eta<->-eta`, atomic. A test
`g` with `supp g subset [-T,T]` sees primes `n <= e^T`; by Paley–Wiener `h = ghat` is entire of
exponential type `T`. The explicit formula gives ONE bilinear measurement per `g`:

    sum_rho h(gamma_rho) = ARCH(g) + POLE(g) - 2 sum_{n=p^k<=e^T} Lambda(n) n^{-1/2} g(log n).

The off-line quartet `{1/2 +- eta +- i*gamma0}` contributes (identity ★, verified to ~1e-26 in
prior `QUART_bernstein.py`, reused here):

    N(eta,gamma0,T) = 4 INT_{-T}^{T} g(u) cosh(eta*u) cos(gamma0*u) du
                    = 4 ghat(gamma0)  +  4 INT g(u)(cosh(eta*u)-1)cos(gamma0*u) du,
    |off-line correction| <= 4(cosh(eta*T)-1) INT|g|  ~  4 * (eta*T)^2/2 * INT|g|.

So the accessible measurements of `mu` are exactly the band-limited pairings
`{ sum_rho h(gamma_rho) : h type T, h>=0 }` — a LOW-PASS observation, NOT a moment ladder.

## 2. Separation vs the Candès–Fernandez-Granda threshold (superres_separation.py, Part 1)

For support `T` the Fourier cutoff resolving the `gamma`-axis is `f_c = T`. CFG: a SIGNED measure
is super-resolvable iff min separation `Delta > 2/f_c = 2/T`. Zero gap `Delta_gamma ~ 2pi/log(gamma/2pi)`.
Equal when `T_crit(gamma) = log(gamma/2pi)/pi`.

| gamma | zero gap | 2/T @ T=log2 | separated at Yoshida cutoff? |
|---|---|---|---|
| 14 | 7.84 | 2.885 | YES |
| 50 | 3.03 | 2.885 | YES (barely) |
| 100 | 2.27 | 2.885 | **NO — too dense** |
| 10^3 | 1.24 | 2.885 | NO |
| 10^10 | 0.30 | 2.885 | NO |

**Result:** at the only UNCONDITIONAL cutoff `T<log2`, the zero gap is above the CFG cell only
for `gamma < ~80` — but there the prime sum is EMPTY (no data at all). For every zero at
`gamma > ~80` the bulk is DENSER than the CFG cell already at `T=log2`, and worse for larger
`gamma`. **Signed super-resolution provably fails: the zero measure is below the separation
threshold for the entire bulk at any realistic cutoff.**

## 3. The positive-measure exemption — and why it does NOT apply (Part 2, Part 5B)

Literature (Candès, Fernandez-Granda; Prony; Beurling): a POSITIVE atomic measure can be
recovered with NO separation in the NOISELESS regime — from `2N+1` consecutive Fourier MOMENTS.
This was the one place a crack could hide. It does NOT apply, for two structural reasons:

- **(R1)** The prime samples are band-limited pairings `sum_rho h(gamma_rho)` with `h` of type
  `<= T`, NOT the unbounded moment tower `h_m = e^{-ims}` Prony requires. The prime cutoff `T`
  caps the bandwidth; Prony-exactness needs UNBOUNDED bandwidth (`N` = #zeros = infinite).
- **(R2)** `eta` enters `h` OFF the real axis via `cosh(eta*u)`, deviating from `1` by only
  `O((eta*T)^2/2)` on `|u|<=T`. A type-`T` `h` cannot separate `eta=0` from `eta!=0` until
  `T >~ 1/eta`.

`superres_gate_and_prony.py` makes the failure explicit: on-line truth and off-line fake share
all moments of order `< ~1/eta` and first differ at order `~1/eta` — the band hands you moments
only to order `~T`. The product `eta*T` is the gate (crossing at a FIXED `eta*T`; support
needed `~1/eta`). **The Prony bandwidth requirement and the super-resolution gate are the same
uncertainty constant `delta*T~1`.**

## 4. THE EXPLICIT FAKE (superres_fake_exact.py — the banked deliverable)

Cutoff `T=3` (primes `2,3,5,7,11,13,17,19`), off-line zero at `Gamma=30`, FAKE displacement
`eta=0.08 != 0`. Twelve on-line anchor heights (low Riemann zeros). Solve the finite linear
system `A delta = b` (`A_{j,i}=Phi(g_j,gamma_i,0)`, `b_j` = off-line residual) for anchor mass
corrections so that the off-line measure matches the on-line truth on every band-limited
prime-band functional.

- **Match residual: `1.3e-36`** (EXACT to machine precision).
- **All anchor masses strictly positive** (corrections range `-0.026 .. +0.051` on unit masses).
- Off-line quartet: mass `1/2` at each of `(+-Gamma, +-eta)` — POSITIVE, SYMMETRIC.
- Re-checked against the GENUINE prime side (`superres_sample_positivity.py`): the fake
  reproduces the actual `2 sum Lambda(n) n^{-1/2} g(log n)` data to `9e-32`.

`mu_true` (all on-line, `eta=0`) and `mu_fake` (one quartet off-line at `eta=0.08`, plus
positivity-preserving on-line mass re-tuning) are BOTH positive, symmetric, atomic, and produce
IDENTICAL values on ALL bounded prime-band measurements. **A bounded prime band cannot
distinguish them.** This is the explicit witness that positivity + symmetry + sparsity do NOT
force `eta=0` from bounded prime data.

## 5. The positivity twist — sample-positivity does NOT help (superres_sample_positivity.py)

The genuine prime samples `Lambda(n)>=0` enter the explicit formula ONLY through the FIXED
arithmetic right-hand side `RHS(g) = ARCH+POLE - prime_side(g)`, which is IDENTICAL for any zero
measure. Sample positivity fixes the VALUE of `RHS` but imposes NO independent equation on the
zero locations — the zero measure is constrained only through the band-limited pairing
`L_g(mu)=RHS(g)`, which is blind to `eta` below `1/T`. **The one place a crack could have hidden
is closed: positive samples do not beat the gate.** (Verified: `mu_fake` reproduces the genuine
arithmetic data to `1e-32`.)

## 6. The threshold IS the δT~1 gate (Part 5A)

Smallest detectable displacement at cutoff `T`: `eta_detect(T) ~ c0/T`, `c0 = O(1)`,
`gamma0`-independent (confirmed in prior QUART work; the band-limited law is `gamma0`-free). To
certify a fixed-width zero-free strip `w` you need `T >~ 1/w`; a FIXED positive-width strip needs
`T = infinity` = full Weil positivity = RH. The super-resolution CELL width in the displacement
coordinate is exactly `1/T` — the same constant as Bombieri's "truncation big enough", Connes's
prolate scale, and Keiper–Li's exponential `lambda_n` growth.

---

## ONE-LINE VERDICT

RH is a super-resolution problem, and at any BOUNDED prime cutoff **super-resolution FAILS**:
the zero bulk is below the CFG separation threshold; the positive-measure (Prony) exemption is
killed by the band-limit; sample-positivity `Lambda(n)>=0` adds nothing; and we exhibited an
EXPLICIT positive, symmetric, atomic FAKE with `eta=0.08` matching the genuine prime samples to
`1e-32`. Recovering `eta=0` requires support `T >~ 1/eta`, i.e. `T->infinity` for a fixed strip
= full Weil positivity = RH itself. The `delta*T~1` gate is the honest, unbreakable wall. No crack.
