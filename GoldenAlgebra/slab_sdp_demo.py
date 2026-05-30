#!/usr/bin/env python3
"""
slab_sdp_demo.py
================

Run an actual Sum-of-Squares solver on a slab inequality.

Target: SlabPolyIneq [] 140 200 (1/2) (49/20).
Reason: this is the slab `slabPolyIneq_140_200_empty_cloud` already proves
analytically in rh.lean.  An independent SOS certificate at the polynomial
level confirms the SDP route works end-to-end (even though it is unnecessary
here because the analytic chain suffices).

Polynomialization (after multiplying both sides by `T^2 * ((T-x)^2 + y^2) *
((T+x)^2 + y^2)`):

  closedFormSErrorBoundCD (1/2) (49/20) y T
      = (y / T^2) * ((17/2) * log T + 439/10)

  smoothTailRationalLowerBoundAbs x y T
      = (log(T/(2*pi)) / (2*pi)) * y * ((T-|x|)/((T-|x|)^2 + y^2)
                                        + (T+|x|)/((T+|x|)^2 + y^2))

For `x >= 0` (use `slabPolyIneq_of_nonneg_x` on the Lean side) we replace
`|x|` with `x` and avoid the absolute value.  The two analytic constants:

  log T          replaced by upper bound  L_hi(T)  on [Tmin, Tmax]
  log(T/(2*pi)) replaced by lower bound  L_lo(T)  on [Tmin, Tmax]

We use the tangent at the slab's lower endpoint as the upper bound (`log`
is concave, tangent above) and the constant value at the lower endpoint
as the lower bound (`log` is increasing).

The resulting polynomial inequality is degree ~6 in `(x, y, T)` and
amenable to a small SDP.
"""

from __future__ import annotations

import math
import sys

import numpy as np
import sympy as sp


def setup_target(Tmin: float, Tmax: float, C: float, D: float):
    """Build the cleared-denominator target polynomial."""
    x, y, T = sp.symbols('x y T', real=True)

    # Tangent-line upper bound for log T on [Tmin, Tmax]:
    #   log T <= log(Tmin) + (T - Tmin)/Tmin   (concave => tangent above).
    log_T_hi = sp.Float(math.log(Tmin)) + (T - sp.Float(Tmin)) / sp.Float(Tmin)
    # Constant lower bound for log(T/(2*pi)) on [Tmin, Tmax]:
    log_ratio_lo = sp.Float(math.log(Tmin / (2 * math.pi)))
    two_pi = sp.Float(2 * math.pi)

    # error_ub_poly = numerator of (17C*log_T_hi + 17D + 9C/2) * y / T^2.
    # After multiplying by T^2 the y/T^2 becomes y.
    err_coeff = sp.Float(17 * C) * log_T_hi + sp.Float(17 * D + 9 * C / 2)
    err_T2 = err_coeff * y  # = T^2 * closedFormSErrorBoundCD (with log_T_hi)

    # smooth tail lower bound (x >= 0): use log_ratio_lo constant.
    rho_lo = log_ratio_lo / two_pi
    Tm = T - x
    Tp = T + x
    Dm = Tm**2 + y**2
    Dp = Tp**2 + y**2

    tail = rho_lo * y * (Tm / Dm + Tp / Dp)
    # cloud is empty for this demo.
    margin = tail  # = smoothTailRationalLowerBoundAbs x y T (lower bound)

    # Multiply both sides by T^2 * Dm * Dp to clear denominators.
    err_cleared = err_T2 * Dm * Dp                     # already has y, not 1/T^2
    margin_cleared = rho_lo * y * (Tm * Dp + Tp * Dm) * T**2
    target_poly = sp.expand(margin_cleared - err_cleared)

    return x, y, T, target_poly, Dm, Dp


def build_and_solve(Tmin: float, Tmax: float, C: float, D: float,
                    degree: int = 4, verbose: bool = True):
    from SumOfSquares import SOSProblem, poly_variable

    x, y, T, target, Dm, Dp = setup_target(Tmin, Tmax, C, D)

    if verbose:
        print(f"slab: T in [{Tmin}, {Tmax}],  (C, D) = ({C}, {D})")
        print(f"target polynomial degree: {sp.Poly(target, x, y, T).total_degree()}")
        n_monoms = len(sp.Poly(target, x, y, T).terms())
        print(f"target has {n_monoms} monomials")

    # Domain constraints.
    g_T_lo = T - sp.Float(Tmin)
    g_T_hi = sp.Float(Tmax) - T
    g_x = x
    g_y = y
    g_reg = T - 2 * (1 + x + y)    # 2(1+x+y) <= T  (adaptive region)

    constraints = {
        'g_T_lo': g_T_lo,
        'g_T_hi': g_T_hi,
        'g_x':    g_x,
        'g_y':    g_y,
        'g_reg':  g_reg,
    }

    prob = SOSProblem()
    vars_ = [x, y, T]

    # Putinar certificate: target = sigma_0 + sum sigma_i * g_i
    sigma_empty = poly_variable('s0', vars_, degree)
    prob.add_sos_constraint(sigma_empty, vars_, name='s0')
    rhs = sigma_empty

    sigma_polys = {'sigma_empty': (sigma_empty, sp.Integer(1))}
    for name, g in constraints.items():
        sig = poly_variable('s_' + name[2:], vars_, degree)
        prob.add_sos_constraint(sig, vars_, name='s_' + name[2:])
        sigma_polys['sigma_' + name] = (sig, g)
        rhs = rhs + sig * g

    identity = sp.expand(target - rhs)
    poly_id = sp.Poly(identity, *vars_)
    n_eq = 0
    for monom_coeff in poly_id.coeffs():
        pic_expr = prob.sp_to_picos(sp.expand(monom_coeff))
        prob.add_constraint(pic_expr == 0)
        n_eq += 1
    if verbose:
        print(f"SDP: {n_eq} coefficient-matching equalities,"
              f" {len(sigma_polys)} SOS multipliers, degree budget {degree}")

    if verbose:
        print("Solving SDP via cvxopt ...")
    try:
        prob.solve(solver='cvxopt')
    except Exception as e:
        print(f"  cvxopt failed: {e}")
        return None
    status = str(prob.status)
    if verbose:
        print(f"SDP status: {status}")
    return status, sigma_polys, target, constraints


def numeric_check(target, sigmas, constraints, Tmin, Tmax,
                  n_samples=1000, rng_seed=42):
    rng = np.random.default_rng(rng_seed)
    x, y, T = sp.symbols('x y T', real=True)
    f_target = sp.lambdify((x, y, T), target, 'numpy')
    f_sigs = {n: (sp.lambdify((x, y, T), s, 'numpy'),
                  sp.lambdify((x, y, T), p, 'numpy'))
              for n, (s, p) in sigmas.items()}

    max_err = 0.0
    min_target = math.inf
    for _ in range(n_samples):
        T_val = rng.uniform(Tmin, Tmax)
        xy_max = T_val / 2 - 1
        if xy_max <= 0: continue
        x_val = rng.uniform(0, xy_max)
        y_val = rng.uniform(1e-3, max(1e-3, xy_max - x_val))
        if x_val + y_val > xy_max: continue
        lhs = float(f_target(x_val, y_val, T_val))
        rhs = sum(float(s(x_val, y_val, T_val) * p(x_val, y_val, T_val))
                  for s, p in f_sigs.values())
        max_err = max(max_err, abs(lhs - rhs))
        if lhs < min_target: min_target = lhs
    return max_err, min_target


def main():
    import argparse
    p = argparse.ArgumentParser()
    p.add_argument('--Tmin', type=float, default=140.0)
    p.add_argument('--Tmax', type=float, default=200.0)
    p.add_argument('--C', type=float, default=0.5)
    p.add_argument('--D', type=float, default=49 / 20)
    p.add_argument('--degree', type=int, default=4)
    args = p.parse_args()

    print("=" * 72)
    print("slab_sdp_demo: actual SDP on the SlabPolyIneq form")
    print("=" * 72)
    print()

    out = build_and_solve(args.Tmin, args.Tmax, args.C, args.D, args.degree)
    if out is None or 'optimal' not in out[0].lower():
        print(f"\nSDP did not produce a certificate (status: "
              f"{out[0] if out else 'failed'}).")
        if args.degree < 8:
            print(f"Try --degree {args.degree + 2} or smaller slab.")
        return
    status, sigmas, target, constraints = out
    print(f"\nSDP found a certificate at degree {args.degree}!")

    max_err, min_target = numeric_check(target, sigmas, constraints,
                                         args.Tmin, args.Tmax)
    print(f"\nNumeric sanity check (1000 samples):")
    print(f"  max |identity residual|      = {max_err:.3e}")
    print(f"  min target on samples        = {min_target:.6f}")
    if min_target >= 0:
        print(f"  inequality verified empirically.")
    else:
        print(f"  WARNING: target dipped negative — bound chain may be off.")


if __name__ == '__main__':
    main()
