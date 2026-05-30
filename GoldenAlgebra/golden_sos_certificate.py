#!/usr/bin/env python3
"""
golden_sos_certificate.py
=========================

Sum-of-Squares / Positivstellensatz certificate solver for the
Riemann tail-margin inequality used in `rh.lean`.

Goal
----
Certify, on the adaptive domain

    D = { (T, x, y) :  T >= T0,  x >= 0,  y >= y_min,  2*(1 + x + y) <= T }

the polynomial inequality

    TailMargin_poly_lb(x, y, T)  -  ErrorBound_poly_ub(y, T)  >=  0

where
  * `TailMargin_poly_lb` is a polynomial *lower* bound for the
    Cauchy-kernel tail integral
        M(x, y, T) = integral_{T}^{infty}  K(x, y, u) * rho(u) du,
        K(x, y, u) = y * (1/((x-u)^2 + y^2) + 1/((x+u)^2 + y^2)),
        rho(u)    = (1/(2 pi)) * log(u / (2 pi)).
  * `ErrorBound_poly_ub` is a polynomial *upper* bound for the
    closed-form D=1/2 error
        E(y, T) = (y / T^2) * (8.5 * log(T) + 10.75)
    obtained by replacing log(T) with a polynomial majorant
    on T >= T0.

The script

  1. Builds the polynomial inequality symbolically (sympy).
  2. Encodes it as a Putinar Positivstellensatz problem
       p(x, y, T) = sigma_0 + sigma_T * (T - T0)
                  + sigma_x * x + sigma_y * (y - y_min)
                  + sigma_B * (T - 2*(1 + x + y))
     with each sigma_i a sum of squares.
  3. Solves the resulting SDP via `SumOfSquares` (uses `cvxpy` + `scs`).
  4. Extracts each sigma_i, prints it, sanity-checks the identity
     numerically on a random sample of points, and writes
       golden_sos_certificate.json   (machine-readable certificate)
       golden_sos_certificate.lean   (Lean stub with the polynomials).

Install
-------
    pip install sympy cvxpy scs SumOfSquares picos numpy

Run
---
    python golden_sos_certificate.py            # default T0=50, degree 4
    python golden_sos_certificate.py --T0 50 --degree 6
"""

from __future__ import annotations

import argparse
import json
import math
import sys
from pathlib import Path

import numpy as np
import sympy as sp


# ---------------------------------------------------------------------------
# 1. Polynomial models of the analytic objects
# ---------------------------------------------------------------------------

def log_upper_bound(T: sp.Symbol, T0: float) -> sp.Expr:
    """Polynomial upper bound for log(T) on [T0, infty).

    log is concave, so the tangent line at T = T0 lies above it:
        log(T) <= log(T0) + (T - T0) / T0.
    This is exact at T0 and accurate near T0; we use it because
    SOS only consumes polynomials.  A user who wants tighter bounds
    on a bounded slab can swap in a degree-2 secant majorant here.
    """
    return sp.Float(math.log(T0)) + (T - sp.Float(T0)) / sp.Float(T0)


def error_bound_poly(y: sp.Symbol, T: sp.Symbol, T0: float) -> sp.Expr:
    """Polynomial upper bound for E(y, T) = (y / T^2) * (8.5 log T + 10.75).

    We multiply through by T^2 later (clearing the rational denominator),
    so here we just return the *numerator polynomial* of the upper bound:

        T^2 * E(y, T)  <=  y * (8.5 * log_ub(T) + 10.75).
    """
    return y * (sp.Rational(85, 10) * log_upper_bound(T, T0)
                + sp.Rational(1075, 100))


def tail_margin_poly_lb(x: sp.Symbol, y: sp.Symbol, T: sp.Symbol,
                        T0: float) -> sp.Expr:
    """Polynomial lower bound for T^2 * M(x, y, T).

    Lemma (Cauchy-kernel asymptotic lower bound).  For u >= T and
    0 <= x, 0 < y with 2(1 + x + y) <= T:

        K(x, y, u)  =  y * (1/((x-u)^2 + y^2) + 1/((x+u)^2 + y^2))
                  >=  2 y / ((u + x + y)^2)        (since (x-u)^2 + y^2
                                                    <= (x+u)^2 + y^2
                                                    <= (x + u + y)^2)
                  >=  2 y / (3u/2)^2  =  8 y / (9 u^2)
        (uses x + y <= T/2 - 1 < u/2, so u + x + y < 3u/2).

    Integrate against rho(u) = (1/(2 pi)) log(u/(2 pi)):

        M(x, y, T)  >=  (4 y / (9 pi)) * integral_T^infty log(u/(2 pi))/u^2 du
                     =  (4 y / (9 pi T)) * (log(T / (2 pi)) + 1).

    Multiplied by T^2:

        T^2 * M(x, y, T)  >=  (4 y T / (9 pi)) * (log(T / (2 pi)) + 1).

    For SOS we need log polynomial too.  log is increasing, so on
    [T0, infty) we have log(T/(2 pi)) >= log(T0/(2 pi)) — a constant
    lower bound that is exact at T0 and throws away the growth.
    The growth lives in the explicit `T` factor, so this is enough.
    """
    log_lb_const = sp.Float(math.log(T0 / (2.0 * math.pi)))
    coeff = sp.Rational(4, 9) / sp.pi
    return coeff * y * T * (log_lb_const + 1)


# ---------------------------------------------------------------------------
# 2. SOS / Positivstellensatz problem
# ---------------------------------------------------------------------------

def scalar_22_15_certificate(T0: float, verbose: bool = True):
    """Closed-form certificate for the rh.lean `scalarGap22_15` inequality.

    Target:  scalarGap22_15(T) >= 0 for all T >= T0,  where
        scalarGap22_15(T)
            = (22/15) * T / (2*pi) * log(T/(2*pi))
              - ((17/2) * log T + 439/10).

    Polynomialization on [T0, infty):
        log(T)       <=  log(T0) + (T - T0)/T0          (concave -> tangent above)
        log(T/(2pi)) >=  log(T0/(2pi))                  (monotone -> floor)

    Substituting gives a polynomial under-approximation
        gap_poly(T) = a * T + b
    which equals the true gap exactly at T = T0 and lies below it for T > T0.
    Schmüdgen certificate (T >= T0):
        gap_poly(T) = a * (T - T0)  +  (a * T0 + b).

    Both `a` and the corner slack `a*T0 + b` come out positive for the
    rh.lean coefficients at T0 = 140.  (At T0 = 122 the corner slack
    crosses zero — the rh.lean choice T0 = 140 has comfortable margin.)
    """
    try:
        import mpmath as mp
    except ImportError:
        mp = None

    if mp is not None:
        # High-precision rigorous values.
        mp.mp.dps = 60
        T0m = mp.mpf(T0)
        two_pi = 2 * mp.pi
        log_T0_over_2pi = mp.log(T0m / two_pi)
        log_T0 = mp.log(T0m)
        a_mp = mp.mpf('22') / 15 * log_T0_over_2pi / two_pi - mp.mpf('17') / 2 / T0m
        b_mp = -mp.mpf('17') / 2 * (log_T0 - 1) - mp.mpf('439') / 10
        slack_mp = a_mp * T0m + b_mp
        # Derivative at T0:  (22/15)/(2pi) * (log(T0/(2pi)) + 1) - 17/(2 T0)
        dgap_at_T0 = (mp.mpf('22') / 15) / two_pi * (log_T0_over_2pi + 1) \
                     - mp.mpf('17') / (2 * T0m)
        # True gap at T0 (this is the rh.lean value; gap_poly agrees here).
        gap_true_at_T0 = (mp.mpf('22') / 15 * T0m / two_pi) * log_T0_over_2pi \
                         - (mp.mpf('17') / 2 * log_T0 + mp.mpf('439') / 10)
        a, b, slack = float(a_mp), float(b_mp), float(slack_mp)
    else:
        a = (22 / 15) * math.log(T0 / (2 * math.pi)) / (2 * math.pi) - 17 / (2 * T0)
        b = -(17 / 2) * (math.log(T0) - 1) - 439 / 10
        slack = a * T0 + b
        gap_true_at_T0 = ((22 / 15) * T0 / (2 * math.pi)) * math.log(T0 / (2 * math.pi)) \
                         - ((17 / 2) * math.log(T0) + 439 / 10)
        dgap_at_T0 = ((22 / 15) / (2 * math.pi)) * (math.log(T0 / (2 * math.pi)) + 1) \
                     - 17 / (2 * T0)
        a_mp = b_mp = slack_mp = None

    x, y, T = sp.symbols('x y T', real=True)
    target = sp.Float(a) * T + sp.Float(b)
    g_T = T - sp.Float(T0)
    g_x = x
    g_y = y                # placeholder (unused in scalar inequality)
    g_B = T - 2 * (1 + x + y)
    single_constraints = {'g_T': g_T, 'g_x': g_x, 'g_y': g_y, 'g_B': g_B}

    sigmas = {
        'sigma_g_T':   (sp.Float(a),     g_T),
        'sigma_empty': (sp.Float(slack), sp.Integer(1)),
    }

    if verbose:
        print("=" * 72)
        print("scalarGap22_15 certificate  (rh.lean CLVII-A target)")
        print("=" * 72)
        print(f"  T0                       = {T0}")
        print(f"  scalarGap22_15(T0)  (true)  = {float(gap_true_at_T0):.15g}")
        if mp is not None:
            # Use mpmath for honest displayed precision.
            print(f"  a  = (22/15)*log(T0/2pi)/(2pi) - 17/(2 T0)")
            print(f"     = {mp.nstr(a_mp, 30)}")
            print(f"  b  = -(17/2)*(log(T0) - 1) - 439/10")
            print(f"     = {mp.nstr(b_mp, 30)}")
            print(f"  corner slack  a*T0 + b   = {mp.nstr(slack_mp, 30)}")
            print(f"  derivative g'(T0)        = {mp.nstr(dgap_at_T0, 30)}")
        else:
            print(f"  a                          = {a:.15g}")
            print(f"  b                          = {b:.15g}")
            print(f"  corner slack  a*T0 + b     = {slack:.15g}")
            print(f"  derivative g'(T0)          = {dgap_at_T0:.15g}")
        print(f"  Certificate:  gap_poly(T) = a*(T-T0) + (a*T0+b)")
        if a < 0 or slack < 0:
            sys.exit("Negative SOS multiplier — bump T0.")

    return target, single_constraints, sigmas, 'closed_form_scalar22_15'


def closed_form_certificate(T0: float, y_min: float, verbose: bool = True):
    """Closed-form Schmüdgen certificate for the bilinear target a*T*y + b*y.

    By construction `target = a*T*y + b*y` with a, b real and a > 0 (the
    tail margin grows linearly in T while the error grows logarithmically).
    On the slab { T >= T0, y >= y_min } the decomposition

        target = a * (y - y_min) * (T - T0)
               + a * y_min      * (T - T0)
               + (a*T0 + b)     * (y - y_min)
               + y_min * (a*T0 + b)

    is a Schmüdgen certificate with four non-negative constant
    multipliers, provided the slack at the corner

        slack(T0) := a * T0 + b

    is non-negative.  No SDP needed.
    """
    x, y, T = sp.symbols('x y T', real=True)

    tail_lb_T2 = tail_margin_poly_lb(x, y, T, T0).subs(sp.pi, sp.Float(math.pi))
    err_ub_T2 = error_bound_poly(y, T, T0)
    target = sp.expand(tail_lb_T2 - err_ub_T2)

    poly = sp.Poly(target, x, y, T)
    coeffs = dict(poly.terms())  # {(ex, ey, eT): coeff}
    # The target should only contain monomials y, T*y.
    unexpected = [m for m in coeffs if m not in {(0, 1, 0), (0, 1, 1)}]
    if unexpected:
        sys.exit(f"closed-form path expected target = a*T*y + b*y; "
                 f"got unexpected monomials {unexpected}: {target}")
    a = float(coeffs.get((0, 1, 1), 0))
    b = float(coeffs.get((0, 1, 0), 0))
    slack_at_corner = a * T0 + b

    if verbose:
        print("=" * 72)
        print("Closed-form Schmüdgen certificate (bilinear target a*T*y + b*y)")
        print("=" * 72)
        print(f"  a = {a:.15g}")
        print(f"  b = {b:.15g}")
        print(f"  slack at corner  (a*T0 + b)  = {slack_at_corner:.6f}")
        if slack_at_corner < 0:
            sys.exit("Slack at (T=T0, y=y_min) is negative; "
                     "polynomial bounds are not feasible — raise T0.")

    g_T = T - sp.Float(T0)
    g_x = x
    g_y = y - sp.Float(y_min)
    g_B = T - 2 * (1 + x + y)
    single_constraints = {'g_T': g_T, 'g_x': g_x, 'g_y': g_y, 'g_B': g_B}

    sigmas = {
        'sigma_g_T_g_y':  (sp.Float(a),
                           g_T * g_y),
        'sigma_g_T':      (sp.Float(a * y_min),
                           g_T),
        'sigma_g_y':      (sp.Float(slack_at_corner),
                           g_y),
        'sigma_empty':    (sp.Float(y_min * slack_at_corner),
                           sp.Integer(1)),
    }

    return target, single_constraints, sigmas, 'closed_form'


def build_and_solve(T0: float, y_min: float, degree: int,
                    verbose: bool = True, solver: str = 'cvxopt'):
    try:
        from SumOfSquares import SOSProblem, poly_variable
    except ImportError as exc:
        sys.exit(
            "FATAL: SumOfSquares is not installed.\n"
            "       pip install sympy cvxpy scs SumOfSquares picos cvxopt\n"
            f"       (import error: {exc})"
        )

    x, y, T = sp.symbols('x y T', real=True)

    # Build the polynomial inequality and substitute numerical pi so the
    # coefficients are plain floats (SumOfSquares matches monomial
    # coefficients; symbolic pi confuses that step).
    tail_lb_T2 = tail_margin_poly_lb(x, y, T, T0).subs(sp.pi, sp.Float(math.pi))
    err_ub_T2 = error_bound_poly(y, T, T0)
    target = sp.expand(tail_lb_T2 - err_ub_T2)

    # Domain constraints g_i(x, y, T) >= 0:
    g_T = T - sp.Float(T0)
    g_x = x
    g_y = y - sp.Float(y_min)
    g_B = T - 2 * (1 + x + y)  # geometric boundary
    single_constraints = {
        'g_T': g_T,
        'g_x': g_x,
        'g_y': g_y,
        'g_B': g_B,
    }

    if verbose:
        print("=" * 72)
        print("Schmüdgen Positivstellensatz problem")
        print("=" * 72)
        print(f"  domain   :  T >= {T0},  x >= 0,  y >= {y_min},"
              f"  2(1+x+y) <= T")
        print(f"  target polynomial (cleared by * T^2):")
        sp.pprint(target)
        print(f"  multiplier degree budget: {degree}")
        print()

    # ------------------------------------------------------------------ #
    # Schmüdgen: include every subset-product of the g_i (length 0..k),   #
    # each with its own SOS multiplier.                                   #
    #                                                                     #
    #   target  =  sum_{S subset of {g_i}}  sigma_S  *  prod(S)           #
    #                                                                     #
    # For 4 single constraints we get 1 + 4 + 6 = 11 subsets of size <=2  #
    # (we cap subset size at 2 — enough for bilinear targets, keeps the   #
    # SDP small).                                                          #
    # ------------------------------------------------------------------ #
    from itertools import combinations

    prob = SOSProblem()
    variables = [x, y, T]

    sigma_polys = {}      # name -> sympy poly with picos coefficient vars
    product_polys = {}    # name -> product of g_i's

    # Subset of size 0  (the free SOS term).
    sigma_polys['sigma_empty'] = poly_variable('s_empty', variables, degree)
    product_polys['sigma_empty'] = sp.Integer(1)
    prob.add_sos_constraint(sigma_polys['sigma_empty'], variables,
                            name='s_empty')

    # Subsets of size 1 and 2.
    g_items = list(single_constraints.items())
    for k in (1, 2):
        for subset in combinations(g_items, k):
            names = [n for n, _ in subset]
            prod_g = sp.Integer(1)
            for _, g in subset:
                prod_g = prod_g * g
            tag = 'sigma_' + '_'.join(names)
            sym_tag = 's_' + '_'.join(n[2:] for n in names)
            sig = poly_variable(sym_tag, variables, degree)
            sigma_polys[tag] = sig
            product_polys[tag] = prod_g
            prob.add_sos_constraint(sig, variables, name=sym_tag)

    # Putinar/Schmüdgen identity: target == sum_S sigma_S * prod(S).
    rhs = sp.Integer(0)
    for tag in sigma_polys:
        rhs = rhs + sigma_polys[tag] * product_polys[tag]
    identity = sp.expand(target - rhs)
    poly_identity = sp.Poly(identity, *variables)

    n_eq = 0
    for monom_coeff in poly_identity.coeffs():
        pic_expr = prob.sp_to_picos(sp.expand(monom_coeff))
        prob.add_constraint(pic_expr == 0)
        n_eq += 1
    if verbose:
        print(f"  Schmüdgen subsets used: {len(sigma_polys)}")
        print(f"  coefficient-matching equalities: {n_eq}")
        print(f"  solving via {solver} ...")

    prob.solve(solver=solver)
    status = prob.status
    if verbose:
        print(f"SDP status: {status}")
    if 'optimal' not in str(status).lower() and 'feasible' not in str(status).lower():
        sys.exit(f"SDP did not solve (status={status}). "
                 "Try --degree 4 or relax y_min / T0.")

    # ------------------------------------------------------------------ #
    # Recover concrete polynomials by substituting solved picos values    #
    # back into the sympy expressions, then prune coefficients smaller    #
    # than tol (these are numerical noise).                               #
    # ------------------------------------------------------------------ #
    def prune(expr, tol=1e-8):
        expr = sp.expand(expr)
        poly = sp.Poly(expr, *variables)
        cleaned = sp.Integer(0)
        for monom, coeff in poly.terms():
            c = float(coeff)
            if abs(c) >= tol:
                term = sp.Float(c)
                for var, exp in zip(variables, monom):
                    if exp:
                        term = term * var**exp
                cleaned = cleaned + term
        return sp.expand(cleaned)

    recovered = {}
    for name in sigma_polys:
        raw = prob.subs_with_sol(sigma_polys[name])
        recovered[name] = (prune(raw), product_polys[name])
    return target, single_constraints, recovered, str(status)


# ---------------------------------------------------------------------------
# 3. Numeric sanity check + Lean stub emission
# ---------------------------------------------------------------------------

def numeric_check(target, sigmas, T0, y_min, n_samples=4000, rng_seed=0):
    rng = np.random.default_rng(rng_seed)
    x, y, T = sp.symbols('x y T', real=True)

    f_target = sp.lambdify((x, y, T), target, 'numpy')
    f_terms = []
    for name, (sigma, product) in sigmas.items():
        f_sigma = sp.lambdify((x, y, T), sigma, 'numpy')
        f_prod = sp.lambdify((x, y, T), product, 'numpy')
        f_terms.append((name, f_sigma, f_prod))

    max_err = 0.0
    min_target = math.inf
    min_sigma = {name: math.inf for name, _, _ in f_terms}
    for _ in range(n_samples):
        T_val = rng.uniform(T0, 10 * T0)
        x_val = rng.uniform(0, (T_val / 2) - 1 - y_min)
        y_val = rng.uniform(y_min, max(y_min + 1e-3,
                                       (T_val / 2) - 1 - x_val))
        lhs = float(f_target(x_val, y_val, T_val))
        rhs = 0.0
        for name, fs, fp in f_terms:
            sval = float(fs(x_val, y_val, T_val))
            rhs += sval * float(fp(x_val, y_val, T_val))
            if sval < min_sigma[name]:
                min_sigma[name] = sval
        max_err = max(max_err, abs(lhs - rhs))
        if lhs < min_target:
            min_target = lhs
    return max_err, min_target, min_sigma


def emit_lean_stub(path: Path, T0: float, y_min: float, target, constraints,
                   sigmas, status: str):
    def lean_of(expr):
        return sp.sstr(sp.expand(expr))

    body = [
        "/-",
        f"  Auto-generated SOS certificate (SDP status: {status})",
        f"  Domain: T >= {T0}, x >= 0, y >= {y_min}, 2(1 + x + y) <= T",
        "",
        "  Inequality (cleared of denominators, multiplied by T^2):",
        f"    {lean_of(target)}  >=  0",
        "",
        "  Schmüdgen decomposition:",
        "    target = sum_S  sigma_S * prod(g_i in S)",
        "  where each sigma_S is a sum of squares and each g_i >= 0 on the slab.",
        "-/",
        "",
        "import Mathlib.Analysis.SpecialFunctions.Pow.Real",
        "",
        "namespace GoldenAlgebra.SOSCertificate",
        "",
        f"def T0 : ℝ := {T0}",
        f"def yMin : ℝ := {y_min}",
        "",
    ]
    for name, g in constraints.items():
        body.append(f"-- constraint {name} >= 0:  {lean_of(g)}")
    body.append("")
    for name, (sigma, product) in sigmas.items():
        body.append(f"-- {name}")
        body.append(f"--   product : {lean_of(product)}")
        body.append(f"--   sigma   : {lean_of(sigma)}")
        body.append("")
    body.append("end GoldenAlgebra.SOSCertificate")
    path.write_text("\n".join(body))


def emit_json(path: Path, T0: float, y_min: float, target, constraints,
              sigmas, status: str):
    payload = {
        'sdp_status': status,
        'domain': {
            'T0': T0,
            'y_min': y_min,
            'constraint_polynomials': {k: str(v) for k, v in constraints.items()},
        },
        'target_polynomial': str(target),
        'schmudgen_certificate': {
            name: {'product': str(p), 'sigma': str(s)}
            for name, (s, p) in sigmas.items()
        },
    }
    path.write_text(json.dumps(payload, indent=2))


# ---------------------------------------------------------------------------
# 4. Entrypoint
# ---------------------------------------------------------------------------

def main():
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('--T0', type=float, default=50.0,
                        help='lower endpoint of T (default 50)')
    parser.add_argument('--y-min', type=float, default=0.1,
                        help='lower endpoint of y (default 0.1)')
    parser.add_argument('--degree', type=int, default=4,
                        help='SOS multiplier degree budget (default 4)')
    parser.add_argument('--out-dir', type=Path,
                        default=Path(__file__).parent,
                        help='where to write certificate files')
    parser.add_argument('--mode', choices=('closed', 'sdp', 'scalar22_15'),
                        default='closed',
                        help='"closed" — exact algebraic Schmüdgen for the '
                             'bilinear y*T target (default). '
                             '"sdp" — full SOS solver on the same target. '
                             '"scalar22_15" — closed-form certificate for the '
                             'rh.lean scalarGap22_15 inequality at T0 = 140.')
    parser.add_argument('--quiet', action='store_true')
    args = parser.parse_args()

    if args.mode == 'closed':
        target, constraints, sigmas, status = closed_form_certificate(
            T0=args.T0, y_min=args.y_min, verbose=not args.quiet,
        )
    elif args.mode == 'scalar22_15':
        target, constraints, sigmas, status = scalar_22_15_certificate(
            T0=args.T0, verbose=not args.quiet,
        )
    else:
        target, constraints, sigmas, status = build_and_solve(
            T0=args.T0, y_min=args.y_min, degree=args.degree,
            verbose=not args.quiet,
        )

    if not args.quiet:
        print()
        print("=" * 72)
        print("Recovered Schmüdgen certificate (pruned, tol=1e-8)")
        print("=" * 72)
        for name, (sigma, product) in sigmas.items():
            print(f"\n{name}")
            print(f"  product = {sp.sstr(product)}")
            print(f"  sigma   = {sp.sstr(sigma)}")

    print("\nNumeric sanity check ...")
    max_err, min_target, min_sigma = numeric_check(target, sigmas,
                                                   T0=args.T0,
                                                   y_min=args.y_min)
    print(f"  max |target - sum_S sigma_S * prod(S)|  = {max_err:.3e}")
    print(f"  min target on samples                    = {min_target:.6f}")
    print(f"  min sigma values on samples (should be >= 0):")
    for name, v in min_sigma.items():
        flag = "" if v >= -1e-6 else "  <-- NEGATIVE"
        print(f"    {name:30s} {v:14.6e}{flag}")
    if min_target < -1e-6:
        print("  WARNING: target dipped below zero on the sample — "
              "polynomial bounds may not be valid.")
    if max_err > 1e-3:
        print("  WARNING: identity error is large — SDP solution may be "
              "numerically loose; try --degree 4 or different --T0.")

    json_path = args.out_dir / 'golden_sos_certificate.json'
    lean_path = args.out_dir / 'golden_sos_certificate.lean'
    emit_json(json_path, args.T0, args.y_min, target, constraints, sigmas,
              status)
    emit_lean_stub(lean_path, args.T0, args.y_min, target, constraints,
                   sigmas, status)
    print(f"\nWrote:\n  {json_path}\n  {lean_path}")


if __name__ == '__main__':
    main()
