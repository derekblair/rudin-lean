#!/usr/bin/env python3
"""Deterministic candidate probe for Rudin 10.43 (Python standard library only).

This is NOT a kernel proof or a search over all gauges. The accompanying notes
give exact analytic proofs; this script checks their rational constant and
compares analytic Hessians to independent Cartesian finite differences.
All sampled extrema are labelled sampled and are not certified suprema.
"""

import cmath
from fractions import Fraction
import json
import math


def cutoff(s):
    if not 1.0 < s < 2.0:
        return 0.0, 0.0, 0.0
    t = s - 1.0
    q = 64.0 * t**3 * (1.0 - t)**3
    dq = 192.0 * t**2 * (1.0 - t)**2 * (1.0 - 2.0 * t)
    ddq = 384.0 * t * (1.0 - t) * (1.0 - 5.0 * t + 5.0 * t*t)
    return q, dq, ddq


def packet_profile(s, k):
    q, dq, ddq = cutoff(s)
    c, sn = math.cos(k*s), math.sin(k*s)
    return q*c, dq*c-k*q*sn, ddq*c-2*k*dq*sn-k*k*q*c


def tangential_hessian_squared_max(s, m, a, q, dq, ddq):
    # Exact maximum over theta of squared Frobenius norm, at fixed s.
    sin_coefficient = (a/m*(2*dq+s*ddq))**2 + 2*(a/m*dq)**2
    sin_coefficient += (a/m*(dq-m*m*q/s))**2
    cos_coefficient = 2*(a*dq)**2 + (2*a*q/s)**2
    return max(sin_coefficient, cos_coefficient)


def exact_midpoint_moment():
    # In t=s-1, s*chi(s)=64t^3-128t^4+128t^6-64t^7.
    coefficients = [0, 0, 0, 64, -128, 0, 128, -64]
    return sum(Fraction(c, j+1)*Fraction(1, 2)**(j+1)
               for j, c in enumerate(coefficients))


def pure_rows():
    result = []
    for n in (2, 4, 8, 16, 32):
        m = 2**n
        a = 1.0/(n*m)
        max_hessian = 0.0
        for j in range(4097):
            s = 1.0+j/4096
            max_hessian = max(max_hessian, tangential_hessian_squared_max(
                s, m, a, *cutoff(s)))
        result.append({
            "n": n, "m": m, "radius": 4.0**(-n),
            "datum_gradient_exact_at_selected_point": 2.0/(3*n),
            "tangential_hessian_sampled_max": math.sqrt(max_hessian),
            "tangential_hessian_analytic_upper_bound":
                (1+26/m+252/(m*m))/n,
            "radial_hessian_analytic_lower_bound":
                float(Fraction(349*m*m-1822, 7560*n*m)),
        })
    return result


def tangential_value(x, y, m, a):
    s = math.hypot(x, y)
    q = cutoff(s)[0]
    scalar = a/m*q*math.sin(m*math.atan2(y, x))
    return (-y*scalar, x*scalar)


def hessian_formula_cartesian(x, y, m, a):
    s, theta = math.hypot(x, y), math.atan2(y, x)
    q, dq, ddq = cutoff(s)
    sn, co = math.sin(m*theta), math.cos(m*theta)
    # Tensor indices: output, first input, second input; frame=(e_r,e_theta).
    hp = [[[0.0 for _ in range(2)] for _ in range(2)] for _ in range(2)]
    hp[1][0][0] = a/m*(2*dq+s*ddq)*sn
    hp[0][0][1] = hp[0][1][0] = -a/m*dq*sn
    hp[1][0][1] = hp[1][1][0] = a*dq*co
    hp[0][1][1] = -2*a*q/s*co
    hp[1][1][1] = a/m*(dq-m*m*q/s)*sn
    rot = [[math.cos(theta), -math.sin(theta)],
           [math.sin(theta), math.cos(theta)]]
    return [[[sum(rot[o][i]*rot[p][j]*rot[r][k]*hp[i][j][k]
                  for i in range(2) for j in range(2) for k in range(2))
              for r in range(2)] for p in range(2)] for o in range(2)]


def finite_difference_checks():
    checks = []
    for n in (1, 2, 4, 6, 8):
        m, a = 2**n, 1/(n*2**n)
        theta, s = 0.31/m, 1.23
        x, y = s*math.cos(theta), s*math.sin(theta)
        step = 0.0003/m
        value = lambda xx, yy: tangential_value(xx, yy, m, a)
        center = value(x, y)
        xp, xm = value(x+step, y), value(x-step, y)
        yp, ym = value(x, y+step), value(x, y-step)
        corners = [value(x+sx*step, y+sy*step)
                   for sx, sy in ((1,1), (1,-1), (-1,1), (-1,-1))]
        analytic = hessian_formula_cartesian(x, y, m, a)
        errors = []
        for o in range(2):
            numerical = [[(xp[o]-2*center[o]+xm[o])/step**2,
                          (corners[0][o]-corners[1][o]-corners[2][o]+corners[3][o])/(4*step**2)],
                         [0.0, (yp[o]-2*center[o]+ym[o])/step**2]]
            errors.extend(abs(numerical[p][r]-analytic[o][p][r])
                          for p, r in ((0,0), (0,1), (1,1)))
        numerical_divergence = (xp[0]-xm[0]+yp[1]-ym[1])/(2*step)
        expected = a*cutoff(s)[0]*math.cos(m*theta)
        checks.append({"n": n, "max_hessian_finite_difference_error": max(errors),
                       "divergence_finite_difference_error": abs(numerical_divergence-expected)})
    return checks


def oscillatory_moment(s, k):
    # Exact antiderivative formula evaluated in floating point. Used only for
    # k>=2. Endpoint cancellation can affect numerical precision; the proof
    # instead uses the uniform analytic integration-by-parts bound |J|<=27/k.
    coeff = [0.0, 0.0, 0.0, 64.0, -128.0, 0.0, 128.0, -64.0]

    def primitive(t):
        derivative = coeff[:]
        total = 0j
        for j in range(8):
            p = sum(c*t**i for i, c in enumerate(derivative))
            total += (-1)**j*p/(1j*k)**(j+1)
            derivative = [i*derivative[i] for i in range(1, len(derivative))]
        return cmath.exp(1j*k*(1+t))*total

    return (primitive(min(max(s-1, 0), 1))-primitive(0)).real


def mixed_rows():
    rows = []
    for k, m in ((1,2), (2,32), (32,2), (32,32), (256,4), (4,256)):
        sampled_gradient = sampled_hessian_sq = 0.0
        selected = "tangential" if k <= m else "radial"
        for j in range(4097):
            s = 1+j/4096
            q, dq, ddq = packet_profile(s, k)
            sampled_gradient = max(sampled_gradient, abs(dq), m*abs(q)/s)
            if selected == "tangential":
                value = tangential_hessian_squared_max(s, m, 1, q, dq, ddq)
            else:
                moment = oscillatory_moment(s, k)
                jp, jpp = s*q, q+s*dq
                rr = jpp/s-2*jp/s**2+2*moment/s**3
                rt_r = -m*(jp/s**2-2*moment/s**3)
                rt_t = jp/s**2-2*moment/s**3
                tt_r = jp/s**2-(m*m+2)*moment/s**3
                tt_t = -2*m*moment/s**3
                value = max(rr*rr+2*rt_t*rt_t+tt_r*tt_r,
                            2*rt_r*rt_r+tt_t*tt_t)
            sampled_hessian_sq = max(sampled_hessian_sq, value)
        rows.append({"radial_frequency": k, "angular_frequency": m,
                     "selected_primitive": selected,
                     "datum_gradient_sampled_max": sampled_gradient,
                     "primitive_hessian_sampled_max": math.sqrt(sampled_hessian_sq),
                     "analytic_hessian_upper_bound": 450*(k+m)})
    return rows


def main():
    moment = exact_midpoint_moment()
    assert moment == Fraction(349, 1120)
    checks = finite_difference_checks()
    assert max(row["max_hessian_finite_difference_error"] for row in checks) < 1e-5
    assert max(row["divergence_finite_difference_error"] for row in checks) < 1e-6
    print(json.dumps({
        "status": "candidate family repaired; no counterexample established",
        "evidence_level": "exact rational check and floating-point analytic/numerical cross-checks; not Lean",
        "midpoint_moment_exact": str(moment),
        "pure_angular_family": pure_rows(),
        "cartesian_finite_difference_checks": checks,
        "mixed_packets": mixed_rows(),
        "limitations": ["Finite differences and sampled extrema are not proofs.",
                        "No minimization over all gauges or arbitrary frequency superpositions.",
                        "No claim of universal C1 to C2 solvability."],
    }, indent=2))


if __name__ == "__main__":
    main()
