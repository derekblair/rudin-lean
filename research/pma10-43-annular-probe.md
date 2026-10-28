# New counterexample probe: growing annular frequencies are repairable

Research lane `thm-1043-final-clause`, 2026-10-27. This extends, rather than repeats, the
fixed-angular-profile repairs in the merged `pma10-43-endpoint-obstruction.md`
and `t14-cex-gauge-obstruction.md`. **Outcome: another candidate family is
excluded, not a counterexample or proof of the endpoint.** Everything below
is informal mathematics, accompanied by deterministic computation; none of
these analytic assertions has been formalized in Lean.

The new point is that the angular frequencies tend to infinity toward the
singularity, and then that independent radial and angular frequencies can
both tend to infinity. The latter is repaired by choosing which direction
to integrate separately on each annulus. This does not handle arbitrary
frequency superpositions with cancellations in the C¹ norm.

## 1. An exact whole-plane C¹ datum outside every C¹,α class

For n=1,2,... let

    r_n = 4^(−n),    m_n = 2^n,    a_n = 1/(n m_n),
    χ(s) = 64(s−1)^3(2−s)^3  for 1<s<2, and 0 otherwise.

χ is C² on R (its value and first two derivatives vanish at the endpoints),
and on [1,2] it satisfies

    |χ| ≤ 1,    |χ′| ≤ 12,    |χ″| ≤ 96.

Indeed, with t=s−1, χ′=192t²(1−t)²(1−2t) and
χ″=384t(1−t)(1−5t+5t²). The annuli r_n<r<2r_n are disjoint.
For x=(r cosθ,r sinθ)≠0 define

    h(x) = Σ_n a_n r_n χ(r/r_n) cos(m_n θ),    h(0)=0.

Each nonzero x meets at most one summand. The integer frequencies make the
formula single-valued, independent of the choice of angular coordinate.
On the nth annulus, with s=r/r_n,

    |h|/r ≤ a_n,
    |Dh| ≤ a_n(12+m_n) → 0.

The first bound gives Dh(0)=0, and the second gives its continuity. Thus
h∈C¹(R²), compactly supported in the disk r≤1/2. At
r=3r_n/2, θ=π/(2m_n), the tangential derivative has magnitude

    |Dh| = a_n m_n/(3/2) = 2/(3n).

Consequently Dh is not Hölder at 0 for ANY positive exponent: dividing this
quantity by (3r_n/2)^α tends to infinity for every α>0. This is an actual
non-Hölder member of the exact input class, not a Hölder-strengthened test.

## 2. A C² primitive, with complete Hessian calculation

Let e_r=(cosθ,sinθ), e_θ=(−sinθ,cosθ), and define

    V_n = (a_n r_n r/m_n) χ(r/r_n) sin(m_nθ) e_θ,
    V = Σ_n V_n,    V(0)=0.

The same disjoint supports apply. The polar divergence is
(1/r)∂_θ(V_n·e_θ)=a_n r_n χ(s)cos(m_nθ)=h_n.

For completeness, for any C² radial profile q(s), constants a,r₀, integer
m≥1, and V=(a r₀r/m)q(s)sin(mθ)e_θ, s=r/r₀, its Cartesian Hessian written
in the orthonormal polar input/output frames has the following components:

    D²V[e_r,e_r] = (a/m)(2q′+s q″) sin(mθ) e_θ,
    D²V[e_r,e_θ] = −(a/m)q′ sin(mθ)e_r + a q′ cos(mθ)e_θ,
    D²V[e_θ,e_θ] = −2a(q/s)cos(mθ)e_r
                    + (a/m)(q′−m²q/s)sin(mθ)e_θ.

The mixed component is symmetric. These are Cartesian derivatives expressed
in moving frames, not second polar partials. They follow from
H_rr=V_rr, H_rθ=V_rθ/r−V_θ/r², H_θθ=V_θθ/r²+V_r/r.
The sum of absolute values of these tensor components, counting the mixed
input entries twice, bounds the Frobenius norm, which is invariant under
orthonormal frame changes. For q=χ the displayed bounds imply

    ||D²V_n||_F ≤ a_n(m_n+26+252/m_n)
                 = (1+26/m_n+252/m_n²)/n → 0.

Also |V_n|=O((a_n/m_n)r²) and
|DV_n|=O(a_n(1+26/m_n)r), uniformly in n. Hence V and DV have successive
zero derivatives at 0, and D²V extends continuously by zero there. Across
each annulus boundary, χ,χ′,χ″ vanish. Therefore V∈C²(R²) and div V=h
globally, including at 0. Thus G(x,y,z)=(−V₂(x,y),V₁(x,y),0) is an actual
C² potential for the admissible C¹ divergence-free field F=(0,0,h).

## 3. The canonical radial primitive fails badly for the same datum

The usual radial divergence primitive is

    R(r,θ) = e_r r^(−1) ∫₀ʳ t h(t,θ) dt.

It is C¹ by differentiation of the radial homotopy formula for C¹ data. It
is C² away from 0: on any annulus bounded away from 0, the inner-annulus
Hessian series is absolutely uniformly convergent, since its coefficients
are bounded by a constant times a_k r_k³ m_k² = 2^(−5k)/k.

For the nth angular mode set J(s)=∫₁ˢ tχ(t)dt, truncated at 2 when s≥2.
Its contribution to R is

    a_n r_n² (J(s)/s)cos(m_nθ)e_r.

The scalar B(θ)=e_r·D²R[e_θ,e_θ], restricted to r=3r_n/2, has cos(m_nθ)
Fourier coefficient

    c_n = a_n[χ(s)/s − (m_n²+2)J(s)/s³] at s=3/2.

No other annulus contributes to that coefficient, since all m_k are
distinct. Exact rational integration gives

    J(3/2)=349/1120,    J(3/2)/(3/2)³=349/3780,
    c_n=a_n(1822−349m_n²)/3780.

Fourier coefficient extraction gives |c_n|≤2 supθ|B(θ)|. Since
|B|≤||D²R||_F, for n≥2,

    sup_{|x|=3r_n/2} ||D²R(x)||_F
      ≥ (349m_n²−1822)/(7560 n m_n) → ∞.

This proves that R is not C² in any neighborhood of 0. Its failure remains
only a failure of this operator, because Section 2 gives a C² replacement.
Unlike earlier fixed-profile witnesses, the bad derivative here is driven
by angular frequencies tending to infinity, not a fixed angular mode.

## 4. Independent radial/angular frequencies: a larger repairable class

Keep r_n=4^(−n) and χ as above. Let m_n be arbitrary positive integers,
k_n arbitrary real numbers ≥1, and a_n arbitrary real amplitudes satisfying

    ε_n = |a_n|(k_n+m_n) → 0.

Consider the separated oscillatory packets

    h_n = a_n r_n χ(s)cos(k_n s)cos(m_nθ),    s=r/r_n,
    h=Σh_n, h(0)=0.

This is globally C¹ with zero first jet at 0, since |h|/r≤|a_n| and
|Dh|≤|a_n|(12+k_n+m_n)→0. We prove there is a C² divergence primitive.
The construction is linear for fixed frequencies, but the choice of which
formula to use depends on the frequency pair.

### 4a. When k≤m, use the tangential primitive

Put q(s)=χ(s)cos(ks), and use the formula of Section 2 with q in place of χ.
Then |q|≤1, |q′|≤12+k, |q″|≤96+24k+k². The Hessian calculation gives

    ||D²V_n||_F
       ≤ |a|[m+26+2k+(252+53k+2k²)/m]
       ≤ 336 |a|m ≤ 450 ε_n.

It is supported on its own annulus. Its derivatives of orders j=0,1 also
satisfy |D^j V_n|≤450 ε_n r_n^(2−j) there.

### 4b. When k>m, use the radial primitive

Set J(s)=0 for s≤1 and

    J(s)=∫₁^{min(s,2)} tχ(t)cos(kt)dt,
    V_n=a r_n² (J(s)/s)cos(mθ)e_r.

Then div V_n=h_n. Integration by parts, with χ=0 at the endpoints, gives
the bound |J|≤27/k on all s. On 1≤s≤2,

    |J′|≤2,    |J″|≤25+2k.

The Hessian in polar frames is

    H_rr = a(J″/s−2J′/s²+2J/s³)cos(mθ)e_r,
    H_rθ = −am(J′/s²−2J/s³)sin(mθ)e_r
              +a(J′/s²−2J/s³)cos(mθ)e_θ,
    H_θθ = a[J′/s²−(m²+2)J/s³]cos(mθ)e_r
              −2am(J/s³)sin(mθ)e_θ.

The sum of absolute tensor entries on the active annulus is bounded by

    |a|[35+2k+4m+216/k+162m/k+27m²/k]
      ≤ 446 |a|k ≤ 450 ε_n.

For s≥2, J′=J″=0. The same sum is at most

    |a||J|(m²+6m+8)/s³
      ≤ 405 |a|(m²/k)s^(−3) ≤ 450 ε_n s^(−3).

Thus radial primitives have tails, rather than disjoint support; this is
accounted for explicitly. For j=0,1,2, their tail bounds are

    |D^j V_n(x)| ≤ 450 ε_n r^(2−j)(r_n/r)³  (r≥2r_n),

and their active-annulus bounds are ≤450 ε_n r_n^(2−j). For j=0,1 these
follow directly from the formula and |J|≤27/k, |J′|≤2; for j=2 they are the
bounds just calculated. Below the annulus, the field is zero.

### 4c. Sum and extend at the origin

At a fixed r>0 at most one field is in its active annulus. Every other
nonzero field is an inner radial tail. Geometric spacing gives a uniformly
bounded sum of (r_n/r)³ over these tails. The fields with outer annuli are
zero. The tail bounds also give C² normal convergence on every compact set
away from 0. Because ε_n→0, the resulting sum satisfies

    |V|=o(r²),    |DV|=o(r),    |D²V|=o(1)  as r→0.

It therefore extends C² with zero second jet, and its divergence is h.
This proves that arbitrarily increasing *both* frequencies does not defeat
all potentials within this separated, geometrically spaced packet class.

## 5. The precise remaining limitation

The construction is controlled by packetwise size |a_n|(k_n+m_n), not the
C¹ norm of an arbitrary sum of packets. For simultaneous superpositions at
one scale, the sum of these sizes can greatly exceed the C¹ norm of the
sum because of cancellations. Splitting into packets and choosing their
integration directions separately does not establish the universal
C¹→C² estimate required by the earlier obstruction report. Nor does this
argument cover arbitrary nonsmooth C¹ radial profiles: tangential inversion
uses q″, while radial inversion uses angular second derivatives. Frequency
localization can organize those derivatives but can also lose control of
the endpoint norm. Those estimates, with compatible gauges across all
overlapping frequencies, remain missing.

## 6. Reproducible computation and its limits

Run `python3 research/pma10-43-annular-probe.py` from the repository root.
It uses only the standard library, introduces no dependency, and writes
deterministic JSON to stdout. [`evidence/t14-quantitative/annular-frequency-results.json`](../evidence/t14-quantitative/annular-frequency-results.json) records the run. The code independently verifies the rational integral 349/1120,
checks the tangential Cartesian Hessian and divergence against centered
finite differences, and samples both the pure and mixed packet formulas.

- Maximum finite-difference Hessian error in the five recorded checks:
  3.12×10⁻⁷; maximum divergence error: 1.96×10⁻⁸.
- For n=8,16,32, the exact radial-Hessian lower bounds are respectively
  1.4771, 189.0878, and 6.1960×10⁶, while the rigorous tangential-Hessian
  upper bounds are 0.13818, 0.062525, and 0.0312501.
- Six mixed-frequency pairs test both choices of integration direction;
  the output labels all sampled maxima as sampled, not certified extrema.

The analytic inequalities above supply the informal proofs; finite
differences and samples are only implementation cross-checks. There is no
optimization over all gauges, no new universal estimate, no counterexample
to the printed contract, and no claimed Lean proof in this artifact.
