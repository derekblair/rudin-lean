# PMA 9.42 independent hostile and source review

Verdict: accepted for the reviewed bytes. No hidden strengthening, vacuous
premise, incorrect derivative, or substitution of the integral notion was found.
The Gaussian section (9.43) was outside this review.

Source: the local PMA third-edition PDF, printed pages 236–237 (PDF 245–246).
Reviewed code: `rudin/Rudin/PMA/Chapter09/Integrals.lean`, from its imports through
the end of `pma9_42`, stopping before the first `PMA 9.43` comment.
SHA256 of that exact prefix:
`5fd0c3a3b5848848a1329f321d3c19cae0c9c2437ae539af7e3700036d88e9e2`.

## Hypothesis and conclusion comparison

- `hI` requires native Riemann–Stieltjes integrability of every parameter slice
  on the complete closed parameter interval, including its endpoints.
- `hD` supplies an actual derivative in the second variable, on one neighborhood
  of the interior point s, uniformly over the integration variable. This makes
  explicit the existence presupposed by the derivative expressions in printed
  condition (d). Taking epsilon=1 there gives such a common neighborhood.
  It imposes no derivative existence away from that neighborhood.
- `hU` is exactly uniform continuity at s in the parameter, uniformly over x.
  It neither requires continuity as a function of x nor joint continuity.
- The supplied derivative function D cannot be an arbitrary surrogate near s:
  `HasDerivAt (phi x) (D x t) t` fixes its value uniquely on the relevant region.
- `c < s < d` ensures a nonempty parameter interval and two-sided differentiation
  at an interior point. Total functions outside the rectangle do not affect the
  theorem because all limiting arguments occur in a smaller interior neighborhood.
- The conclusion separately proves integrability of the derivative slice and
  `HasDerivAt` of the integral with precisely its Riemann–Stieltjes integral as
  derivative. The order of variables is correct.
- `RSIntegrable` and `RSIntegral` are the Chapter 6 closed-cell Darboux definitions.
  No Lebesgue or Bochner replacement is used in 9.42. Monotonicity and endpoint
  order are already contained in each integrability witness; the explicit
  `_hab` and `_hAlpha` arguments are consequently redundant, not loopholes.
- Allowing a=b additionally covers the degenerate integration interval; it
  does not remove any printed case.

## Proof and nonvacuity checks

The difference quotients are integrable by native linearity. A mean-value
argument gives their uniform convergence to the derivative slice. The two
filter lemmas prove integrability of that limit and convergence of the native
integrals. Their `[l.NeBot]` assumptions prevent extraction from an empty filter;
the punctured real neighborhood used by 9.42 satisfies this requirement.
The estimates also handle zero integrator mass because their denominators use
mass+1 rather than dividing by the mass.

Two hostile client theorems were compiled:

1. An arbitrary native integrable multiplier q(x) gives the expected derivative
   for phi(x,t)=t*q(x). No continuity of q or the integrator is assumed.
2. The same conclusion is obtained at s=1 for phi(x,t)=abs(t)*q(x), with parameter
   interval [-1,2]. Thus a cusp at t=0 inside that interval is allowed; the
   formalization genuinely asks for derivatives only near s.

The clients are retained in `evidence/ch09-b-integrals-probe.lean`. To avoid
interfering with active changes to 9.43, the check fed the exact reviewed prefix
plus those clients to `lake env lean --stdin`; it exited 0. The result and prefix
hash are retained in `evidence/ch09-b-integrals-review-check.log`.
`pma9_42` and both client theorems use only `propext`, `Classical.choice`, and
`Quot.sound`. The final integrating build should also check the retained client
against the completed `Integrals` module.
