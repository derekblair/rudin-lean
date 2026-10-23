# Independent hostile review: Chapter 8 double series, Taylor, and operations

Reviewer: `power_series_api`, 2026-10-22. The reviewer authored neither the
three reviewed modules nor their contracts. The review read the independent
source inventory in `research/pma-ch08-source-review.md`, each complete source
file, the `Represents`/analytic bridge in `PowerSeries.lean`, and the relevant
native Chapter 6/7 integral definitions and contracts. No Lean or Lake invocation
and no reviewed-source mutation was performed during this review. Kernel build,
client elaboration, and recursive axiom results remain separate production gates.

## Frozen inputs

Paths are relative to `rudin/`.

| File | SHA-256 | Decision |
|---|---|---|
| `Rudin/PMA/Chapter08/DoubleSeries.lean` | `7cb78d7c111d3be2a9bc0f5e67a02c0020e988ba39e24f67db050787aae57e7e` | ACCEPT |
| `Rudin/PMA/Chapter08/Taylor.lean` | `9c666fab54b9e7a3a7b7ac073e5b9ca9a8a7d2d31e2ccb7a7be303af472c0347` | ACCEPT |
| `Rudin/PMA/Chapter08/Operations.lean` | `2b4ce0759198e1a2c854a8398d7b285c5edd64de0d36fd19aa3ba824245ae07a` | ACCEPT |

The Taylor hash includes the final `mul_assoc` simplification and the implicit
point argument in applications of `EqOn`. These changes preserve every contract.

## PMA 8.3: existence before interchange

The hypotheses match the source: every norm row has an ordered sum `b i`, and
the ordered series of those row sums converges. The contract does not assume
unconditional summability of the original complex matrix. Nonnegativity of
`b i` is proved from the norm-row sums, so converting ordered convergence of `b`
to `Summable b` is justified rather than an extra premise.

The result explicitly supplies `rows`, `columns`, and a common outer sum `s`.
Every inner row, every inner column, and both outer series receive a
`Chapter03.SeriesHasSum` proof. The intermediate product-index summability is
derived from the absolute row data before any `tsum` is used. Consequently a
matrix with an undefined inner sum cannot satisfy the conclusion merely because
Lean totalizes its `tsum` to zero. Both outer sums are established by actual
`HasSum.tendsto_sum_nat` conversions.

Adversarial boundary inspection: zero rows, zero row totals, finite support,
non-real coefficients, and rows of different signs do not impose extra
restrictions. A conditionally convergent outer sequence of arbitrary signed
row totals cannot bypass the absolute premise: the totals here are necessarily
nonnegative. The source's positive indices are explicitly reindexed to naturals
starting at zero.

## PMA 8.4: translated radius and actual Taylor coefficients

`Represents` is an ordered-series statement with real arguments and complex
coefficients. `pma8_4_contract` allows every interior real center `a`, not only
zero. Its coefficients are the actual real iterated derivatives of `f` at `a`,
scaled by `1/n!`, with the displacement raised to the correct order. Order zero
is retained. The conclusion is an ordered sum equal to `f x`, not merely a
convergence assertion for another function or an equality of totalized sums.

The bound is exactly `R - ‖a‖₊` in extended nonnegative reals, with the strict
interior premise `‖a‖₊ < R`. There is no claim of maximality of the new radius.
At finite `R` this gives the source bound `R - |a|`. At `R = ∞`, the norm of a
real center is finite, so subtraction leaves infinity; no `toReal` conversion
collapses the entire-function case to radius zero. At `a = 0`, the original
open radius remains available. At `x = a`, positivity of the translated radius
includes the expansion center and its constant term.

The proof applies the library change-of-origin theorem to a representation
derived from ordered convergence, then converts the genuine iterated Fréchet
derivative expansion to scalar real derivatives. Altering `f` arbitrarily
outside the original interval does not affect the statement or these interior
derivatives. The triangle-inequality domain guarantee is carried by the
change-of-origin theorem.

## PMA 8.5: interior accumulation away from zero

The accumulation witness may be any real `a` with `‖a‖₊ < R`; the contract
does not force `a = 0`. The set in the closure hypothesis deletes `{a}`.
Thus one equality at an isolated point cannot trigger identity, and an
accumulation point only at the boundary is excluded by the strict interior
premise.

Using the global equality set introduces no weakness: an interior point has
an open neighborhood contained in the interval, so points outside the interval
cannot supply arbitrarily nearby equality points. Both functions are analytic
throughout the same connected real ball. The proof first obtains equality on
the whole interval by the analytic identity theorem and only then invokes
coefficient uniqueness. The result states both coefficient equality and
pointwise equality of the sums throughout the interval.

Adversarial inspection covered an accumulation point different from zero,
isolated equality, endpoint-only accumulation, and arbitrary definitions of the
functions outside the interval. None exposes a false conclusion or narrows the
source's allowable accumulation point.

## Supplementary operations: absolute interior convergence and native integrals

Addition retains the ordered Chapter 3 convention. Multiplication obtains
interior norm summability from the established analytic representation before
using the verified Cauchy-product result; it does not silently multiply
conditionally convergent boundary sums. The coefficient convolution is exactly
the Chapter 3 `CauchyProduct`, with the real-to-complex monomial bridge applied.
The supplement is not assigned an invented numbered Rudin node.

The integration theorem proves both `ComplexRSIntegrable f α a b` and an ordered
series of the native complex Riemann–Stieltjes integrals. The underlying complex
integrability definition is coordinatewise native Chapter 6 `RSIntegrable`, and
the integral is assembled from its two native real integrals. No Lebesgue
integral substitution occurs.

Only `MonotoneOn α (Icc a b)` is assumed. In particular, a monotone step
integrator with an interior jump is admitted: no continuity or differentiability
of the integrator is smuggled into `powerSeries_term_integrable` or the invoked
Chapter 7 uniform-series integration contract. The monomial integrands are
continuous. Uniform convergence is proved on the compact interval, and its
subset-of-open-ball hypothesis prevents an unsupported assertion at a boundary
of the power-series convergence domain.

The hypotheses permit `a = b`. The general Stieltjes result inherits the native
singleton theorem, and `powerSeries_term_integral` handles the singleton case
explicitly before invoking the strict-interval fundamental theorem. The explicit
integrated-coefficient series has the correct denominator `n+1` and coefficient
`(b^(n+1)-a^(n+1))/(n+1)`. At order zero it reduces to `(b-a) • c 0`, and at
equal endpoints every term and the native integral vanish. Complex, including
purely imaginary, coefficients are preserved by real scalar multiplication.

The supplement explicitly addresses ordered endpoints `a ≤ b`; it makes no
claim to supply a separate orientation convention for reversed endpoints.
This is consistent with its stated native Stieltjes scope. The separately
reviewed exponential/logarithm development introduces its own oriented native
ordinary-integral wrapper where the source requires it.

## Verdict

No semantic defect, false domain generalization, hidden stronger convergence
premise, or omitted source clause was found in these frozen inputs. All three
modules are accepted for the described source scope. This is an independent
adversarial source/proof review, not a substitute for the root's serialized
compiler checks and recursive axiom audit. Any later source change requires
hash reconciliation and review of the changed bytes.
