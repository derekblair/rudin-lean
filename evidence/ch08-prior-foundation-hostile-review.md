# Independent adversarial review of the Chapter 8 foundations

Reviewer: `double_series`, 2026-10-22. The reviewer authored neither reviewed
module; their production authorship is confined to DoubleSeries, Taylor and
Operations. This review read the complete actual Lean definitions, public
contracts and proofs, the Chapter 3 ordered-series definitions, the relevant
pinned Mathlib signatures, and `research/pma-ch08-source-review.md`. Existing
semantic acceptance was not substituted for checking the actual declarations.
No build was run and no production source was edited during this review.

Reviewed files, relative to the repository root:

| File | SHA256 |
| --- | --- |
| `rudin/Rudin/PMA/Chapter08/PowerSeries.lean` | `af7669152ab11b348b454ccfacb37928c67be845b7428377bd29dfd6e6552518` |
| `rudin/Rudin/PMA/Chapter08/Abel.lean` | `2a7a23da0c64df9c38dff6975bd0f5e34f1a428a5d4fa86480c35b7498260239` |

**Final verdict: ACCEPTED for 8.1 and 8.2 and the reviewed attached scope.** No
false, vacuous, circular, or narrowed statement was found. The signed-endpoint
advisory was resolved by the explicitly reviewed supplement below. Compilation,
default production inclusion and recursive axiom auditing remain separate
integration gates. Acceptance applies to the hashes above, not later edits.

## PowerSeries: hostile checks

- `Represents` quantifies every real argument in the open extended ball and
  requires the Chapter 3 ordered partial-sum limit. It does not assume absolute
  convergence, analyticity, differentiability, or a formal-series radius bound.
  Coefficients and values are complex; real scalar multiplication matches the
  coefficient-left convention via `realSeries_term_reference`.
- The positive-radius premise in the principal contract prevents an empty
  neighborhood from proving arbitrary coefficient uniqueness. At radius
  infinity all finite arguments remain in the premise; it is not converted
  into a finite real by `toReal`.
- `represents_hasFPowerSeries` first derives the radius lower bound from the
  ordinary term-to-zero consequence at every nonnegative real radius below R.
  Only then does it invoke the formal series' interior summability and identify
  its sum with the supplied ordered limit by uniqueness. Thus the bridge does
  not assume its own analytic conclusion or identify a divergent totalized
  sum with a given function. Quantifying all finite subradii also establishes
  the claimed infinite-radius case.
- Uniform convergence is on the full closed interval `[-r,r]`, including its
  endpoints, under the correct strict inequality `r<R`. The quantified NNReal
  radius permits `r=0`; the proof uses compactness and does not divide by r or
  silently require a nondegenerate interval. There is no assertion of uniform
  convergence on the entire original open interval or its boundary.
- Continuity and all derivative assertions are local to the original open
  interval, so arbitrary values of f outside it do not invalidate the claims.
  Each successor derivative is accompanied by an actual `HasDerivAt` proof;
  the totalized `iteratedDeriv` function alone is not used as evidence of
  derivative existence.
- For order k, reindexing the source's original term index as n+k gives the
  product `(n+1)...(n+k)`, exactly `(n+1).ascFactorial k`. The case k=0 retains
  the whole original series and the constant coefficient. The origin formula
  retains k=0, and coefficient uniqueness cancels a nonzero factorial in ℂ.
- The smooth but nonanalytic witness is an actual existential conjunct. It
  expresses the source's warning without claiming every smooth function is
  represented by its Taylor series or treating an exercise as a new node.

## Abel: hostile checks

- The endpoint premise is `Chapter03.SeriesHasSum`; it is not `Summable` and
  does not impose absolute convergence. The explicit interior `HasSum`
  conclusion is derived from the Cauchy property of that ordered limit and
  the strict norm inequality. Conditional endpoints therefore remain covered.
- `abelPowerSeries` uses `tsum`, but the contract supplies actual interior
  sums. At the boundary `abelEndpointExtension` explicitly uses the given
  ordered sum A. It does not assume that A equals the unconditional `tsum`
  of a conditionally convergent coefficient series.
- Both limits use the correct nontrivial left-neighborhood filter on ℝ.
  Positive endpoint scaling divides only by an explicitly positive R. The
  transformed coefficients and the argument x/R recover the original terms
  algebraically, rather than replacing the original coefficient sequence.
- Continuity relative to `Iic R` at R is a local statement. Although the
  extension is globally defined and its values far outside the convergence
  interval may be totalized sums, these values are excluded by a sufficiently
  small neighborhood of the positive endpoint. The supplied endpoint value
  agrees with the limit, and inclusion of R does not make the filter trivial.
- The Cauchy-product conjunct is exactly Chapter 3's ordinary-series theorem:
  both factors and their Cauchy product have supplied ordered sums, without
  an added absolute-convergence premise. The Mathlib Abel dependency of that
  earlier result is disclosed; it is not a circular reference to the new
  Chapter 8 declaration.

## Initial advisory: negative convergent endpoints (resolved below)

The numbered source theorem 8.2 concerns the unit right endpoint. The preceding
source discussion refers more generally to a convergent endpoint, then chooses
the right endpoint for notation. The current public contract explicitly scales
to positive/right endpoints only. For a negative endpoint L, apply the positive
statement at `-L` to coefficients `a n * (-1)^n`, then reflect the argument
`x -> -x`; this gives the limit from the right and continuity relative to
`Ici L`. The source reviewer independently confirmed this scope distinction.

This is not an incorrect premise or conclusion in numbered 8.2, and the existing
statement supplies the mathematical reflection argument. A named negative-
endpoint limit and continuity corollary is recommended to make the attached
any-endpoint claim explicit and mechanically reviewable. The integrating lane
was notified; no corollary has been silently claimed as separately implemented
by this review.

## Signed-endpoint delta review and advisory closure

The reviewer read the complete updated Abel module and accepted the change from
`0d62e22630716fc1e93bf07b1f795be62d3768e1342ac0eef55cd502b64fa480`
to `2a7a23da0c64df9c38dff6975bd0f5e34f1a428a5d4fa86480c35b7498260239`.
The table and final verdict above identify this latest snapshot.

The new public negative-endpoint clause is a genuine strengthening of
`pma8_2_contract`; it retains every prior conjunct and explicitly adds interior
sum existence, the right-hand limit at -R, and continuity of the ordered-sum
extension relative to `Ici (-R)`, for every R>0. This parametrization covers
every strictly negative endpoint. Its premise is the original ordered endpoint
series, without absolute convergence.

`abel_reflection` proves exact termwise equality after multiplying coefficients
by (-1)^n and negating the real argument. The proof of the negative limit also
identifies the reflected positive-endpoint partial sums exactly; it does not
rearrange a conditional series. Negation maps the right neighborhood of -R to
the left neighborhood of R, so the approach direction is correct. The negative
extension again takes A at the endpoint and agrees with the original sum on
the punctured approach. The independent interior-existence lemma uses the norm
of -R, avoiding an invalid comparison of a norm with a negative radius.

The root's `evidence/ch08-foundation-probes-final.log` reports successful
compilation of signed Abel and all eleven foundation/operations clients.
This corroborates the integration report and is not a reviewer-owned build.
The source-scope advisory is **CLOSED**, with no remaining semantic request.
