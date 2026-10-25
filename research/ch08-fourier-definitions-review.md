# Independent source review: PMA 8.9 and 8.10

Reviewer: the Fourier convergence author. The reviewer authored the base
Fourier definitions and analytic helpers, but did not author the implementation
or proof terms in `FourierDefinitions.lean` or `FourierExponentialExample.lean`.
This review compares their new statements and constructions against the printed
source rather than treating successful compilation as evidence of fidelity.

Source: PMA third edition, printed pp.185–187, directly read from the local
third-edition PDF during the Fourier inventory.

Final reviewed SHA256 of `rudin/Rudin/PMA/Chapter08/FourierDefinitions.lean`:
`838556f9c93699b817ac8e30457f13bab19c889cf79f0fb91e29b56a9869561b`.

## 8.9

The sine/cosine polynomial has a distinct constant coefficient and exactly
the positive frequencies 1 through N. Its coefficients are complex, as in
the source. Both directions of its equivalence with the exponential
representation are proved. Finite integer support is also proved equivalent
to a symmetric integer interval, including the empty-support and N=0 cases.

The principal contract includes continuity and periodicity, the normalized
native Riemann integral of every exponential frequency, Fourier coefficient
recovery both inside and outside the specified finite interval, and the
real-value criterion. The latter includes the zero coefficient and uses the
correct symmetry `c(-n) = conjugate(c(n))`; its condition on all signed indices
is equivalent to the source's condition on nonnegative indices. It imposes
no condition on coefficients outside the polynomial's support interval.

`HasRiemannFourierSeries` records the native-integrable function's Fourier
coefficients, with no assertion that the associated series converges.

Verdict for 8.9 and its attached finite-polynomial discussion: accepted.

## 8.10

The normalized complex-exponential example is independently accepted in
`research/ch08-exponential-orthonormal-review.md`, including its complete
integer-frequency enumeration. This example is reused, not reimplemented.

The real-system Gram calculation includes the constant, both trigonometric
families, and all mixed pairings. Its source-facing formulas explicitly give
the constant `1/sqrt(2*pi)`, then `cos((n+1)x)/sqrt(pi)` at index `2n+1` and
`sin((n+1)x)/sqrt(pi)` at index `2n+2`. The natural-index shift is explicit;
every printed positive frequency occurs. Inspection of Mathlib's indexing
equivalence confirms false corresponds to the even underlying index and true
to the odd one, so the stated sequence order is also correct.

The orthonormality predicates use native Riemann integrals, with existence of
each displayed integral. The relative-series predicate includes the printed
orthonormal-system premise and records the coefficient integrals without
asserting convergence. During review, that premise was added to this predicate
and its principal clause, resolving a draft generalization beyond the source's
stated scope. The reviewed final version needs no corresponding deviation.

Verdict for 8.10, both examples, and the relative Fourier-series definition:
accepted. No numbered item or worked example in this two-node scope is omitted.

## Kernel evidence

The final `evidence/ch08-fourier-definitions-build.log` reports
`Build completed successfully (8953 jobs).` The reviewed module was freshly
built without warnings. The final exhaustive namespace axiom audit and chapter
integration remain the integrating agent's gates. This review changed no Lean
source and makes no independent-authorship claim about the base Fourier
definitions it depends on.
