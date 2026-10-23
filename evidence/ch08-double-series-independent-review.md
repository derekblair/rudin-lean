# PMA-8.3 independent fidelity and source review

Reviewer: `ch8_fidelity`; author: `double_series`; date: 2026-10-22.

**Semantic verdict: ACCEPTED.** Reviewed source: `rudin/Rudin/PMA/Chapter08/DoubleSeries.lean`, SHA256 `220fdc967ef1e8fda1da5311d920d6df9895cd6848ae6531c5cf8d5e0c3531cd`.

Reference scope: independently inspected Rudin third edition, printed pp.175-176, recorded in `research/pma-ch08-source-review.md`. No Lean source authorship, build, or git mutation was performed by this reviewer. Kernel verification, recursive axiom auditing, and production inclusion are separate gates and must be recorded by the integrating lane.

## Back-translation

For every complex double sequence and every real sequence of row norm sums, assume each ordered row norm series sums to the specified real value and the ordered series of these real values converges. There exist complex row sums, complex column sums, and a common complex outer sum: every ordered row and column series converges to its corresponding value, and the ordered series of row sums and of column sums both converge to the common value.

This matches the complete numbered source theorem. The internal natural index `i` denotes source index `i+1`, in both coordinates, as documented in the source header. The theorem covers arbitrary complex entries and imposes no extraneous positivity on them. Nonnegativity of each real row norm sum is derived rather than assumed.

## Fidelity and proof inspection

- The hypotheses retain ordinary ordered convergence through `Chapter03.SeriesHasSum` and `SeriesConverges`. Replacing these premises by unconditional summability could silently narrow a theorem in general; here the proof converts only the nonnegative norm data, with its nonnegativity justified.
- The conclusion explicitly supplies each inner sum and both outer sums. It is stronger than, and faithfully implies, a bare equality of totalized `tsum` expressions, so divergence cannot make the result vacuous.
- `doubleSeries_summable_norm` first proves summability of the complete product-index norm family using the nonnegative row theorem. The main proof then obtains complex product summability and uses valid product factors, product summation, and commutation.
- Both row and column directions are present, and the common sum is constructed from the original row ordering. Zero entries and zero total mass are admitted without extra hypotheses.
- No proof placeholder, unsafe evaluator, extra axiom, or result-as-premise circularity was found by inspection. The file's only import is existing Chapter 3; library references are actual absolute-summability theorems.

No mathematical or source-fidelity correction is requested. If production source bytes change, identify and review those changes before carrying forward this exact-source acceptance.

## Strict-implicit delta review

The source hash `7cb78d7c111d3be2a9bc0f5e67a02c0020e988ba39e24f67db050787aae57e7e`
adds only `set_option autoImplicit false` to the previously reviewed file.
Removing that exact option line and its blank line reproduces the earlier
SHA256 byte for byte. This delta is accepted and strengthens the prevention of
accidentally generalized implicit premises.
