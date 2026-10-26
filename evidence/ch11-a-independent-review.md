# Chapter 11 first-half independent source review

Review date: 2026-10-25. Branch: `lane/rudin-ch11-a`.
Initial review snapshot: `87bccf9b0ffc22c4593898fa51bc731ad8f4339b`, with the
working-tree additions listed below. The chapter is being assembled concurrently;
the final build and complete namespace audit are recorded by the coordinating agent.

The reviewer independently inspected the other agents' Foundations,
SetFunctionSeries, Geometry, Construction, Regularity, Euclidean, NullSets,
Measurable, StieltjesExample, Examples, and GeometryApproximation modules against
the supplied third-edition PDF, printed pp. 301–315. The reviewer authored Simple,
Integration, and GeometryRing; checks of those modules below concern interfaces
and source coverage and are not represented as an independent implementation review.
Only short source paraphrases are retained here.

## Findings

No false statement or concealed restriction to finite real integrands was found
in the reviewed core statements. The approximation-based measurable-set definition
is retained literally, and its equivalence to Carathéodory measurability is proved;
it is not replaced by an assumed native measurable-set predicate. The extension
argument starts from finite additive content, regularity, and elementary geometry,
without assuming countable additivity of that content.

The regularity proof for arbitrary locally finite measures in
`elementary_measure_regular` in GeometryApproximation retains boundary atoms. Its
inner approximation writes each mixed interval as a closed box intersected with
an open box, rather than discarding endpoints. This is sufficient for the
Stieltjes regularity clause after specializing to the supplied locally finite
Stieltjes measure.

The final follow-up review confirmed `pma11_6b_regular`, `stieltjesRegularContent`,
and both `volumeRegularContent_outer` and `stieltjesRegularContent_outer` in
Examples. The native outer values agree with the constructed values on every
set, including nonmeasurable sets. The chapter entrypoint now imports all example
and geometry modules. The coordinating agent confirmed the Examples target
build. No numbered-node assembly gap remains.

## Numbered-node coverage

| Nodes | Reviewed coverage and assessment |
|---|---|
| 11.1 | Literal ring and sigma-ring closures, finite intersections, countable intersections. The empty-family convention is explicit. |
| 11.2 | Extended-real values; range exclusions; finite/countable additivity; equations (5)–(9); countable additivity implies finite additivity. The finite-total absolute-series observation is proved in SetFunctionSeries. |
| 11.3 | Continuity along increasing sets under the printed hypotheses. No extra finite-additivity premise remains in the main theorem. |
| 11.4 | All four endpoint choices in each coordinate; elementary finite unions; product-volume formula; finite disjoint decomposition; well-defined volume; additivity; ring closure and a positive-dimensional counterexample to sigma closure. |
| 11.5 | Regularity encoded with nonnegative extended values and subtraction-free inequalities. On the finite contents used in 11.7 these are equivalent to the printed inequalities. |
| 11.6(a) | Both approximants are elementary, with the required closed/open and measure bounds. |
| 11.6(b) | All four Stieltjes interval values, real-valued nondegenerate formulas, degenerate behavior, finite additivity, local finiteness, regularity with elementary approximants, and packaging for the general extension are present. The constructed outer measure is identified with native outer values on all sets. |
| 11.7 | Exact countable-cover infimum over open elementary sets; nonnegativity by codomain and monotonicity. |
| 11.8 | Agreement with the original content on elementary sets and countable subadditivity. Compact-subcover argument is proved rather than assumed. |
| 11.9 | Symmetric difference, extended set distance, convergence, elementary-approximation finite measurability, and countable-union measurability. |
| 11.10 | Sigma-ring closure and countable additivity on the approximation-defined family. Finite measurability is characterized by Carathéodory measurability plus finite outer measure. An elementary exhaustion is required only for the full Carathéodory equivalence, and Euclidean cubes supply it. |
| 11.11(a–d) | Open/closed measurability; small-difference closed/open approximations including infinite-measure sets; Borel sigma-ring and minimality; Borel envelopes modulo null sets and Borel-plus-null decomposition. |
| 11.11(e–f) | Null sigma-ring; countable Lebesgue-null sets in positive dimension; the uncountable perfect null Cantor example and its stage-volume formula. |
| 11.12 | Sigma-ring measure spaces without forcing the universe measurable; measurable-space condition; faithful native bridge; Lebesgue completion, counting, probability examples. |
| 11.13–11.16 | Real-threshold definition for extended-real functions and equivalence to native measurability; continuous examples; four threshold criteria; extended absolute values. Page 311 was checked visually: (44) is a weak superlevel condition, not an equality fiber condition. |
| 11.17 | Supremum, infimum, upper/lower limits, binary extrema, positive/negative parts, and pointwise-limit corollary, including infinite values. |
| 11.18 | Continuous functions of pairs of measurable real functions and the sum/product consequences. The separate narrative composition caution is noted below. |
| 11.19–11.20 | Finite-range simplicity without built-in measurability; characteristic functions and fiber decomposition; arbitrary/nonmeasurable pointwise approximation; measurable and nonnegative monotone versions; bounded uniform approximation; simultaneous nonnegative, monotone, uniform approximation. The source's real-function statement is interpreted with codomain real numbers. |
| 11.21 | Nonnegative integral, exact supremum over finite-valued nonnegative measurable simple functions, range/fiber sum, and agreement on simple functions. |
| 11.22 | Both infinite values retained in the integrand and integral; separate defined-domain and integrability predicates; finite integral iff integrable on the defined domain; native real-integral compatibility. |
| 11.23(a–f) | All six clauses, including finite real scalar multiplication for extended-real integrands and integrability of arbitrary measurable extended-real functions on null sets. |

## Explicit conventions, repairs, and stronger statements

1. **11.2 nonempty domain.** `AdmissibleSetFunction.finite_value` excludes an empty
   ring/domain, in addition to the prohibited infinity ranges. This makes explicit
   the nonemptiness already needed to write the source's empty-set value. The
   literal closure-only definition of a ring itself still permits an empty family.
2. **Positive Euclidean dimension.** Failure of sigma closure and the countable-null
   claim require positive dimension. This is the book's ordinary convention;
   zero-dimensional Euclidean volume has one point of mass one. Other geometry
   statements are proved for all natural dimensions.
3. **11.6(b), degenerate open interval.** The printed untruncated expression for
   an open degenerate interval can be negative at a jump. The implementation
   uses `ofReal`, proves the literal real formulas for strictly ordered endpoints,
   and separately proves all degenerate cases. This repair is already documented
   at the node and must remain in the final deviation list.
4. **11.9–11.10 distance discussion.** The unrestricted distance can be infinite.
   Calling the unrestricted quotient an ordinary metric space would be false.
   Construction explicitly flags the extended-metric correction and constructs
   the zero-distance equivalence relation.
5. **Native totalization of integration.** The source assumes a measurable
   integration set. Native restriction gives expressions on arbitrary sets as a
   stronger extension; the Integration comments now explicitly distinguish this
   from the source's domain. In particular, subset preservation is proved for
   arbitrary subsets. The signed expression is also totalized outside its
   mathematical defined-domain predicate. Neither convention narrows 11.22.
6. Natural-number sequences start at zero. Nonnegative quantities use nonnegative
   extended reals; signed quantities use `EReal`. Real functions are embedded
   explicitly where needed. These are representation choices with the relevant
   bridges proved, not lost cases.

## Ancillary narrative not claimed as formalized

- The cautionary example immediately after 11.18, concerning composition of a
  Lebesgue-measurable outer function with a continuous inner function, is not
  established. It is unnumbered and the numbered 11.18 theorem is complete.
  Measurable.lean explicitly records this gap; replacing Lebesgue measurability by
  Borel measurability would make the caution false.
- The explanatory quotient-space interpretation after (29) is represented by
  the zero-distance setoid and the correct finite/infinite-distance distinction.
  A separate quotient metric construction and closure-identification theorem are
  not provided. The source identifies this interpretation as explanatory rather
  than a premise of Theorem 11.10.

## Validation relevant to this review

The reviewer observed successful target builds for Simple and Integration
(`Build completed successfully (8925 jobs)`) and GeometryRing (same job count,
17 seconds for that module). A transitive axiom check of 37 public Simple and
Integration declarations reported only `propext`, `Classical.choice`, and
`Quot.sound`. The coordinating agent's final complete build and namespace-wide
axiom audit cover the assembled chapter, including the newly connected examples.
