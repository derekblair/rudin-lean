# Chapter 9 first-half coverage and representations

The source inventory and half boundary are in `ch09-a-inventory.md`.
All identifiers below live in namespace `Rudin.PMA.Chapter09`.

| Node | Module | Principal declarations and included content |
|---|---|---|
| 9.1 | LinearFoundations | `pma9_1_vectorSpace_iff`, `pma9_1_span_iff`, `pma9_1_independent_iff`, `pma9_1_dimension_iff`, `pma9_1_unique_coordinates`; all five definitions, zero space, standard basis |
| 9.2 | LinearFoundations | `pma9_2`, `pma9_2_dimension`, `pma9_2_corollary`; finite spanning bound and Euclidean dimension |
| 9.3 | LinearFoundations | `pma9_3_a`, `pma9_3_b`, `pma9_3_b_card`, `pma9_3_c`; basis criterion, existence/cardinality and extension |
| 9.4 | LinearFoundations | `pma9_4_linearMap`, `pma9_4_basis_image`, `pma9_4_inverse`; linearity, basis determination, inverse linearity and both identities |
| 9.5 | LinearFoundations | `pma9_5`, `pma9_5_range`; injectivity iff surjectivity |
| 9.6 | Operators | `pma9_6_norm_eq_sup`, `pma9_6_bound`, `pma9_6_least_bound_positive_dimension`; space, algebra, composition and norm |
| 9.7 | Operators | `pma9_7_column_bound`, `pma9_7_a`, `pma9_7_b`, `pma9_7_distance`, `pma9_7_c` |
| 9.8 | Operators | `pma9_8_a`, `pma9_8_open`, `pma9_8_inverse_continuous`, `pma9_8_inverse_involution` |
| 9.9 | Operators | `pma9_9_matrixEquiv`, `pma9_9_composition`, `pma9_9_frobenius_bound_sq`, `pma9_9_entrywise_continuous`; also columns, range, coordinate action |
| 9.10 | Differentiation | `pma9_10_linear_derivative`, `pma9_10_linear_map_eq`; scalar/vector derivative and remainder formulations |
| 9.11 | Differentiation | `pma9_11`, `pma9_11_differentiableOn`; derivative definition and exact norm-ratio equivalence |
| 9.12 | Differentiation | `pma9_12`; derivative uniqueness |
| 9.13 | Differentiation | `pma9_13_continuous`; exact remainder, differential as a map, and continuity |
| 9.14 | Differentiation | `pma9_14`, `pma9_14_remainder`; linear-map example |
| 9.15 | Differentiation | `pma9_15`; chain rule |
| 9.16 | Differentiation, DiscontinuousPartials, PartialCounterexamples | `pma9_16_hasPartial`, `pma9_16_partial`, `pma9_16_iff_limit`; coordinate derivatives; `pma9_16_partials_not_imply_continuity` and `pma9_16_continuous_partials_not_differentiable` prove the two failure-of-converse observations |
| 9.17 | Differentiation | `pma9_17`, `pma9_17_entries`, `pma9_17_column`, `pma9_17_directional_limit`; Jacobian and action formulas |
| 9.18 | Differentiation | curve chain rule, coordinate and inner-product expressions, gradient, directional derivative and maximum over unit vectors |
| 9.19 | ContinuousDifferentiability | `pma9_19`, `pma9_19_corollary`; derivative bound and constancy |
| 9.20 | ContinuousDifferentiability | `IsC1On`, `pma9_20`, `pma9_20_continuity`; C¹ and epsilon-delta characterization |
| 9.21 | PartialContinuity, PartialCriterion | `hasFDerivAt_of_continuous_partials`, `pma9_21`; both directions with no differentiability assumed in the partial-derivative hypothesis |
| 9.22 | ContinuousDifferentiability | `IsContraction`, `pma9_22`; literal real-factor definition and equivalence to Mathlib |

## Representations and explicitly documented generalizations

- Finite families use zero-based `Fin n` indices. Algebraic assertions in 9.1–9.6 and 9.9 allow abstract real vector spaces. The chapter introduction expressly allows this algebraic extension. Finite-dimensional hypotheses remain explicit where needed.
- Euclidean statements use `EuclideanSpace ℝ (Fin n)`, with its Euclidean norm. The sup-norm coordinate space occurs only inside the proof of 9.21, transported by a continuous linear equivalence.
- Linear maps are bundled with continuity for norm and derivative statements. `pma9_6_continuousEquiv` proves that every algebraic map on these Euclidean spaces is included.
- Zero dimensions/empty independent families are allowed. For 9.6's least-bound statement, nonnegativity is needed in dimension zero; the original sign-free assertion is proved separately for positive dimension. No positive-dimensional book case is lost.
- 9.9 permits an arbitrary topological parameter space, generalizing the printed metric-space assumption.
- Functions on open subsets are represented by arbitrary total extensions with local hypotheses. Differential and partial-derivative functions use Mathlib's totalized values; all claims about their derivative meaning include existence hypotheses. The printed norm-ratio limits are proved equivalent to these predicates.
- 9.10 permits vector-valued real-line derivatives; 9.15 uses local derivative hypotheses, which suffice without a global image/domain condition. The book's domain setting is a special case.
- 9.19 and 9.20 permit real normed spaces. 9.19 assumes differentiability at each point of the convex set, so openness is unnecessary. Both contain the printed Euclidean open-domain case.
- 9.22 retains the book's real factor, including a negative factor when all distances are zero. Its equivalence with a nonnegative factor is proved; no positivity assumption is added to the definition.

- 9.16's two existential counterexample observations are witnessed by `xy/(x²+y²)` and `xy/√(x²+y²)`, each set to zero at the origin. These are explicitly documented alternative witnesses, not formalizations of the referenced exercises. Both have all coordinate partial derivatives everywhere. Their scalar codomain is ℝ, the real line identified with one-dimensional Euclidean space in 9.10.
- 9.17–9.18 also prove directional formulas for arbitrary vectors, including the coordinate/unit-vector cases in the text. The maximum assertion retains the nonzero-gradient condition.
