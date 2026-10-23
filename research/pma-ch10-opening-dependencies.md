# Chapter 10 primitive mappings: scope and dependencies

Author: `double_series`, 2026-10-23. Assigned scope is PMA-10.5 through PMA-10.7, printed pages 248-250 (PDF pages 257-259). The PDF was visually inspected with in-memory Poppler rendering; no rendered pages or source proof text were saved. Independent source reviewer `ch8_fidelity` confirmed this scope and the attached statements.

`Chapter10/Primitive.lean` uses `Chapter09.Euclidean`, the source `C1On` predicate, coordinate partials, the standard-basis operator matrix, and the existing Jacobian. Its numbered contracts preserve:

- 10.5: a map that changes only one coordinate; the equivalent finite-sum formula; the derivative matrix and Jacobian at any point where the scalar component is differentiable; the nonzero coordinate-partial criterion for invertibility. No unnecessary `C1` hypothesis is imposed on this pointwise statement.
- 10.6: flips interchange two distinct standard basis vectors, equivalently two coordinates. Prefix projections include zero and identity endpoints, their coordinate action, and their range/kernel coordinate spans.
- 10.7: for positive dimension, the exact local factorization into `n` primitive maps and `n-1` flips or identities, with all primitive maps locally `C1`, fixing zero, and having invertible derivatives there. Lists record the composition order explicitly and exact lengths prevent an unbounded-generation substitute.

The existing local inverse theorem `Chapter09.inverse_neighborhood_c1` supplies actual open neighborhoods and inverse functions. The proof uses successive coordinate elimination near zero; derivative invertibility produces a nonzero remaining coordinate entry, and the scalar update is inverted locally. The resulting composition identities are neighborhood equalities. This is an implementation description, not stored source proof text.

Pinned local Mathlib APIs inspected:

- `ContinuousLinearMap.smulRight`, finite sums of continuous linear maps, and `HasFDerivAt` addition/subtraction/smul rules for primitive derivatives.
- `Matrix.det_updateRow_sum` for the determinant of an identity matrix with one changed row.
- `Chapter09.coordinatePartial_eq_fderiv` and `operatorMatrix_apply` for the native coordinate bridge.
- `Module.Basis.constr_range`, basis expansions, and `Submodule.span_induction` for coordinate-subspace descriptions.
- `ContDiffAt.eventually`, `ContDiffAt.congr_of_eventuallyEq`, and open partial homeomorphism inverse identities for local factorization.

No direct nonlinear primitive-factorization theorem was found in the pinned calculus/manifold sources. Builds and integration remain exclusively with the parent agent; this author does not run Lean or lake.

The parent reported a green full Primitive build in `evidence/ch10-primitive-compile.log`.
The independent reviewer accepted the complete proof at SHA256
`200eb8e36d54cdf771415de92c1046cf4c92d64c123d0fed62a4ee7e64639f5b`.

## Subsequent assignment: PMA-10.9

The parent reassigned change of variables to this author. The exact typed contract
in `Chapter10/ChangeOfVariables.lean` was independently accepted before completing
its proof draft. The contract uses native `Coord n` integrals and explicitly links
the derivative determinant both to its standard matrix and to the Chapter 9
Euclidean Jacobian. It assumes regularity and injectivity only on the open domain.

The proof draft constructs an `OpenPartialHomeomorph` from the restriction using
the local inverse theorem. The inverse transports the compact support of the
original function into a compact subset of the open source. This controls the
support and continuity of the pullback extended by zero. Native slice
integrability follows from global continuity; `wholeRIntegral_eq_integral`
then connects to Mathlib's
`MeasureTheory.integral_image_eq_integral_abs_det_fderiv_smul`.
The absolute determinant is retained, and arbitrary values outside the source
are excluded by an explicit indicator. The proof draft is awaiting the parent's
serialized compile; it is not yet a completed node.

## Subsequent assignments: PMA-10.12, 10.14, 10.16, 10.17

The parent later assigned the worked examples and the standard-form/wedge-product
algebra to this author. Printed pages 254–255 and 257–260 were visually inspected
using in-memory PDF rendering. The independent reviewer accepted the exact typed
contracts before the corresponding proofs were finished.

`FormExamples.lean` contains the full 10.12 contract and the endpoint and ellipse
proofs. `SphereExamples.lean` constructs the spherical surface, establishes its
norm, exact image and interior injectivity, computes the derivative determinant,
and evaluates the native triple Riemann integral. It assembles the complete
`pma10_12` theorem. At this update, compiler fixes are pending; no completion claim
is made for the example node.

`StandardForms.lean` retains the shared `standard_expansion` signature and proves
the Chapter 9 tuple-sign bridge, sorting to the actual exterior basis, regular
coefficient expansion, and all three displayed example identities from 10.14.
Its additional `exteriorBasis_repr_eq_zero_of_degree` helper is used by the
differentiation author to preserve homogeneous degree. The module is undergoing
the parent's serialized compiler passes.

`WedgeProducts.lean` contains full proof drafts for 10.16 and 10.17. Its
`crossInversionCount` literally counts pairs with the second coordinate smaller
than the first. `tupleSign_append` splits the all-pairs sign product into two
increasing blocks and the cross pairs, deriving the parity formula. General form
products use genuine coefficient double sums, giving continuity and homogeneous
degree. The shared `homogeneous_mul_mem` and `homogeneous_mul_dx_comm` signatures
are coordinated with the author of 10.18–10.20. This file is awaiting its first
serialized compile, so its proof draft is not yet kernel acceptance.
