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
are excluded by an explicit indicator. The parent reported the complete theorem and its independent probes green in
`evidence/ch10-change-of-variables-probes-compile.log`; the source file is frozen
for the reviewer's final hash check.

## Subsequent assignments: PMA-10.12, 10.14, 10.16, 10.17

The parent later assigned the worked examples and the standard-form/wedge-product
algebra to this author. Printed pages 254–255 and 257–260 were visually inspected
using in-memory PDF rendering. The independent reviewer accepted the exact typed
contracts before the corresponding proofs were finished.

`FormExamples.lean` contains the full 10.12 contract and the endpoint and ellipse
proofs. `SphereExamples.lean` constructs the spherical surface, establishes its
norm, exact image and interior injectivity, computes the derivative determinant,
and evaluates the native triple Riemann integral. It assembles the complete
`pma10_12` theorem. The parent reported this full node green in
`evidence/ch10-sphere-examples-compile.log`; both source modules are frozen for
final independent hash review.

`StandardForms.lean` retains the shared `standard_expansion` signature and proves
the Chapter 9 tuple-sign bridge, sorting to the actual exterior basis, regular
coefficient expansion, and all three displayed example identities from 10.14.
Its additional `exteriorBasis_repr_eq_zero_of_degree` helper is used by the
differentiation author to preserve homogeneous degree. The parent reported this module green in
`evidence/ch10-form-separation.log`; its source is frozen.

`WedgeProducts.lean` contains full proof drafts for 10.16 and 10.17. Its
`crossInversionCount` literally counts pairs with the second coordinate smaller
than the first. `tupleSign_append` splits the all-pairs sign product into two
increasing blocks and the cross pairs, deriving the parity formula. General form
products use genuine coefficient double sums, giving continuity and homogeneous
degree. The shared `homogeneous_mul_mem` and `homogeneous_mul_dx_comm` signatures
are coordinated with the author of 10.18–10.20. The parent reported the complete module and independent FormAlgebraProbes green
in `evidence/ch10-form-algebra-probes-compile.log`; source bytes are frozen for
final hash review.


## Subsequent assignments: PMA-10.26–10.27 and face geometry

Printed pages 266–270 were visually inspected using in-memory PDF rendering. The
independent reviewer accepted the full 10.26 contract after adding the generic
characterization of an affine map between arbitrary real modules, with no norm
or finite-dimensional assumption in that clause. It also accepted the exact
10.27 contract, including all vertex permutations, dimension zero, degenerate
simplices, continuous forms and native integrability of both parametrizations.

`AffineSimplices.lean` defines `vertexLinear`, the generic `affineMapFromVertices`,
`affineSimplexMap`, and `affineSimplexSurface`. The vertex family is arbitrary;
independence appears only in the conclusion about a nonzero full-dimensional
Jacobian. Signed point integrals use a sign acting on the integration functional.
The source does not identify differently parametrized maps literally.

`AffineFaces.lean` defines `standardFaceAffine` and `standardFaceMap` by deleting
one standard vertex. Its helper interface gives smoothness, preservation of the
standard simplex, the actual vertex action, arbitrary affine restriction,
paired-deletion composition identities, and the two explicit face formulas.
The parent implements the numbered boundary/chain contracts in separate files.

`SimplexOrientation.lean` defines the affine `simplexVertexPermutation` and proves
its inverse and exact simplex image. An augmented vertex matrix identifies the
edge determinant with the permutation sign, without dividing by a possibly zero
edge determinant. A derivative-chain-rule and exterior-evaluation lemma gives
the signed integrand. The native change-of-variables helper provided by the
parent then gives the native integral identity. The parent reported `AffineSimplices` and `AffineFaces` green. The reviewer
accepted the full 10.26 proof at SHA256
`952393bfb0741aa222a1acfb7b23c3c0316cba9e74a5b80303885031d3b1467c`.
The parent subsequently reported `SimplexOrientation` green; its source is frozen.

The agreed chain architecture stores each C2 simplex's global map as data and
its open-neighborhood regularity and target containment as Prop fields. This
makes equality of maps sufficient for face and pushforward identities. Finite
integer chains use Finsupp, and integration equivalence is stated separately;
there is no premature quotient requiring boundary well-definedness before
Stokes. The parent owns `SimplexChains`, `AffineChains`, and `SimplexBoundaries`.


`SimplexFormFaces.lean` was added at the Stokes author's request. Its two public
helpers `evaluateForm_dx_standard` and `evaluateForm_upper_standard` express,
respectively, the coordinate cofactor sign and the alternating coordinate-face
expansion of the upper-face tangent frame. Their proofs use actual exterior
algebra evaluations and determinant identities, including degree zero. The
independent reviewer accepted their mathematical statements and proof drafts.
The root-owned `ch10-simplex-form-faces-compile.log` now reports a successful build;
the helper source is frozen.

## Subsequent assignments: the C¹ square consequence of 10.31 and full 10.32

Printed pages 271–272 were visually inspected. The source reviewer confirmed that
the two-triangle integral decomposition is stated for the unit square, while the
sphere example uses the actual nonunit rectangle and its four actual side
intervals. The parent owns the full 10.31 contract, including positive-region
parametrization independence and finite unions; this author supplies the square
consequence as `squareBoundary_contract` and `squareBoundary`.

`SurfacePrecomposition.lean` constructs C¹ precompositions without requiring a C²
extension. Its native reversal theorem retains arbitrary ordered interval
endpoints, including zero length. The parent reported this module green.
`RectangleEdges.lean` defines the four counterclockwise affine sides on their
actual coordinate intervals and proves their native integrability. The parent
reported the final explicit side-by-side proof green in 2.6 seconds, with no
panic diagnostics; its source is frozen.

`SphereBoundary.lean` contains the independently accepted full 10.32 contract
and proof draft. It establishes the exact image of the literal spherical map,
computes the four edge maps, proves both poles integrate to zero, and applies
native interval reversal to the two meridians. All conclusions quantify over
every continuous one-form on any target containing the image. No exactness or
additional differentiability of the form is assumed. The parent reported full
10.32 green, and its production source is frozen.

`SquareIntegral.lean` proves the elementary scalar native integral split using
two nested interval integrals and substitutions in both variables. A continuous
extension outside the square is used only in the proof. `SquareBoundaries.lean`
then identifies the two actual affine triangle maps, their determinants, all
six face maps, the shared diagonal cancellation, and the four exterior edges.
Its exact C¹ contract has been independently accepted. The parent reported
`SquareIntegral`, `SquareBoundaries`, the assembled `BoundaryDefinitions` 10.31,
and independent `BoundaryExamplesProbes` green. These source files are frozen.

## Subsequent assignments: PMA-10.36–10.37

Printed page 277 was visually inspected in memory. `PuncturedExamples.lean`
contains the independently accepted exact contracts. Both require functional
nonbounding, rather than just inequality of literal free chains. The circle
quantifies every positive radius and keeps the actual interval [0,2π]; the sphere
is the exact map and rectangle from 10.32. The radial norm-cubed denominator is
accompanied by an explicit real-power bridge.

`AngularForm.lean` and `PuncturedPlane.lean` contain the complete 10.36 proof draft:
explicit quotient coordinate derivatives prove closedness; actual ellipse
integrands give constant angular density one; the native integral is 2π; and a
normalized C² one-simplex supplies the cycle used by the 10.35 consequences.
Their root-owned compiler checks are pending. `CellNormalization.lean` supplies
native interval normalization and the actual C² simplex transport; its first
compile accepted all integral proofs and required one function-extensionality
repair. `RectangleNormalization.lean` supplies corresponding native rectangular
normalization and actual-side boundary compatibility for the forthcoming 10.37
chain transport. It is queued for its first root-owned compile.

The parent subsequently reported `CellNormalization`, `RectangleNormalization`,
and `RectangleChains` green. Their actual normalized maps, native integral
identities, and all-continuous-form boundary transport are now compiled; these
files are frozen. `AngularForm` is undergoing localized instance-coherence and
pointwise-function elaboration repairs, so the principal 10.36/10.37 compilation
gates remain pending.

`RadialForm.lean` contains the complete closedness proof and norm-cube/real-power
bridge. The independent reviewer accepted its mathematical argument. The full
10.37 assembly is now in `PuncturedSphere.lean`: it constructs the literal
punctured-sphere surface, differentiates its spherical map, computes the actual
radial density as sin(theta), integrates natively to 4*pi, and transports every
continuous form to an explicit two-simplex chain. The source 10.32 cancellation
makes that chain a functional cycle; the 10.35 consequences prove nonexactness
and nonbounding by any C2 three-chain in the punctured space. Full proof review
and the root-owned compiler checks are pending, with no completed claim yet.

The parent reported all 10.36/10.37 production files green, including the complete
`PuncturedSphere` principal. The only contract-text repair for 37 renamed the
reserved binder token `Σ` to `Φ`; no type or assertion changed. These files are
frozen for final independent hash reconciliation and client gates.

## Subsequent assignments: PMA-10.42 and PMA-10.46

Printed page 281 and printed pages 283–285 were visually read in memory. The
independent reviewer accepted both exact typed contracts before proof work.
`VectorFields.lean` is now green and independently reviewed at SHA256
`39ea65f583ee3129f4974264abb946e5a313e43693f56aa758c55df91247c6f8`.
It supplies both genuine continuous vector/form correspondences, their explicit
inverse coefficient extractions and uniqueness, all finite C^r coefficient
regularity bridges, and the literal gradient/curl/divergence definitions with
source C1 output-continuity conclusions. `VectorFormDerivatives.lean` is also
reported green and supplies the exterior-derivative bridges and closedness iff
zero curl/divergence. Both files are frozen.

`AreaElements.lean` contains the independently accepted full 46 contract and a
complete proof draft queued for its first parent-owned compile. The directed
normal uses the ordered derivative-column cross product, while its actual
Jacobian-minor representation is proved separately. The draft proves the full
rank0/1/2 geometry, native area existence from image-only density continuity,
and translated affine rectangle area with ordinary parameter measure, including
zero widths. It additionally supplies the flux integrand identity for reuse in
49. No injectivity, immersion, or C2 requirement is imposed on the C1 surface.

The parent reported `AreaElements` green; the full C1 source contract is now
proved and frozen. The independent reviewer accepted the complete mathematics.

## Subsequent assignment: PMA-10.47

Printed page 285 was visually checked in memory. `Torus.lean` contains the exact
independently accepted contract; it and `TorusGeometry.lean` are parent-reported
green. `TorusCalculus.lean` proves actual Jacobian/normal formulas and the native
volume/area integrals, with routine compiler repairs in progress. `CellImageVolume`
extends the native density formula to interior-only injectivity by proving the
cell frontier and its differentiable image null; `TorusVolume` then uses the full
closed solid image to identify ordinary volume. These drafts received independent
mathematical acceptance and are in the serialized compilation queue.

The six-face boundary is derived from native scalar cell FTC, signed omitted
coefficients and C2 pullback, then transported to all continuous forms by the
proved coefficient-approximation criterion `chainEq_of_c1`. `CellFTC` was handed
to the power-series agent for compiler ownership; this agent owns `CellFaces`
and `CubicalStokes`. The power-series agent owns `TorusBoundary`, including literal
periodic-face cancellation and the rank-one central face. `TorusProof` assembles
the full principal once those source-preserving helpers compile. No completed
47 claim is made while any compilation or independent final review is pending.

The parent now reports `TorusCalculus`, `CellImageVolume`, and `TorusVolume`
green: all literal torus geometry, derivative, native volume/area, and ordinary
image-volume calculations compile. The independent reviewer read and accepted
the complete `CellFaces` and `CubicalStokes` mathematical argument, including
its extension from C1 forms to every continuous form. Those files remain frozen
for compiler diagnostics; the torus-specific boundary cancellation and final
principal gates remain pending.
