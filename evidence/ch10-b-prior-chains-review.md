# Reconciliation review: recovered PMA 10.27–10.33

Date: 2026-10-25. Prior implementation: `origin/ch8-codex-20261022` at `bb50a20`.
Scope: read-only review of recovered production modules and relevant probes against
printed PMA pp.267–275 (PDF pp.276–284), with the 10.26 signed-point interface
inspected from the prior branch. No implementation edits or builds were performed
for this review. The parent is running the current snapshot build and axiom audit;
this document does not replace those gates.

## Finding

The recovered implementation supplies substantive proofs for all seven numbered
nodes 10.27–10.33. I found no mathematical blocker or silently strengthened
hypothesis in the reviewed public contracts. Their integration into this lane still
depends on the first-half API. The previous conclusion that these seven nodes had
no implementation is superseded by this recovery.

The discarded `swapFirstVertexParameter` helper is unnecessary for the recovered
10.27 proof. The prior code already treats every vertex permutation by an actual
affine self-map, including movement of vertex zero, and proves the determinant,
parameter-domain image, inverse, composition, native-integrability and integral
identities. The old helper's explicit `Function.update` and coordinate-sum spelling
is not reproduced verbatim, but every property it was intended to support is
available in stronger general form. There is no reason to retain a second map API.

## Numbered-node evidence

| Node | Principal and key files | Source coverage found |
| --- | --- | --- |
| 10.27 | `SimplexOrientation.pma10_27`; `SimplexChangeOfVariables` | All vertex permutations, arbitrary ambient and simplex dimensions, repeated/dependent vertices, genuine continuous homogeneous forms, reordered target inclusion, native existence for both orders, and multiplication of the actual integral by permutation sign. |
| 10.28 | `AffineChains.pma10_28`; `SimplexChains` | Finite multiplicities, weighted native integral sum, additive/scalar laws, cancellation, functional chain equality separate from equality of maps, and exact transfer to the C2 chain representation. |
| 10.29 | `SimplexBoundaries.pma10_29`; `AffineFaces` | Alternating omitted-vertex boundary, ordered face vertices, the changed base point for face zero, zero-insertion remaining faces, triangle signs, and affine/C2 boundary agreement. |
| 10.30 | `ChainMaps.pma10_30`; `SimplexChains`; `SimplexBoundaries` | Actual C2 composition on an open neighborhood, no injectivity premise, native pullback integration, finite-chain linearity, boundary/pushforward commutation, and recovery of the affine case. |
| 10.31 | `BoundaryDefinitions.pma10_31`; `PositiveRegions`; `PositiveRegionUnions`; `PositiveBoundaries`; `SquareIntegral`; `SquareBoundaries` | Positive interior Jacobian only, closed-domain injectivity, image as closure of an open set, positive boundaries independent of parametrization for all continuous test forms, finite unions with disjoint interiors, square coverage by the two printed affine triangles, determinant +1, surface-integral decomposition, diagonal cancellation and four oriented outer edges. |
| 10.32 | `SphereBoundary.pma10_32`; `RectangleEdges` | Literal latitude/longitude map and rectangle, full unit-sphere image, four literal edge maps, both constant-pole integrals zero, reversed-meridian integrals opposite, and zero boundary functional for every continuous one-form. |
| 10.33 | `ChainStokes.pma10_33`; `SimplexFTC`; `SimplexStokes`; `StokesTransport` | General finite C2 chains of every positive dimension in every ambient dimension, C1 forms, actual native surface and boundary integrals, no rank/injectivity/nondegeneracy premise, and no conditional Stokes assumption left in the principal. |

The displayed tetrahedron boundary in 10.31 is the dimension-three specialization
of the proved general alternating-face formula. The cyclic triangle presentation
in 10.29 follows from its explicitly proved triangle signs and the dimension-one
orientation theorem. Oppositely ordered affine-simplex cancellation in 10.28
combines the actual 10.27 integral sign with the proved chain-additivity law.
These presentations are not each given an additional separately named principal.

## Important proof checks

- `simplexVertexPermutation` is an affine map through the permuted standard
  vertices, not multiplication of a parametrization by a scalar. Its composition,
  inverse, and exact image lemmas establish the actual reparametrization. The
  augmented-vertex determinant proves the sign without affine independence of the
  target vertices. `affineSimplexMap_comp_permutation` explicitly connects the
  reordered map to the original map composed with that parameter change.
- `simplexRIntegral_comp_of_abs_det_one` first establishes the native iterated
  Riemann-integrability assertion. It then uses the proved native/measure bridge
  and the Jacobian theorem. Thus 10.27 does not replace native integration with a
  measure-only definition or assume its conclusion as an orientation convention.
- The zero-dimensional permutation clause of 10.27 is necessarily the identity
  permutation of `Fin 1`. The independent negative sign on a zero-simplex comes
  from first-half `signedAffineIntegral` and the final clause of `pma10_26`, which
  evaluates a signed point to its signed function value. These two interfaces
  together cover the source's zero-dimensional convention.
- `C2Simplex` retains its map and existence of an open C2 neighborhood. The
  apparently more direct representation is justified by
  `C2Simplex.standard_mapBy`: every such simplex is the pushforward of the
  standard affine simplex, after restricting to the preimage of the form domain.
- `PositiveSimplex` permits a singular derivative on the boundary.
  `PositiveSimplex.jacobian_nonneg` derives nonnegativity there from interior
  positivity. `PositiveSimplex.closure_openCarrier` proves the asserted closure
  property. `PositiveRegion` requires disjoint carrier interiors, not disjoint
  closed pieces. Frontier-null and image-integral proofs justify union additivity.
- `PositiveSimplex.boundary_independent` and the region version initially apply
  Stokes to C1 forms, then use `chainEq_of_c1`, uniform smooth coefficient
  approximation, and explicit integral error bounds. Their final `ChainEq`
  quantifies all continuous forms. This closes a common regularity gap in 10.31.
- The square supplement accepts an arbitrary C1 `Surface`, preserving the source
  surface scope; it does not require that square surface to be C2.
- The final Stokes theorem combines an actually proved scalar-coordinate FTC and
  the actual signed-face integrands into `standard_simplex_stokes`. The standard
  case is then transported using pullback differentiation and native integration,
  and extended by finite integer linearity. The conditional helper
  `simplex_stokes_of_standard` is discharged in `ChainStokes.pma10_33`.

Relevant probes inspected: `SimplexChainProbes` tests a base-vertex-moving swap,
a repeated vertex, and signed endpoint evaluation; `BoundaryExamplesProbes` tests
continuous nonsmooth sphere coefficients and the C1 square scope;
`PositiveBoundaryProbes` tests a cubic parametrization with singular endpoint;
`StokesProbes` tests folded/noninjective maps, negative multiplicity and the scalar
endpoint case. Their current build status belongs to the parent's build log.

## Representation choices and deviations

No narrowed source theorem was found. The following choices should remain visible
in the final report rather than being mistaken for literal source syntax:

1. Chains are finitely supported integer combinations, extending the source's
   finite-collection notation and representing negative orientation by integer
   coefficients. Raw free-chain equality is distinct from `ChainEq`/
   `AffineChainEq`, which compare all form integrals. This distinction is documented
   beside the chain definitions.
2. General C2 simplexes are stored as their actual parameter maps with open
   neighborhood regularity; their standard-affine pushforward representation is
   proved, not imposed as an opaque assumption.
3. Dimension zero is included in native integration and permutation statements;
   signed-point orientation is supplied by the separate first-half signed-integral
   interface. Stokes uses `d + 1`, exactly the positive-dimensional source scope.
4. Positive-boundary independence is proved using Stokes and smooth approximation
   after the book's source order. This is a proof-order difference, not an added
   hypothesis or circular definition.

## Dependency subset for 10.27–10.33

A recursive scan of `Rudin.PMA.Chapter10.*` imports from the seven principal
modules found **58 chapter modules**: **25 recovered second-half modules** and
**33 first-half modules currently absent from the lane's chapter directory**.
This is a chapter-module scan, not a count of transitive Mathlib/earlier-chapter
imports.

The direct first-half interface frontier is:
`AffineSimplices`, `ChangeOfVariables`, `ExteriorDerivativeRules`,
`PullbackDifferentiation`, `PullbackEvaluation`, `Simplex`, `SphereExamples`,
`StandardForms`, `SurfacePullbacks`.

Recovered second-half closure:
`AffineChains`, `AffineFaces`, `BoundaryDefinitions`, `ChainMaps`, `ChainStokes`,
`FormApproximation`, `FormIntegralContinuity`, `PositiveBoundaries`,
`PositiveRegionUnions`, `PositiveRegions`, `RectangleEdges`, `SimplexBoundaries`,
`SimplexChains`, `SimplexChangeOfVariables`, `SimplexFTC`, `SimplexFormFaces`,
`SimplexOrientation`, `SimplexStokes`, `SphereBoundary`, `SquareBoundaries`,
`SquareIntegral`, `StandardSimplexSurface`, `StokesCoefficients`, `StokesTransport`,
`SurfacePrecomposition`.

First-half closure:
`AffineSimplices`, `ChangeOfVariables`, `CoordinateDifferentiation`,
`ExteriorDerivative`, `ExteriorDerivativeRules`, `FormDefinitions`, `FormExamples`,
`FormOperations`, `FormRegularity`, `FormSeparation`, `FormsAlgebra`, `FormsCore`,
`Integration`, `IntegrationMeasure`, `IntegrationProofs`, `NativeSeparation`,
`Partition`, `Primitive`, `PullbackAlgebra`, `PullbackDifferentiation`,
`PullbackEvaluation`, `PullbackRegularity`, `Pullbacks`, `ScalarForms`, `Simplex`,
`SimplexSlices`, `SphereExamples`, `StandardForms`, `SurfaceDomains`, `SurfaceMaps`,
`SurfacePullbacks`, `Surfaces`, `WedgeProducts`.

## Historical evidence versus this review

The prior branch contains independent source and production reviews at
`research/pma-ch10-source-review.md` and `research/pma-ch10-production-review.md`.
The source review records final acceptance of the 10.27–10.30 contracts and proofs,
then the two substantive 10.31 component contracts, sphere example and full
Stokes assembly. Historical production gates report 9063 jobs through 10.30 and
9090 jobs through 10.35, with only `propext`, `Classical.choice`, and `Quot.sound`.
Those are historical claims from the recovered branch, not fresh compiler/audit
results produced by this reviewer. A byte comparison of the 25 recovered
second-half production modules listed above against `bb50a20` found no
differences. Current snapshot compilation and the recursive axiom audit must be
reported from the parent's current run.
