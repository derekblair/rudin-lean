# Independent Chapter 10 compatibility fidelity review

Reviewed the integrated working-tree `Chapter10/Prerequisites.lean` against recovered commit `bb50a2079f8e189d8e282e2521bbadb64f4f98eb`, merged main `f7f4e813348d0fb8ddc3b6645f794448266b44b9`, and all changed Chapter 10 production modules against source B `2e65e410a527aa25bf776d6d61b6c56db0ee137f`. This was a read-only source review. No builds or proof attempts were run by this reviewer.

## Finding

No mathematical conflict, hidden hypothesis strengthening, or weakening of a verified Chapter 10 conclusion was found. The adapter keeps the recovered mathematical representations under `Rudin.PMA.Chapter10` while importing the live merged Chapters 8/9. The nine changed production modules have only import changes and explicit namespace-reference adaptations. Their bodies and statements match source B exactly after those enumerated substitutions. Fresh kernel acceptance remains the parent integration build's responsibility.

The recovered and live `lean-toolchain`, `lake-manifest.json`, and `lakefile.toml` are byte-identical, so this reconciliation does not include a toolchain or Mathlib-version change.

## Prerequisite declarations

The adapter contains 27 named declarations. Automated comparison after removing comments and normalizing whitespace found 23 complete declaration bodies identical to their recovered originals. The remaining four are the C1 alias and three bridge proofs listed below. Namespace relocation is intentional and disclosed.

| Group | Declarations | Fidelity finding |
|---|---|---|
| Euclidean coordinates | `Euclidean`, `standardBasis`, `Operator`, `operatorMatrix`, `standardBasis_repr`, `standardBasis_apply`, `operatorMatrix_apply` | All seven declarations match recovered `Chapter09/Linear.lean`. The space remains `EuclideanSpace ℝ (Fin n)`, with Euclidean norm, the same orthonormal-coordinate basis, continuous linear maps, and target-row/source-column matrix convention. |
| Coordinate derivatives | `coordinateVector`, `HasCoordinatePartial`, `coordinatePartial`, `hasCoordinatePartial_of_hasFDerivAt`, `coordinatePartial_eq_fderiv`, `linear_apply_eq_sum_coordinates` | All six declarations match recovered `Chapter09/Differentiation.lean`. Coordinate derivatives remain derivatives at zero along `x + t • coordinateVector n j`; they are not replaced with the merged chapter's differently ordered function-space coordinate interface. No total-differentiability assumption is added to the partial-derivative definitions. |
| Determinants | `tupleSign`, `columnDet`, `jacobian`, `partialJacobian`, `pma9_38_contract`, `operator_isUnit_iff_det_ne_zero`, `operator_isInvertible_iff_isUnit`, `pma9_38` | All eight match recovered `Chapter09/Determinants.lean`. Signs, column orientation, full Jacobian, first-block partial Jacobian, differentiability assumptions, and invertibility conclusions are unchanged. The `pma9_38` package is scoped Chapter 10 support, not a replacement for main's Chapter 9 nodes. |
| Inverse predicate | `InverseNeighborhood` | Exact recovered declaration: forward function equals `f`, `a` belongs to the source, and source is contained in `E`. The open partial homeomorphism continues to supply openness, continuity, bijection, and both inverse identities. |
| Native integral bridge | `orientedRIntegral_eq_intervalIntegral` | Exact recovered theorem statement and proof from `ParameterIntegrals.lean`; still requires global continuity and handles both integration orientations and equal endpoints. Uses the unchanged native Chapter 6 primitives and current Chapter 8 integral definition. |
| C1 predicate | `C1On` | Changed from recovered `def` to an `abbrev` of main `Chapter09.IsC1On`. Main's definition is literally the same conjunction `(∀ x ∈ E, DifferentiableAt ℝ f x) ∧ ContinuousOn (fderiv ℝ f) E`. These are definitionally equal predicates, not just similar descriptions. Generic normed-space typeclass contexts match. |
| C1 equivalence | `c1On_iff_contDiffOn` | Recovered theorem statement is identical, including the `IsOpen E` hypothesis. Its proof invokes merged `Chapter09.pma9_20`; no new openness or smoothness assumption is inserted at a Chapter 10 call site. |
| Local inverse | `inverse_neighborhood_c1` | Recovered statement is identical, including generic normed-space contexts and `CompleteSpace V` only. The same `hE`, `ha`, C1 hypothesis, and invertible derivative at `a` yield the same neighborhood, C1 inverse on all its target, and inverse derivative formula at every target point. New proof obtains the neighborhood from merged `pma9_24`, derives two-sided differential identities from the actual inverse equations, packages the differential as a continuous linear equivalence, and obtains the same derivative formula. This does not assume derivative invertibility everywhere as an extra input. |
| Uniform native integral limit | `rsIntegral_tendsto_of_uniformFilterLimit` | Recovered statement is identical, including general index type/filter, nontriviality, eventual native integrability, and uniform convergence on `Icc a b`. Direct application of main `Chapter09.rsIntegral_uniformLimit_filter` preserves both limit-integrability and convergence conclusions. |

The declaration-comparison details are saved in `/tmp/ch10-prerequisite-declaration-comparison.json`. The 23 unchanged declarations consist of the first five table groups; the final four rows explain every intentional deviation.

## Name resolution and preservation of Chapter 10 statements

The support lives in `Rudin.PMA.Chapter10`, so existing unqualified Euclidean/coordinate/determinant references in that namespace resolve to the recovered definitions. This intentionally avoids `Chapter09.coordinatePartial` in main, whose coordinate space and argument order differ. The former explicitly qualified `Chapter09.Euclidean`, `Chapter09.coordinateVector`, and two native-integral helper references were changed only where necessary to point to the scoped equivalents.

`Euclidean` unfolds to exactly the old type. The other scoped definitions have identical bodies in terms of that type. `C1On` unfolds through main `IsC1On` to exactly the old conjunction. Thus changing the qualified names does not alter the ambient norm, parameter domain, derivative convention, differentiability order, quantifiers, or hypotheses of the Chapter 10 declarations. Nothing asserts equality of the incompatible old and new Chapter 9 coordinate interfaces.

## Nine adapted production modules

| File under `Chapter10/` | Exact change |
|---|---|
| `AffineSimplices.lean` | Redirect `Chapter09.Determinants` import to `Chapter10.Prerequisites`. |
| `CoordinateDifferentiation.lean` | Redirect `Chapter09.Differentiation` import to prerequisites. |
| `Integration.lean` | Redirect `Chapter09.ParameterIntegrals` import; replace three `Chapter09.Euclidean` type references with scoped `Euclidean`. |
| `IntegrationProofs.lean` | Replace explicit Chapter09 qualification on the oriented-integral bridge and uniform-filter-limit helper. |
| `NativeSeparation.lean` | Replace explicit Chapter09 qualification on Euclidean types and `coordinateVector`; no hypotheses or proof expressions otherwise change. |
| `Partition.lean` | Redirect `Chapter09.Linear` import to prerequisites. |
| `PrefixCoordinates.lean` | Redirect `Chapter09.Differentiation` import to prerequisites. |
| `Primitive.lean` | Replace the two Chapter09 Inverse/Determinants imports with the one prerequisites import. |
| `StandardForms.lean` | Redirect `Chapter09.Determinants` import to prerequisites. |

I enumerated every differing source-B production module. Exactly these nine differ. For each, removing import lines and applying only the four named Chapter09-to-scoped reference substitutions makes the complete source byte-identical. There are no changed tactics, theorem assumptions, conclusions, local definitions, or unlisted edits in those nine files. Snapshot hashes of the inspected versions are in `/tmp/ch10-nine-module-comparison.json`.

## Other observations

- `Chapter10.lean` still described recovered proof modules as preserved “verbatim” at initial inspection. That wording is inaccurate for the nine adapted files and was flagged to the parent for correction. This is a documentation issue, not a mathematical defect.
- The earlier audit adaptations and new integration audit are intentionally separate verification-code changes. Their comparator blocks remain intact and are covered in `/tmp/ch10-coverage-review.md`.
- The 10.43 contract/partial results are not among the adapted production files. This review neither modifies nor attempts its missing C² vector-potential clause.
