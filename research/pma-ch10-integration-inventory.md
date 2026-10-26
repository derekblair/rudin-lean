# Chapter 10 prerequisite inventory (before integration)

Baseline: `origin/main = f7f4e813348d0fb8ddc3b6645f794448266b44b9`.
First half: `origin/lane/rudin-ch10-a = c7262b1fe9978c573e4e15ea506d972411e4d963`.
Second half: `origin/lane/rudin-ch10-b = 2e65e410a527aa25bf776d6d61b6c56db0ee137f`.
Recovered provenance: `origin/ch8-codex-20261022 = bb50a2079f8e189d8e282e2521bbadb64f4f98eb`.

The two lane trees predate merged Chapters 8/9 and several closed review findings; therefore a tree checkout or merge selecting their old prerequisite versions would regress main. Import only Chapter 10 assets and scoped provenance. All main Chapter 1–9 sources and aggregates remain authoritative.

The 13 files reported missing by the lane snapshot audit are historical missing paths, not 13 still-missing paths at today's main. Six Chapter 8 files are now present byte-for-byte, four Chapter 9 paths are present with newly merged interfaces, and three old Chapter 9 paths were replaced by a different module layout. No whole old Chapter 9 module should be copied.

## Historical missing-file decisions

| Prior path (under `rudin/Rudin/PMA`) | Current main status and decision |
| --- | --- |
| `Chapter08/Abel.lean` | Present, byte-identical to recovered source; use main. |
| `Chapter08/DoubleSeries.lean` | Present, byte-identical; use main. |
| `Chapter08/Exponential.lean` | Present, byte-identical; use main. |
| `Chapter08/Operations.lean` | Present, byte-identical; use main. |
| `Chapter08/PowerSeries.lean` | Present, byte-identical; use main. |
| `Chapter08/Taylor.lean` | Present, byte-identical; use main. |
| `Chapter09/Determinants.lean` | Present, supersedes old node proofs. Main uses `pma9_33_sign`, `pma9_33_detColumns`, and `pma9_38_jacobian` (the last over function-coordinate space). Ch10's Euclidean `tupleSign`, `columnDet`, `jacobian`, `partialJacobian`, and invertibility helpers are not present under the old API. Bring only these narrow definitions/helpers into a scoped Ch10 prerequisites module, attributed to recovered source; do not replace main. |
| `Chapter09/Differentiation.lean` | Present, supersedes old node proofs. Main supplies `pma9_coordinate` and partial predicates, with `IsC1On` and `pma9_20` in `ContinuousDifferentiability`. Ch10 needs Euclidean-coordinate aliases/helpers. Adapt imports to scoped prerequisites and bridge `C1On` to main's exact `IsC1On` definition. |
| `Chapter09/HigherDerivatives.lean` | Present, supersedes old nodes 9.39–9.41. Not directly used for any Ch10 theorem; was a transitive import of old ParameterIntegrals. Drop old copy. Important name collision: main `Chapter09.coordinatePartial i f x` uses `Fin n → ℝ`; recovered `coordinatePartial f x j` uses `EuclideanSpace ℝ (Fin n)`. Preserve the recovered Euclidean definition under `Chapter10.coordinatePartial`, leaving main untouched. |
| `Chapter09/Inverse.lean` | Present, supersedes old 9.24/9.25 proofs. Main's generic `pma9_24` provides the C1 local inverse; adapt the old `inverse_neighborhood_c1` interface through main, then obtain the derivative formula from the open partial homeomorphism. No old node contracts or proofs needed. |
| `Chapter09/Linear.lean` | Absent by design: merged `LinearFoundations` and `Operators` supersede it. Preserve only Ch10's exact Euclidean aliases (`Euclidean`, `standardBasis`, `Operator`, `operatorMatrix`) and three evaluation lemmas in the scoped prerequisite module. Drop the old nodes 9.1–9.9. |
| `Chapter09/ParameterIntegrals.lean` | Absent by design: `Integrals.lean` supersedes old nodes 9.42–9.43. Ch10 uses only `rsIntegral_tendsto_of_uniformFilterLimit` and `orientedRIntegral_eq_intervalIntegral`. Alias the first to main `rsIntegral_uniformLimit_filter`; recover only the exact oriented native integral bridge (missing under this interface), attributed. Drop the rest. |
| `Chapter09/PartialExamples.lean` | Absent by design: merged `DiscontinuousPartials`/`PartialCounterexamples` supersede old 9.16 examples. No Ch10 symbol uses it directly; eliminate its old transitive edge and drop old copy. |
| `Chapter08.lean` aggregate | Main's complete 22-node aggregate supersedes recovered 8.1–8.6 aggregate and lanes' two-foundation-module aggregate. Keep main unchanged. |

## Mathematical conflict assessment

No contradictory mathematical prerequisite was found. The coordinate-partial collision is an interface/representation difference (argument order, basepoint parameterization, Euclidean norm versus function-space norm), not a license to redefine either declaration. Keeping Ch10's exact Euclidean definition in its own namespace avoids changing any verified Ch10 proposition. Main remains the source of its own Chapter 9 numbering and proofs. The compatibility module must explicitly import main Chapter09, so the live build checks coexistence of both representations. Helpers not available under a matching main interface are attributed extra Ch10 support, not replacement Chapter 9 proofs.

## Every transitive recovered Rudin prerequisite

This is the full import closure before adaptation, using the recovered prerequisite-complete snapshot (38 files; excludes Ch10 itself and Mathlib). `byte-identical` compares current main against `bb50a20`.

| Path | Comparison | Decision |
| --- | --- | --- |
| `Chapter01.lean` | different | Use main; standalone 1.2 and review repairs supersede prior version. |
| `Chapter01Audit.lean` | different | Use main transitive axiom audit; adapt Ch10 audit caller to its return shape if required. |
| `Chapter01Probes.lean` | byte-identical | Use current main unchanged. |
| `Chapter02.lean` | byte-identical | Use current main unchanged. |
| `Chapter03.lean` | different | Use main review-repaired statements; no prior rollback. |
| `Chapter04.lean` | different | Use main review-repaired statements; no prior rollback. |
| `Chapter05.lean` | byte-identical | Use current main unchanged. |
| `Chapter06.lean` | different | Use main full aggregate, including the closed jump finding. |
| `Chapter06/Basic.lean` | byte-identical | Use current main unchanged. |
| `Chapter06/Calculus.lean` | byte-identical | Use current main unchanged. |
| `Chapter06/Criterion.lean` | byte-identical | Use current main unchanged. |
| `Chapter06/Curve.lean` | byte-identical | Use current main unchanged. |
| `Chapter06/Definitions.lean` | byte-identical | Use current main unchanged. |
| `Chapter06/Endpoint.lean` | byte-identical | Use current main unchanged. |
| `Chapter06/Exceptional.lean` | byte-identical | Use current main unchanged. |
| `Chapter06/Integrability.lean` | byte-identical | Use current main unchanged. |
| `Chapter06/Jump.lean` | different | Use main repaired jump theorem; no Ch10 direct use of the old proof. |
| `Chapter06/Moment.lean` | byte-identical | Use current main unchanged. |
| `Chapter06/Monotone.lean` | byte-identical | Use current main unchanged. |
| `Chapter06/Properties.lean` | byte-identical | Use current main unchanged. |
| `Chapter06/Refinement.lean` | byte-identical | Use current main unchanged. |
| `Chapter06/Split.lean` | byte-identical | Use current main unchanged. |
| `Chapter06/Vector.lean` | byte-identical | Use current main unchanged. |
| `Chapter07/Calculus.lean` | byte-identical | Use current main unchanged. |
| `Chapter08.lean` | different | Keep main complete aggregate; drop prior partial aggregate. |
| `Chapter08/Abel.lean` | byte-identical | Use current main unchanged. |
| `Chapter08/DoubleSeries.lean` | byte-identical | Use current main unchanged. |
| `Chapter08/Exponential.lean` | byte-identical | Use current main unchanged. |
| `Chapter08/Operations.lean` | byte-identical | Use current main unchanged. |
| `Chapter08/PowerSeries.lean` | byte-identical | Use current main unchanged. |
| `Chapter08/Taylor.lean` | byte-identical | Use current main unchanged. |
| `Chapter09/Determinants.lean` | different | Use merged chapter and scoped Ch10 compatibility; drop prior whole module (see decisions above). |
| `Chapter09/Differentiation.lean` | different | Use merged chapter and scoped Ch10 compatibility; drop prior whole module (see decisions above). |
| `Chapter09/HigherDerivatives.lean` | different | Use merged chapter and scoped Ch10 compatibility; drop prior whole module (see decisions above). |
| `Chapter09/Inverse.lean` | different | Use merged chapter and scoped Ch10 compatibility; drop prior whole module (see decisions above). |
| `Chapter09/Linear.lean` | absent | Use merged chapter and scoped Ch10 compatibility; drop prior whole module (see decisions above). |
| `Chapter09/ParameterIntegrals.lean` | absent | Use merged chapter and scoped Ch10 compatibility; drop prior whole module (see decisions above). |
| `Chapter09/PartialExamples.lean` | absent | Use merged chapter and scoped Ch10 compatibility; drop prior whole module (see decisions above). |

## Adaptation plan

Add `Chapter10/Prerequisites.lean` importing the merged Chapter09 and current Chapter08 (including its native integral API). Keep the recovered support in the Chapter10 namespace, disclosing source provenance. Redirect the eight direct Chapter09 import edges in seven Ch10 modules to that module (deduplicate the two imports in Primitive). Explicit `Chapter09.Euclidean` / `Chapter09.coordinateVector` / two integral-helper references in Integration, IntegrationProofs, and NativeSeparation become scoped Ch10 references. Unqualified recovered names naturally resolve to the Ch10 definitions in existing namespace blocks. No verified mathematical statement is weakened.

This inventory is source inspection, not yet a kernel acceptance result. Root's full live-tree build and transitive audit are the final gates.

## Implemented prerequisite adapter provenance

`rudin/Rudin/PMA/Chapter10/Prerequisites.lean` imports current `Chapter08` and `Chapter09.SecondHalf` (which includes FirstHalf). It adds only the following 27 scoped declarations, under `Rudin.PMA.Chapter10`, so the merged chapter declarations coexist unchanged:

| Provenance | Scoped declarations | Difference from recovered declarations |
| --- | --- | --- |
| Recovered `Chapter09/Linear.lean` | `Euclidean`, `standardBasis`, `Operator`, `operatorMatrix`, `standardBasis_repr`, `standardBasis_apply`, `operatorMatrix_apply` | Declaration bodies unchanged; namespace moved into Ch10. |
| Recovered `Chapter09/Differentiation.lean` | `coordinateVector`, `HasCoordinatePartial`, `coordinatePartial`, `hasCoordinatePartial_of_hasFDerivAt`, `coordinatePartial_eq_fderiv`, `linear_apply_eq_sum_coordinates` | Declaration bodies unchanged; namespace moved into Ch10, preventing the coordinatePartial collision with main. |
| Main `Chapter09/ContinuousDifferentiability.lean` | `C1On`, `c1On_iff_contDiffOn` | `C1On` is an abbreviation of main `IsC1On` (definitionally the exact recovered conjunction); the comparison theorem is main `pma9_20` with unchanged type. |
| Recovered `Chapter09/Determinants.lean` | `tupleSign`, `columnDet`, `jacobian`, `partialJacobian`, `pma9_38_contract`, `operator_isUnit_iff_det_ne_zero`, `operator_isInvertible_iff_isUnit`, `pma9_38` | Declaration bodies unchanged; namespace moved into Ch10. The scoped `pma9_38` packages exactly the former Euclidean API; it does not replace main's Chapter09 node. |
| Recovered `Chapter09/Inverse.lean` / main `Chapter09/Inverse.lean` | `InverseNeighborhood`, `inverse_neighborhood_c1` | Predicate body unchanged. Helper statement unchanged; proof now invokes main `Chapter09.pma9_24`, obtains both inverse differential identities, bundles them as a continuous linear equivalence, and derives the same inverse derivative formula. |
| Main `Chapter09/Integrals.lean` | `rsIntegral_tendsto_of_uniformFilterLimit` | Statement identical to recovered helper; proof directly invokes main `rsIntegral_uniformLimit_filter`. |
| Recovered `Chapter09/ParameterIntegrals.lean` | `orientedRIntegral_eq_intervalIntegral` | Declaration body unchanged; namespace moved into Ch10; it uses the current native Chapter06/08 APIs. |

The moved definitions retain EuclideanSpace, Euclidean operator norms, centered coordinate slices, determinant conventions, and derivative assumptions exactly. In particular, no sup-norm replacement or argument-order mutation is made to the recovered Ch10 propositions.

## Preliminary kernel check

The root's full live-tree integration build successfully compiled
`Rudin.PMA.Chapter10.Prerequisites` on its first attempt, at progress 9029/9177.
No adapter diagnostics or follow-up edits were required. This establishes the
adapter's kernel acceptance against the merged Chapter 8/9 imports; the overall
full-build completion and transitive Chapter 10 axiom audit were still pending
when this preliminary result was recorded.

# Chapter 10 coverage and audit review

Reviewed source heads: `origin/lane/rudin-ch10-a` = `c7262b1fe9978c573e4e15ea506d972411e4d963`; `origin/lane/rudin-ch10-b` = `2e65e410a527aa25bf776d6d61b6c56db0ee137f`. Full brief read. This review initially uses git objects, not an integration build.

## Source inventory

- First half: 35 recovered production modules + 4 supplementary production modules + 10 probes + first-half aggregate + first-half audit = 51 files.
- Second half: 79 recovered production modules + 15 probes + second-half aggregate + second-half audit = 96 additional files.
- Combined: 118 production modules, 25 probe modules, 2 aggregates, 2 audit modules = 147 Lean files.
- All 45 recovered first-half files and all 94 recovered second-half files match both their manifest SHA-256 and the original bb50a2079f8e189d8e282e2521bbadb64f4f98eb bytes. Every first-half Ch10 file is unchanged between the A and B heads.
- The four supplementary first-half files are `AffineOrientation.lean`, `ExactOneFormComplements.lean`, `FormExampleGeometry.lean`, and `PartitionComplements.lean`.
- The import closure of the two source audit modules includes all 147 Ch10 Lean files, including all 25 probe modules; no source file is orphaned. This is a static closure check, not a build claim.

## Principal and contract inventory

Every numbered item 10.1–10.51 has its own `pma10_N_contract` definition. Exactly 50 have a principal `pma10_N` theorem. Only `pma10_43` is absent. The first-half audit checks 26 principals and compares all 26 principal types to contracts, plus the relative-orientation contract. The second-half audit checks and compares the other 24 principals.

| Node | Principal/contract module | State |
|---|---|---|
| 10.1 | `Integration.lean` | `pma10_1` and contract present |
| 10.2 | `Integration.lean` | `pma10_2` and contract present |
| 10.3 | `Integration.lean` | `pma10_3` and contract present |
| 10.4 | `Integration.lean` | `pma10_4` and contract present |
| 10.5 | `Primitive.lean` | `pma10_5` and contract present |
| 10.6 | `Primitive.lean` | `pma10_6` and contract present |
| 10.7 | `Primitive.lean` | `pma10_7` and contract present |
| 10.8 | `Partition.lean` | `pma10_8` and contract present |
| 10.9 | `ChangeOfVariables.lean` | `pma10_9` and contract present |
| 10.10 | `SurfaceDomains.lean` | `pma10_10` and contract present |
| 10.11 | `FormDefinitions.lean` | `pma10_11` and contract present |
| 10.12 | `FormExamples.lean` | `pma10_12` and contract present |
| 10.13 | `FormOperations.lean` | `pma10_13` and contract present |
| 10.14 | `StandardForms.lean` | `pma10_14` and contract present |
| 10.15 | `FormSeparation.lean` | `pma10_15` and contract present |
| 10.16 | `WedgeProducts.lean` | `pma10_16` and contract present |
| 10.17 | `WedgeProducts.lean` | `pma10_17` and contract present |
| 10.18 | `ExteriorDerivative.lean` | `pma10_18` and contract present |
| 10.19 | `ExteriorDerivative.lean` | `pma10_19` and contract present |
| 10.20 | `ExteriorDerivative.lean` | `pma10_20` and contract present |
| 10.21 | `Pullbacks.lean` | `pma10_21` and contract present |
| 10.22 | `Pullbacks.lean` | `pma10_22` and contract present |
| 10.23 | `Pullbacks.lean` | `pma10_23` and contract present |
| 10.24 | `Pullbacks.lean` | `pma10_24` and contract present |
| 10.25 | `Pullbacks.lean` | `pma10_25` and contract present |
| 10.26 | `AffineSimplices.lean` | `pma10_26` and contract present |
| 10.27 | `SimplexOrientation.lean` | `pma10_27` and contract present |
| 10.28 | `AffineChains.lean` | `pma10_28` and contract present |
| 10.29 | `SimplexBoundaries.lean` | `pma10_29` and contract present |
| 10.30 | `ChainMaps.lean` | `pma10_30` and contract present |
| 10.31 | `BoundaryDefinitions.lean` | `pma10_31` and contract present |
| 10.32 | `SphereBoundary.lean` | `pma10_32` and contract present |
| 10.33 | `StokesTransport.lean` | `pma10_33` and contract present |
| 10.34 | `ClosedExact.lean` | `pma10_34` and contract present |
| 10.35 | `ClosedFormConsequences.lean` | `pma10_35` and contract present |
| 10.36 | `PuncturedExamples.lean` | `pma10_36` and contract present |
| 10.37 | `PuncturedExamples.lean` | `pma10_37` and contract present |
| 10.38 | `ConvexPrimitives.lean` | `pma10_38` and contract present |
| 10.39 | `Poincare.lean` | `pma10_39` and contract present |
| 10.40 | `DiffeomorphicExactness.lean` | `pma10_40` and contract present |
| 10.41 | `CellTriangulation.lean` | `pma10_41` and contract present |
| 10.42 | `VectorFields.lean` | `pma10_42` and contract present |
| 10.43 | `VectorPotentials.lean` | partial: exact contract and first three clauses; no principal |
| 10.44 | `VolumeElements.lean` | `pma10_44` and contract present |
| 10.45 | `PlanarGreen.lean` | `pma10_45` and contract present |
| 10.46 | `AreaElements.lean` | `pma10_46` and contract present |
| 10.47 | `Torus.lean` | `pma10_47` and contract present |
| 10.48 | `Circulation.lean` | `pma10_48` and contract present |
| 10.49 | `Flux.lean` | `pma10_49` and contract present |
| 10.50 | `ClassicalStokes.lean` | `pma10_50` and contract present |
| 10.51 | `DivergenceTheorem.lean` | `pma10_51` and contract present |

## Probe inventory

- `BoundaryExamplesProbes.lean`
- `CellTriangulationProbes.lean`
- `ChangeOfVariablesProbes.lean`
- `ClassicalCalculusProbes.lean`
- `ClosedFormProbes.lean`
- `ConvexExactnessProbes.lean`
- `ConvexPrimitiveProbes.lean`
- `ExteriorDerivativeProbes.lean`
- `FormAlgebraProbes.lean`
- `FormProbes.lean`
- `IntegrationProbes.lean`
- `PartitionProbes.lean`
- `PositiveBoundaryProbes.lean`
- `PrimitiveProbes.lean`
- `PullbackProbes.lean`
- `PuncturedProbes.lean`
- `ScalarPotentialProbes.lean`
- `SimplexChainProbes.lean`
- `SimplexProbes.lean`
- `SphereExampleProbes.lean`
- `StokesProbes.lean`
- `TorusProbes.lean`
- `VectorFieldProbes.lean`
- `VectorIntegrationProbes.lean`
- `VolumeAreaProbes.lean`

## Exact 10.43 boundary

- `VectorPotentials.lean` preserves the exact four-clause `pma10_43_contract`, with `ContDiffOn ℝ 2 G E` in the final vector-potential conclusion.
- `pma10_43_forward` proves the two forward C² identities; `pma10_43_scalar_converse` proves the full C² scalar-potential converse.
- `vectorPotential_c1_of_equivalent_convex` gives only `ContDiffOn ℝ 1 G E` and has an explicit comment distinguishing it from the stronger C² requirement. It is not counted as completion.
- `SecondHalf.lean`, the second-half audit and `research/pma-ch10-b-43-blocker.md` explicitly record the incompleteness. The audit rejects a principal named `pma10_43`.
- Preserve `VectorPotentials.lean` byte-for-byte and copy the blocker record unchanged. Do not attempt to prove the missing clause.

## PDF check

The launch path `/home/derekblair/sources/pma3.pdf` is absent. The relocated file is `/home/derekblair/projects/math/references/sources/pma3.pdf` (351 pages). Using the PDF skill workflow, extracted and visually inspected complete printed pages 281–282 (PDF pages 290–291); printed 281 explicitly requires a C² vector potential in the final converse while the input field is C¹. Page 282 continues the node and then begins 10.44. No proof text is reproduced in this report.

## Required fresh audit adaptation

Current main has `Rudin.PMA.Audit.checkModuleAxioms` in `Rudin/PMA/AxiomAudit.lean`. It selects declarations by actual module ownership, retains private/generated/equation declarations even outside chapter namespaces, and invokes Lean `collectAxioms` transitively. Its only allowed axioms are `propext`, `Classical.choice`, and `Quot.sound`.

The recovered first-half audit still calls the removed `checkNamespaceAxioms`; the second-half audit implements its own namespace-based filter. Both need minimal audit-only changes to use current main’s module audit. Preserve all existing principal/contract comparators and coverage checks.

Recommended integration audit: import both chapter audits, require all 50 principals, all 51 contracts, and the three named 10.43 partial results; explicitly reject `pma10_43`; call `checkModuleAxioms` for the `Rudin.PMA.Chapter10` module prefix. This prefix includes production, second-half audit, integration audit, and all probe modules. The separate `Rudin.PMA.Chapter10Audit` outer audit is not a submodule of `Chapter10` and can be audited with `allowEmpty := true` separately. Explicitly require each of the 25 probe modules to be imported. Wire the root `Rudin.lean` to this integration audit; keep `Chapter10.lean` as first-half aggregate to avoid its second-half import cycle.

No build was run during this read-only review. Fresh integration build and actual audited declaration/module counts must be supplied by the integration lane.

## Preserved 10.43 SHA-256 identities

- `rudin/Rudin/PMA/Chapter10/VectorPotentials.lean`: `d7c1a926415911e523a70a29c0957bc63dc271b981f86c04dcbcb11ee37f4c84`.
- `rudin/Rudin/PMA/Chapter10/SecondHalf.lean`: `1458d6d4fc6db181417779558d4f73cc4959472af1111828c5d1c8cd6e04a8cf`.
- `research/pma-ch10-b-43-blocker.md`: `4a62677650a432454338bf12b37f75c26f171149fae6e07bb44795e26f1a1704`.

## Audit implementation delivered

- `Chapter10Audit.lean`: replaced indirect `Chapter01Audit` import with direct current `AxiomAudit` import; replaced two namespace audits with a single module-ownership audit covering the chapter and all its imported probes. All principal, supplementary, and contract checks are unchanged.
- `Chapter10/SecondHalfAudit.lean`: replaced raw Lean audit imports with current `AxiomAudit`; retained all 24 contract comparisons, principal lookups, and the explicit rejection of `pma10_43`; replaced its namespace-filtered traversal with `checkModuleAxioms`.
- New `Chapter10/IntegrationAudit.lean`: imports both adapted audits; checks all 51 contracts, 50 principal theorem names, 3 retained partial-10.43 theorems, 5 first-half supplementary theorem names, and the relative-orientation supplementary contract. Requires every one of the 25 probe modules. Uses source-module ownership and recursive axiom collection, plus a separate audit for the outer first-half audit module. Adds a definitional comparison of the exact four-clause 10.43 contract (including final C² vector output), and explicit type comparisons of the two forward identities, C² scalar converse, and weaker C¹ vector helper. The contract comparison asserts only definitional equivalence; it supplies no proof of the unresolved C² clause.
- All comparator blocks in the existing audits were compared byte-for-byte against source and preserved. The three changed/new audit files have zero forbidden proof tokens under the repository's comment/string-aware scanner.
- `VectorPotentials.lean`, `SecondHalf.lean`, and the 10.43 blocker record were rechecked byte-identical after integration import.

The exact audit diffs against source are in `/tmp/ch10-audit-adaptations.diff`. No build was run by this reviewer, per parent instruction; fresh kernel verification remains the integration gate.

Parent-requested supplementary check: `IntegrationAudit.lean` also directly imports the merged Chapter09 stub aggregate and `Chapter09.SecondHalf`, then separately logs and runs a source-module-owned recursive audit of all merged Chapter09 production modules. Required anchors are `pma9_1_span_iff`, `pma9_22`, and `pma9_43`. This supplements the retained Chapter09 legacy namespace audits without modifying Chapter09 source, and is reported separately from the Chapter10 declaration/module totals.

## Final integration decisions beyond the source-lane inventories

The historical statement that prerequisites must be integrated separately is superseded by this live-tree integration. `Rudin.lean` directly imports all merged Chapter 9 audits because main's Chapter09 aggregate is a stub, and imports the Chapter 10 integration gate. Chapter08Audit and GammaAudit required audit-API repairs to current module ownership; their mathematical comparisons and coverage were retained. No merged Chapter 8/9 mathematical module was replaced.

The new integration prerequisite module contains 27 declarations: 23 recovered support bodies plus four adapters to the merged API. Independent fidelity review found no weakened conclusion or strengthened hypothesis. The nine adapted production modules change only imports or four scoped helper references. Source B's 147 Chapter 10 files include 135 byte-identical files and 12 disclosed adaptations (nine production modules, first-half aggregate commentary, two audits); two new support/audit files give 149 total. See `evidence/ch10-integration-manifest.json`, the independent integration reviews, and the final build/validation logs.
