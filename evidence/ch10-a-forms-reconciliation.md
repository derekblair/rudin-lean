# Chapter 10 forms reconciliation review

Source branch reviewed: `origin/ch8-codex-20261022` (`bb50a20`).
Book: `/root/sources/pma3.pdf`, PDF pages 263–275, printed pages 254–266.
The entirety of numbered nodes 10.10–10.25 was read from the PDF text. Printed
page 257 was also rendered and visually checked because the two reordering
examples and the two-form coefficients are poorly recognized by OCR.

## Acceptance and evidence

The reused implementation is substantive. It does not replace the integral
meaning of equality with an unproved tensor equality and does not assume the
conclusions of 10.15, 10.20, or 10.22–10.25.

| Nodes | Review finding |
|---|---|
| 10.10 | `SurfaceDomains.pma10_10` establishes compactness of both admissible parameter domains, the open-neighborhood C¹ extension convention, construction from such data, and both conversions between one-surfaces and regular curves. Maps are not assumed injective or immersive. |
| 10.11 | `surfaceIntegral_fromCoefficients` is exactly the sum of selected Jacobian minors in (35); `pma10_11` proves continuity and native iterated-Riemann integrability, coefficient regularity, and the zero-form/function correspondence. |
| 10.12(a) | `xyDifferential_endpoint` is the actual surface integral over the unit interval and proves the stated endpoint formula. The contract includes the closed-curve consequence. |
| 10.12(b) | `ellipseSurface`, `ellipse_integrands`, and `ellipse_integrals` establish the displayed ellipse parameterization, closed endpoints, both trigonometric integrands, and both actual integral values ±πab. |
| 10.12(c) | `SphereExamples` proves the full derivative, Jacobian r² sin θ, native integral 4π/3, image equal to the closed unit ball, and injectivity on the parameter cell's interior. |
| 10.13 | Integral linearity is proved using native-integral/measure-integral equivalence; transpositions and repeated indices are proved algebraically and transferred to actual surface integrals; high-degree vanishing is proved. |
| 10.14 | Increasing indices are cardinality-k finite subsets with their canonical increasing enumeration. Basis count, permutation sign, standard expansion, regularity, both printed reordering examples, and the printed nonstandard two-form example match. |
| 10.15 | `FormEqOn` universally quantifies actual admissible surfaces. `exists_nonzero_axis_cell` constructs a positive-width cell inside an open preimage neighborhood on which a nonzero continuous coefficient has nonzero native integral. `axisSurface_integral_coefficient` extracts exactly the chosen standard coefficient. Their contradiction proves coefficient vanishing and `formEqOn_iff_eqOn`. No separation hypothesis is assumed. |
| 10.16 | Concatenation, zero for shared indices, the exact cross-inversion exponent, and associativity are proved. |
| 10.17 | Wedge degree/continuity, the double standard expansion (57), both distributive laws, associativity, scalar products, and graded commutativity are proved. |
| 10.18 | Exterior differentiation is defined with coefficient differentials on the left. The degree, continuity, standard formula (60), zero-form formula, and derivative evaluation are proved. |
| 10.19 | Actual native curve integrals of df equal endpoint differences. Equal-endpoint and closed-curve consequences are proved. `xdy_not_exact` uses the positive unit-circle integral to refute a global C¹ potential. |
| 10.20 | The Leibniz sign is (-1)^k. The d² proof uses proved C² mixed-partial symmetry and alternating cancellation, and establishes the necessary C¹ regularity of dω. |
| 10.21 | Pullback is induced by the actual Fréchet derivative, with no injectivity or rank assumption. The coefficient substitution formula, regularity, and scalar-function substitution are proved. |
| 10.22 | Additivity and products are algebra-map consequences. Commutation with differentiation requires exactly a C² map and C¹ form, and is proved by chain/product rules and closed products of exact differentials. |
| 10.23 | The composition law uses the actual chain rule at points in the open source; the map ordering matches the book. |
| 10.24–10.25 | Identity/composed parameter surfaces are explicitly built. Pullback evaluation proves equality of the actual integrands, then continuity and native integrability give the displayed equalities of surface integrals. The ambient extension is correctly restricted to the preimage of the target before composition. |

## Representation choices and generalizations to disclose

* Coordinate indices are zero-based (`Fin n`), rather than 1 through n.
* Form fields are total exterior-algebra-valued representatives with regularity
  restricted to E. The book's operational equality is the separate relation
  `FormEqOn`. `pma10_15` and `formEqOn_iff_eqOn` prove the bridge on open sets;
  tensor equality is not silently substituted for the definition.
* Standard indices are finite subsets of cardinality k, identified with increasing
  tuples by `Set.powersetCard.ofFinEmbEquiv`. The count is `n.choose k` rather than
  factorial division, including sensible values when k exceeds n.
* Parameter coordinates use finite products with the sup norm, while ambient
  spaces use Euclidean norm. `coordEquivEuclidean` explicitly bridges these models.
  This is a representation choice, not a change in integration domain or topology.
* Surfaces store a chosen extension and neighborhood. The derivatives used by
  the integral are those of this actual extension; no global target condition is
  imposed outside the compact domain.
* Several elementary algebraic statements hold without openness, continuity, or
  positive-degree hypotheses. The numbered analytic contracts retain the book's
  open-domain and C¹/C² hypotheses wherever needed. Degrees and dimensions zero
  are additionally supported; the zero-form/function correspondence is proved.
* The exact-form integral theorem is generalized from [0,1] to every permitted
  one-dimensional cell/simplex, with its endpoints explicitly supplied.
* Ellipse integral helper theorems hold for arbitrary real semiaxes, but the
  numbered example retains the printed positivity hypotheses.
* Derivative and pullback equalities are stated as `EqOn` E for representatives,
  rather than global equality outside E. The established separation theorem
  connects this to equality of integration functionals on E.

## Gaps identified in the earlier source and repair status

The old `FormExamples` comment explicitly deferred the geometric interpretations
in 10.12(b,c) to 10.44–10.45. Thus its numerical integral calculations alone did
not formally establish that the ellipse integral equals the bounded region's
area, or that the spherical integral equals image volume. These omissions are now repaired in the new independent
`FormExampleGeometry.lean` supplement. Its actual-source compile in the isolated
pinned environment returned exit 0 without diagnostics:

```
cd .lane-validation/rudin
lake env lean Rudin/PMA/Chapter10/FormExampleGeometry.lean
```

The supplement proves:

* `ellipseRegion_eq_inequality`: the diagonal image of the closed unit disk is
  exactly the region with normalized squared coordinates summing to at most one.
* `ellipseMap_image_eq_frontier`: the actual ellipse curve covers exactly that
  region's frontier (the unit-circle coverage and invertible scaling are proved).
* `ellipseRegion_isCompact`, `ellipseRegion_volume`, and
  `ellipseRegion_volume_ne_top`: this is a compact region of finite area πab.
* `ellipse_integral_eq_area`: the original native form integral equals that area.
* `spherical_integral_eq_image_volume`: the original native form integral equals
  Lebesgue volume of its actual image, the closed unit ball.
* `sphericalMap_identifies_boundary_points`: two explicit distinct frontier
  points of the spherical parameter cell have the same image.
* `pma10_12_geometry`: the supplementary numbered-example contract bundling these
  geometric conclusions.

The added representation choice is explicit in the module comment: geometric
area/volume is Lebesgue measure, converted to a real by `ENNReal.toReal`. The
ellipse region includes its boundary. No injectivity of the spherical map on its
entire parameter cell is asserted or assumed.

The alternate calculation printed in 10.19, d(x dy)=dx∧dy≠0, was not stated in
the earlier source. Nonexistence of a potential was already proved by the other
printed argument. The root assigned this small supplementary calculation to
another agent; this review does not claim its completion.

## Files reviewed in full

`FormsCore`, `FormsAlgebra`, `Surfaces`, `SurfaceDomains`, `FormRegularity`,
`ScalarForms`, `FormDefinitions`, `FormOperations`, `FormExamples`,
`SphereExamples`, `StandardForms`, `NativeSeparation`, `FormSeparation`,
`WedgeProducts`, `CoordinateDifferentiation`, `ExteriorDerivative`,
`ExteriorDerivativeRules`, `ExactOneForms`, `Pullbacks`, `PullbackAlgebra`,
`PullbackRegularity`, `PullbackDefinitions`, `PullbackDifferentiation`,
`PullbackEvaluation`, `SurfaceMaps`, and `SurfacePullbacks`.

This is a statement/proof-structure fidelity review. The new supplement has
compiled cleanly against the reused `SphereExamples.olean` and its real imported
prerequisites. The root owns the complete target `lake build` result and exhaustive
namespace axiom audit, including this supplement. This review does not substitute
its local compile for those complete-target checks.

No further omitted conclusions were found in the reviewed 10.10–10.25 contracts
and worked examples after the geometry repair, apart from the explicitly noted
alternate derivative calculation in 10.19 assigned to the other agent. Chosen
C¹ extensions are stored as representatives; the implementation does not claim
literal equality of records for two extensions of the same compact-domain map.

A local audit already launched before the root's consolidated-audit instruction
also completed successfully: all 16 newly declared definitions/theorems depend
only on `propext`, `Classical.choice`, and `Quot.sound`. Exact output is in
`evidence/ch10-a-form-geometry-axioms.log`. This is supplementary to the root's
required exhaustive namespace audit.

## Independent review of the other authors' supplements

Reviewed `AffineOrientation.lean`, `PartitionComplements.lean`, and
`ExactOneFormComplements.lean` in full against printed 10.26 (page 267), 10.8
(page 251), and 10.19 (page 261). The existing affine and partition contracts
were also checked to establish what the supplements actually add. Definition
7.14 was consulted to verify the meaning of the book's C(X) notation.

* **10.26 relative orientation — accepted.** The relation is explicitly witnessed
  by a vertex permutation of the specified sign. This is the book's convention,
  not a theorem disguised as a premise. Agreement with `tupleSign` is proved,
  and the nontrivial parameterization identity is proved through affine
  uniqueness at the vertices. No affine-independence assumption is added.
  Repeated vertices are retained, and the constant one-simplex example correctly
  demonstrates why sign uniqueness cannot be asserted in that case. The
  integral sign law remains 10.27, outside this lane; the supplement does not
  claim or assume it. Signed zero-simplices remain in the earlier `pma10_26`
  contract, rather than being incorrectly encoded by permutations of one vertex.
* **10.8 complex corollary — accepted.** A single partition is constructed first,
  independently of f. The identity is proved pointwise on K using the partition
  sum and outside K using actual support vanishing. Continuity and support
  containment of every complex summand are proved. This removes the earlier
  restriction to real-valued f. The book's C(X) means bounded continuous complex
  functions; Lean's `ContinuousMap` omits a bundled boundedness certificate, but
  the retained compact-support hypothesis implies boundedness. The partition
  functions themselves have the explicit global bounds zero and one. This is a
  harmless change of representation/generalization, not an extra hypothesis.
* **10.19 displayed derivative — accepted.** The coordinate derivative is computed
  from the actual Fréchet derivative of a coordinate projection and the proved
  finite-basis differentiation rule. Nonvanishing of dx∧dy is proved by evaluation
  on the standard tangent basis, where the determinant is one. Neither the
  derivative identity nor nonvanishing is assumed. The final nonzero expression
  is stated in the exterior-algebra representative; its operational form meaning
  is justified by the already reviewed 10.15 separation bridge for this constant
  two-form. The earlier unit-circle argument separately proves nonexactness for
  C¹ potentials, so no C² restriction has been introduced into that conclusion.

No new narrowed mathematical statements or circular proofs were found in these
three supplements. This additional review is independent of their authors and
of the root's compile/axiom checks. It closes the previously noted source-level
10.19 displayed-calculation omission, subject to its compilation succeeding.
