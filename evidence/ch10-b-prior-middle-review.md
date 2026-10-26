# Prior Chapter 10 implementation: source review of 10.34–10.41

Reviewed branch: `origin/ch8-codex-20261022`, commit
`bb50a2079f8e189d8e282e2521bbadb64f4f98eb`.

This is a read-only review of existing proof source, compared with printed
Chapter 10 pp. 275–280 and the lane inventory. The prior production and source
reviews were read as historical evidence, not treated as proof authority. No
production code was written or replaced, and no proof was redone. A current
combined build and recursive axiom audit remain the integrating lane's checks.

## Principal declarations and substantive coverage

All names below are in `Rudin.PMA.Chapter10`; file paths are under
`rudin/Rudin/PMA/Chapter10/`. Lines identify the reviewed commit.

| Node | Principal and location | Source-fidelity finding |
| --- | --- | --- |
| 10.34 | `pma10_34`, `ClosedExact.lean:70` | `IsExactOn` requires an actual C¹ primitive; `IsClosedOn` requires a C¹ form with zero exterior derivative. Exact-to-closed separately assumes the resulting form is C¹. Its proof uses proved Stokes, literal boundary cancellation, and simplex separation, so it does not silently require a C² primitive. |
| 10.35 | `pma10_35`, `ClosedFormConsequences.lean:134` | Covers the coefficient cross-partial criterion, scalar-potential criterion, equality of exact-form integrals for functionally equal boundaries, vanishing on cycles, closed-form vanishing on boundaries, and literal plus functional boundary-squared zero. `exact_chainIntegral_eq_primitive_boundary` retains the explicit primitive formula. The earlier `scalarDifferential_closed_surface`/`pma10_19` supplies the closed C¹-curve specialization. |
| 10.36 | `pma10_36`, `PuncturedPlane.lean:137` | Uses the literal angular form on the punctured plane, all positive circle radii and the original interval. The integrand is proved equal to one and its native integral to 2π. The normalized C² simplex preserves every continuous-form integral; its endpoints cancel. Nonexactness and functional nonbounding follow from this actual nonzero period. |
| 10.37 | `pma10_37`, `PuncturedSphere.lean:147` | Uses the literal cyclic radial two-form; proves the norm-cubed denominator equals the source real-power denominator. The original spherical map and rectangle give the sine integrand and native 4π integral. An actual two-simplex chain preserves all continuous-form integrals, has zero functional boundary, and cannot bound in punctured space. |
| 10.38 | `pma10_38`, `ConvexPrimitives.lean:23` | Preserves arbitrary convex open domains, C¹ input/output, and all later-coordinate derivative conditions. `exists_prefix_retraction` constructs the needed global section; `exists_coordinate_primitive_of_retraction` constructs and differentiates the integral. No product-domain or fixed-fiber-basepoint assumption is added. `p : Fin n` correctly translates the source's one-based index. |
| 10.39 | `pma10_39`, `Poincare.lean:18` | Gives a global C¹ primitive from a closed C¹ form of every positive degree on a convex open set. `radial_primitive` constructs the coefficient integral and proves the derivative identity using the radial homotopy and FTC. The empty-domain case is handled separately; no nonempty or C² hypothesis is added. |
| 10.40 | `pma10_40`, `DiffeomorphicExactness.lean:21` | Preserves the fixed-degree exactness hypothesis in its first clause. `C2DomainEquivalence` has actual C² maps, two-sided inverse identities on the domains, and mapping-into proofs. Pullback commutation and composition construct the target primitive. The second clause derives the all-positive-degree convex corollary. |
| 10.41 | `pma10_41`, `CellTriangulation.lean:136` | Constructs finitely many affine staircase maps, proves their cell cover and determinants, preserves actual native integrals, realizes C² cell surfaces as genuine finite simplex chains, and proves the induced boundary and Stokes formulas. Supporting `staircaseChambers_interiors_disjoint` proves disjoint chamber interiors. This covers the mathematical cell-to-chain assertion in the numbered remark. |

No unproved substantive claim or narrowed hypothesis was found in these eight
numbered contracts and their inspected principal/supporting proof bodies. This
finding concerns these source obligations; it does not substitute for compiling
the reconciled checkout or auditing its full imported dependency closure.

## Representation choices and extensions to disclose

1. **10.34:** `IsExactOn E 0 ω` is defined to be `False`. This is an explicit
   convention outside Rudin's positive-degree exactness definition. The numbered
   source claim is stated only in positive degrees. The local definition's
   comment identifies positive-degree exactness; the prior review also explicitly
   records the zero-degree convention.
2. **10.36–10.37:** The original parameter intervals/rectangle are retained as
   surfaces and converted to normalized simplex chains by proved identities for
   every continuous test form. This is a representation bridge, not a restriction
   to a different curve/surface. The radial denominator's norm formulation has
   an explicit equality to the printed expression.
3. **10.39:** The proof uses radial homotopy instead of Rudin's coordinate
   induction. Its statement and regularity agree with the source. This is a
   proof-method change, not a changed theorem.
4. **10.40:** The formal contract permits distinct ambient dimensions and every
   positive degree; Rudin states the theorem in one ambient dimension and with
   degree bounded by that dimension. The printed theorem is included as a
   specialization. This is a generalization, not an extra hypothesis.
5. **10.41:** The cell representation additionally permits zero dimensions and
   collapsed sides. The proofs handle both explicitly. The usual nondegenerate
   source cells are included; this is additional scope.

The prior branch's remaining 10.43 C² vector-potential issue is outside this
eight-node review. Nothing in 10.39 promises a C² primitive for a general
closed C¹ two-form: its proved C¹ primitive must not be relabeled to close that
separate regularity obligation.

## Reconciliation evidence

The principal module bytes match the final hashes recorded by the prior source
review; this was independently recalculated from `git show`:

| Module | SHA-256 |
| --- | --- |
| ClosedExact | `f9f36417c5158ea2636bda0ecd77ce9620b8592e3925f28a9e98c724128fd24e` |
| ClosedFormConsequences | `b5638a9cb819df81d6a2b9e57e64def1650ccf4fe5481e869bbb83521333a493` |
| PuncturedPlane | `b418425dd45d4e372b64bf86d38445c624db9c01efae5720168c9ba6d87d0de3` |
| PuncturedSphere | `acfa4deceaa9f13b4d9fffd0b937bc0a6a8e7061c4cbfe07103238a0491ce128` |
| ConvexPrimitives | `4bf04a34e5ff6c8b9e2a4ba2d04923ba94d9e47e9fe70110b68699b691c81432` |
| Poincare | `26acef677a2bf51e404c7802b3d521fba76cbcd8f5c332def5fa878c95a9ee71` |
| DiffeomorphicExactness | `c5d66c04f33476cb3d375f50d0e1debc4c83c6f2447f92294acda9e76a0710b1` |
| CellTriangulation | `05b470cda814f680aa38ffd4d29cae1051fde51233d0cf84f93f811e67230b81` |

A token scan of these eight modules plus `PuncturedExamples`, `RadialPrimitive`,
`ExactnessTransport`, and `ConvexPrimitiveIntegral` found no `sorry`, `admit`, or
`axiom` token. This is a source scan, not the required kernel axiom audit. No
build was run by this reviewer, to avoid overlapping the integrating lane's
serialized build.
