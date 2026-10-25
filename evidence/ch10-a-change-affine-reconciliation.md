# Chapter 10.9 and 10.26: reconciliation and source fidelity

Reviewed the complete brief, the printed statements in `/root/sources/pma3.pdf`,
and the earlier implementation on `origin/ch8-codex-20261022` (head
`bb50a2079f8e189d8e282e2521bbadb64f4f98eb`).
The lane now reuses that implementation. The independent change-of-variables
draft is superseded and is not part of the chapter imports.

## Source scope

- **10.9:** printed pp.252–253, PDF pp.261–262.
- **10.26:** printed pp.266–267, PDF pp.275–276; its final paragraph precedes 10.27.
- The complete chapter contains **51 numbered nodes (10.1–10.51)**. Lane A's
  first half is **10.1–10.26**, with lane B starting at 10.27.

## 10.9: reused implementation passes statement review

`ChangeOfVariables.lean` proves `pma10_9_contract` in `pma10_9`.
The main quantified clause retains the printed hypotheses: open source,
injectivity on that source, continuously differentiable mapping there,
nonzero Jacobian there, continuous real integrand, compact closed support,
and support contained in the image. There is no global injectivity,
global smoothness, or smooth inverse assumption.

The Chapter 9 predicate `C1On` means differentiability at every source point
and continuity of the derivative on the source. It is the printed notion on
an open set. The coordinate model is explicitly transported to the Euclidean
model; `coordinateJacobian_eq_matrix` and `jacobian_euclideanTransform` prove
agreement with the matrix and Chapter 9 Jacobians.

The potentially delicate claims are proved, not assumed:

- `coordinate_open_image` applies the inverse function theorem locally.
- `coordinate_partialHomeomorph` constructs the inverse on the image.
- `zeroExtendedPullback_support` transports the compact closed support by
  that inverse and proves that the transformed closed support stays inside
  the source. It does not infer compactness from an arbitrary global inverse
  image.
- `zeroExtendedPullback_continuous` proves continuity of the explicit zero
  extension. Values of the total Lean function outside the open source do
  not influence the transformed integrand.
- `native_changeOfVariables` invokes Mathlib's change-of-variables theorem
  only after rewriting **native iterated Riemann integrals** using the proved
  `wholeRIntegral_eq_integral` bridge in `IntegrationMeasure.lean`.
- The contract also proves `IteratedRIntegrable` for both integrands, including
  all recursive slice-integrability obligations.

**Deviation assessment:** none found in 10.9. The explicit zero extension and
the coordinate-to-Euclidean equivalence make representation choices explicit;
the statement is not silently replaced by a bare Bochner-integral identity.
Using the general Mathlib theorem instead of Rudin's primitive-map/partition
proof changes the proof route, not the assumptions or conclusion.
The formal contract additionally permits dimension zero; this harmless extension
does not remove any of the positive-dimensional printed cases.

## 10.26: reused implementation plus a missing paragraph supplied

`AffineSimplices.lean` proves the following parts of the printed node:

- The characterization of affine maps by a constant plus a linear map.
- Determination by the value at zero and standard basis vectors.
- The affine parametrization for arbitrary ordered vertices, including
  repeated or affinely dependent vertices, as an actual simplex surface.
- The vertex values, linear part, smoothness, and derivative.
- The full-dimensional Jacobian as the determinant of the edge columns.
- Nonzero determinant and invertibility under the printed linear-independence
  assumption, together with positive/negative orientation.
- Positive orientation of the standard simplex.
- Signed zero-simplex integration as signed evaluation of a 0-form.

The old `pma10_26_contract` did **not** encode the relative-orientation
paragraph on printed p.267: reordering all vertices by a permutation of sign
plus or minus one, with the resulting notation interpreted relationally rather
than as equality of parametrizations. The old `SimplexOrientation.lean` concerns
10.27 and contains the later integral identity; importing that entire module
would cross the agreed lane boundary.

The new first-half module `AffineOrientation.lean` supplies this omission:

- `HasAffineRelativeOrientation`, `SameAffineOrientation`, and
  `OppositeAffineOrientation` encode the vertex-permutation relations.
- Reflexivity, symmetry, composition of signs, and the two possible signs
  are proved.
- `constantAffineSimplex_both_orientations` demonstrates explicitly why
  repeated vertices prevent any assertion of a unique relative sign.
- `affineSimplexMap_relative_reparametrization` proves the actual composition
  relationship between the two parametrizations.
- `affinePermutationSign_tupleSign` connects permutation parity to Rudin's
  tuple sign from 9.33.
- `pma10_26_relativeOrientation` proves the supplementary contract.

Names are distinct from the later `SimplexOrientation.lean`, preserving lane B
compatibility. The relation permits degenerate vertex families and does not
assert uniqueness of the orientation sign in that case. No equality of affine
maps is inferred from equality of orientation. The integration identity remains
10.27's responsibility, as in the printed order.

**Deviation assessment:** no strengthening or narrowing introduced. The
relative-orientation supplement repairs an omitted source definition; it does
not replace the inherited 10.26 theorem.

## Validation and dependencies

The reused modules depend on the earlier Chapter 6/8/9 foundation and Chapter 10
integration/forms modules. The lane's base does not contain all these foundation
files. The parent maintains the isolated `.lane-validation/rudin` project using
the exact earlier foundation and the lane's Chapter 10 files, with the pinned
Lean 4.34.1 toolchain and Mathlib.

After the prerequisite objects became available, the command
`lake env lean Rudin/PMA/Chapter10/AffineOrientation.lean`, run in
`.lane-validation/rudin`, completed with **exit 0 and no diagnostics**.
The parent records the final aggregate build and namespace-wide axiom audit.
All proofs in the supplement are explicit, with no admitted goals or new axioms.
A direct `#print axioms` audit of all ten supplementary theorems also completed
with exit 0; each reported exactly `propext`, `Classical.choice`, and `Quot.sound`.

## Independent review of the 10.12 geometry supplement

Reviewed the full `FormExampleGeometry.lean` against printed pp.254–255 and
checked its use of `FormExamples.lean` and `SphereExamples.lean`.
**Accepted: no missing geometric assertion or strengthened hypothesis found.**

- For positive semiaxes, the ellipse region is the image of the closed unit
  disk under the explicitly defined diagonal scaling. Its normalized-coordinate
  inequality is proved in both directions.
- The determinant of that actual scaling is proved to be the product of the
  semiaxes. The measure calculation uses that determinant and the standard disk
  measure, yielding finite area. The native integral of `x dy` is equated to
  that area's real value.
- The parametrized ellipse image is proved to be exactly the region's frontier:
  the unit-circle coverage is proved using polar coordinates, and an invertible
  diagonal homeomorphism transports the frontier. Thus “enclosed region” is not
  merely a label attached to an unrelated set.
- The spherical integral is identified with the measure of the **actual image**
  of the parametrization. The inherited `sphericalMap_image` proves that this
  image is the closed unit ball; the ball-volume formula also establishes that
  its measure is finite, so conversion by `ENNReal.toReal` does not hide infinity.
- Distinct boundary points with the same image are constructed explicitly on
  the radius-zero face. The inherited `pma10_12` separately proves injectivity
  on the parameter interior, the Jacobian, and native iterated integrability.

Representation note: area and volume in the supplement use Lebesgue measure
converted to real numbers, as its module comment states. The differential-form
integrals remain the native iterated Riemann integrals from the inherited chapter.
The supplement proves equality between these quantities, rather than replacing
the native integral or assuming the desired geometric identification.
