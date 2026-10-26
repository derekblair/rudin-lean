import Rudin.PMA.Chapter10.Simplex
import Rudin.PMA.Chapter10.Primitive
import Rudin.PMA.Chapter10.Partition
import Rudin.PMA.Chapter10.PartitionComplements
import Rudin.PMA.Chapter10.ChangeOfVariables
import Rudin.PMA.Chapter10.SphereExamples
import Rudin.PMA.Chapter10.FormExampleGeometry
import Rudin.PMA.Chapter10.FormSeparation
import Rudin.PMA.Chapter10.WedgeProducts
import Rudin.PMA.Chapter10.ExactOneForms
import Rudin.PMA.Chapter10.ExactOneFormComplements
import Rudin.PMA.Chapter10.ExteriorDerivativeRules
import Rudin.PMA.Chapter10.PullbackDefinitions
import Rudin.PMA.Chapter10.PullbackDifferentiation
import Rudin.PMA.Chapter10.SurfacePullbacks
import Rudin.PMA.Chapter10.AffineSimplices
import Rudin.PMA.Chapter10.AffineOrientation

/-!
# PMA Chapter 10, first half: 10.1–10.26

Reconciled with `ch8-codex-20261022` at
`bb50a2079f8e189d8e282e2521bbadb64f4f98eb`. The recovered proofs are retained with the import/name adaptations recorded
in the integration inventory, with separate supplementary modules for attached
claims. The integration uses merged Chapter 8–9 through the scoped prerequisite
compatibility module; all retained proofs build in the live tree. The default
`Rudin` target also imports `Chapter10.IntegrationAudit`, which includes the
second half and all probe modules.
The second-half lane starts at 10.27 and may import this module.

## Representation conventions and source generalizations

Coordinate indices start at zero. Compact-domain C¹ regularity is represented
by an extension on an open neighborhood, as the book stipulates. The native
Chapter 6 Riemann integral is used recursively, and agreement with the measure
integral is proved. Forms use homogeneous exterior-algebra representatives;
the coefficient formula and equality detected by actual surface integrals are
proved. These are equivalent representations, not additional hypotheses.
-/

/-! ### PMA-10.1
`pma10_1`: every slice exists, intermediate functions are continuous, and the
native iterated integral agrees with the set integral. Generalization: dimension
zero is included, with its integral equal to evaluation at the unique point.
-/

/-! ### PMA-10.2
`pma10_2`: existence and equality in every integration order, also in dimension zero.
-/

/-! ### PMA-10.3
`pma10_3`: closed support and enclosing-cell independence for real and complex functions.
-/

/-! ### PMA-10.4
`pma10_4`: simplex zero-extension Riemann integrability, slice continuity, and order independence.
-/

/-! ### PMA-10.5
`pma10_5`: primitive coordinate replacement, derivative matrix, determinant, and invertibility.
Generalization: the auxiliary `IsPrimitiveOn` predicate is defined on arbitrary
sets; it specializes to the book's definition on open sets, and 10.7 explicitly
requires an open domain.
-/

/-! ### PMA-10.6
`pma10_6`: flips and coordinate projections, including their ranges and kernels.
-/

/-! ### PMA-10.7
`pma10_7`: local factorization into exactly n primitive maps and n−1 flips or identities.
The positive-dimension premise makes explicit the source's implicit requirement
that a primitive coordinate can be selected.
-/

/-! ### PMA-10.8
`pma10_8`: a finite continuous subordinate partition and the supported-function corollary.
`pma10_8_complex_corollary` supplies the complex-valued case omitted from the
recovered corollary, keeping the partition real-valued.
The continuous-map type does not bundle boundedness; compact support implies
boundedness for every function occurring in this corollary.
-/

/-! ### PMA-10.9
`pma10_9`: native change of variables, inverse continuity, and compact support of
the continuous zero-extended transformed integrand.
-/

/-! ### PMA-10.10
`pma10_10`: surfaces and their C¹-curve correspondence. Generalization: zero-dimensional
surfaces are admitted; arbitrary ambient sets can be used internally, while the
printed open-set hypotheses are retained in the numbered contract.
-/

/-! ### PMA-10.11
`pma10_11`: ordered coefficient/minor formula, native integrability, regularity, and
scalar zero-forms. Generalization: the regularity bridge is supplied for every
natural-number order, including the printed C¹ and C² cases.
-/

/-! ### PMA-10.12
`pma10_12`: all three examples, including the spherical image and interior injectivity.
`pma10_12_geometry` adds the ellipse's enclosed-area interpretation, the spherical
image-volume interpretation, and explicit boundary identifications. Area and volume
use Lebesgue measure, with finite measure established for the relevant regions.
-/

/-! ### PMA-10.13
`pma10_13`: functional equality, linearity, index signs, repetitions, and excessive degree.
The algebraic index identities hold even without continuity; the integral identities
retain the hypotheses that establish their integrability.
-/

/-! ### PMA-10.14
`pma10_14`: basic-form count, signed sorting, standard presentation, and displayed examples.
-/

/-! ### PMA-10.15
`pma10_15`: uniqueness is deduced from vanishing of all actual surface integrals.
-/

/-! ### PMA-10.16
`pma10_16`: basic wedge multiplication, overlap vanishing, inversion signs, and associativity.
-/

/-! ### PMA-10.17
`pma10_17`: general wedge multiplication and its algebraic laws, including scalar forms.
-/

/-! ### PMA-10.18
`pma10_18`: the coordinate exterior derivative and its regularity.
-/

/-! ### PMA-10.19
`pma10_19`: the exact-form endpoint formula and nonexactness of x dy.
`pma10_19_xdy_derivative` also proves the printed calculation d(x dy) = dx ∧ dy ≠ 0.
`pma10_19_dxdy_not_formEqOn_zero` explicitly gives nonvanishing in the book's
surface-integral meaning of equality, using the proved 10.15 separation theorem.
Generalization: the endpoint formula holds on any ordered compact parameter
interval, encompassing the book's unit interval.
-/

/-! ### PMA-10.20
`pma10_20`: the C¹ graded Leibniz rule and vanishing second derivative for C² forms.
-/

/-! ### PMA-10.21
`pma10_21`: pullback, its coefficient formula, and regularity.
-/

/-! ### PMA-10.22
`pma10_22`: pullback preserves addition and multiplication and commutes with exterior
differentiation for a C² map and C¹ form.
-/

/-! ### PMA-10.23
`pma10_23`: the contravariant pullback composition law.
-/

/-! ### PMA-10.24
`pma10_24`: native integration after pullback to the identity parameter surface.
-/

/-! ### PMA-10.25
`pma10_25`: native integration over a composed surface, without injectivity or rank assumptions.
-/

/-! ### PMA-10.26
`pma10_26`: affine simplexes, full-dimensional orientation, and signed zero-simplex evaluation.
`pma10_26_relativeOrientation` supplies the omitted relative-orientation paragraph
using vertex permutations, with the book's tuple-sign convention and affine
reparametrization. Relative orientation is a relation, including for degenerate
vertex families; no uniqueness of its sign is asserted in that case.
The general affine characterization is stated for real modules, which includes
the printed Euclidean spaces.
-/
