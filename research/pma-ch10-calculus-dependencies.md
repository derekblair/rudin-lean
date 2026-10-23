# Chapter 10 calculus dependency map

This note records the pinned local API and implementation plan. It is not a
compilation or final fidelity claim. Source statements are fixed independently
in the Chapter 10 inventory; the author also visually inspected printed
pp.245–248 and 252–253 (PDF pages 254–257 and 261–262) of the authorized local
third-edition PDF. No source transcription is retained here.

## Native integration interface (10.1–10.4)

`Chapter10/Integration.lean` uses `Coord n := Fin n → ℝ`. A `Cell n` stores two
coordinate endpoints and their pointwise weak ordering, so singleton side
intervals and dimension zero remain available. `nativeSliceIntegral` integrates
the last coordinate with Chapter 6's `RIntegral`. `iteratedRIntegral` repeats
that operation; `IteratedRIntegrable` separately records existence of every
slice integral. The base in dimension zero is evaluation at the unique point.

The public contracts retain continuity of the intermediate functions, arbitrary
coordinate order, compact-support independence of the containing cell, and the
simplex zero-extension argument. `wholeRIntegral` is defined through a chosen
containing cell; its relation to the whole-space measure integral is a theorem.
`simplexRIntegral` is the native unit-cell integral of the zero extension from
`standardSimplex`. Euclidean ambient functions enter through `WithLp.toLp 2`.
This gives later surface integration the same native parameter integral.

Pinned APIs supporting these bridges:

- `Chapter09.orientedRIntegral_eq_intervalIntegral` connects native one-variable
  integration to the measure interval integral for globally continuous real
  functions. The new module must extend the bridge to functions continuous only
  on the closed interval, using a continuous extension and native integral
  congruence, and treat the singleton interval explicitly.
- `Chapter09.rsIntegral_tendsto_of_uniformFilterLimit` gives native integral
  continuity from uniform convergence of the parameter slices, with arbitrary
  nontrivial filters.
- `UniformContinuousOn.tendstoUniformlyOn`, together with compactness of a closed
  cell, supplies the required uniform convergence of continuous slices.
- `MeasureTheory.measurePreserving_piFinSuccAbove` splits a finite coordinate
  product at any index. With `integral_prod`/`integral_prod_symm`, this supports
  the induction from the recursive native integral to the cell measure integral.
- `MeasureTheory.measurePreserving_piCongrLeft` and
  `volume_measurePreserving_piCongrLeft` give invariance under coordinate
  permutations. Existence of all source slice integrals must still be proved;
  a measure-integral equality alone does not assert it.
- `ContinuousOn.integrableOn_compact` supplies finite-dimensional measure
  integrability. `ContinuousMap.exists_restrict_eq` (Tietze extension) is
  available for continuous real functions on closed subsets when needed.

The simplex zero extension is discontinuous at its boundary. Its first native
slice integrals need an actual one-dimensional integrability argument and a
continuity estimate in the remaining coordinates. This is genuine local proof
work; it is not covered merely by Fubini's almost-everywhere slice existence.
Once those slices are continuous, the ordinary-cell recursion applies.

## Change of variables (10.9)

The source has an open domain, an injective `C¹` transformation, nonzero
Jacobian everywhere on that domain, and a continuous compactly supported real
function whose support is contained in the image. The transformed integrand is
zero outside the original domain. Its global continuity, compact support
contained in that domain, and native integrability are part of the intended
bridge; arbitrary values of a globally extended transformation outside its
domain must not enter the integral.

The pinned `Mathlib/MeasureTheory/Function/Jacobian.lean` supplies:

- `integrableOn_image_iff_integrableOn_abs_det_fderiv_smul`: for a measurable
  set `s`, a derivative within `s` at every point, and `InjOn f s`, integrability
  on `f '' s` is equivalent to integrability of the absolute-determinant weighted
  pullback on `s`.
- `integral_image_eq_integral_abs_det_fderiv_smul`: under the same derivative
  and injectivity hypotheses, the corresponding Bochner integrals agree.
- `integral_target_eq_integral_abs_det_fderiv_smul`: the open-partial-homeomorphism
  formulation of the same identity.

These apply to the chosen additive Haar measure in a finite-dimensional real
space. Their hypotheses are weaker than the source change-of-variables theorem;
using them does not remove the source's additional conclusions about continuous
compact support. The source determinant must be explicitly identified with the
continuous linear map determinant, using the Chapter 9 matrix bridge. Absolute
value is required: no orientation convention belongs to this function integral.

Proposed module split: `Integration.lean` for 10.1–10.4 and reusable native
bridges, then `ChangeOfVariables.lean` for 10.9. Nodes 10.5–10.7 and 10.8 are
owned by the algebra and parent lanes respectively. This avoids dependency
cycles with later differential-form integration.

## Differential forms, chains, and Stokes landscape

The pinned `Mathlib/Analysis/Calculus/DifferentialForm/Basic.lean` represents an
n-form field by `E → E [⋀^Fin n]→L[ℝ] ℝ` and supplies `extDeriv`, its explicit
signed omission formula, linearity, `extDeriv_extDeriv_apply`, and
`extDeriv_pullback`. The pullback theorem assumes two derivatives of the map
and differentiability of the form, matching the regularity that must be tracked
when transporting the source's compact-domain extension convention.

These are useful algebra/calculus components, not an existing complete source
integration package. Searches found no generic integral of differential forms
over parameterized simplices or chains, nor a generic simplex-chain Stokes
theorem. The source's all-tuple coefficients and equality by every admissible
surface integral need explicit bridges to any alternating-field representation.
In particular pointwise tensor equality cannot silently replace the source's
functional equality without a separation theorem.

`Mathlib/Analysis/BoxIntegral/DivergenceTheorem.lean` proves
`BoxIntegral.hasIntegral_GP_pderiv` and the corresponding box divergence theorem
for a generalized Henstock–Kurzweil integral, with signed opposite-face terms.
`ContinuousOn.hasBoxIntegral` in `BoxIntegral/Integrability.lean` connects
continuous box integrals to measure integrals for all integration parameters.
This is a possible auxiliary route for rectangular Stokes calculations, but it
is not directly the native iterated simplex theorem and does not supply the
source boundary-chain bookkeeping. Boundary cancellation, orientation signs,
standard-simplex integration, and the exact form integration functional remain
genuine chapter-specific work.

All API names above were read from the current local pinned Mathlib sources;
no floating online documentation, package installation, build, or git mutation
was used by this research lane. Root owns serialized compiler and axiom gates.

## Implemented proof architecture (compiler gates pending)

`Integration.lean` contains the accepted source contracts and shared definitions.
`IntegrationProofs.lean` proves native rectangular slice continuity and existence
from the native Chapter 6 and Chapter 9 uniform-limit theorem.
`IntegrationMeasure.lean` proves the native-to-measure bridge by finite-coordinate
product disintegration, then coordinate-order and containing-cell independence,
including the complex component extension.

`SimplexSlices.lean` proves endpoint-value invariance using the native indefinite
integral theorem 6.20 and the one-variable mean value theorem. A stopped continuous
slice is then natively integrable by the interval split and endpoint lemmas, even
when its allowed interval collapses. Tietze extension gives a continuous ambient
function whose fiber primitive has the explicit upper endpoint
`max 0 (1 - sum x_i)`. The pinned
`intervalIntegral.continuous_parametric_primitive_of_continuous` proves continuity
of that first integrated function. Thus every fiber and all remaining native
integrations exist before `Simplex.lean` applies the measure bridge and permutation
invariance. This proof uses no almost-everywhere substitute for source slice
existence. The independent source reviewer accepted the full proof drafts.

The algebra lane now owns `ChangeOfVariables.lean` for 10.9 and uses the native
whole-space bridge with an explicit zero extension and compact pullback support.
All compiler execution remains serialized by the root agent; this note is not a
claim that pending module builds or final axiom audits have passed.

## Opening integration gate

Root's serialized compiler has now passed `Integration`, `IntegrationProofs`,
`IntegrationMeasure`, `SimplexSlices`, and `Simplex`, including the exact
numbered10.1–10.4 contracts. The independent reviewer also accepted the actual
all-fiber simplex proof. These modules are frozen for the opening section audit.

Additional source10.15 work is in `NativeSeparation.lean` and
`FormSeparation.lean`: positive-volume native boxes detect a nonzero continuous
coefficient, coordinate-plane derivatives yield the determinant pairing with
the standard exterior basis, and the resulting actual surface integral
contradicts functional vanishing. Both `NativeSeparation` and `FormSeparation` have passed their compiler gates; the full functional separation proof retains independent semantic acceptance.


## Exterior differentiation and pullback drafts

The source18–20 contracts are in `ExteriorDerivative.lean`. Its derivative is
an explicit finite sum of coefficient partial derivatives with `dx_i` multiplied
on the left. `CoordinateDifferentiation.lean` has compiled and supplies ordinary
partial product rules and C² mixed-partial symmetry. `ExactOneForms.lean` proves
the native curve FTC, including actual native integrability and path/closed-curve
conclusions; the ellipse computation rules out a C¹ primitive for `x dy`.
`ExteriorDerivativeRules.lean` proves graded Leibniz and `d² = 0` by finite
coefficient sums and antisymmetric cancellation. These full proof drafts have
independent semantic acceptance; remaining compiler gates are owned by root.

`PullbackRegularity.lean` supplies coefficientwise closure under sums, scalar
multiplication, and wedge products. The exterior-algebra pullback of each basis
wedge is explicitly a product of coordinate differentials. This yields C^r
pullback regularity from C^(r+1) regularity of the map and C^r regularity of the
form, including the continuous case required in21.

`PullbackDifferentiation.lean` proves the scalar chain rule in the same native
exterior model. C² coordinate functions give closed products of their exact
differentials. Applying the finite-sum and variable-scalar product rules to the
standard coefficient expansion then proves22: `d(T*ω) = T*(dω)` with only C¹
regularity of `ω`. This avoids adding a second derivative hypothesis on the
source form. Both new files are full proof drafts; semantic and compiler gates
are still pending at this note's update.


## Differentiation gates and scalar Stokes ingredient

Root's serialized builds have now passed `ExteriorDerivative`, `ExactOneForms`,
`ExteriorDerivativeRules`, `PullbackRegularity`, and `PullbackDifferentiation`.
Thus the exact source18–20 and22 production proofs are compiled; root's separate
21/23–25 modules are also green. The independent source reviewer accepted all
full proof drafts and was sent final compiled hashes and proof-only corrections.
Final section probes and recursive axiom audits remain root-owned gates.

`SimplexFTC.lean` is a new complete proof draft for the scalar ingredient of33.
It preserves the actual order of all coordinates except the selected inserted
coordinate, proves explicit native existence on both sides, and uses a direct
product-measure disintegration followed by the already connected one-dimensional
FTC. The proof includes zero-dimensional faces and collapsed fibers. It is
independent of chain orientation; the top-face vertex permutation is a separate
geometry obligation documented in `pma-ch10-stokes-dependencies.md`. Its full proof has independent mathematical acceptance and its serialized compiler
gate is now green. The final native existence claims are unchanged.


## Standard simplex Stokes assembly

`StandardSimplexSurface.lean` exposes the identity-coordinate C² simplex for the
general transport lane. `StokesCoefficients.lean` supplies the omitted-coordinate
coefficient functionals, their C¹ regularity, and differentiation through finite
exterior-basis expansions. Both have passed root's serialized compiler.

`SimplexStokes.lean` is now a complete proof draft of the independently accepted
standard simplex Stokes contract. Its upper-face identification uses the actual
affine vertex permutation `i.cycleRange.symm`; each lower face keeps the original
order of its surviving coordinates. The signed evaluation lemmas live in the
geometry lane's `SimplexFormFaces.lean`. Native finite-sum and subtraction rules,
the scalar FTC, and the explicit face integrands then assemble the actual
integer-chain boundary integral. The final assembly's semantic and compiler
gates are pending; no unchecked result is being reported as complete.

## Stokes gate and exact forms

The complete standard-simplex calculation in `SimplexStokes.lean` has now passed
root's serialized compiler. Root's general C² simplex/finite-chain wrapper
`ChainStokes.lean` is also green, exposing the full source10.33 contract. The
independent reviewer accepted the complete coefficient proof and received its
final compiled hash. This note does not replace root's remaining section probes
or recursive audit.

For10.34, `SimplexSeparation.lean` proves that actual integrals over affine
coordinate simplices separate every coefficient. Its scalar positivity lemma
uses a small inner cell to establish positive simplex measure; no exact simplex
volume is needed. `SimplexBoundarySquared.lean` cancels each deleted-vertex pair
with the reversed deletion order using the pinned `Fin` parity identity.
`ClosedExact.lean` then applies Stokes twice to a C¹ exact form and its C¹
primitive. This preserves the source regularity without applying the C²
`d²=0` theorem to a merely C¹ primitive. These three full drafts have accepted
contracts and pending compiler gates at this update.

## Later Poincare API boundary

Pinned `Mathlib/MeasureTheory/Integral/CurveIntegral/Poincare.lean` proves only
the one-form Poincare lemma. Its most convenient open-domain interface is
`Convex.exists_forall_hasFDerivAt_of_fderiv_symmetric` (line379): on a convex open
set, a differentiable operator-valued one-form with symmetric derivative has a
primitive whose Frechet derivative is the given form. This can supply the
one-form case after an explicit coordinate/exterior bridge, and a C¹ given
form gives a C² potential through the usual derivative regularity criterion.
It does not establish the arbitrary-degree source10.39 theorem. A higher-degree
radial homotopy proof still needs genuine coefficient algebra and parameter
integral differentiation; the pinned dominated differentiation interfaces are
in `Mathlib/Analysis/Calculus/ParametricIntegral.lean`.
# Coordinate primitives and Poincare continuation (2026-10-23)

Source 10.38 is now compiled through `ConvexPrimitives.pma10_38`. Its proof uses the global smooth selection on convex projection fibers (`ConvexSections`, `ConvexLinearSections`, `PrefixCoordinates`) and a compact parameter integral (`ConvexPrimitiveIntegral`). The independent source reviewer accepted the complete construction, including the empty/unbounded domain possibilities and the zero-dimensional prefix.

Source 10.39 has a complete proof draft in `CoefficientIntegrals`, `ContractionCalculus`, `RadialHomotopy`, `RadialPrimitive`, and `Poincare`. The root agent's `ContractionAlgebra` supplies the compiled grade-lowering and Euler identities. The analytic construction integrates the radial contraction coefficientwise and proves its exterior derivative by the scalar fundamental theorem. It uses only C1 input coefficients and produces a C1 primitive in every positive degree. The compiler gates are still pending; this paragraph does not claim 10.39 complete.

The separate source 10.43 C2 vector-potential regularity obligation is tracked in `pma-ch10-potential-regularity.md`. It is not inferred from the C1 primitive of 10.39.
