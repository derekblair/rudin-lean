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
contradicts functional vanishing. Their compiler gates remain pending.
