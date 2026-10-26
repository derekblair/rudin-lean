# Chapter 10 second-half analytic API inspection

Inspected 2026-10-25. This is source evidence and an implementation map, not a
claim that an unimplemented theorem is impossible. No third-party implementation
was copied, installed, or added to the project.

## Subsequent repository reconciliation

The initial checkout inspection below was superseded by the user's pointer to
`origin/ch8-codex-20261022`, fetched at
`bb50a2079f8e189d8e282e2521bbadb64f4f98eb`. That repository branch already
implements the missing simplex Stokes and all-degree Poincaré bridges discussed
below. It has 24 second-half principal theorems and the explicit unresolved
C² vector-potential clause of 10.43. The lane reuses its 79 second-half
production modules and 15 probes; it does not treat absent Mathlib wrappers as
an ongoing mathematical blocker. See the reconciliation manifest and the
independent prior-branch reviews. Missing prerequisites in the standalone lane
are a separate integration issue.

## Pinned local sources

Mathlib checkout: `d13f23b723b8a846827a245b89c10fc7d3f11612`.
Paths below are relative to `rudin/.lake/packages/mathlib/Mathlib/`.

* `Analysis/Calculus/DifferentialForm/Basic.lean:73`: `extDeriv` represents
  forms by continuous alternating maps. `extDeriv_apply` (line 199) is the
  alternating sum of coefficient derivatives; `extDeriv_extDeriv_apply`
  (229) and `extDeriv_extDeriv` (235) prove the square-zero identity with
  second-order regularity. `extDerivWithin_pullback` (240) and
  `extDeriv_pullback` (260) prove pullback naturality with a differentiable
  form and a twice continuously differentiable map.
* A recursive search for `extDeriv|extDerivWithin` throughout `Mathlib/`
  returns only that file, `DifferentialForm/VectorField.lean`, and
  `Geometry/Manifold/MFDeriv/NormedSpace.lean`. None connects exterior
  differentiation to an integral. A recursive search for
  `simplex.*integr|integr.*simplex|chain.*integr|integr.*chain` in
  `Analysis/` and `MeasureTheory/` returned no matches.
* `MeasureTheory/Integral/DivergenceTheorem.lean:266` provides
  `MeasureTheory.integral_divergence_of_hasFDerivAt_off_countable`. Its domain
  is the rectangular box `Set.Icc a b` in `Fin (n + 1) → ℝ`; the conclusion
  is a sum of upper-face minus lower-face integrals. The hypotheses require
  continuity, a derivative off a countable exceptional set, and integrable
  divergence. This is useful analytic infrastructure, but its statement
  does not mention oriented simplices or singular chains.
* `MeasureTheory/Integral/CurveIntegral/Poincare.lean:379` provides
  `Convex.exists_forall_hasFDerivAt_of_fderiv_symmetric`: on a convex open
  set, a differentiable `ω : E → E →L[ℝ] F` whose derivative is symmetric
  has a primitive. Its conclusion is `∃ f, ∀ a ∈ s, HasFDerivAt f (ω a) a`.
  Lines 357 and 369 provide corresponding within-set versions. The file's
  documented scope is **1-forms**. It does not prove the all-degree
  Poincaré lemma in Rudin 10.39.
* `LinearAlgebra/CrossProduct.lean` has `crossProduct` (50), `cross_apply`
  (66), `dot_self_cross` (87), `dot_cross_self` (94), the determinant
  identity `triple_product_eq_det` (106), and `cross_dot_cross` (112).
  These support the local algebra in 10.46. Gradient definitions and
  derivative bridges live in `Analysis/Calculus/Gradient/Basic.lean`.

## Required bridges for the assigned statements

* **10.33:** after first-half forms, integration, and pullback are available,
  prove Stokes on the standard simplex, identify every oriented face and
  its integral, transfer by the twice continuously differentiable
  parametrization, and extend linearly to chains. Existing box divergence
  alone is not this statement.
* **10.35, 10.36, 10.37, 10.45, 10.50, 10.51:** the advertised chain-boundary
  consequences depend on 10.33 and on equality/boundary conventions for
  the first-half integral. Replacing general chains or admissible regions
  by rectangles would narrow the printed statements.
* **10.39:** the local 1-form primitive theorem can supply the degree-one
  case after a representation bridge. Degree two and above need a new
  proof, for example a verified homotopy operator or the book's coordinate
  induction with 10.38. A degree-one specialization is not full 10.39.
* **10.40 and 10.43:** pullback naturality and inverse-map identities support
  transport of exactness. The divergence-free-to-curl implication in
  10.43 needs the degree-two instance of 10.39, which the local 1-form
  theorem does not provide. The direct square-zero identities can use
  `extDeriv_extDeriv_apply` after coordinate representation lemmas.
* **10.44, 10.46–10.49:** changes of variables, coordinate determinants,
  cross products, and ordinary integrals are available, but their equality
  to the chosen first-half form integrals must be proved.

At the initial read-only inspection, both lanes' `Rudin/PMA/Chapter10.lean`
files contained only the existing documentation header, so there was no
first-half definition or theorem API to target at that time. This is a
snapshot, not a claim about the other lane's later progress.

## Public prior art reconciled

### Smooth cubical Stokes

Repository: <https://github.com/d0d1/lean-stokes-theorem>, inspected head
`adffb99be9fd00a42369561068c9d11475cbedb8`.

* `LeanStokes/SingularCubeStokes/Defs.lean:38` defines
  `SmoothSingularCube` with a global `ContDiff ℝ ⊤` field.
* `LeanStokes/SingularCubeStokes/Theorem.lean:118` proves `singularStokes`
  for such a cube and a globally `ContDiff ℝ ⊤` form. The conclusion uses
  integration on the unit cube and an alternating sum of cubical faces.
* `LeanStokes/CubeStokes/Theorem.lean:40` proves `stokes_on_box` with
  local derivative and integrability hypotheses; it remains a box theorem.
* `LeanStokes/CubeStokes/Bridge.lean:40` has
  `extDeriv_topCoeff_eq_extDerivCoord`; the singular proof uses this
  coordinate bridge and Mathlib pullback naturality.
* The project pins Lean 4.29.1 and Mathlib commit
  `5e932f97dd25535344f80f9dd8da3aab83df0fe6`, whereas this lane pins Lean
  4.34.1 and the Mathlib commit recorded above. Its repository declares
  GPL-3.0-only licensing. Its README reports a successful build and axiom
  audit; those reports were not treated as a local verification here.
* All 45 Lean files at that commit were fetched read-only (4081 source
  lines including the root module). A lexical scan after removing nested
  block comments and line comments found no `sorry`, `admit`, `axiom`,
  `unsafe`, or `sorryAx` tokens. This is source inspection, not a build or
  transitive axiom audit under the lane's pinned toolchain.

This is relevant proof architecture, but it cannot simply replace Rudin's
finite-regularity simplex theorem. Importing it verbatim would still leave
regularity, domain, boundary, representation, and pinned-version bridges.

### Prove2Me Rudin localization result

Canonical public page:
<https://prove2.me/theorems/38ff57be-6b91-4b46-a7ca-979c14d3a883>.

The page labels `Rudin.ch10_closed_pointwise` proved and identifies Lean
4.33.1 / Mathlib `0df444a`. Its displayed theorem imports
`Definitions.Def_Rudin_ch10_forms`, uses coefficient tuples and a
`SimplexSurface` representation, and ends with `by sorry`. The public HTML
contains no solution source, definition source, or proof-download link.
The statement is a localization implication from vanishing integrals to
pointwise closedness; it is neither general Stokes nor Poincaré.

The public API documentation at <https://prove2.me/skill.md> distinguishes
theorem statement modules (which contain placeholders) from solution
modules. It documents theorem details, submission lists, and submission
solution endpoints as requiring bearer authentication. No credentials were
requested or sent, and no statement placeholder was imported as proof.
Anonymous GET requests to the documented theorem endpoint and its
submission-list endpoint both returned HTTP 401 with a missing/invalid
authorization-header error. Thus the full claimed proof and imported
definitions were not accessible through the inspected public routes.
