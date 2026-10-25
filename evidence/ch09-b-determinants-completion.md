# PMA 9.30–9.31 and 9.33–9.38 completion evidence

Source: PMA third edition, printed pages 228–235, reviewed directly from the local
PDF. Work is in `Rudin/PMA/Chapter09/Determinants.lean`.

Completed nodes: 9.30, 9.31, 9.33, 9.34, 9.35, 9.36, 9.37, 9.38.
No remaining node in this assigned group.

Coverage includes null space/range/rank and full-rank/zero-rank consequences;
projection definition, fixed-range characterization, unique range/kernel
splitting, existence with prescribed range, and infinitely many projections
onto a nonzero proper subspace; the exact tuple-sign product, its values,
transposition and repetition properties, all-tuples determinant sum and proved
equivalence with Mathlib's determinant; column coordinates and determinant as a
function of columns; all four properties of 9.34; multiplicativity;
invertibility criterion in linear and matrix form; basis-change intertwining
and basis-independent determinant; Jacobian definition, derivative computation,
actual coordinate partial derivatives, and the first-block implicit-function
criterion.

Representation changes and generalizations, documented in source:

- Finite vector/matrix indices start at zero; subtracting two indices in the
  sign product is unchanged by the shift from the printed convention.
- The projection existence and infinitude results are proved for arbitrary real
  vector spaces, extending the printed finite-dimensional assumptions.
- Rank uses cardinal dimension for arbitrary vector spaces, with a separate
  finite-rank natural-number interface. Invertibility/basis independence are
  expressed for arbitrary finite-dimensional real vector spaces.
- The Jacobian definition is total, following `fderiv` outside differentiability
  points. The actual-partial-derivative theorem explicitly assumes
  differentiability. This extension does not change values on the printed domain.

Verification on Lean4.34.1 and pinned Mathlib:

- `lake build Rudin.PMA.Chapter09.Determinants`: exit0,
  `Build completed successfully (8925 jobs).`
- `lake build Rudin.PMA.Chapter09.DeterminantsAudit`: exit0,
  `Build completed successfully (8928 jobs).`
- Recursive audit checked49 declarations in the Chapter9 import closure at that
  stage (44 determinant-group declarations and5 inverse declarations).
  Every transitive axiom was one of `propext`, `Classical.choice`, `Quot.sound`.
- Source has no `sorry`, `admit`, `native_decide` or axiom declarations.

Source SHA-256:
`122996fe4b4d7b5cb7bea71026b2b64df39cd85b353166b55904deb282614830`.

The integrating agent will rerun the full final audit after all first-half
imports and second-half sections are present.
