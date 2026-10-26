# First-half reconciliation: integration, 10.1–10.4

Source commit: `bb50a2079f8e189d8e282e2521bbadb64f4f98eb` on
`origin/ch8-codex-20261022`. Compared the actual definitions, contracts, and
proofs in `Integration`, `IntegrationProofs`, `IntegrationMeasure`, `SimplexSlices`,
and `Simplex` against printed pp.245–248 of the supplied third-edition PDF.
This review is separate from the fresh compilation and recursive axiom audit.

Accepted mathematical coverage:

- **10.1:** `Cell` includes ordered, possibly equal endpoints. The recursive
  value uses the existing Chapter 6 `RIntegral` in last-coordinate-first order.
  `IteratedRIntegrable` asserts existence of every encountered slice integral.
  Intermediate continuity is proved by uniform continuity and the native
  uniform-limit integral theorem. The one-dimensional measure bridge is proved
  first; the multidimensional bridge follows by Fubini and induction.
- **10.2:** permutation reindexes both cell endpoints and the function. Native
  integrability is proved for each order, and equality follows from an explicit
  measure-preserving coordinate equivalence. It is not merely an equality
  between unconditionally totalized integral values.
- **10.3:** support is `tsupport`, the closure of the nonzero set. Compactness
  produces an enclosing cell. Real and complex integral existence and
  enclosing-cell independence are proved; the complex case uses real and
  imaginary components with support-containment proofs.
- **10.4:** each simplex fiber is proved Riemann integrable, even when it
  collapses and its endpoint value is nonzero. The stopped-slice lemma splits
  the interval and handles endpoint values natively. Extension from the closed
  simplex supplies a continuous moving-endpoint formula, which proves the first
  marginal is continuous. Subsequent integrations exist. Coordinate symmetry
  gives every integration order and the integral value.

No narrowed hypothesis or repaired false assertion was found. Generalization:
the implementation includes dimension zero, with integral equal to evaluation
at the unique point. Zero-based coordinate indexing and the proved measure
bridge are representation conventions. The first-half umbrella flags these
conventions at the relevant node.

The six earlier integration/simplex probe assertions cover zero dimension,
collapsed cells and simplex fibers, coordinate permutations with unequal sides,
complex components, and a genuinely discontinuous simplex zero extension.

The earlier source depends on Chapter 9 `ParameterIntegrals`, which is absent
from the lane baseline and itself imports earlier Chapter 8–9 sources. The
isolated build uses exact Git blobs for those prerequisites. The root lane's
failure to resolve them is an integration blocker, not a missing mathematical
proof in these five reused files.
