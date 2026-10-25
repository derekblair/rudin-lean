# Independent source-fidelity review: PMA 9.23–9.29

Reviewer: the determinants subagent, independent of the authorship of these files.
Source: `/root/sources/pma3.pdf`, printed pages 220–228. The explicit example
on printed page 227 was additionally rendered and inspected visually because
its OCR loses matrix entries and fraction bars.

Reviewed source hashes (SHA-256):

- `Inverse.lean`: `26a19ca7630862816959425b0efb26a775e9409c98bcfa57b34794ae4115ab7f`
- `Implicit.lean`: `71e0916b38a4ccff31bf8a624f8de7709dfd10a4d5744559889700cb5b0e64cf`

## Findings

No substantive statement-fidelity defect found in the reviewed declarations.

- 9.23 proves existence and uniqueness on a complete nonempty metric space, and
  separately convergence of the iterates. Nonemptiness is a necessary repair to
  the printed statement and is explicitly documented at the theorem. The
  principal theorem accepts the first half's exact `IsContraction` predicate and
  uses its proved equivalence to Mathlib's nonnegative `ContractingWith` encoding.
  This wrapper was re-reviewed after rebasing the first-half definitions.
- 9.24 packages both open neighborhoods, injectivity, exact image and inverse
  identities in an `OpenPartialHomeomorph`. It includes source containment in the
  original domain and C1 regularity throughout the inverse's open domain. The
  generic inverse-derivative lemma correctly computes the derivative when an
  invertible derivative is supplied at the corresponding source point.
- 9.25 permits every open subset of the original open domain and concludes its
  image is open. No global injectivity is assumed.
- 9.26 represents concatenated real coordinates by products. The two block
  restrictions and reconstruction identity match the printed linear notation.
- 9.27 proves both the explicit solution and actual existence and uniqueness;
  it does not replace the existence conclusion by a conditional identity.
- 9.28 gives open U and W, both base-point memberships, containment U in the
  original domain, a C1 function on W, its base value, graph membership and zero
  equation, uniqueness among all x with `(x,y)` in U, and the derivative with the
  correct order and minus sign. The Banach-space generalization includes all
  real finite-dimensional cases.
- 9.29 has exactly the printed two functions, base point, derivative blocks and
  six implicit derivative coefficients. The final theorem supplies a genuine
  local C1 implicit function, rather than only a matrix computation.

## Representation changes requiring the final report

The file comments already record generalization to real Banach spaces and product
coordinates. The explicit nonemptiness repair at 9.23 must also be listed in the
final report. There are no narrowed scopes or unreported strengthened premises
in this reviewed group.

This review is of statement meaning and source fidelity. The final production
build and recursive axiom audit remain the integrating agent's responsibility.
