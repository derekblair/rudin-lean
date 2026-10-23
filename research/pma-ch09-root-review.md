# Chapter 9 independent root review

The root agent independently inspected printed p.219 (PDF p.228) in memory
using pdftoppm and the PDF skill, and reviewed the complete C1Partials.lean
candidate. The root did not author that proof.

PMA-9.21 contract ACCEPTED: the domain is open in Euclidean n-space; the
conclusion equates total C1 regularity with existence and continuity of every
coordinate partial, with no premise assuming total differentiability in the
converse. Scalar components give the vector-valued assertion. Empty coordinate
index types remain covered. The candidate constructs the derivative from
coordinate coefficients using a finite telescoping sum and a local uniform
mean-value remainder; proof typechecking remains a separate gate.

Root-authored inverse/implicit/contraction proofs require the other reviewer's
acceptance and are not covered by this independent-review claim.

## Final compiled 9.21 acceptance

The complete final proof and Mathlib wrapper were independently reviewed by the
root, who did not author either file. The wrapper exports the pinned library’s
proved parameterized mean-value remainder; it adds no assumption and introduces
no axiom. The finite-coordinate proof constructs the derivative from actual
coordinate derivative witnesses, uses a local remainder estimate and telescopes
the coordinate increments. Scalar components then establish the vector result.
All compiler fixes concern presentation, coercions and library visibility.
The source contract is unchanged. Both files compile. Accepted exact hashes:

- `C1Partials.lean`: `e152f7838b60823276969374f474053d0c16e6c9b2650bf3fe06ed093c8870b3`.
- `MathlibPartialBridge.lean`: `4acf81e1aa30be2f512b0f430cbd6a1ea52d5c5c17382f1911ba88abe203fb78`.
