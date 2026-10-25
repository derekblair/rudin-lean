# Independent fidelity review: PMA 9.10–9.18

The core `Differentiation.lean` declarations were reviewed against printed
third-edition pages 211–218, read directly from `/root/sources/pma3.pdf`.
The final reviewed core Git blob is
`7667b2eefa3046064ea553b3c9dd4818d0e0d72f`.
The final recheck includes the explicit arbitrary-direction generalization at
9.17, the zero-dimensional convention, and the simplified final calculation
in the gradient-maximum proof; the reviewed mathematical contracts remain intact.

The core numbered statements and formulas are represented faithfully:

- 9.10: scalar and vector slope limits, the normalized remainder criterion,
  and identification of one-variable derivatives with linear maps.
- 9.11–9.12: the specified total derivative, differentiability throughout a
  domain, the printed punctured-limit characterization, and uniqueness.
- 9.13–9.15: remainder decomposition, the operator-valued differential,
  continuity, the derivative of a linear map, its zero remainder, and chain rule.
- 9.16–9.17: coordinate decomposition, partial-derivative definitions and
  their limits, existence under total differentiability, derivative columns,
  entries, directional limits, and application to an arbitrary increment.
- 9.18: the curve chain rule in operator, coordinate, and gradient forms;
  coordinate derivatives of curves; the gradient; directional derivatives;
  and the maximizing unit direction when the gradient is nonzero.

The review identified two items and sent them to the author and coordinator:

1. **Resolved and rechecked:** `pma9_13_differential_eq` proves that the totalized
   `fderiv` agrees with every supplied derivative. The definition's comment
   explicitly explains its zero default at nondifferentiable points.
2. The prose attached to 9.16 asserts that partials alone do not imply
   continuity, and that even continuity plus partials does not imply total
   differentiability. The core file did not itself supply witnesses. The team
   assigned explicit witnesses to `DiscontinuousPartials.lean` and
   `PartialCounterexamples.lean`. Their final independent review is recorded in
   `evidence/ch09-a-counterexamples-review.md`. The latter witness is authored
   by this reviewer, so its implementation is not an independent review result
   of this document.

Representational differences are documented at the declarations: functions on
open sets are represented by total extensions with local hypotheses; linear
maps are bundled continuously (all Euclidean linear maps are continuous);
full-neighborhood remainder limits use a zero value at the origin, with the
punctured version separately proved; and the directional formula extends from
unit directions to arbitrary vectors. The counterexample witnesses are
convenient alternatives to the exercises referenced by the text, rather than
claims to formalize the entire exercises.

No edits to the core `Differentiation.lean` were made by this reviewer. Build and
axiom status must be taken from the final verification records, not this source
coverage review.
