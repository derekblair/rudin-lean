# PMA 6.26–6.27: native polygonal length and Riemann arc length

Status: both accepted contracts have complete Lean proofs in `rudin/Chapter06CurveDraft.lean`. No placeholders or custom axioms. The final source hash is recorded in the independent review.

## Source scope and accepted interpretation

Only the local statement blocks for 6.26–6.27 on PDF pages 145–146 were consulted. No book proof text or book content was copied into the repository. The parent approved the actual typed contracts before proof work.

The native public `Partition a b` has finitely many weakly monotone points with explicit endpoints; repeated points and zero-width cells are permitted. `PolygonalLength` is the literal finite sum of norms of consecutive image differences. `CurveLength` is the extended-nonnegative-real supremum over these native endpoint partitions. It is not defined using a measure integral or a library variation operator.

`CurveOn` contains `a ≤ b` and continuity on the closed interval; `ArcOn` additionally requires injectivity there; `ClosedCurveOn` requires the two endpoint images to coincide; rectifiability includes being a curve and finite length. A singleton parameter interval has zero length. The predicates are generalized from finite Euclidean spaces to normed additive groups where appropriate, and 6.27 is quantified over real inner-product spaces, which includes the source setting.

The derivative premise of 6.27 is an actual `HasDerivWithinAt` statement throughout the closed interval, including one-sided endpoint semantics, together with continuity of the velocity. It does not assume rectifiability, length bounds, integrability, or the desired identity.

The initially approved 6.27 contract used `a < b`, consistent with the inventory's convention for derivative clauses. During review it was optionally strengthened to `a ≤ b`; the equality case now proves the full integrability-and-length conclusion using the native zero-interval integral theorem. This is a strengthening, not a correction of an established fidelity defect.

## Proof structure

6.26 proves all literal definition clauses plus two useful faithful bridges. Every native partition sum is bounded by `eVariationOn`. Conversely, every monotone chain from the library variation definition is padded with the native left and right endpoints, which produces an allowed weakly monotone partition and dominates that chain sum. This proves equality of the native polygonal supremum with variation, including chains with duplicate points. It then proves the equivalence of native rectifiability with continuity plus bounded variation.

6.27 uses native Darboux sums from `Rudin.PMA.Chapter06.Basic` and the proved continuous-integrability theorem in `Rudin.PMA.Chapter06.Integrability`:

1. Compactness bounds the continuous velocity. The derivative bound gives a Lipschitz bound, hence finite variation and native rectifiability.
2. A local norm-increment estimate compares each curve increment to the constant-velocity linear increment. Its error is bounded by the velocity oscillation times the cell width.
3. The derivative bound by the cell supremum controls the variation of that cell. Finite additivity of variation over a weakly monotone partition yields native curve length at most every upper Darboux sum of speed, hence at most the native upper integral.
4. Uniform continuity of velocity provides partitions with small cell oscillation. The local increment estimate makes an upper Darboux sum at most its polygonal length plus an arbitrarily small error. Taking the native polygonal supremum proves the reverse inequality.
5. Continuous speed is native Riemann integrable, so its lower and upper Darboux integrals agree, giving the requested equality with `RIntegral`.

No Lebesgue or interval integral is substituted for the Riemann definition. The library variation results used are chain bounds, finite additivity, and Lipschitz control, not an assumed arc-length identity.

## Validation

Command: `./lake-local env lean Chapter06CurveDraft.lean` in the isolated workspace. Both `pma6_26` and `pma6_27` compile with recursive axiom reports containing only `propext`, `Classical.choice`, and `Quot.sound`.

Three standalone probes verify singleton length zero, real line length `ofReal (b-a)`, and a constant closed curve on `[0,1]` that is not an arc. These probes and the rectifiability and increment-estimate helpers have the same standard-only axiom sets. The draft contains no `sorry`, `admit`, or custom `axiom` declarations.

This is author validation; a separate independent review is requested before integration. Only the assigned curve draft and this design report were changed for the curve task; all Chapter 5 sources were preserved.
