# Independent review: PMA 6.26–6.27

Reviewer: `completion_evidence`, a fresh reviewer of the vectors worker's implementation. Date: 2026-10-10. Outcome: **accepted**.

Reviewed file: `rudin/Chapter06CurveDraft.lean`, 371 lines.

Final SHA256: `0fcd03a02ba4b7c7a57a647b14befac8b93fa006238ed13abc910849362d1b50`.

## Contract and source fidelity

6.26 defines the source objects directly: a continuous parameterized map on an ordered closed interval; an arc additionally injective there; a closed curve with equal endpoint values; polygonal length as the finite sum of edge norms on the native partition; and length as the supremum in `ℝ≥0∞` over those partition lengths. Rectifiability includes the curve condition and finite length. The definitions depend on the parameterized map and preserve possibly infinite lengths.

6.27 assumes a supplied derivative vector at every interval point through `HasDerivWithinAt`, and relative continuity of that derivative. These are the appropriate one-sided endpoint conditions. It concludes rectifiability, **native** ordinary Riemann integrability of the speed, and equality of native curve length with the native Riemann integral. The theorem generalizes Euclidean space to real inner product spaces; no finite-dimensional source cases are lost. No measure-theoretic integral is silently substituted.

The reviewer initially questioned the strict interval premise in the earlier draft, but the current inventory explicitly restricts derivative clauses to nondegenerate intervals, and the parent had approved that contract. Therefore it was not a source-fidelity defect. The final author nevertheless supplied an optional strengthening to `a≤b`: the equality case is proved using the actual singleton Darboux-integral theorem and singleton variation. This strengthening is sound, and the original strict branch is unchanged.

## Complete proof review

- The native partition-to-variation correspondence is proved in both directions. A partition extends to a monotone infinite sequence by repeating its last point. Conversely, a finite monotone sequence is padded with the interval endpoints; nonnegative extra edge lengths bound the original sequence sum. Thus `CurveLength = eVariationOn` is proved, not adopted as a replacement definition.
- Boundedness of the continuous derivative on a compact interval yields a Lipschitz estimate through the mean value inequality. Composition with the identity interval's bounded variation proves finite curve length before the final use of `ENNReal.toReal`.
- `curveIncrement_norm_estimate` subtracts the affine map with constant derivative `w`, applies the derivative norm bound, and uses the reverse triangle inequality. This establishes the needed quantitative estimate between an actual curve increment and `width * ‖w‖`.
- The upper bound on curve length by each speed upper sum uses exact variation additivity across the native partition and a local derivative norm bound by the closed-cell speed supremum. It then passes to the genuine upper Darboux integral.
- For the reverse bound, uniform continuity of the derivative provides a fine native partition. On every cell, the increment estimate and the speed oscillation bound give `speed-upper-sum ≤ polygonal-length + 2η(b-a)`. Choosing `η = ε/(2(b-a))` and using the defining supremum proves the reverse integral bound.
- Continuous speed is separately proved Riemann integrable with the native 6.8 theorem. Equality of its upper and lower integrals connects the preceding comparison to `RIntegral`; the finite-length proof justifies the final `ENNReal.ofReal_toReal` conversion.
- The singleton, identity-line, and closed-constant/non-arc probes check meaningful boundary distinctions. The constant curve is not incorrectly classified as an arc on `[0,1]`.

No remaining semantic, endpoint, totalization, circularity, or proof-validity findings were identified.

## Independent checks

The reviewer ran `./lake-local env lean Chapter06CurveDraft.lean` against the final hash. It completed with exit zero and no warnings or errors. The seven included transitive axiom reports—6.26, 6.27, rectifiability, the increment estimate, and three probes—each contain only `propext`, `Classical.choice`, and `Quot.sound`. A separate lexical scan found no placeholders, custom axioms, `native_decide`, unsafe declarations, or opaque declarations. The source hash was checked again after compilation and remained unchanged.

Production integration and chapter-wide validation remain the parent's responsibility.
