# Independent source-fidelity review: PMA 9.19–9.22

Reviewed against PMA third edition, printed pp. 218–220, read directly from `/root/sources/pma3.pdf` through `pdftotext`. The cross-referenced 9.16 partial-derivative definitions and defining quotient theorem in `Differentiation.lean` were also inspected.

Reviewed source blobs:

- `rudin/Rudin/PMA/Chapter09/ContinuousDifferentiability.lean`: `85adb835a058653a65c38b952071f73565c9f0a9`
- `rudin/Rudin/PMA/Chapter09/PartialContinuity.lean`: `a5131890450f3f00a7cc877255cc369539dbe6ba`
- `rudin/Rudin/PMA/Chapter09/PartialCriterion.lean`: `54b9236c3c0dc1b5988f0ea914ff4a11199f8bab`

Result: no missing numbered-node content, hidden total-differentiability premise in 9.21's converse, or Euclidean-norm substitution found. The final 9.21 bridge was rechecked after its reported successful `lake env lean Rudin/PMA/Chapter09/PartialCriterion.lean` run (exit 0). The changes pin the composed line parameter and the vector congruence; no statement or mathematical premise changed. Compilation of the final dependency graph remains covered by the root agent's build/audit evidence.

- **9.19:** The derivative norm bound, resulting Lipschitz estimate, and attached zero-derivative constancy corollary are all represented. The extension to real normed spaces and omission of openness are explicitly commented. Differentiability at every point of the convex set supplies the needed stronger local hypothesis, so the book's open-set case is included.
- **9.20:** `IsC1On` includes both differentiability and continuity of the operator-valued derivative. The comparison with `ContDiffOn` assumes the open domain exactly where required. The separate epsilon-delta statement uses operator norm for derivative differences.
- **9.21 forward:** Differentiability supplies each coordinate partial; evaluation of the continuous operator-valued derivative proves continuity of the partial values.
- **9.21 converse:** The stated right side assumes only existence of the one-dimensional coordinate partials and continuity of their values on the open set. In the finite-coordinate induction, block derivatives are obtained from the induction hypothesis and the assumed coordinate derivatives; the strict-derivative combination theorem then produces total differentiability. The helper `hasFDerivAt_coordinateDerivative` has a differentiability premise, but its sole use in this induction occurs after that premise has been proved. There is no circular assumption of total differentiability.
- **Euclidean norm:** The public 9.21 theorem has domain and codomain `EuclideanSpace ℝ (Fin _)`. The sup-norm finite product appears only in `PartialContinuity.lean`; `PartialCriterion.lean` transports through `PiLp.continuousLinearEquiv 2` and finishes with `contDiffOn_piLp 2`. This is an explicit equivalence-of-norms transport, not an assertion that the sup norm is the Euclidean norm.
- **Partial definition:** `pma9_16_hasPartial` is the derivative of a scalar component along a standard coordinate line; its linked quotient theorem is the printed partial derivative limit. `partial_hasDerivAt_update` merely shifts the real line parameter from zero to the coordinate value. The totalized `lineDeriv` values are accompanied by actual existence assumptions in 9.21.
- **9.22:** The definition retains the book's real contraction factor with only `c < 1`. The proof of equivalence with a nonnegative Mathlib factor uses `max c 0`, so empty/singleton metric spaces and negative factors cause no silent strengthening.

No implementation changes requested. The known deviations are documented generalizations (normed spaces/open-set omission at 9.19, normed spaces at 9.20, and zero-dimensional Euclidean instances); the metric-space contraction definition itself is faithful.
