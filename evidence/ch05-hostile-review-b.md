# Fresh hostile production-gate review: PMA 5.7–5.12

**Verdict: PASS for the assigned six-node scope. No confirmed mathematical or statement-fidelity defect found.** This is a fresh adversarial gate, separate from the earlier fidelity acceptance.

Reviewer: `/root/vectors`. These six nodes were authored by a different worker. I did not use the earlier acceptance as a premise for this verdict. I independently read the local book's definition/theorem statement blocks for 5.7–5.12 and the 5.12 corollary on PDF pages 116–118, then checked the actual integrated contracts, implementation proofs, relevant reference theorem signatures, and Chapter 4 one-sided-limit/discontinuity definitions. No textbook proof text was used or reproduced. No Lean source was edited.

## Exact reviewed state

| Item | SHA-256 |
| --- | --- |
| `rudin/Rudin/PMA/Chapter05.lean` | `55acec19c187d4ae0d6bfc37c78ee32df5711a997f3d4e0aeea876eb876904cb` |
| `rudin/Rudin/PMA/Chapter05Probes.lean` | `a59995311bfe25b74920cee0aef6ed6ed3674c4568374058c141c1fcb0f96093` |
| Integrated middle-node assembly block | `54113da5cfc7681596644bd4ac6a50832fa18eca3b4511e8fa00c17a8274b6e8` |

The assembly-block fingerprint begins at the literal `Chapter05MiddleDraft.lean` assembly marker and ends immediately before the `Chapter05LHopitalDraft.lean` marker. Whole-file hashes were unchanged at the end of the review. Production integration is covered by this review only insofar as it preserves the reviewed content.

## Hostile checks and outcomes

**5.7: local extrema.** The radius is strictly positive; the value inequality is non-strict; the center itself is included. Metric-space quantification does not silently assume a Euclidean or complete domain. The comparator with `IsLocalMax`/`IsLocalMin` has the correct inequality directions. A fresh compiler probe verifies that a constant function has both extrema at every supplied point, catching an accidental strict-extremum definition.

**5.8: Fermat.** The point is explicitly in `Ioo a b`, so the source interval is nondegenerate and locally contains a full neighborhood. The derivative and extrema are relative to `Icc a b`; the proof converts to ordinary local data only after obtaining that neighborhood. Neither endpoint differentiability nor a global extremum is assumed. The actual endpoint-identity counterexample is retained: a relative minimum at the left endpoint can have derivative one. Thus the interior premise is substantive rather than decorative.

**5.9: Cauchy mean value.** Both functions are continuous on the closed interval and differentiable only on the open interval. The conclusion is the cross-multiplied identity with an actual interior witness; there is no division, denominator-derivative nonzero premise, monotonicity premise, or endpoint derivative requirement. I checked the pinned reference theorem's complete relevant signature. A fresh probe instantiates the theorem with an oscillatory numerator lacking any finite right endpoint derivative and a constant second function whose derivative is zero. The actual contract accepts both cases together.

**5.10: ordinary mean value.** The same endpoint/interior separation is preserved, and `a < b` prevents an empty-witness loophole or division by zero in the reference slope. The factor and equation orientation match the source. The existing stronger boundary probe proves the MVT conclusion while denying every finite one-sided source derivative at zero for the oscillatory example; its right-limit argument is valid. This is stronger evidence than merely denying a chosen total extension's two-sided derivative.

**5.11: derivative signs.** All three conclusions concern only the open interval. The increasing/decreasing conclusions are non-strict, and the zero-derivative conclusion compares every pair of interval points. No endpoint continuity or endpoint differentiability is inserted. A fresh probe takes a function that is zero throughout the open interval but equals one at the left endpoint; the actual theorem proves both monotonicity directions and constancy on the open interval without asserting equality to the exceptional endpoint value.

**5.12: derivative IVP and corollary.** The hypothesis supplies actual within-derivatives at every closed-interval point, including the two one-sided endpoint derivatives. `a < b` prevents arbitrary derivatives on a singleton from satisfying the source contract. Both strict endpoint-derivative orderings are retained, and both yield a witness strictly inside the interval. No continuity of the derivative is assumed. A fresh probe applies the theorem to `|t| + t²` on `[0,1]`, using the relative right derivative at zero and a derivative value strictly between the endpoint values. A separate compiled instantiation checks the reversed derivative ordering.

The corollary does not collapse into a continuity claim: it excludes `FirstKindDiscontinuityOn`, while the checked oscillatory derivative still has a second-kind discontinuity. The Chapter 4 first-kind definition includes failure of continuity and existence of both finite one-sided limits, so the conclusion excludes removable discontinuities as well as jumps.

The interior-only first-kind predicate does not silently lose the endpoints: the two additional contract conjuncts state that every existing finite one-sided derivative limit agrees with the derivative value. Their guards include the appropriate endpoint. Fresh compiled instantiations establish the left-limit agreement at `b` and right-limit agreement at `a` from ordinary one-sided neighborhood filters. The proofs use nondegenerate subintervals and uniqueness of the corresponding within-derivative; they do not rely on a vacuous filter at the wrong endpoint.

## Fresh kernel evidence

Review-only `./lake-local env lean --stdin` scripts imported the frozen final chapter/probe modules and proved the following six adversarial declarations without placeholders:

1. `constant_extrema_are_nonstrict`.
2. `cauchy_accepts_zero_second_derivative`.
3. `darboux_accepts_relative_endpoint`.
4. `darboux_reverse_order_is_retained`.
5. `endpoint_finite_limit_agreement`.
6. `open_interval_monotonicity_does_not_assume_endpoint_continuity`.

Every script exited with code 0. The sixth script emitted one deprecated-lemma-spelling warning in the temporary review code; there was no proof error or production-source change. Recursive axiom reports for all six fresh probes contain only `propext`, `Classical.choice`, and `Quot.sound`.

A separate fresh axiom check reported exactly those same three standard axioms for each of `pma5_7` through `pma5_12`, for the endpoint Fermat counterexample, and for the derivative second-kind-discontinuity probe. The temporary declarations were evaluated from standard input and were not added to project sources.

## Limits and disposition

This gate checks the six assigned source statements, their supplied proofs, and the identified adversarial boundary cases. It is not a claim of an independent review of every Mathlib theorem, all of Chapters 1–4, the other Chapter 5 nodes, host ownership, or future production changes. Successful probes supplement the direct statement review; they do not by themselves exhaust all possible mistakes.

No correction or blocked item remains in this assigned scope. The reviewed six-node content is suitable to pass this part of the hostile production gate.
