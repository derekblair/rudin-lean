# PMA-5.13 independent semantic and proof review

Reviewer: fresh `oscillation` worker, assigned by root after implementation of the main l'Hopital proof. Review is read-only with respect to Lean sources. The only reviewer-authored file is this report.

Reference scope: the accepted `research/pma-ch05-inventory.md` and `evidence/pma-ch05-source-review.md`, PMA 5.13. The source book is not copied or reproduced. The review uses the previously accepted source extraction rather than claiming a new page-level source inspection.

## Verdict

**ACCEPTED.** The full PMA-5.13 contract, proof, and source interval bridge cover the accepted source scope. No hidden hypothesis, missing endpoint/target/form case, or incorrect statement was found. Independent final compilation and the recursive axiom audit passed. Acceptance applies to the exact source hash below, not to later edits or to a chapter integration that has not yet been checked.

## Main contract coverage

The explicit `EndpointApproach` constructors cover right-hand approach to every finite left endpoint, left-hand approach to every finite right endpoint, approach to positive infinity, and approach to negative infinity. Their filters are respectively `nhdsGT`, `nhdsLT`, `atTop`, and `atBot`. All four are proved nontrivial, so no empty-filter limit loophole appears.

`EndpointLimit` is a limit of real function values embedded in `EReal`, with an arbitrary `A : EReal`. It includes every finite target and both infinite targets. Inputs and derivatives remain real-valued throughout, as required.

The alternatives in `pma5_13_contract` are exactly zero-over-zero, denominator tending to positive infinity, and denominator tending to negative infinity. Neither infinite-denominator alternative assumes a limit or boundedness for the numerator. The derivative of the denominator is only assumed eventually nonzero. The denominator itself is proved eventually nonzero as an output, rather than imposed as an additional hypothesis. Consequently totalized real division does not silently stand in for a quotient on forbidden source points.

Eventual derivative hypotheses are a local generalization of the source's derivatives throughout a nondegenerate interval. Final source interval equivalence is checked separately below; the local contract does not require derivatives at the endpoint.

## Proof review

The zero-over-zero branch uses the pinned Mathlib `HasDerivAt.lhopital_zero_nhdsGT`, `lhopital_zero_nhdsLT`, `lhopital_zero_atTop`, and `lhopital_zero_atBot`. I inspected their actual signatures: they require eventual point derivatives, eventual nonzero denominator derivative, and the two zero limits; they allow an arbitrary output filter. Pulling the `EReal` neighborhood filter back along the embedding of real numbers therefore covers infinite as well as finite targets without assuming a nonexistent finite limit.

The zero-over-zero denominator nonvanishing argument applies that library theorem to `g/g`, obtaining limit one from `g'/g'`. Values with `g=0` give a zero quotient and are excluded by eventual positivity. This uses the already established library result and is not circular in the new theorem.

For an infinite positive denominator, the proof extracts a convex tail contained in the simultaneous eventual hypotheses and derivative-ratio bound. Every endpoint filter has the required interval/ray basis. Nontriviality supplies a finite anchor point in that tail. Cauchy's mean value theorem applies to the closed segment joining the anchor and a later point because convexity keeps it inside the derivative domain; point differentiability supplies the endpoint continuity used by that theorem. Both orderings of the two real inputs are explicitly handled.

The ratio algebra divides only by a nonzero derivative and a strictly positive denominator increment. Positive divergence of `g` supplies both a positive `g(x)` and `g(x)>g(y)` eventually. No monotonicity or fixed sign of `g'` is assumed. The anchored correction `(f(y)-v*g(y))/g(x)` tends to zero because its numerator is a single finite constant; there is no condition on varying `f(x)`.

Lower and upper bounds then establish finite, positive-infinite, and negative-infinite targets. The upper bound negates only the numerator. The negative-infinite denominator branch negates both numerator and denominator, preserving both derivative and function ratios and leaving the target unchanged. These sign choices are correct.

## Final interval bridge and validation

The added `pma5_13_source_interval` states the source theorem using Chapter 4's `ExtendedLimitOn`, including its nonvacuity condition. Its only representation premise is equality of the source approach filter with one of the four endpoint filters. The draft proves that premise for both endpoints of each bounded open interval and for the finite endpoints of both kinds of half-line. Its general positive-/negative-infinity identities apply to the corresponding rays and to the whole real line, using their standard tail-membership facts. Together these cover every `-infinity <= a < b <= +infinity` source interval and both endpoint directions.

The bridge transports domain-wide point derivatives to eventual derivatives by proving that the source domain belongs to its approach filter. It transports both input and output limits through the Chapter 4 reference equivalence. The output's nonvacuity is supplied by the endpoint filter's established nontriviality. The bridge does not impose global denominator nonvanishing, endpoint continuity/differentiability, numerator limits in the infinite branches, or any additional smoothness.

After the owner confirmed the final source was stable, I independently ran `./lake-local env lean Chapter05LHopitalDraft.lean` from the isolated workspace root. It exited 0 with no warnings or errors. The two principal theorem reports and recursive namespace audit returned:

```text
'Rudin.PMA.Chapter05.pma5_13' depends on axioms: [propext, Classical.choice, Quot.sound]
'Rudin.PMA.Chapter05.pma5_13_source_interval' depends on axioms: [propext, Classical.choice, Quot.sound]
PMA 5.13 draft audit: 67 declarations; only propext, Classical.choice, Quot.sound.
```

I inspected the audit implementation: it collects all constants in the Chapter 5 namespace and recursively checks their axiom dependencies against exactly the three permitted standard axioms, raising an error for any other dependency. A whole-file forbidden-token scan for proof placeholders, `native_decide`, or new axiom declarations returned no matches.

The final 376-line source hash was unchanged before and after validation:

```text
fcdfd806b3a52876c0aa465f293b46dfcf315604f4fb33b846253755840d8ca0  rudin/Chapter05LHopitalDraft.lean
```

The toolchain is Lean 4.34.1 with Mathlib pinned to `d13f23b723b8a846827a245b89c10fc7d3f11612`. No source changes were made by this reviewer. No blocker remains for this standalone node review; chapter integration and its build are separate root-owned checks.
