# Independent proof review: full PMA 6.12

Verdict: **ACCEPTED** for all five clauses of `pma6_12`, together with the stronger endpoint-inclusive split and concatenation helpers. No added integrator continuity, hidden premise, incorrect boundary convention, or unresolved obligation was found.

The reviewer authored neither the split proofs nor the final properties wrapper. This review reads their actual proof bodies and combines them with the separately completed independent review of the algebra and order helpers in `ch06-integrability-independent-review.md`.

## Exact reviewed snapshots and validation

- `rudin/Chapter06SplitDraft.lean`: 337 lines; SHA256 `d235d56777fc5e5a25db12e834769fd2192273d55a9d5921ceb80b857499a888`.
- `rudin/Chapter06PropertiesDraft.lean`: 26 lines; SHA256 `a50ff1516880bd4110cb95e7b81baf44a64980ca2400aa1e377f2b093e8634c1`.

Both files independently compiled with `./lake-local env lean <filename>` from the isolated root, returning exit 0 without warnings or errors. The source hashes were unchanged after compilation and review. The imported `Rudin/PMA/Chapter06/Split.lean` snapshot has exactly the same hash as the reviewed split draft.

Read-only audits passed each source through Lean standard input with appended `#print axioms` commands; no source edit was needed. `pma6_12`, `split_ordered`, `pma6_12_split`, `split_append_lowerSum`, `split_append_upperSum`, `split_rsIntegrable_append`, and `split_append` each depend only on `propext`, `Classical.choice`, and `Quot.sound`. Both audit compilations exited 0. A full-source scan found no `sorry`, `admit`, `native_decide`, custom `axiom`, or `unsafe` token.

## Restriction and additivity, including endpoint cuts

`splitLeftPartition` clamps the old partition points above the cut using minimum; `splitRightPartition` clamps points below the cut using maximum. Both retain the old cell count and permit repeated points, so the construction remains valid for cuts at either endpoint and for an entirely degenerate interval.

The cell-cost argument distinguishes cells wholly to the left, wholly to the right, and crossing the cut. A collapsed cell contributes zero because its raw integrator increment is zero. In a crossing cell, the infimum on either smaller closed cell is at least the infimum on the old cell, while its supremum is at most the old supremum. Boundedness supplies the required conditional infimum/supremum hypotheses; nondecreasingness supplies nonnegative integrator increments. The two increments telescope exactly through the actual value of the integrator at the cut. No continuity or one-sided value replacement is used, so jumps at the cut are treated by the native Darboux definitions.

Summing gives the lower-sum and upper-sum comparisons. Each smaller gap is at most the original gap because the other smaller gap is nonnegative. The native gap criterion therefore proves integrability on both subintervals. Bounding the original integral and both smaller integrals by these same sums makes their additivity error arbitrarily small and hence zero.

`split_ordered` uses weak inequalities on both sides of the cut and proves restriction plus integral additivity. `pma6_12_split` specializes it to the source's strictly interior cut. Neither adds any integrator regularity to the original native integrability hypothesis.

## Concatenation and the converse

`splitAppendPartition` concatenates the complete point lists, retaining the common endpoint twice. Its cross-list monotonicity follows from the endpoint bounds of the two original partitions. The resulting extra cell has equal endpoints and therefore zero integrator increment, regardless of any discontinuity at that point.

The list path-cost calculation proves exact addition of raw lower and upper sums. It handles repeated points and zero-cell partitions without assuming strictly increasing partition points. Boundedness on the full interval follows from the maximum of the two bounds. Monotonicity on the full interval follows from each half's monotonicity, using the shared actual integrator value at the cut for cross-cut comparisons.

Concatenating partitions whose two gaps are each below half the requested error proves full-interval integrability. The forward additivity result then gives the integral identity. Both directions are therefore established natively, with no circular appeal to the unproved numbered theorem.

## Full five-clause assembly

The 26-line wrapper has type exactly the previously accepted `pma6_12_contract`. Each conjunction is populated by completed, reviewed theorems:

1. Function addition, its integral identity, arbitrary real scalar multiplication, and its identity.
2. Integral comparison under the stated pointwise order.
3. Both restricted integrability claims and interval additivity at a strictly interior cut.
4. The absolute integral bound with total integrator increment.
5. Integrator addition and positive integrator scaling, with both integrability assertions and both integral identities.

The arbitrary scalar in clause (a) is not restricted to nonnegative values. The positive scalar condition in clause (e) is the accepted source condition. Each wrapper invocation supplies precisely the required original hypotheses; the abstract algebra helper premises reviewed earlier do not become extra assumptions on `pma6_12`. All conclusions use the original native Stieltjes integral and integrability definitions.

There are no remaining blockers for these exact snapshots. The earlier scalar review's exclusion of the split proof and the complete wrapper is resolved by this report; unrelated Chapter 6 nodes are outside its scope.
