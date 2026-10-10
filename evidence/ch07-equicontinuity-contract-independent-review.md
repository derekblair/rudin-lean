# Independent pre-proof review: PMA-7.19 and PMA-7.21–7.25

Reviewer: oscillation, 2026-10-10. Author: curve_hostile. The reviewer authored none of these contracts. Actual source read in full: `rudin/Chapter07EquicontinuityDraft.lean`, SHA256 `4f3b28d22bfe251c3cac596b7a24d88390bbefcc5f98ade7b67492cdad322f74`. A fresh independent `./lake-local env lean Chapter07EquicontinuityDraft.lean` exited 0 with no warnings. Comparison sources: accepted `research/pma-ch07-inventory.md` and its independent source-review record.

**ACCEPTED as faithful typed contracts; root oversight requested before proof implementation.** This review found no omitted conjunct or strengthened hypothesis.

| Node | Actual-type checks |
| --- | --- |
| 7.19 | Pointwise bounds depend on the point but cover all indices; a uniform bound covers every index and domain point. Attached countable-subset selection has a strictly increasing index function, a genuine pointwise limit, no topology on the arbitrary domain, and no exclusion of finite or empty subsets. |
| 7.21 | The exact peak is `x²/(x²+(1-(n+1)x)²)`, so all source indices are positive. It includes continuity on `[0,1]`, bounds between 0 and 1, uniform boundedness, pointwise limit zero, exact peak 1 at reciprocal index, membership of that point in the domain, and nonexistence of *any* uniformly convergent subsequence to *any* limit. Both boundedness observations are present. The n²-scaled 7.6 bump, cast to ℂ, is an allowed witness for pointwise convergence of individually bounded functions without uniform boundedness. The source inventory explicitly permits reuse of 7.6; no additional exercise is introduced. |
| 7.22 | Epsilon/delta quantifiers use one δ across all pairs of domain points and all family members. The contract includes comparison to `UniformEquicontinuousOn`, individual uniform continuity, and failure for the exact peak family. It does not silently substitute pointwise equicontinuity. |
| 7.23 | The countable-set diagonal conclusion has both strict monotonicity and pointwise convergence at every point. There is no continuity, nonemptiness, or ambient-domain topology assumption. |
| 7.24 | The domain is an arbitrary compact subset of a metric space; every complex term is continuous there, and uniform convergence yields the source's uniform equicontinuity for the entire sequence. No conclusion is weakened to a tail. |
| 7.25 | Only pointwise boundedness is an input. Both full-sequence uniform boundedness and existence of a strictly indexed, uniformly convergent subsequence are conclusions. The limit is continuous on the compact subset. The complex codomain and empty/singleton compact subsets are retained. |

The concrete n² bump proof should consume or compare with completion_evidence's 7.6 witness instead of creating inconsistent index conventions. This is coordination work, not a statement blocker. Parent/root has been notified of this acceptance and the exact source hash. This record does not certify future proofs, axioms, or a hostile gate. No draft or protected source was edited by the reviewer.
