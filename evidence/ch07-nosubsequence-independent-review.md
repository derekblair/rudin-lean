# Independent final review: PMA 7.20

Reviewer: root; author: ch6_production. **ACCEPT** on 2026-10-10.

Read every line of canonical `Chapter07/NoSubsequence.lean`, SHA256 `a0f5e92e41fe61bbda351ab4a0497ef621ec7f3ceb7f136f742dfaca2c69f7b6`, and compared the concrete type with the accepted inventory and pre-proof contract. Positive frequencies are explicitly reindexed by n+1. Continuity, the unit bound, and nonexistence of one strictly increasing subsequence converging at every point of the entire interval [0,2π] are all retained. The equivalent bad-point theorem supplies an actual domain point with no real limit, not a totalized-limit inequality.

The proof uses exact cosine integrals to establish sine orthogonality, then the constant positive squared-distance integral 2π. Consecutive terms of a hypothetical strict subsequence have pointwise squared difference tending to zero, bounded by 4; pinned Mathlib dominated convergence contradicts that positive integral. All measure-integral uses are internal to this counterexample. This does not replace a native Chapter 6 claim or certify Chapter 11.

Fresh independent `./lake-local env lean Chapter07NoSubsequenceRootProbe.lean` passed without warnings. Its two clients exclude a uniformly convergent strict subsequence and expose a bad point for the actual Real.sin formula. Recursive audits found 16 imported chapter declarations and two fresh client declarations, with only propext, Classical.choice, and Quot.sound. The source hash remained exact. No source edits or protected-file changes occurred.
