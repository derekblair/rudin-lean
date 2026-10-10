# PMA 7.20 design and statement acceptance

Root independently inspected the complete typed contract SHA256
`e3221806d5966935c0caec100d69c450e5493ef215214bd9698c8e4c944e0d8e`
and accepted it against the approved inventory before proof work began.
The positive-frequency reindexing is explicit: zero-based term `n` is
`sin((n+1)*x)`. The full domain is `[0,2π]`; one strictly increasing index
map must work at every point. Continuity and the common absolute bound one
are separate required conjuncts. The contract compiled successfully.

Proof plan: squared differences of consecutive terms of a hypothetical
pointwise-convergent subsequence tend to zero at every interval point and
are bounded by four. Mathlib's dominated convergence theorem makes their
measure integrals tend to zero. Orthogonality of distinct positive integer
sine frequencies makes every such integral exactly `2π`, a contradiction.

Pinned API: `MeasureTheory.tendsto_integral_of_dominated_convergence`,
`intervalIntegral.integral_comp_mul_left`, the exact sine/cosine antiderivative
integrals, and elementary trigonometric identities. These library facts include
measure theory which appears later in the textbook; the source itself invokes
11.32. This proof does not depend on or claim a formalization of Chapter 11.
The final conclusion contains no integral, so a measure integral is only an
internal proof tool; no native Chapter 6 integral assertion is being replaced.
No book text or proof text was copied.

## Completed proof delivery

Canonical module: `rudin/Rudin/PMA/Chapter07/NoSubsequence.lean` (190 lines),
SHA256 `a0f5e92e41fe61bbda351ab4a0497ef621ec7f3ceb7f136f742dfaca2c69f7b6`.
The final draft is byte-for-byte identical. Both the direct draft compilation and
`./lake-local build Rudin.PMA.Chapter07.NoSubsequence` passed with no warnings or
errors; the latter reported 8,924 jobs. The principal `pma7_20` has all accepted
conjuncts. The explicit `sineSequence_subsequence_has_bad_point` theorem proves
the equivalent bad-point quantifiers for every strict subsequence. The two small
probes distinguish constant-index repetitions from strict subsequences and confirm
that convergence at the zero endpoint does not contradict failure elsewhere.

`Chapter07NoSubsequenceAuditScratch.lean` independently instantiates the bad-point
statement with explicit sine functions and the explicit full interval. Its fresh
run exited zero and recursively audited all 16 imported Chapter 7 declarations
against only `propext`, `Classical.choice`, `Quot.sound`. A comment/string-stripped
scan found no forbidden proof/declaration token. Earlier failed elaborations were
ordinary local proof development and are not completion claims. No resistant
mathematical case remains. Independent final review is requested separately;
this author record is not that review or the later chapter hostile gate.
