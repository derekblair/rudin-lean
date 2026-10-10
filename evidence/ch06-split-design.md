# Native interval restriction and additivity (PMA 6.12(c))

The parent approved the source contract before implementation: for `a<c<b`, source Stieltjes integrability on `[a,b]` implies integrability on both pieces, and the integral is their sum. The implementation proves the stronger ordered-endpoint version `a≤c≤b`, without adding continuity, strict integrator monotonicity, or a backend integral.

For a native finite partition `P`, use the two weakly monotone chains `min(P.point i,c)` and `max(P.point i,c)`. They have the same number of cells as `P` and the required piece endpoints. A cell stays unchanged on its side, collapses to zero width on the other side, or splits at `c`. The raw integrator increments telescope even at discontinuities; the shared value `α(c)` cancels exactly.

Closed-cell infimum and supremum inclusion proves

`L(P) ≤ L(left(P)) + L(right(P))`, and

`U(left(P)) + U(right(P)) ≤ U(P)`.

Each piece gap is therefore at most the parent gap. The native epsilon-gap criterion gives both restrictions. Their integral sum lies between the original lower and upper sums for every partition, as does the parent integral. Arbitrarily small parent gaps force the two real values to coincide.

This argument handles repeated points and endpoint cuts directly, and needs no separate sorted-node insertion, concatenation, or claim of measure equivalence. Only the assigned draft and this evidence file are written; integration into production remains the parent's responsibility.

## Requested converse helper

The parent subsequently requested the converse for the finite-discontinuity proof. `splitAppendPartition P Q` concatenates both complete native node arrays with `Fin.append`, retaining the common endpoint twice. The resulting duplicate cell has zero raw weight. A generic finite path-cost identity proves exact additivity of both lower and upper sums; these equalities need no boundedness, continuity, or monotonicity hypotheses.

Boundedness on the pieces combines using the maximum of their two bounds. Monotonicity of the integrator combines by comparing across the shared point. Two partitions with gaps below `ε/2` concatenate to a partition with gap below `ε`, proving `split_rsIntegrable_append`. `split_append` packages both integrability and integral additivity. The original forward theorem remains `pma6_12_split`, while `split_ordered` supplies cuts at either endpoint.

## Validation

At 2026-10-10 16:19 UTC, roughly five minutes after the assignment began, the complete 337-line draft compiled with exit zero and no warnings. Its SHA256 is `d235d56777fc5e5a25db12e834769fd2192273d55a9d5921ceb80b857499a888`. The lexical scan found no proof placeholders, custom axioms, opaque or unsafe declarations, or `native_decide`. The stable file was submitted to the parent and independent reviewer. The calculus worker separately owns the standalone zero-interval helper; no duplicate implementation was made here.

Transitive axiom checks passed for ten public splitting/concatenation results, including both final directions: only `propext`, `Classical.choice`, and `Quot.sound` occur.
