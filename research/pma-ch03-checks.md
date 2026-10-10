# Chapter 3 verification log

Source and node scope: pma-ch03-inventory.md. Independent review: pma-ch03-fidelity.md.
Each node is typechecked, independently back-translated, compared to Mathlib,
and followed by a passing default build and namespace axiom audit before its local commit.

| Node | Independent fidelity verdict and reference |
|---|---|
| PMA-3.1 | PASS: literal metric convergence, divergence, centered boundedness, all five complex examples, and positive-real ambient-space contrast. |
| PMA-3.2 | PASS: finite neighborhood exceptions, uniqueness, boundedness, and a sequence in the limit-point set. |
| PMA-3.3 | PASS: all four algebra operations plus reciprocal with termwise and limit nonzero guards. |
| PMA-3.4 | PASS: Euclidean coordinate equivalence, vector sum, real inner product, and convergent scalar sequence. |
| PMA-3.5 | PASS: strictly increasing subsequence indices, actual composition, subsequential limit, every-subsequence equivalence, cluster-point reference. |
| PMA-3.6 | PASS: compact-set membership and bounded Euclidean subsequences. |
| PMA-3.7 | PASS: closed set of all subsequential limits. |
| PMA-3.8 | PASS: literal two-index Cauchy criterion and `CauchySeq` reference. |
| PMA-3.9 | PASS: `ENNReal` diameter, pairwise supremum reference, tail range, unqualified Cauchy equivalence. |
| PMA-3.10 | PASS: diameter unchanged by closure, nonempty decreasing compact stages, unique intersection point. |
| PMA-3.11 | PASS: convergent implies Cauchy, compact Cauchy convergence, Euclidean equivalence. |
| PMA-3.12 | PASS: literal sequential completeness, `CompleteSpace` reference, compact/Euclidean/closed cases, rational incompleteness. |
| PMA-3.13 | PASS: consecutive non-strict inequalities, increasing/decreasing alternative, `Monotone`/`Antitone` references. |
| PMA-3.14 | PASS: monotonic hypothesis and convergence iff boundedness. |
| PMA-3.15 | PASS: eventual real thresholds for both infinities and real-filter/EReal comparators. |
| PMA-3.16 | PASS: all extended subsequential limits, their supremum/infimum, and filter limsup/liminf comparators. |
| PMA-3.17 | PASS: membership, eventual strict bounds beyond the extremum, and unique characterization for both extrema. |
| PMA-3.18 | PASS: arbitrary surjective rational enumeration, all real limits and both infinities; exact shifted oscillatory formula; finite-limit equivalence. |
| PMA-3.19 | PASS: eventual inequality and both extended extrema. |
| PMA-3.20 | PASS: all five limits, exact positive-index formulas, and each required parameter guard. |
| PMA-3.21 | PASS: inclusive block sums, zero-index partial sums, positive-index Icc bridge, ordinary sums/convergence/divergence, explicit conditional-filter references. |
| PMA-3.22 | PASS: complete complex Cauchy criterion with inclusive blocks and the displayed `≤ε`. |
| PMA-3.24 | PASS: nonnegative real terms and bounded partial sums. |
| PMA-3.25 | PASS: eventual norm comparison and eventual nonnegative divergent lower comparison. |
| PMA-3.26 | PASS: sum for every `0≤x<1`, including zero, and divergence for every `x≥1`. |
| PMA-3.27 | PASS: positive indices, nonnegative terms including zero, non-strict decrease, exact condensation weights and indices. |
