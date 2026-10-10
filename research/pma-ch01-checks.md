# Chapter 1 verification log

Pinned Lean 4.34.1 and Mathlib d13f23b723b8a846827a245b89c10fc7d3f11612.
Every completed node is typechecked and followed by `lake build` before its local commit.
Independent back-translations are supplied by the fidelity review agent; Mathlib comparisons
are explicit wrapper proofs or equivalence lemmas in the chapter.

Source checked against the third edition PDF hosted by [Lehman College](https://www.lehman.edu/faculty/rbettiol/lehman_teaching/2020mat320/baby_Rudin.pdf).
The inventory incorrectly says 1.2 is absent: it is a remark on rational incompleteness,
folded into 1.1 under PROGRAM.md's rule for remarks. The requested target count stays 37.

| Node | Independent back-translation and fidelity | Reference/probe |
|---|---|---|
| PMA-1.1 | PASS: every rational has square unequal to 2; each positive rational below/above the threshold has a larger/smaller witness on the same side. | `irrational_sqrt_two`, `irrational_sqrt_ratCast_iff_of_nonneg`; witnesses verified by rational algebra. |
| PMA-1.3 | PASS: Membership, empty sets, inclusion, strict inclusion and mutual-inclusion equality match the source. | Explicit iff comparisons to Set membership/emptiness/subset/ssubset/equality. |
| PMA-1.4 | PASS: The chapter notation denotes all rational numbers. | Alias of ℚ; every element has an integer numerator and nonzero integer denominator. |
| PMA-1.5 | PASS: Irreflexivity, trichotomy and transitivity give exactly one of the three source alternatives. | Pairwise exclusion proof; every Mathlib LinearOrder satisfies these axioms. |
| PMA-1.6 | PASS: An ordered carrier is equipped with a relation satisfying the preceding order axioms. | Construction from LinearOrder; rational order iff positive difference. |
| PMA-1.7 | PASS: Bounds use non-strict inequalities and boundedness asserts existence of such a bound. | Definitional iff comparisons to upperBounds, lowerBounds, BddAbove and BddBelow. |
| PMA-1.8 | PASS: A supremum/infimum is a bound admitting no strictly better bound; uniqueness included. | Iff proofs against IsLUB/IsGLB under LinearOrder. |
| PMA-1.9 | PASS: The rational gap has exact bound sets but no rational endpoints; the negative rational interval and positive reciprocal examples include all membership distinctions. | upperBounds/lowerBounds classification; isLUB_Iio/Iic; exists_nat_one_div_lt. |
| PMA-1.10 | PASS: Every nonempty subset bounded above has a supremum in the carrier. | ConditionallyCompleteLinearOrder comparator; ℚ fails the property by node 1.9. |
| PMA-1.11 | PASS: Every nonempty bounded-below subset has an infimum equal to the supremum of its lower bounds. | isLUB_lowerBounds equivalence with IsGLB; one common witness returned. |
| PMA-1.12 | PASS: Closure is in operation types; commutativity, associativity, identities, inverses and distributivity reproduce every A/M/D clause, including 1≠0. | Mathlib Field implies the predicate; Field.ofMinimalAxioms reconstructs a Field preserving primitive operations. |
| PMA-1.13 | PASS: Field notation, natural powers and the rational field agree with the remarks. | sub_eq_add_neg, div_eq_mul_inv, power recursion, generic field axioms specialized to ℚ. |
| PMA-1.14 | PASS: Additive cancellation, uniqueness of identity/inverse and double negation hold using only additive axioms. | AddCommGroup lemmas add_left_cancel, eq_neg_of_add_eq_zero_right, neg_neg. |
