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
| PMA-1.15 | PASS: Nonzero multiplicative cancellation, uniqueness of identity/inverse and double inversion follow from multiplication axioms. | GroupWithZero lemmas; every clause has the source nonzero restriction. |
| PMA-1.16 | PASS: Multiplication by zero, no zero divisors, single/double negation identities match all field consequences. | zero_mul, mul_eq_zero, neg_mul/mul_neg, neg_mul_neg. |
| PMA-1.17 | PASS: The strict field order is preserved by translation and positive products are positive; sign terminology is explicit. | pma_ordered_field_axioms_iff compares exactly to IsStrictOrderedRing. |
| PMA-1.18 | PASS: Negation reverses sign, signed multiplication preserves/reverses strict inequalities, nonzero squares and 1 are positive, inverses reverse positive order. | Ordered-field reference lemmas, including sq_pos_of_ne_zero and inv_lt_inv₀. |
| PMA-1.19 | PASS: ℝ satisfies field/order/LUB contracts and contains an injectively and order-preservingly embedded rational subfield. | Mathlib ℝ, isLUB_csSup, Rat.castHom/cast_injective/cast_lt; existing construction reused for the existence theorem. |
| PMA-1.20 | PASS: A positive real multiple by some positive integer exceeds any prescribed real; a rational lies strictly between any two distinct ordered reals. | exists_nat_gt and exists_rat_btwn; positive ℕ denotes positive integers. |
| PMA-1.21 | PASS: Every positive real has a unique positive nth root for n>0; the unnumbered multiplicativity corollary is included. | Real.rpow_inv_natCast_pow, pow_left_inj₀, Real.mul_rpow; source printed positivity omission corrected explicitly. |
| PMA-1.22 | PASS: positive reals have the prescribed greedy decimal digits and are the supremum of finite truncations; every arbitrary digit expansion determines a unique real supremum. | Int.floor bounds/division/modulo, finite geometric bound, isLUB_csSup; equality of digit partials and floor truncations proved. |
| PMA-1.23 | PASS: Extended reals are finite reals and two infinities; order, finite/sign-guarded arithmetic, suprema/infima and failure of field inverses match all conventions. | EReal cases/order/arithmetic; complete-lattice bounds; real unbounded images have infinite endpoints. |
| PMA-1.24 | PASS: Complex numbers are exactly ordered real pairs with coordinate equality, addition and the prescribed multiplication. | Complex structure extensionality and definitionally identical pair operations. |
| PMA-1.25 | PASS: The complex pair operations satisfy every field axiom, with the prescribed zero and one. | All A/M/D clauses match pmaFieldAxioms ℂ; Mathlib complex Field instance. |
| PMA-1.26 | PASS: Real-axis pairs preserve arithmetic and injectively identify the real field inside the complex field. | Coordinate formulas; ofReal_inv; real-part injectivity. |
| PMA-1.27 | PASS: The imaginary unit is the pair (0,1). | Definitional comparison with Complex.I. |
| PMA-1.28 | PASS: The square of the imaginary unit is minus one. | Complex.I_sq. |
| PMA-1.29 | PASS: Every ordered pair (a,b) has representation a+bi. | Coordinate extensionality with the source pair multiplication. |
| PMA-1.30 | PASS: Conjugation negates the imaginary coordinate; real and imaginary parts return the respective real coordinates. | Definitional comparisons with conj/re/im. |
| PMA-1.31 | PASS: Conjugation preserves sums/products; sum/difference with conjugate recover parts; the product is nonnegative real and positive off zero. | Ring-hom mapping; Complex.add_conj/sub_conj/mul_conj and normSq positivity. |
| PMA-1.32 | PASS: Absolute value is the nonnegative real square root of the real conjugate product. | Real.sqrt normSq is definitionally the norm; nonnegative-square characterization proved. |
| PMA-1.33 | PASS: All five modulus properties are present: positivity/zero, conjugation, product, real-part bound and triangle inequality. | norm_pos_iff/zero/mul/add; Complex.norm_conj and abs_re_le_norm. |
| PMA-1.34 | PASS: Finite complex summation is the sum of n entries. | Fin n indexing represents the source n-term list; zero/successor unfolding verified. |
