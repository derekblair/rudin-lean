# Independent Chapter 1 fidelity review

Reviewer: separate agent from all statement/proof authors. Date: 2026-10-09.

## Sources and scope corrections

The inventory source path is absent on bakkie and the expected path on xanthe did not contain the file. A third-edition scan was obtained for read-only checking from [Lehman College's course copy](https://www.lehman.edu/faculty/rbettiol/lehman_teaching/2020mat320/baby_Rudin.pdf). PDF title is *Rudin (1976) Principles of Mathematical Analysis.djvu*. The locally inspected scan is `/tmp/rudin-fidelity/pma3.pdf`; book page numbers are used below.

The inventory incorrectly says 1.2 does not exist. Printed page 2 has **1.2 Remark**. Under PROGRAM.md's rule that remarks are folded into their nearest node, its mathematical content is covered by 1.1 and 1.9: rational numbers fail the least-upper-bound property. The requested 37 target nodes are retained; this is a correction to the inventory explanation, not a silently omitted result.

On printed page 10, 1.21's uniqueness sentence really omits the qualification that the root is positive. This was checked in a rendered image, not inferred from OCR. Unrestricted uniqueness is false for even exponents. The inventory's intended unique-positive-root statement is the correct reading, consistent with the surrounding root discussion. A negation probe below certifies the counterexample to the unrestricted printed version. **Supersession ([#19](https://github.com/derekblair/rudin-lean/issues/19)):** The omission claim and its claimed visual confirmation above were wrong: Theorem 1.21 on printed p. 10 says “one and only one positive real y”. The probe refutes only uniqueness with positivity removed, not the printed theorem; the correction is recorded in `PROGRESS.md` (PR #18).

OCR confuses `<` and `≤` in several definitions and examples. Rendered printed page 4 confirms that bounds are non-strict; 1.9(b) uses rational `r < 0` versus rational `r ≤ 0`. Rendered printed page 15 confirms 1.35 is the **squared** complex Cauchy–Schwarz inequality, with conjugation on the second sequence.

## Landscape recheck

The recheck used indexed web search and GitHub's public repository-search/tree APIs on 2026-10-09. The stronger API search located prior Lean corpora that indexed search did not surface. No complete zero-placeholder implementation of all 37 requested main-text nodes was established. This is a bounded source inspection, not proof of nonexistence or a build certification of third-party projects.

- [sinianluoye/LeanOfRudinAnalysis](https://github.com/sinianluoye/LeanOfRudinAnalysis/tree/master/Rudin/Chapter1) has substantial Chapter 1 work: set/order/field definitions, rational examples, a Dedekind-cut real construction, rational powers/nth roots, extended reals, and complex operations/modulus. Current source contains an actual placeholder in `Examples.lean` at `b_has_no_min`; its complex file ends after the real-part modulus bound. The inspected tree contains no complete final complex Schwarz/Euclidean section or decimal expansion coverage. It is substantial prior partial formalization, not absent work.
- [Neuron-Group/RudinAnalysis](https://github.com/Neuron-Group/RudinAnalysis/tree/main/RudinAnalysis/TheRealAndComplexNumberSystems) has opening rational-square results, ordered-set bounds/completeness, field/ordered-field laws, and a Dedekind-cut ordered-field construction. Those five substantive Chapter 1 files contain no textual proof placeholders. The inspected tree has no Chapter 1 extended-real, complex, decimal or Euclidean-space files, so it does not cover the full requested chapter. No third-party build was run.
- Despite its repository name, [hbghlyj/rudin-chapter-1-lean](https://github.com/hbghlyj/rudin-chapter-1-lean) describes selected exercises in its primary README. Its Chapter 1 files cover algebra, real/complex/exponential and Euclidean exercise material. This overlaps individual main-text results, but does not provide the requested complete numbered-node inventory. No third-party build was run.
- [Naproche's own formalizations page](https://naproche.github.io/formalizations.html) reports a student formalization of the first five chapters in 2022, distributed with Isabelle/Naproche. This is relevant prior formalization in another system.
- [ProofNet-Verified's primary README](https://github.com/marcusm117/ProofNet-Verified/blob/main/README.md) and the [UW Math AI group's own page](https://github.com/uw-math-ai) describe textbook-exercise formalization that includes Rudin, rather than full numbered-main-text coverage.

Mathlib supplies the underlying mathematics. The project's contribution is complete requested node coverage and an explicit fidelity/axiom audit trail; no claim that Chapter 1 had never previously received Lean attention is supported.

## Source contracts (brief paraphrases, no proof text)

| Node | Required mathematical content |
|---|---|
| 1.1 | No rational square equals 2; positive rationals below/above that threshold have no maximum/minimum. |
| 1.3 | Membership, empty/nonempty set, subset, proper-subset witness, equality by mutual inclusion. |
| 1.4 | Rational-number notation. |
| 1.5 | Exactly one of less/equal/greater; transitivity. |
| 1.6 | A carrier equipped with such an order; rational order via positive difference. |
| 1.7 | Non-strict upper/lower bounds; existence of bounds. |
| 1.8 | Upper bound with no smaller bound; lower bound with no larger bound; uniqueness. |
| 1.9 | Rational square-threshold gap; two zero-supremum examples with different membership; reciprocal-integer supremum/infimum. |
| 1.10 | Every nonempty bounded-above subset has a supremum in the carrier. |
| 1.11 | Nonempty bounded-below sets have infima; supremum of their lower bounds is that infimum. |
| 1.12 | Commutative, associative, closed addition/multiplication; identities; additive inverses; nonzero multiplicative inverses; `1 ≠ 0`; distributivity. |
| 1.13 | Standard arithmetic abbreviations and powers; rationals satisfy field axioms. |
| 1.14 | Additive cancellation; uniqueness of zero and negatives; negation involution. |
| 1.15 | Nonzero multiplicative cancellation; uniqueness of one and inverse; inverse involution. |
| 1.16 | Zero product law; nonzero products; negation sign identities. |
| 1.17 | Field order with translation preservation and positive-product closure; positive/negative terminology. |
| 1.18 | Negation reverses sign; positive/negative multiplication preserves/reverses order; nonzero squares positive; inverse reverses positive order. |
| 1.19 | A complete ordered field exists; rational arithmetic and positivity embed faithfully. |
| 1.20 | Positive-real Archimedean multiples; strictly-between rational density. |
| 1.21 | Unique positive real natural-number root for a positive input and positive exponent. |
| 1.22 | Positive reals are suprema of decimal truncations; bounded digit expansions determine reals. |
| 1.23 | Extended-real carrier/order/completeness and finite-real infinity arithmetic conventions. |
| 1.24 | Complex real pairs; coordinate equality; pair addition/multiplication. |
| 1.25 | Pair operations satisfy field axioms, with specified zero/one pairs. |
| 1.26 | Real-axis pair addition/multiplication and faithful embedding. |
| 1.27 | Imaginary unit is the pair `(0,1)`. |
| 1.28 | Imaginary unit squared is minus one. |
| 1.29 | Every real pair has representation `a + bi`. |
| 1.30 | Conjugation negates second coordinate; real/imaginary coordinate projections. |
| 1.31 | Conjugation preserves sums/products; sum/difference formulas; conjugate product real nonnegative, positive off zero. |
| 1.32 | Modulus is the nonnegative square root of conjugate product. |
| 1.33 | Positivity/zero, conjugate invariance, multiplicativity, real-part bound, triangle inequality. |
| 1.34 | Finite complex summation notation. |
| 1.35 | Squared norm of finite conjugated-product sum is bounded by product of squared-norm sums. |
| 1.36 | Finite real tuples; coordinate addition/scaling; dot product; Euclidean norm. |
| 1.37 | Nonnegative definite homogeneous norm; dot-product bound; triangle and distance-triangle inequalities. |
| 1.38 | Norm difference defines a metric; one/two dimensional identifications preserve real/complex modulus. |

## Completed independent back-translations

### PMA-1.1 — PASS

`rationalBelowSqrtTwo` consists exactly of positive rationals whose square is strictly below 2. `rationalAboveSqrtTwo` uses strict positivity and square strictly above 2. The universal square theorem excludes a rational square equal to 2. The two extremum theorems produce a strictly larger/smaller element of the respective set for every supplied element. This matches all three source claims. The source's explanatory 1.2 remark is folded here as described above.

Reference comparison: the square obstruction derives from Mathlib's irrational square-root characterization and `irrational_sqrt_two`; the explicit order witnesses retain rational domains throughout. Hypotheses are nonvacuous: rational 1 is in the first set and rational 2 in the second (probe pending).

### PMA-1.3 — PASS

Membership is set membership. Empty means no element. Subset means universal membership implication. Proper subset additionally produces an element in the larger set outside the smaller. Equality is characterized by mutual inclusion. All source quantifiers and the proper-subset witness agree. The reference theorem checks equivalence to Mathlib's empty set, subset, strict subset and extensional equality. `IsNonemptySet` explicitly means existence of a member; its comparator matches `Set.Nonempty` and the negation of `IsEmptySet`, completing the source terminology.

### PMA-1.4 — PASS

The alias is exactly Lean's rational type. The added theorem states every rational can be represented by integer numerator/nonzero denominator, agreeing with rational meaning without treating distinct quotient presentations as distinct rationals. Reference: `Rat.num_div_den` and `Rat.den_ne_zero`.

### PMA-1.5 — PASS

The relation is irreflexive, trichotomous and transitive. These jointly give the source's exactly-one condition: the explicit theorem excludes every pair of alternatives. Conversely the source exactly-one condition implies irreflexivity, so the formulation is equivalent rather than weaker. Mathlib linear orders satisfy the contract via `lt_irrefl`, `lt_trichotomy`, `lt_trans`. The final order-notation comparator certifies that greater-than reverses the argument order and non-strict less-than means strict less-than or equality, equivalently exclusion of the reverse strict inequality.

### PMA-1.6 — PASS

An `OrderedSet` packages a carrier, less-than relation, and order-contract witness. It does not silently require a ring or field. The rational example has less-than equivalent to positive difference, as in the source. Reference: `sub_pos`.

### PMA-1.7 — PASS

An upper bound is greater than or equal to every member; a lower bound is less than or equal to every member. Being bounded is existential availability of the corresponding bound. The non-strict inequalities are correct, including endpoints. Direct definitional equivalences to `upperBounds`, `lowerBounds`, `BddAbove`, `BddBelow` were reviewed.

### PMA-1.8 — PASS

A supremum is an upper bound admitting no strictly smaller upper bound; an infimum is a lower bound admitting no strictly larger lower bound. Comparators prove equivalence to `IsLUB`/`IsGLB` in a linear order, and uniqueness is derived. No nonexistent empty-set supremum is presumed; existence is represented separately.

### PMA-1.9 — PASS

The upper bounds of the below-threshold rational set are exactly the above-threshold set. The lower bounds of the latter are the below-threshold set together with nonpositive rationals. Both sets are bounded, while neither requested extremum exists in the rational carrier. This includes the source's stronger bound classifications, not merely a failure to identify a candidate root. The negative-rational open/closed intervals have the same supremum zero and the correct respective endpoint membership. `positiveReciprocals` explicitly quantifies natural `n > 0`, excluding division by zero, and the result states supremum one, infimum zero, and correct membership. References: `isLUB_Iio`, `isLUB_Iic`, `exists_nat_one_div_lt`, plus the independently checked 1.1 witnesses.

### PMA-1.10 — PASS

Every nonempty bounded-above subset has a least upper bound **in the same carrier**. Both premises are present. This is an existence contract rather than an assertion that a totalized supremum function is always meaningful. Reference: `IsLUB` with standard `BddAbove`.

### PMA-1.11 — PASS

For a nonempty bounded-below subset in a linear order satisfying the least-upper-bound property, there exists one element that is simultaneously the supremum of all lower bounds and the infimum of the original set. The same witness connects the two conclusions, and no real-field algebra is assumed. Reference: `isLUB_lowerBounds`.

### PMA-1.12 — PASS

The predicate lists exactly the algebraic laws: commutativity, associativity, identities, inverse existence, distinct zero/one, and distributivity. Closure is encoded by operations returning the carrier. Source left identities and formal right identities are equivalent using the explicitly stated commutativity. The inverse witnesses need no predefined negation/inversion operators. Both directions of reference comparison are provided: Mathlib fields satisfy the predicate, and `pmaFieldOfAxioms` reconstructs a `Field` with the same primitive operations via `Field.ofMinimalAxioms`. Choosing inverse notation uses only classical choice.

### PMA-1.13 — PASS

Subtraction/division, square/cube, and repeated addition by two/three agree with the explicit source abbreviations. The power-zero and successor laws extend this to all natural powers. The rational field satisfies the stated predicate. Source explanatory remarks about avoiding repeated derivations carry no extra mathematical claim. References: `sub_eq_add_neg`, `div_eq_mul_inv`, `pow_two`, `pow_succ`, standard field arithmetic.

### PMA-1.14 — PASS

Additive cancellation, right identity uniqueness, additive inverse uniqueness, and double negation are all universal over an additive commutative group, without an unnecessary field assumption. Every implication's variables and equality orientation match the source. References: `add_left_cancel`, `eq_neg_of_add_eq_zero_right`, `neg_neg`.

### PMA-1.15 — PASS

The four multiplicative analogues retain the source's nonzero premise. `GroupWithZero` is used independently of addition, generalizing the field context; the distinguished zero has the standard absorbing behavior. Cancellation and identity/inverse uniqueness are explicit. References: `mul_left_cancel₀`, `mul_inv_cancel₀`, `inv_inv`.

### PMA-1.16 — PASS

Zero times any element is zero. A zero product forces a zero factor, logically equivalent by classical contraposition to the source's product of two nonzero factors being nonzero. Negation of either factor gives the same negated product, and negating both restores the product. References: `zero_mul`, `mul_eq_zero`, `neg_mul`, `mul_neg`, `neg_mul_neg`.

### PMA-1.17 — PASS

A field with a linear order is an ordered field exactly when translating strict inequalities preserves them and products of positive elements are positive. Positivity/negativity are defined by strict comparison with zero. Commutativity makes the formal translation on the right equivalent to the source's translation on the left. `pma_ordered_field_axioms_iff` proves both directions against `IsStrictOrderedRing`; this rules out silently assuming additional order compatibility without accounting for it.

### PMA-1.18 — PASS

Positive `x` is equivalent to negative `-x`. Multiplying by positive/negative elements respectively preserves/reverses strict order. Nonzero squares and one are positive. For `0 < x < y`, the inverse of `y` is positive and strictly below the inverse of `x`. Renaming variables and using commutativity reconciles right-versus-left multiplication. References: `neg_lt_zero`, `mul_lt_mul_of_pos_right`, `mul_lt_mul_of_neg_right`, `sq_pos_of_ne_zero`, `zero_lt_one`, `inv_pos`, `inv_lt_inv₀`.

### PMA-1.19 — PASS

The actual carrier `ℝ` satisfies the explicit field, ordered-field, and least-upper-bound predicates. An injective strictly monotone ring homomorphism embeds `ℚ`; ring-homomorphism laws preserve arithmetic and zero/one, and strict monotonicity gives the source's positivity preservation. Exhibiting this concrete model proves the existential source statement without reproducing its appendix construction. References: `isLUB_csSup`, `Rat.castHom`, `Rat.cast_injective`, `Rat.cast_lt`.

### PMA-1.20 — PASS

For any positive real `x` and real `y`, some positive natural `n` has `y < n*x`. Positive naturals and positive integers parametrize the same source multiples. Between every strictly ordered pair of reals lies the image of a rational, with strict inequalities on both sides. References: `exists_nat_gt`, `div_lt_iff₀`, `exists_rat_btwn`.

### PMA-1.21 — PASS

For positive real `x` and positive natural `n`, exactly one positive real `y` has `y^n=x`. Positivity restricts the uniqueness domain explicitly, repairing the confirmed printing omission. Natural positive exponents encode the source's positive integer exponents. References: `Real.rpow_inv_natCast_pow`, `Real.rpow_pos_of_pos`, `pow_left_inj₀`. Rendered page 11 also contains an unnumbered corollary asserting multiplicativity of positive nth roots; `pma_positive_nth_root_mul` includes it using the same inverse-natural exponent and `Real.mul_rpow` under positive-factor and positive-exponent hypotheses. **Supersession ([#19](https://github.com/derekblair/rudin-lean/issues/19)):** The claimed repair of a printing omission was wrong: positivity is explicit in Theorem 1.21 on printed p. 10 (“one and only one positive real y”). The formal statement matches that restriction; the correction is recorded in `PROGRESS.md` (PR #18).

### PMA-1.22 — PASS

Truncations are floors of the scaled real divided by the scale. For positive input, the initial natural is its integer floor, and every integer candidate below the input is at most that initial value. Digits are in `Fin 10`, hence exactly zero through nine; the next scaled floor's remainder modulo ten supplies the digit. The recurrence and exact partial-sum equality tie these digit objects to the truncations. Each chosen digit is the **largest integer** that leaves the next partial sum at or below the input, as certified by the integer-candidate iff theorem. The input is the least upper bound of its truncations and canonical digit partial sums. Conversely any nonnegative integer part and infinite zero-through-nine digit sequence has bounded increasing partials with a unique real supremum. The resulting value recovers the input for the constructed expansion. This does not incorrectly assert uniqueness of digit sequences: trailing-nine expansions are admitted by the converse. Non-strict selection matches the rendered source page. References: `Int.floor_le`, `Int.lt_floor_add_one`, `Int.le_floor`, `Int.floor_div_natCast`, `Int.mul_ediv_add_emod`, `exists_pow_lt_of_lt_one`, `isLUB_csSup`.

### PMA-1.23 — PASS

The carrier is Mathlib `EReal`, with exhaustive finite-real/minus-infinity/plus-infinity cases. The explicit finite predicate means being an embedded real and its comparator is exactly exclusion of both infinities. Both infinities strictly bound every finite real. The specified finite-real addition, subtraction, division, and signed multiplication conventions are all explicitly covered. Every nonempty subset has least upper and greatest lower bounds; unbounded real sets acquire the appropriate infinite extremum. Failure of additive inverses establishes that the chosen arithmetic is not a field. Mathlib totalizes other infinity expressions, whereas Rudin states only selected conventions; the formal theorems use the source's finite/sign guards and do not claim an unstated convention is in the book. References: `EReal.rec`, coercion order lemmas, signed multiplication lemmas, `isLUB_sSup`, `isGLB_sInf`.

### PMA-1.24 — PASS

Every complex number is a pair of reals. Equality is coordinate equality, addition adds corresponding coordinates, and multiplication has real coordinate `ac-bd` and imaginary coordinate `ad+bc`. The construction is exhaustive and faithful rather than only assigning a pair-shaped notation to some complex numbers. These are definitionally the corresponding Mathlib `Complex` operations, with `Complex.ext_iff` as equality comparator.

### PMA-1.25 — PASS

All field laws hold for the very complex carrier/operations used in 1.24. The zero/one are definitionally the pairs `(0,0)`/`(1,0)`. The expanded conclusion matches the field-axiom predicate, including distinct zero/one and nonzero inverse existence. References: standard complex `Field` instance and the same individual laws as 1.12.

### PMA-1.26 — PASS

Real-axis pairs add and multiply as their underlying reals. The pair agrees definitionally with the real-to-complex coercion, and this map is injective. The inherited field coercion also preserves zero/one/inverses. No spurious identification of unequal real coordinates is introduced.

### PMA-1.27 — PASS

The imaginary unit is exactly `(0,1)`, definitionally Mathlib's `Complex.I`.

### PMA-1.28 — PASS

That same imaginary unit squared equals complex minus one. Direct reference: `Complex.I_sq`.

### PMA-1.29 — PASS

The complex pair with real coordinates `a,b` equals the complex image of `a` plus the image of `b` times the defined imaginary unit. Both coercions and multiplication are in `ℂ`; no real square-root expression is substituted. Reference: coordinate extensionality and `Complex.mul_re`/`Complex.mul_im`.

### PMA-1.30 — PASS

Conjugation leaves the real coordinate and negates the imaginary coordinate. Real/imaginary-part functions recover precisely the two coordinates. Definitional comparators establish the source operations for every pair.

### PMA-1.31 — PASS

Conjugation preserves addition and multiplication. Adding a conjugate gives the coerced real twice the real part; subtraction gives twice the imaginary unit times the imaginary part. The conjugate product equals a coerced real norm-square, which is nonnegative and positive exactly off zero. This explicitly proves the product is real, not merely that its real part is nonnegative. References: `map_add`, `map_mul`, `Complex.add_conj`, `Complex.sub_conj`, `Complex.mul_conj`, `Complex.normSq_nonneg`, `Complex.normSq_pos`.

### PMA-1.32 — PASS

Complex modulus is the nonnegative real square root of the real norm-square; the preceding node identifies that real quantity with the complex conjugate product. The specification certifies nonnegativity and the coerced square equaling the product. The definition is exactly Mathlib's complex norm, not a max-coordinate or coordinate-sum norm. Reference: definitional norm comparator and `Complex.sq_norm`.

### PMA-1.33 — PASS

Modulus is positive exactly off zero and vanishes at zero; conjugation preserves it; multiplication multiplies it; the absolute real part is bounded by it; and it obeys the triangle inequality. All source clauses are present with the right real-valued absolute values and non-strict inequalities. References: `norm_pos_iff`, `norm_zero`, `Complex.norm_conj`, `norm_mul`, `Complex.abs_re_le_norm`, `norm_add_le`.

### PMA-1.34 — PASS

Complex finite summation is indexed by `Fin n`, a zero-based enumeration of the source's `1,…,n`. The zero and append-final-element recursion check its ordered finite-sum meaning. Allowing the empty case is a harmless extension. Reference: `Fin.sum_univ_castSucc`.

### PMA-1.35 — PASS

The square of the modulus of the sum of `a_j*conj(b_j)` is at most the product of the two squared-modulus sums. Both outer and summand squares are present. Complex inner-product arguments are intentionally reversed because Mathlib conjugates its first argument; the explicit `hi` comparator proves the exact source summation orientation. References: `PiLp.inner_apply`, `RCLike.inner_apply`, `norm_inner_le_norm`, `EuclideanSpace.norm_sq_eq`.

### PMA-1.36 — PASS

The carrier is Euclidean real `k`-space, with exactly `k` coordinates. Coordinate theorems certify ordinary vector addition and real scalar multiplication; the zero-vector comparator certifies that every coordinate of the origin is zero. The inner product is the coordinate product sum and norm is the square root of sum of coordinate squares, equivalently square root of self-dot-product. `EuclideanSpace` supplies the claimed real vector-space laws. Allowing dimension zero extends the source's positive dimensions without changing them. References: `PiLp.inner_apply`, `EuclideanSpace.norm_eq`.

### PMA-1.37 — PASS

All six properties are present: nonnegative norm, zero norm iff zero vector, scalar homogeneity with real absolute value, absolute dot-product bound, sum triangle inequality, and the three-point difference triangle inequality. The same norm/inner product defined in 1.36 is used throughout. References: `norm_nonneg`, `norm_eq_zero`, `norm_smul`, `abs_real_inner_le_norm`, `norm_add_le`, `norm_sub_le_norm_sub_add_norm_sub`.

### PMA-1.38 — PASS

Distance is the norm of the difference. It agrees with the inherited metric, and all four metric properties are certified. The real-line identification extracts its only coordinate and preserves norm as real absolute value. The plane identification maps coordinates zero/one to the complex real/imaginary pair and preserves modulus. Both are bijective real linear isometries, so this covers the source's dimensional identifications substantively. References: `dist_eq_norm`, metric laws, `PiLp.equivOfUnique`, `Complex.orthonormalBasisOneI`.

## Prove-or-disprove and nondegeneracy probes

The separately authored `Chapter01Probes.lean` contains 23 kernel-checked declarations. It was compiled successfully against a concatenated snapshot of the completed statements/proofs and then independently through its ordinary import of the integrated `Rudin.PMA.Chapter01` module. The final default `lake build` also imports the probes through the axiom-audit module.

The probes establish nonvacuous rational gap sets, reject reflexive relations as strict orders, accept endpoint equality in bounds, reject self proper-subsets, derive failure of the rational least-upper-bound property, prove that an empty real subset has no least upper bound and thus cannot be included in an unqualified completeness contract, check the open/closed zero endpoints and reciprocal one/zero membership, and disprove cancellation without a nonzero factor and an incorrectly directed positive inverse inequality.

A concrete positive square has both roots `1` and `-1`, certifying failure of the source's unrestricted uniqueness sentence. Complex probes check imaginary-coordinate conjugation, modulus of the 3–4 pair equal to 5, a nonzero imaginary unit with zero real part, its conjugated singleton sum equal to one, exact normalization of squared Schwarz for that unit, a terminating decimal with digits two/five/zero under the non-strict convention, and real-plane Euclidean norm of the 3–4 vector equal to five. An intentionally unsquared right-hand side is formally disproved using scalar two. **Supersession ([#19](https://github.com/derekblair/rudin-lean/issues/19)):** Attributing unrestricted uniqueness to the source was wrong: Theorem 1.21 on printed p. 10 says “one and only one positive real y”. The ±1 probe remains valid only against uniqueness with positivity removed; the correction is recorded in `PROGRESS.md` (PR #18).

On three samples (rational square obstruction, unique positive root, complex triangle inequality), `fail_if_success` commands attempt to establish the negation with `aesop`; all attempts fail and the matching correct statements are then proved. Failed automation alone is weak evidence, so the concrete counterexamples and direct equivalence checks supply the substantive probe evidence. No probe assumes the truth of a negative result or inserts a placeholder proof.

## Final review status

All 37 target nodes have independent back-translation and source comparisons. Final integrated declarations, including the added nonempty, order-notation, finite-extended-real and zero-vector comparators, were reread and pass the same semantic contracts. All 15 inventory definitions plus every other introduced definition were checked. All 18 mathematical theorem/proposition/example nodes were examined beyond the minimum sampling rule. Source 1.2 is folded into neighboring coverage and the 1.21 printing error is explicitly repaired. Per-node compilation and final chapter axiom audit/build are the integrating agent's separate verification obligations; this report does not substitute its semantic review for those checks. **Supersession ([#19](https://github.com/derekblair/rudin-lean/issues/19)):** The 1.21 printing-error claim was wrong: printed p. 10 already states “one and only one positive real y”. The correction concerns our attribution, not Rudin's theorem, and is recorded in `PROGRESS.md` (PR #18).
