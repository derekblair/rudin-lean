# Chapter 2 verification log

Source and node scope: pma-ch02-inventory.md. Independent review: pma-ch02-fidelity.md.
Each node is typechecked, independently back-translated, compared to Mathlib,
and followed by a passing default build and namespace axiom audit before its local commit.

| Node | Independent fidelity verdict and reference |
|---|---|
| PMA-2.1 | PASS: Functions give a unique value for each input; range is exactly Set.range. |
| PMA-2.2 | PASS: Images/preimages and onto/one-to-one match Mathlib image/preimage/range/Surjective/Injective. |
| PMA-2.3 | PASS: Bijection existence is equinumerosity; its three relation laws and the equivalence-relation comparator are exact. |
| PMA-2.4 | PASS: Rudin finite/countably infinite/uncountable/at-most terminology has exact iff comparisons to Finite,Countable+Infinite,¬Countable and Countable; positive-integer shift made explicit. |
| PMA-2.5 | PASS: The integers have a bijection with naturals; Equiv.intEquivNat. |
| PMA-2.6 | PASS: Finite sets cannot have an equinumerous proper subset, and every infinite set has one; cardinality of deleting a singleton supplies the comparison. |
| PMA-2.7 | PASS: Sequences are natural-indexed functions; countably infinite sets are exactly ranges of injective sequences. |
| PMA-2.8 | PASS: An infinite subset of a countably infinite carrier inherits countability and remains infinite. |
| PMA-2.9 | PASS: Union/intersection membership matches indexed existential/universal quantification, and empty intersection is equivalent to disjointness. |
| PMA-2.10 | PASS: Both finite examples and all three (0,1]-indexed interval-family properties match the source; exact inclusion iff x≤z. |
| PMA-2.11 | PASS: All source union/intersection commutative, associative, distributive, empty and inclusion laws are included. |
| PMA-2.12 | PASS: Countably infinite indexed sets have an infinite countable union; at-most-countable union corollary included via Set.countable_iUnion. |
| PMA-2.13 | PASS: Positive finite tuples are countably infinite and the rational corollary is included; Fin n product countability and infinitude. |
| PMA-2.14 | PASS: All binary infinite sequences are uncountable; direct diagonal contradiction matches digit set Fin 2. |
| PMA-2.15 | PASS: Distance predicate has precisely positivity/zero/symmetry/triangle axioms; MetricSpace constructor and reverse comparator preserve the distance. |
| PMA-2.16 | PASS: Euclidean, real and complex norm-difference distances and inherited subset metrics match definitions. |
| PMA-2.17 | PASS: All four interval endpoint conventions, k-cell coordinates, open/closed norm balls and convexity contract match reference definitions; all stated convex examples included. |
| PMA-2.18 | PASS: All ten topology predicates independently reviewed; AccPt/IsClosed/interior/IsOpen/Perfect/bounded/Dense iff comparators are exact, including Nonempty ambient condition for boundedness. |
| PMA-2.19 | PASS: All positive-radius neighborhoods are open balls; Metric.isOpen_ball supplies the reference. |
| PMA-2.20 | PASS: Punctured-neighborhood accumulation yields infinite neighborhood intersection; finite-set corollary included. |
| PMA-2.21 | PASS: All seven rows of four property classifications plus reciprocal 0/nonmember accumulation contrasts and real-versus-complex segment openness are included. |
| PMA-2.22 | PASS: Arbitrary-union complement equals intersection of complements, by exact indexed membership equivalence. |
| PMA-2.23 | PASS: Openness iff complement closed, through explicit source predicate comparators. |
| PMA-2.24 | PASS: Arbitrary open unions/closed intersections and finite open intersections/closed unions have all source quantifiers. |
| PMA-2.25 | PASS: Infinite shrinking open intervals intersect in singleton0 which is not open; closed-set union counterexample gives a nonclosed union. |
| PMA-2.26 | PASS: Closure is set union its punctured accumulation points; closure_eq_self_union_derivedSet comparator. |
