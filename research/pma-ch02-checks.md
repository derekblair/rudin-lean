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
