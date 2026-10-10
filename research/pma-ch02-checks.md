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
