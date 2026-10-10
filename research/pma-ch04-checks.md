# Chapter 4 verification log

Source and node scope: pma-ch04-inventory.md. Independent review: pma-ch04-fidelity.md.
Each node is typechecked, independently back-translated, compared to Mathlib,
and followed by a passing default build and namespace axiom audit before its local commit.

| Node | Independent fidelity verdict and reference |
|---|---|
| PMA-4.1 | PASS: Independent definition/contract PASS; exact epsilon–delta punctured limit, ambient accumulation, Tendsto comparator and NeBot equivalence. |
| PMA-4.2 | PASS: Independent contract PASS; every punctured-domain sequence criterion and uniqueness under nontrivial approach; Mathlib filter sequential comparator. |
| PMA-4.3 | PASS: Independent definition/contract PASS; pointwise complex/vector operations, restricted quotient domain, constants and real inequalities. |
| PMA-4.4 | PASS: Independent contract PASS; sums/products, restricted quotient with only nonzero denominator limit, Euclidean vector sum/inner limits; Tendsto algebra. |
| PMA-4.5 | PASS: Independent definition/contract PASS; literal point/on continuity comparators and automatic isolated-point continuity. |
| PMA-4.6 | PASS: Independent contract PASS; domain membership and accumulation, continuity iff punctured limit equals actual value; sdiff-self comparator. |
| PMA-4.7 | PASS: Independent definition/contract PASS; exact composition and continuity of outer map on the inner image. |
| PMA-4.8 | PASS: Independent contract PASS; global continuity iff all open preimages and iff all closed preimages. |
| PMA-4.9 | PASS: Independent contract PASS; continuous complex sum/product/nowhere-nonzero quotient; Mathlib continuous algebra. |
| PMA-4.10 | PASS: Independent contract PASS; all Euclidean coordinates iff continuity, vector sum and inner product continuity. |
| PMA-4.11 | PASS: Independent definitions/contract PASS; projections and norm1-Lipschitz; monomials, all finite complex polynomials, rational restricted-domain quotients and norm composition. |
| PMA-4.12 | PASS: Independent contract PASS; induced metric subtype comparators at each point and globally. |
| PMA-4.13 | PASS: strict norm bound for all domain points and bounded-range reference, including empty domains. |
| PMA-4.14 | PASS: arbitrary compact metric domain and continuous metric-valued image. |
| PMA-4.15 | PASS: closed and bounded Euclidean image and literal boundedness. |
| PMA-4.16 | PASS: nonempty compact domain, actual supremum/infimum equalities, and global maximum/minimum inequalities. |
| PMA-4.17 | PASS: continuous actual bijection and continuity of its inverse. |
| PMA-4.18 | PASS: one positive delta for every pair, `UniformContinuous` reference, and continuity consequence. |
| PMA-4.19 | PASS: arbitrary compact metric domain and literal uniform continuity. |
| PMA-4.20 | PASS: all three noncompact real-set counterexamples, boundedness guard on the third, and every metric-valued function on the integer subspace. |
| PMA-4.21 | PASS: literal Euclidean cos/sin parametrization, actual equivalence, inverse discontinuity at the image of zero, noncompact interval, and compact unit circle. |
| PMA-4.22 | PASS: image of every connected subset, including the empty set. |
| PMA-4.23 | PASS: continuous closed-interval restriction, either strict endpoint ordering, and an interior preimage. |
