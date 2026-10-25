# Independent source-fidelity review: PMA 9.1–9.5

Reviewed against PMA third edition, printed pp. 204–207, read directly from `/root/sources/pma3.pdf` through `pdftotext`. This is an independent statement/proof-structure review, not a replacement for the root agent's compiler and axiom audit.

Reviewed source blob: `767c576d78776bc7398652e93f0b7d23cd4f66fb` (`rudin/Rudin/PMA/Chapter09/LinearFoundations.lean`).

Result: no missing numbered-node content or unflagged restriction found.

| Node | Coverage checked |
|---|---|
| 9.1(a) | Nonempty subset closed under addition/scalar multiplication; equivalence with submodules. |
| 9.1(b) | Finite linear combinations, span/spanning, finite-combination membership, span is a vector space. |
| 9.1(c) | Independence/dependence coefficient criteria; independent vectors are nonzero. |
| 9.1(d) | Dimension via independent families of sizes r and r+1; equivalence with finrank on finite dimensional spaces; zero space. |
| 9.1(e) | Independent spanning basis, unique coordinates, standard Euclidean basis and coordinate expansion. |
| 9.2 | Dimension bound including existence in the book's predicate; attached Euclidean dimension corollary. |
| 9.3(a–c) | Independence iff spanning for n vectors; basis existence/cardinality; extension of an independent family. |
| 9.4 | Functional linearity, bundled linear maps, zero preservation, action/determination by a basis, operators and two-sided linear inverse. |
| 9.5 | Injective iff surjective, with an explicit equivalent range formulation. |

The apparent extra `FiniteDimensional` premise on the abstract 9.3 statements holds automatically for the book's subspaces of Euclidean space. It is consistent with the module's stated generalization to abstract finite dimensional real spaces. The companion `pma9_2_dimension` supplies finite-dimensional existence from a finite spanning family, avoiding reliance on finrank's infinite-dimensional default.

Flagged generalizations were checked: abstract real vector spaces, zero-based finite indexing, the zero-vector spanning-family case at 9.2, and the empty independent family at 9.3(c). The basis-extension conclusion uses containment of ranges, which is the book's set-based conclusion. No implementation changes requested.
