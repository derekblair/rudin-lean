# Chapter 7 hostile review A: 29 non-foundation nodes

**PASS for the 29-node scope below. No blocking finding.** Reviewer: `remaining_scope`, 2026-10-10. This reviewer authored none of these 29 proofs. The reviewer authored Basic and the four foundation nodes **7.1, 7.7, 7.8, 7.9**, which are explicitly excluded from this verdict and assigned to another reviewer. Reviewing consumers of the shared definitions does not constitute an independent review of those four authored nodes.

This was an additional hostile review of the actual definitions, theorem types, and complete proof bodies, not a restatement of earlier contract acceptances. The comparison target was the accepted source inventory, `research/pma-ch07-inventory.md`, SHA256 `f8e87ad7ccb765bfd4407e251958c5378552b209d32eca60a75e13e0ca9da0f0`. All 29 principal declarations are actual proved theorems of the stated contracts. No source implementation was edited by this review.

## Frozen canonical source

All paths in this table are relative to `rudin/Rudin/PMA/Chapter07/`.

| File | Nodes independently reviewed | SHA256 |
|---|---|---|
| `Examples.lean` | 7.2, 7.3, 7.5, 7.6 | `a25907d75b1bae77638eaaea291888989f6d9f319f0d2cea71ee74c9a25f9bd5` |
| `RationalIndicator.lean` | 7.4 | `edcdd11545100cbd19fb90d3382d5baf8a5a7b34907ca7afdf44560ad53fbe3d` |
| `MTest.lean` | 7.10 | `c364dc78a12a188264c39c24f8dfd5da1edc699491442d18cf78b2565aef3e05` |
| `Continuity.lean` | 7.11–7.15 | `8dae8b99a9de2d8b996c47e62ad3ae5396efb503b36a686374f0349a4efa1977` |
| `Calculus.lean` | 7.16–7.17 | `0bc805601a65a1261e944ae9d180b3cb0344c0d9484fc766f1d3df6c3411580d` |
| `Nowhere.lean` | 7.18 | `6d04835c41bda7f4315fc7ac3e65c32b1ccc1e778b8ea145a424193d7d406612` |
| `NoSubsequence.lean` | 7.20 | `a0f5e92e41fe61bbda351ab4a0497ef621ec7f3ceb7f136f742dfaca2c69f7b6` |
| `Equicontinuity.lean` | 7.19, 7.21–7.25 | `baffc08a75f000487493d784939d9b9af42f7c3b4441a52d73a6664aa9ec6ff0` |
| `Algebra.lean` | 7.26–7.33 | `44ebf1128a6a4f6409b4784c648ccecaf804a1ab354c406c02dcde638fde65c2` |

The Algebra draft and canonical copy have the same listed hash. The final 7.33 proof was read before this verdict. No final hash claim is made for the chapter aggregator, audit wrapper, or canonical probe module, which are separately owned integration artifacts.

## Node-by-node attacks and results

| Node | Critical question checked against the actual proof | Result |
|---|---|---|
| 7.2 | Are both inner limits proved before the two totalized `limUnder` expressions are identified? Both positive indices are shifted consistently; the final limits differ. | PASS |
| 7.3 | Is this ordered series convergence, with the exceptional value at zero and actual discontinuity? Each term is continuous; the geometric sum proof proves summability before using its limit. | PASS |
| 7.4 | Are the two successive limits, everywhere discontinuity, and native nonintegrability all present? Rational denominator divisibility and irrational exclusion are proved. Every positive-length partition cell has extrema 0 and 1; repeated cells contribute zero weight. Nonintegrability explicitly requires `a < b`. | PASS |
| 7.5 | Does uniform convergence coexist with an actual derivative divergence? The global sine bound proves uniform convergence, exact derivatives are proved, and their values at zero tend to infinity. | PASS |
| 7.6 | Are both scaling variants and their native integrals retained? Pointwise convergence, integrability, both exact formulas, the infinite and finite nonzero integral limits, and the zero function's native integral are proved using Chapter 6 FTC and linearity. | PASS |
| 7.10 | Does a hidden unconditional-series or positivity premise exclude the source case? Ordered convergence of a majorant is converted to summability only after deriving nonnegativity from a point of the nonempty domain. The empty domain is treated separately. The converse failure uses the conditionally convergent alternating harmonic series and rules out every convergent absolute majorant. | PASS |
| 7.11 | Is the punctured filter nontrivial, and can the limiting point lie outside the set? The explicit accumulation-point premise yields `NeBot`; no membership premise is added. A Cauchy argument produces the common numerical limit, and a uniform interchange theorem gives the punctured function limit. | PASS |
| 7.12 | Is the converse warning proved as well as continuity preservation? Both hold. The squared spike has continuous terms and continuous pointwise limit, but uniform convergence would contradict its diverging native integrals through the proved 7.16 helper. | PASS |
| 7.13 | Is the order condition decreasing, and is compactness essential? Dini is applied with the exact real antitone/continuous premises. The stated open-interval example is continuous, antitone, pointwise zero, and fails uniform convergence at explicit points approaching zero. | PASS |
| 7.14 | Is the function space available for an arbitrary metric domain? The bounded continuous function construction, norm and metric identities, uniform/metric convergence equivalence, sequential closure/closedness equivalences, and compact-domain boundedness are all present. Compactness is used only in its explicitly separate boundedness consequence. | PASS |
| 7.15 | Is a limit actually produced in the same bounded continuous function space? Completeness and the Cauchy-sequence existence conclusion are both supplied, with no compactness assumption on the domain. | PASS |
| 7.16 | Are the native complex integral and ordered series conclusion genuine? Real and imaginary native Darboux integrals are treated separately and recombined. Uniform-limit integrability and convergence are proved. The attached series clause uses finite ordered sums and concludes `SeriesHasSum`; there is no absolute-convergence assumption. Singleton intervals and zero integrator mass are admitted. | PASS |
| 7.17 | Is derivative continuity, boundedness, or integrability smuggled in? None is assumed. A relative-derivative mean-value bound proves uniform Cauchyness from one convergent anchor. A direct small-o estimate proves the limit derivative, including both endpoints. Both complex and real versions are instantiated. | PASS |
| 7.18 | Is nowhere differentiability asserted at every real point, with a valid continuous witness? The geometric tent series has proved uniform norm bounds and summability. Periodic cancellation reduces selected differences to finite sums, producing unbounded local difference quotients at every point. No assumption of the desired conclusion or prescribed-book-witness requirement is introduced. | PASS |
| 7.19 | Are pointwise and uniform boundedness quantifiers distinct, and is the countable-subset consequence present? Yes: the bound depends on the point in the first definition and is global in the second. The attached selection theorem restricts only to the requested countable subset and retains one strictly increasing index map. | PASS |
| 7.20 | Is the common subsequence strict, and does it fail to converge somewhere on the full source interval? Orthogonality fixes every successive distinct-mode squared integral at `2*pi`, while dominated convergence would make it zero. The conclusion excludes one common pointwise-convergent strict subsequence. It does not assert failure at every point. | PASS |
| 7.21 | Are all parts of the moving-peak example and both preceding observations included? The exact peak functions are continuous, bounded by one, pointwise zero, equal one at their moving peaks, and have no uniformly convergent subsequence. The squared-spike boundedness counterexample and the finite-prefix argument for uniformly convergent individually bounded sequences are both proved. | PASS |
| 7.22 | Is equicontinuity uniform over all points and family members? The definition has one delta before both point quantifiers and the family index. Its equivalence is to `UniformEquicontinuousOn`, not merely pointwise equicontinuity. Memberwise uniform continuity and the peak-family failure are proved. | PASS |
| 7.23 | Is the domain allowed to be finite or empty without topology? The countable subtype product argument supplies a strict subsequence and global extension of its limit. No domain topology or nonemptiness assumption appears. | PASS |
| 7.24 | Does the result include the initial sequence members? The proof handles the finite initial family separately and combines its modulus with the limiting function's compact-domain modulus. It proves source-uniform equicontinuity of the full sequence. | PASS |
| 7.25 | Is uniform boundedness a conclusion rather than an assumed replacement for pointwise boundedness? A finite-cover argument derives it first; only then is it used in Arzela–Ascoli. The final conclusion also gives a strict uniformly convergent subsequence and a continuous limit. | PASS |
| 7.26 | Are both complex and real polynomial approximations present, including singleton intervals? Real approximation is lifted through separate real/imaginary parts for the complex case, and a sequence with decreasing error is chosen. No positive interval length is required. | PASS |
| 7.27 | Is every polynomial exactly zero at zero? Each polynomial is normalized by subtracting its constant value at zero. The proof establishes exact vanishing and preserves uniform approximation, including radius zero. | PASS |
| 7.28 | Has a unit been added to the algebra definition? No. The explicitly accepted nonempty-algebra convention is retained. Real/complex scalar versions, sequential closure definitions, polynomial algebras, and both polynomial closure identifications are included. | PASS |
| 7.29 | Is continuity or one common algebra-wide bound required? Neither. Each member has its own finite norm bound. A discrete topology is introduced internally solely to realize arbitrary bounded maps as bounded continuous maps; the theorem's domain has no topology premise. The closure is proved bounded, an algebra, and uniformly closed. | PASS |
| 7.30 | Does nowhere-vanishing keep point-dependent witnesses? Yes. Polynomial separation/nonvanishing is proved in both scalar cases; the even-polynomial failure is witnessed by the distinct endpoints -1 and 1. | PASS |
| 7.31 | Does interpolation secretly use a unit or compactness? The construction uses products and scalar multiples of two nonzero witnesses and a separating function. All divided values are proved nonzero. Real and complex arbitrary prescribed values are covered without topology. | PASS |
| 7.32 | Does real Stone–Weierstrass preserve the non-unital assumptions? Absolute-value closure is derived from the zero-at-zero polynomial approximation, then min/max closure and strong interpolation feed a sublattice density theorem. No constants-in-algebra premise is added; nonemptiness handles empty-domain behavior. | PASS |
| 7.33 | Is the self-adjoint theorem accompanied by a real failure witness without that premise? The complex theorem constructs a real algebra using real/imaginary components and applies the non-unital real theorem. For failure, the actual polynomial algebra on the closed complex unit disk is continuous, separating and nowhere-vanishing. Conjugation is excluded from its uniform closure using holomorphic uniform-limit preservation and an explicit proof that conjugation is not complex differentiable at zero. Non-self-adjointness follows from this obstruction. | PASS |

## Independent compiler and boundary checks

Each of the nine listed canonical source files was separately compiled afresh with `./lake-local env lean Rudin/PMA/Chapter07/<module>.lean`. Every run exited 0. There were no warnings or errors; output consisted only of the intentional axiom reports already present in some modules. The results are saved in `evidence/ch07-hostile-a-source-check.log`.

The separate client `evidence/ch07-hostile-a-client.lean` imports canonical modules only. It compiles cleanly and proves nine review-local checks:

1. The empty-domain M-test accepts the ordered alternating harmonic majorant without requiring a nonnegative majorant premise.
2. A right-hand limiting point outside its domain works in 7.11, with a complex value.
3. Countable selection includes the empty set.
4. Compact selection includes the empty set.
5. Complex polynomial approximation includes a singleton interval for an arbitrary function.
6. Absolute-value approximation includes radius zero with exact normalization.
7. The functions on `Bool` vanishing at `false` form an algebra that does not contain the constant one function.
8. The closure theorem applies to that concrete non-unital algebra.
9. A generic 7.29 client requires neither continuity nor any topology hypothesis; its only function restriction is individual boundedness. This last check is a signature-level test, not a claim to construct a specific discontinuous function.

The same fresh client prints transitive axiom dependencies of every one of the 29 reviewed principal theorems and its nine local checks: **38 reports, each exactly `propext`, `Classical.choice`, `Quot.sound`**. Initial client-only elaboration mistakes were repaired before this final successful run; no source change was needed. A forbidden-token scan of the canonical support sources found no `sorry`, `admit`, custom `axiom`, `native_decide`, `unsafe`, or `implemented_by` occurrence.

Evidence hashes:

- Client: `ac066116f52be2a1290b58ff1a3a546d98e8615af8bf84cc3948a91622aa24c0`.
- Client compiler/axiom log: `c803c81da02d8756a684c667487f57f0ed5b577dbcad64428ee7f81ea24726ec`.
- Nine-source compiler log: `99123911274c745c9b4221f41a015c4e953aab6a26f099c5a3c44d7444125189`.

The preservation checker also passed for all 26 inherited Chapter 5 files, all 60 inherited Chapter 6 files, and all 127 production files. Production remained clean at `cc4328264872054cb72115dfcb3e025b1695ed5c`.

## Scope limits and dependency disclosures

The 7.20 proof uses the pinned library's measure-integral dominated convergence theorem internally. Its conclusion is purely about convergence of the sine sequence, so it does not replace a native Chapter 6 integral or establish any Chapter 11 theorem. Likewise, the 7.33 counterexample legitimately uses pinned complex-analysis uniform-limit theory; strict textbook-order dependency discipline is not claimed.

This PASS covers exactly 7.2–7.6 and 7.10–7.33 at the hashes above. It excludes the reviewer's four authored foundation nodes, final aggregator/audit/probe publication, documentation consistency, Git integration, and any production write or push. Those remain separate gates. No unresolved mathematical or fidelity finding remains in this review's 29-node scope.
