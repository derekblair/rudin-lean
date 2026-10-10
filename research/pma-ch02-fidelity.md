# Independent Chapter 2 fidelity review

Reviewer: a separate agent from the statement/proof authors. Date: 2026-10-09. This is a semantic review; the integrating agent separately performs per-node builds and the axiom audit.

## Source and scope

The primary source is the user-supplied third-edition scan `/home/derekblair/sources/pma3.pdf`. Printed pp.24–42 correspond to PDF pp.33–51. The inventory contains all 47 numbered items, including mathematically substantive remarks and the worked Cantor-set construction. Unnumbered corollaries are folded into the immediately preceding theorem. Source proof text is not reproduced.

Visual checks corrected OCR errors: 2.10 uses the index set `(0,1]`, with `E_x=(0,x)` and non-strict inclusion exactly when `x≤z`; 2.17 requires strictly ordered cell endpoints but non-strict coordinate membership; 2.21's first two rows distinguish the open and closed unit balls. The complete seven-row example table was checked. The final paragraph of 2.44 explicitly states uncountability and measure zero, even though measure itself is deferred to Chapter 11.

Rudin's countability vocabulary differs from Mathlib: countable means countably infinite; at most countable includes finite sets. A bijection with `ℕ` correctly implements the former. The zero-based sequence convention is explicitly permitted by 2.7. For 2.18, literal ball boundedness needs an ambient center, so equivalence with Mathlib boundedness requires `Nonempty X`. In 2.36 the finite-intersection hypothesis includes the empty subfamily, whose intersection is the ambient space, so it already guarantees ambient nonemptiness and handles an empty index family. Empty sets are perfect and connected by the source definitions; nonempty perfect sets are required in 2.43.

## Landscape recheck

The recheck on 2026-10-09 used indexed searches, GitHub's public repository-search API (`Rudin language:Lean`), recursive repository-tree APIs, and primary source files. No complete, independently build-verified, zero-placeholder implementation of all 47 requested main-text nodes was established. This is a bounded search, not a proof of nonexistence, and the user has explicitly authorized continuing regardless of prior overlap.

- [Neuron-Group/RudinAnalysis's metric-spaces source](https://github.com/Neuron-Group/RudinAnalysis/blob/main/RudinAnalysis/BasicTopology/MetricSpaces.lean) is substantial prior Chapter 2 work: metric balls, boundedness, limit points, openness, relative openness, finite subcovers, subspace compactness, closedness, the compact finite-intersection property, and Bolzano–Weierstrass. The inspected 435-line file has 23 named declarations and no textual proof placeholders. Its Chapter 2 tree has only this substantive file plus import/export files; no complete cardinality, perfect-set, Cantor-set, and connectedness corpus was found. No third-party build was run.
- [sinianluoye/LeanOfRudinAnalysis](https://github.com/sinianluoye/LeanOfRudinAnalysis) has substantial Chapter 1 material; the current recursively inspected tree returned no Chapter 2 files.
- [hbghlyj/rudin-chapter-1-lean's own README](https://github.com/hbghlyj/rudin-chapter-1-lean/blob/main/README.md) describes selected exercise formalizations. Its [Chapter 2 source directory](https://github.com/hbghlyj/rudin-chapter-1-lean/tree/main/RudinChapter2) has selected countability, derived-set, closure/interior, connected-closure, compactness, and separability results (32 named declarations across three substantive files). These inspected files have no textual proof placeholders, but they do not constitute all 47 numbered main-text nodes. No third-party build was run.
- [alexanderlhicks/baby-rudin-project](https://github.com/alexanderlhicks/baby-rudin-project) describes an exercise project; its current Chapter 2 tree contains only `Problem1.lean` through `Problem3.lean`.
- [libmath/Rudin](https://github.com/libmath/Rudin) has partition/integration-oriented source modules in its current tree; no Chapter 2 numbered topology corpus was established from that tree.
- [ProofNet-Verified's primary README](https://github.com/marcusm117/ProofNet-Verified/blob/main/README.md) documents selected textbook-exercise statements/proofs, including Rudin. This does not provide full numbered-main-text coverage.
- Mathlib already contains the underlying topology and [the recursive ternary Cantor-set construction](https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Topology/Instances/CantorSet.lean). Those are mathematical references, not a Rudin-numbered coverage/fidelity audit.

No novelty claim beyond the requested coverage and explicit assurance trail is supported by these checks.

## Independent back-translations of authored drafts

### PMA-2.1–2.14 — PASS on current draft

Every definition and every numbered theorem/example signature in `Chapter02OpeningDraft.lean` was independently read and compared to the source inventory.

| Node | Back-translation and reference comparison |
|---|---|
| 2.1 | Mappings are total functions from domain to codomain; each input has one unique value; the defined range is exactly Mathlib `Set.range`. |
| 2.2 | Images and preimages use the specified domains; onto means range equals the whole codomain; one-to-one means equal values imply equal inputs. The comparators match Mathlib image, preimage, surjectivity, and injectivity; the unequal-input formulation is also certified. |
| 2.3 | Equinumerosity is existence of an equivalence/bijection, with both presentations compared. Reflexivity, symmetry, and transitivity have the correct source domains; the arbitrary-relation predicate is compared with `Equivalence`. |
| 2.4 | Finite types admit a bijection with `Fin n`, including `n=0` for the separately allowed empty case. Infinite negates finite. Countable means a bijection with `ℕ`, explicitly compared with positive integers and with `Countable ∧ Infinite`. At most countable is finite-or-countably-infinite, compared with Mathlib `Countable`; uncountable negates both, compared with `¬ Countable`. No finite set is mislabeled as Rudin-countable. |
| 2.5 | Integers admit a bijection with `ℕ`, rather than merely an injection into `ℕ`. Reference: `Equiv.intEquivNat`. |
| 2.6 | No finite set admits a bijection onto a proper subset; every infinite set admits a bijection with some proper subset. The characterization has both directions and uses strict inclusion, not merely unequal cardinal notation. |
| 2.7 | Sequences use the explicitly permitted zero-based indexing. A set is countably infinite iff it is exactly the range of an injective sequence. The theorem preserves equality of the whole range with the set, not just inclusion. |
| 2.8 | The larger set is countably infinite, the subset is infinite, and subset inclusion is explicit; the conclusion is countably infinite. |
| 2.9 | Union membership is existential over the index type; intersection membership is universal. Disjointness means empty intersection and is compared with Mathlib `Disjoint`. Empty index types behave correctly. |
| 2.10 | Both explicit finite-set equalities occur. The interval index is precisely `(0,1]`; `E_x=(0,x)`, inclusion is equivalent to `x≤z`, union is `(0,1)`, and intersection is empty. The crucial endpoint 1 is included in the index. |
| 2.11 | All commutative, associative, distributive, inclusion, empty-set, and subset absorption clauses listed in the source occur with the correct direction. References are the corresponding standard `Set` laws. |
| 2.12 | Every stage is countably infinite, so the union is both at most countable and infinite. The corollary separately allows an arbitrary at most countable index and finite/empty stages. |
| 2.13 | The tuple length is strictly positive; the tuple entries lie in the countably infinite carrier. The resulting function type is countably infinite. Rational countable infinitude is included. Zero-length tuples are correctly excluded from this conclusion. |
| 2.14 | Infinite sequences of `Fin 2` values are uncountable in the source's sense. `Fin 2` is exactly the digit set `{0,1}`; both finite and countably infinite possibilities are excluded through the comparator. |

### PMA-2.15–2.20 — PASS on current draft

The arbitrary real-valued distance predicate requires strict positivity for distinct points, zero self-distance, symmetry, and the correct triangle inequality. The metric constructor preserves the supplied distance exactly, and the reverse comparator shows every Mathlib metric satisfies it. Euclidean distance is norm of difference; subset distances are restrictions of the same ambient function.

All 2.17 definitions recover the correct four interval endpoint conventions, closed coordinate boxes, norm-based balls, and strict-interior affine convexity. The explicit convexity comparator correctly adds the endpoint coefficient cases from membership. Convexity of open/closed balls and coordinate cells covers the worked examples. The definitions are totalized to arbitrary radii, dimension zero, and degenerate/reversed cell endpoints; valid source parameters remain covered, and the proved generalizations do not weaken those cases.

Every 2.18 definition was read: neighborhoods use positive-radius balls in the specification, limit points require a distinct member in every positive-radius ball, isolated points additionally belong to the set, closed sets contain all limit points, interior points have a contained ball, open sets consist of interior points, complements are ambient, perfect means closed and every member a limit point, boundedness explicitly supplies an ambient center, and density uses membership-or-limit-point. Comparators establish agreement with Mathlib `ball`, `AccPt`, `IsClosed`, `interior`, `IsOpen`, complement, `Perfect`, boundedness with `Nonempty X`, and `Dense`.

The neighborhood openness theorem is valid even at nonpositive radii, a harmless extension. The limit-point theorem concludes infinite membership of `E∩ball`, not merely existence of one distinct member. The finite-set corollary excludes all limit points, including points outside the finite set.

### PMA-2.22–2.30 — PASS on current draft

De Morgan's union-complement law retains an arbitrary index type, including the empty family. Open/closed complement equivalences match the literal metric predicates through their comparators. Arbitrary open unions/closed intersections and finite open intersections/closed unions use exactly the necessary index finiteness assumptions.

The shrinking intervals are precisely `(-1/(n+1),1/(n+1))`, implementing source indexing from one. Their intersection is `{0}`, which is proved not open. Their closed complements have a union proved not closed, supplying the second requested counterexample without inventing a different claim.

Closure is defined as the set union its limit points and explicitly compared to Mathlib closure. Closedness, idempotence exactly for closed sets, and minimality among closed supersets match all clauses of 2.27. The supremum theorem preserves both nonemptiness and bounded-above hypotheses and produces membership in the same closure; the closed-set conclusion preserves those hypotheses.

Relative openness quantifies a positive-radius ball intersected with the specified ambient subset. Its equivalence to subtype openness assumes `E⊆Y`, as the source does. The ambient-open representation uses `E=Y∩G` in the correct order and has a full iff statement.

### PMA-2.21 — PASS on complete current draft

The independently inspected rendered source table has seven rows. Every row has all four properties formally present, in the source's column order `(closed, open, perfect, bounded)`:

| Example | Formalized values |
|---|---|
| Open unit ball in `ℂ` | `(false, true, false, true)` |
| Closed unit ball in `ℂ` | `(true, false, true, true)` |
| Arbitrary nonempty finite subset of `ℂ` | `(true, false, false, true)` |
| Embedded integers | `(true, false, false, false)` |
| Embedded positive-integer reciprocals | `(false, false, false, true)` |
| Entire complex plane | `(true, true, true, false)` |
| Embedded segment `(a,b)` with `a<b` | `(false, false, false, true)` |

The three example set definitions preserve their exact embeddings: all integer casts, reciprocals of `n+1` for every natural index, and the real-to-complex image of the open real interval. The reciprocal example additionally certifies that 0 is a limit point while none of its members is a limit point. The segment theorem additionally certifies openness in the real ambient space, preserving the source's ambient-space contrast. All 28 table entries and both additional contrasts are covered.

### PMA-2.31–2.42 — PASS on current draft

Open covers require every member to be ambient open and their union to contain the target; the comparator expands this into the expected pointwise existential membership. The compactness predicate requires a finite family of indices covering the target for every open cover. Its comparator to Mathlib compactness confirms the universe restriction does not lose the finite-subcover property. Finite sets are compact, including the empty set.

The subspace theorem represents the target by its subtype preimage and explicitly proves its ambient image equals the original set from `K⊆Y`. Compact-closed and closed-subset-compact statements use metric separation correctly. The closed-intersection corollary is included.

The compact finite-intersection theorem requires nonempty intersections of all finite subfamilies and allows an arbitrary index type. Its initial draft unnecessarily required a nonempty index type; review removed this restriction, because the empty-index case follows directly from the finite-subfamily hypothesis at the empty finset. The revised signature and empty-index case were independently reread and pass the full source contract. The decreasing compact-sequence corollary explicitly requires every stage nonempty. Infinite subsets produce an accumulation point in the containing compact set. The interval intersection theorem allows degenerate nonempty intervals, a valid extension of the source's nondegenerate cells. Euclidean closed cells have literal closed-coordinate membership; nonemptiness, closedness, and compactness are independently established. Positive dimension is retained on numbered cell theorems.

All three clauses of the Heine–Borel theorem occur in two linked biconditionals: closed and bounded iff compact, and compact iff every infinite subset has an accumulation point in the original set. The infinite-subset property does not require the point to belong to the subset itself. The bounded infinite-set theorem concludes an ambient accumulation point and does not add a closedness hypothesis. Euclidean ambient spaces are inhabited, so Mathlib boundedness agrees with the source's centered-ball predicate.

### PMA-2.43 — PASS on complete current draft

The current theorem requires a nonempty perfect Euclidean subset and concludes it is not at most countable. This is exactly the source's uncountability conclusion. Its reference proof uses injectivity from binary sequences and Cantor's theorem. The interval corollary retains `a<b` and proves both closed and open intervals uncountable; the latter is a valid additional result. A separate theorem explicitly certifies uncountability of the entire real line, completing the source corollary.

### PMA-2.44 — PASS on complete current draft

The aliases refer to Mathlib's actual ternary pre-Cantor stages and Cantor intersection. Stage zero is `[0,1]`; the successor stage is the union of the two affine copies scaled by one third and shifted by two thirds; stages decrease; their total intersection is the specified set. This recursive construction is the book's middle-third deletion, not an unrelated existential perfect subset.

The current combined theorem explicitly certifies compactness, nonemptiness, perfectness, exclusion of every nonempty open interval, uncountability, and Lebesgue volume zero. Perfectness quantifies every member and excludes that member from the accumulating witnesses. No-interval uses `a<b`, avoiding a vacuous empty-segment obstruction. The volume is Mathlib real Lebesgue volume.

The separately defined finite-stage endpoint lists start with `[(0,1)]` and recursively concatenate the two affine-scaled copies. Their lengths are `2ⁿ`, they have no duplicate endpoint pairs, every interval width is `1/3ⁿ`, and their closed-interval union is exactly the recursive pre-Cantor stage. Positive widths ensure nonempty nondegenerate intervals; endpoint bounds keep them within `[0,1]`. Every stage is compact. The full list/count/width/union/stage-compactness assertion is included in the combined theorem, completing the requested finite-stage description.

### PMA-2.45–2.47 — PASS on current draft

Separated sets are defined by disjointness of each set with the other's closure, with an explicit comparator to both empty-intersection clauses. The connected predicate forbids a decomposition into two nonempty separated sets. Its comparator uses Mathlib `IsPreconnected`, which agrees with the source because the empty set is connected under that definition; using Mathlib `IsConnected` would incorrectly add nonemptiness.

Separation implies disjointness. The two interval examples preserve the closed endpoint at 1 in the failed-converse example and omit it from both open intervals in the separated example. The real-line characterization has the exact strict-between condition and proves a biconditional; conversion to Mathlib order-connectedness handles endpoint cases by their given set membership.

## Prove-or-disprove and nondegeneracy probes

The separately authored `Chapter02Probes.lean` contains 13 declarations. They were kernel-checked against a concatenated snapshot of all three completed chapter drafts. The snapshot prefixes two compactness-draft calls to Mathlib `_root_.closure_minimal`, resolving a name collision with the chapter's literal closure-minimality theorem. No definitions or statement hypotheses were changed for this verification.

The probes certify that a finite singleton is at most countable but not countably infinite; zero-length tuples fail the countably-infinite conclusion, showing why 2.13 needs positive tuple length; a singleton has no limit point at its own member, checking the puncture requirement; a zero-radius neighborhood is empty; literal centered-ball boundedness fails in an empty ambient space while Mathlib's empty-set boundedness holds; and the empty real subset is bounded once an ambient center exists.

The empty complex subset is both perfect and open, showing why the nonempty finite-set row in 2.21 needs its guard. A formal counterexample disproves uncountability of every perfect real subset without a nonemptiness premise. Empty real sets satisfy Rudin-connectedness but fail Mathlib `IsConnected`, confirming that the correct reference predicate is `IsPreconnected`. The first Cantor stage is exactly `[0,1/3]∪[2/3,1]`, and `1/2` does not belong to the Cantor intersection. The interval-family index explicitly contains 1, detecting the source OCR error.

These are concrete counterexamples and boundary cases, not merely failed automation attempts to prove a negation. Every probe has an ordinary Lean proof with no placeholder or extra axiom.

## Final integrated review — PASS

All 47 nodes pass independent source/back-translation review, including every definition and every numbered theorem/example. The final integrated `Chapter02.lean` has all 47 numbered markers. Every one of its 193 named authored declarations was compared with the independently reviewed complete drafts: no changed theorem signatures, no changed definition bodies, no missing declaration, and no unexpected additional declaration. This includes the revised arbitrary-index finite-intersection theorem.

The actual `Chapter02Probes.lean` imports the final integrated module directly and compiles successfully with all 13 independently authored proofs. The final chapter audit imports that probe module. The integrating agent confirms every per-node build passed and the final default `lake build` passed; the axiom checker covers 289 declarations, including generated declarations and the probes, and accepts only `propext`, `Classical.choice`, and `Quot.sound`. No fidelity gap or unreviewed source node remains.
