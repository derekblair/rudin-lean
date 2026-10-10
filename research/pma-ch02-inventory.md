# PMA Chapter 2 Inventory — Basic Topology (3rd ed.)

Source: `/home/derekblair/sources/pma3.pdf`, verified 2026-10-09. Printed pages 24–42 are PDF pages 33–51. Scope follows Chapter 1: every numbered definition/theorem/worked example and every substantive numbered remark, including the Cantor-set construction. Unnumbered corollaries are folded into their parent node; exercises are excluded. The 47 targets below preserve Rudin's numbering. Statements are brief mathematical paraphrases; no proof text is reproduced.

Terminology: Rudin's **countable** means countably infinite (bijection with positive integers); **at most countable** includes finite sets. Mathlib `Countable` corresponds to the latter. Positive-integer sequences may use zero-based indexing through the shift `n ↦ n+1`.

## Numbered nodes

- **PMA-2.1** (definition, p.24) — A function `f:A→B` assigns each domain element one value; its range is `{f(x):x∈A}`.
- **PMA-2.2** (definition, pp.24–25) — Image `f(E)={f(x):x∈E}`, preimage `f⁻¹(E)={x:f(x)∈E}`, onto iff range equals codomain, and one-to-one iff equal images imply equal inputs. Deps: 2.1.
- **PMA-2.3** (definition, p.25) — Equicardinality `A∼B` means a bijection exists; this relation is reflexive, symmetric, and transitive. An equivalence relation has these three properties. Deps: 2.2.
- **PMA-2.4** (definition, p.25) — Finite means bijective with `{1,…,n}` for some positive integer `n`, or empty; infinite means not finite; countable means bijective with the positive integers; uncountable means neither finite nor countable; at most countable means finite or countable. Deps: 2.3.
- **PMA-2.5** (worked example, p.25) — The integers are countably infinite. Deps: 2.4.
- **PMA-2.6** (remark, p.26) — A finite set is not equicardinal with a proper subset; an infinite set is equicardinal with some proper subset. Deps: 2.3–2.5.
- **PMA-2.7** (definition, p.26) — A sequence is a function on positive integers (optionally indexed from zero); every countably infinite set is the range of an injective sequence. Deps: 2.1, 2.4.
- **PMA-2.8** (theorem, p.26) — An infinite subset of a countably infinite set is countably infinite. Deps: 2.4, 2.7.
- **PMA-2.9** (definition, pp.26–27) — For an indexed family `E_a`, membership in `⋃_a E_a` means membership in some `E_a`, and in `⋂_a E_a` means membership in every `E_a`; two sets are disjoint iff their intersection is empty.
- **PMA-2.10** (worked examples, pp.27–28) — `{1,2,3}∪{2,3,4}={1,2,3,4}` and their intersection is `{2,3}`; for `0<x≤1`, put `E_x=(0,x)`: `E_x⊆E_z ↔ x≤z`, `⋃_{0<x≤1}E_x=(0,1)`, and `⋂_{0<x≤1}E_x=∅`. Deps: 2.9.
- **PMA-2.11** (remark, p.28) — Union/intersection commute and associate; `A∩(B∪C)=(A∩B)∪(A∩C)`; `A⊆A∪B`, `A∩B⊆A`, `A∪∅=A`, `A∩∅=∅`; if `A⊆B`, then `A∪B=B` and `A∩B=A`. Deps: 2.9.
- **PMA-2.12** (theorem, p.29) — A sequence of countably infinite sets has countably infinite union; a union indexed by an at most countable set of at most countable sets is at most countable (unnumbered corollary). Deps: 2.4, 2.7–2.9.
- **PMA-2.13** (theorem, p.29) — For positive integer `n`, the `n`-tuples from a countably infinite set form a countably infinite set; the rationals are countably infinite (unnumbered corollary). Deps: 2.12.
- **PMA-2.14** (theorem, p.30) — The set of all infinite binary sequences is uncountable. Deps: 2.4, 2.7.
- **PMA-2.15** (definition, p.30) — A real-valued distance gives a metric iff it vanishes on equal points, is positive on distinct points, is symmetric, and satisfies the triangle inequality.
- **PMA-2.16** (worked examples, p.31) — Euclidean distance is `d(x,y)=‖x−y‖`; every subset of a metric space inherits the restricted metric. Deps: 1.37, 2.15.
- **PMA-2.17** (definition with examples, p.31) — Segments/intervals/half-open intervals are `Ioo/Icc/Ico/Ioc`; a `k`-cell is `∏ᵢ[aᵢ,bᵢ]` with `aᵢ<bᵢ`; radius-`r>0` open/closed balls use `‖y−x‖<r/≤r`; convexity requires `λx+(1−λ)y∈E` for `x,y∈E` and `0<λ<1`; balls and cells are convex. Deps: 2.16.
- **PMA-2.18** (definition, p.32) — A neighborhood is a positive-radius open ball; limit points meet every punctured neighborhood; isolated points belong to the set but are not limit points; closed sets contain all limit points; interior points have a contained neighborhood; open sets consist of interior points; complement is relative to the ambient space; perfect means closed with every member a limit point; bounded means contained in some finite-radius ball with an ambient center; dense means every ambient point belongs to the set or is a limit point. Deps: 2.15–2.17.
- **PMA-2.19** (theorem, p.32) — Every positive-radius neighborhood is open. Deps: 2.18.
- **PMA-2.20** (theorem, p.32) — Every neighborhood of a limit point contains infinitely many points of the set; finite sets have no limit points (unnumbered corollary). Deps: 2.18.
- **PMA-2.21** (worked examples, p.33) — In `ℂ`, the tuples `(closed,open,perfect,bounded)` are: open unit ball `(F,T,F,T)`, closed unit ball `(T,F,T,T)`, nonempty finite set `(T,F,F,T)`, embedded integers `(T,F,F,F)`, positive-integer reciprocals `(F,F,F,T)`, all `ℂ` `(T,T,T,F)`, embedded real segment `(a,b)` with `a<b` `(F,F,F,T)`; reciprocals have limit point `0` and none among their members; `(a,b)` is open in `ℝ` and not open in `ℂ`. Deps: 2.18–2.20.
- **PMA-2.22** (theorem, pp.33–34) — The complement of an arbitrary union is the intersection of the complements. Deps: 2.9, 2.18.
- **PMA-2.23** (theorem, p.34) — A set is open iff its complement is closed. Deps: 2.18.
- **PMA-2.24** (theorem, p.34) — Arbitrary unions of open sets are open, arbitrary intersections of closed sets are closed, finite intersections of open sets are open, and finite unions of closed sets are closed. Deps: 2.22–2.23.
- **PMA-2.25** (worked examples, p.35) — `⋂_{n≥1}(−1/n,1/n)={0}` is not open; an infinite union of closed sets can fail to be closed. Deps: 2.21, 2.24.
- **PMA-2.26** (definition, p.35) — The closure of `E` is `E` together with all its limit points. Deps: 2.18.
- **PMA-2.27** (theorem, p.35) — Closure is closed; `closure E=E ↔ E` is closed; closure is contained in every closed superset of `E`. Deps: 2.23, 2.26.
- **PMA-2.28** (theorem, p.35) — The supremum of a nonempty bounded-above subset of `ℝ` belongs to its closure, hence belongs to the set if it is closed. Deps: 1.19, 2.26–2.27.
- **PMA-2.29** (remark/definition, pp.35–36) — For `E⊆Y⊆X`, openness relative to `Y` means each `p∈E` has a positive-radius ambient ball whose intersection with `Y` lies in `E`. Deps: 2.16, 2.18.
- **PMA-2.30** (theorem, p.36) — `E⊆Y` is open relative to `Y` iff `E=Y∩G` for some ambient open set `G`. Deps: 2.19, 2.24, 2.29.
- **PMA-2.31** (definition, p.36) — An open cover is a family of ambient open sets whose union contains the covered set. Deps: 2.9, 2.18.
- **PMA-2.32** (definition, p.36) — Compactness means every open cover has a finite subcover; finite sets are compact. Deps: 2.31.
- **PMA-2.33** (theorem, p.37) — For `K⊆Y⊆X`, compactness of `K` relative to `Y` is equivalent to compactness relative to `X`. Deps: 2.30, 2.32.
- **PMA-2.34** (theorem, p.37) — Compact subsets of metric spaces are closed. Deps: 2.18, 2.32.
- **PMA-2.35** (theorem, p.37) — A closed subset of a compact set is compact. Deps: 2.23, 2.32; includes intersections with ambient closed sets.
- **PMA-2.36** (theorem, pp.38–39) — A nonempty family of compact sets with every finite subfamily having nonempty intersection has nonempty total intersection; in particular a decreasing sequence of nonempty compact sets has nonempty intersection (unnumbered corollary). Deps: 2.34–2.35.
- **PMA-2.37** (theorem, p.38) — An infinite subset of a compact set has a limit point in that compact set. Deps: 2.18, 2.32.
- **PMA-2.38** (theorem, p.38) — A decreasing sequence of nonempty closed bounded real intervals has nonempty intersection. Deps: 1.19, 2.17.
- **PMA-2.39** (theorem, p.39) — A decreasing sequence of `k`-cells, for positive integer `k`, has nonempty intersection. Deps: 2.17, 2.38.
- **PMA-2.40** (theorem, p.39) — Every `k`-cell is compact. Deps: 2.32, 2.39.
- **PMA-2.41** (theorem, p.40) — For a subset of `ℝᵏ`, these are equivalent: closed and bounded; compact; every infinite subset has a limit point in the original set. Deps: 2.34–2.35, 2.37, 2.40.
- **PMA-2.42** (theorem, p.40) — Every bounded infinite subset of `ℝᵏ` has a limit point in `ℝᵏ`. Deps: 2.37, 2.40–2.41.
- **PMA-2.43** (theorem, p.41) — Every nonempty perfect subset of `ℝᵏ` is uncountable; every closed real interval `[a,b]` with `a<b`, and consequently `ℝ`, is uncountable (unnumbered corollary). Deps: 2.18, 2.20, 2.36.
- **PMA-2.44** (worked construction, pp.41–42) — Starting from `[0,1]`, repeatedly delete each component interval's open middle third; the resulting nested stages comprise `2ⁿ` closed intervals of length `3⁻ⁿ`; their intersection, the Cantor set, is nonempty, compact, perfect, contains no nonempty open segment, is uncountable, and has Lebesgue measure zero (measure is introduced in Chapter 11). Deps: 2.17, 2.36, 2.40, 2.43; Mathlib measure reference for the final assertion.
- **PMA-2.45** (definition, p.42) — `A,B` are separated iff `A∩closure B=closure A∩B=∅`; a set is connected iff it cannot be expressed as a union of two nonempty separated sets. Deps: 2.26.
- **PMA-2.46** (remark/examples, p.42) — Separated sets are disjoint; the disjoint sets `[0,1]` and `(1,2)` are not separated, whereas `(0,1)` and `(1,2)` are separated. Deps: 2.45.
- **PMA-2.47** (theorem, p.42) — A subset `E⊆ℝ` is connected iff `x,y∈E` and `x<z<y` imply `z∈E`. Deps: 1.19, 2.45.

## Scope and fidelity notes

- PMA-2.36 makes a nonempty family explicit. For an empty family in an empty ambient metric space, the printed implication needs an ambient nonemptiness convention; the nonempty-family formulation captures its intended finite-intersection argument.
- PMA-2.18's ball-containment definition of boundedness includes an ambient center. Equivalence to Mathlib `Bornology.IsBounded` needs a nonempty ambient space; do not silently omit this condition for empty metric spaces.
- PMA-2.17 uses strictly ordered cell endpoints, while membership uses non-strict inequalities. Results for degenerate closed boxes are valid generalizations, provided the book's nondegenerate case is still covered.
- PMA-2.21's finite-set row requires a nonempty finite subset of the complex plane; its segment row requires `a<b`. All seven rows and the relative-openness contrast belong to the example node.
- PMA-2.43's interval corollary means a nondegenerate interval. Empty or singleton intervals cannot satisfy its uncountability conclusion.
- PMA-2.44's recursive construction is part of the node, as are its stated properties, including the final paragraph's uncountability and measure-zero assertions; a merely existential unrelated perfect set would omit the specified example.
- Exercises 1–30 on printed pp.43–46 are out of scope.

## Count by type

| Type | Count |
|---|---:|
| Definition (including the examples in 2.17) | 13 |
| Theorem | 24 |
| Worked examples | 5 |
| Substantive numbered remarks | 4 |
| Worked construction | 1 |
| **Total** | **47** |
