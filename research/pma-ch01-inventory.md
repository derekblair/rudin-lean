# PMA Chapter 1 Inventory — "The Real and Complex Number Systems" (3rd ed.)

Source: originally `~/workspace/formalization/sources/pma3.pdf` (3rd edition, verified from archive.org). Statements rechecked on 2026-10-09 against the [Lehman College third-edition scan](https://www.lehman.edu/faculty/rbettiol/lehman_teaching/2020mat320/baby_Rudin.pdf).
Scope: every numbered Definition, Theorem, Proposition, Lemma, Corollary, worked Example, plus numbered Remarks/Notation/Discussion items, in Rudin's own numbering. There are 38 numbered targets, including the standalone Remark 1.2 restored by the merged review-finding repair. The Appendix (Steps 1–9, unnumbered Dedekind-cut construction proving Theorem 1.19) and the 18 end-of-chapter Exercises are not numbered nodes and are noted separately below.

## Numbered nodes

- **PMA-1.1** (example) — p² = 2 has no rational solution; the sets A = {p ∈ ℚ⁺ : p² < 2} and B = {p ∈ ℚ⁺ : p² > 2} contain no largest/smallest element.
- **PMA-1.2** (remark) — For rational r < s, the rational midpoint (r + s)/2 lies strictly between r and s.
- **PMA-1.3** (definition) — Set-theoretic terminology: membership, empty set, subset, proper subset, set equality.
- **PMA-1.4** (definition) — ℚ denotes the set of all rational numbers throughout Chapter 1.
- **PMA-1.5** (definition) — Order on a set: a relation < satisfying trichotomy and transitivity.
- **PMA-1.6** (definition) — Ordered set: a set in which an order is defined.
- **PMA-1.7** (definition) — Bounded above/below; upper and lower bounds of a subset.
- **PMA-1.8** (definition) — Least upper bound (supremum, sup E) and greatest lower bound (infimum, inf E).
- **PMA-1.9** (example) — (a) A has no sup and B no inf in ℚ; (b) the rational sets {r : r < 0} and {r : r ≤ 0} both have sup 0, respectively outside/inside the set; (c) for E = {1/n}, sup E = 1 ∈ E and inf E = 0 ∉ E.
- **PMA-1.10** (definition) — Least-upper-bound property of an ordered set.
- **PMA-1.11** (theorem) — An ordered set with the least-upper-bound property also has the greatest-lower-bound property (inf B = sup of its lower bounds). Deps: PMA-1.8, PMA-1.10.
- **PMA-1.12** (definition) — Field: a set with addition and multiplication satisfying axioms (A1)–(A5), (M1)–(M5), and the distributive law (D).
- **PMA-1.13** (remarks) — (a) Notation x⁻¹, x⁰, xⁿ; (b) ℚ is a field; (c) the point of proving field-axiom consequences once.
- **PMA-1.14** (proposition) — Consequences of the addition axioms: cancellation law, uniqueness of 0, uniqueness of −x, −(−x) = x. Deps: PMA-1.12.
- **PMA-1.15** (proposition) — Mirror consequences of the multiplication axioms (cancellation, uniqueness of 1, uniqueness of inverses). Deps: PMA-1.12.
- **PMA-1.16** (proposition) — Consequences of all field axioms: 0x = 0, no zero divisors, (−x)y = −(xy), (−x)(−y) = xy. Deps: PMA-1.12, PMA-1.14.
- **PMA-1.17** (definition) — Ordered field: a field that is also an ordered set with addition preserving order and products of positives positive; positive/negative elements.
- **PMA-1.18** (proposition) — Ordered-field consequences: sign of −x; multiplication by positive/negative preserves/reverses inequalities; x ≠ 0 ⇒ x² > 0 (hence 1 > 0); 0 < x < y ⇒ 0 < 1/y < 1/x. Deps: PMA-1.16, PMA-1.17.
- **PMA-1.19** (theorem) — Existence of an ordered field ℝ with the least-upper-bound property containing ℚ as a subfield. Proved in the Appendix via Dedekind cuts (Steps 1–9). Deps: PMA-1.12, PMA-1.17, PMA-1.10.
- **PMA-1.20** (theorem) — (a) Archimedean property: for x > 0, some positive integer n has nx > y; (b) ℚ is dense in ℝ. Deps: PMA-1.19.
- **PMA-1.21** (theorem) — For every real x > 0 and integer n > 0 there is exactly one positive real y with yⁿ = x (nth roots); positive nth roots are multiplicative (the unnumbered corollary). The printed uniqueness sentence omits “positive”; this restriction is necessary for even n and agrees with the surrounding construction. Deps: PMA-1.19.
- **PMA-1.22** (discussion) — Every positive real is the supremum of its finite decimal truncations; infinite decimals correspond to reals (decimals not used further).
- **PMA-1.23** (definition) — Extended real number system: ℝ ∪ {−∞, +∞} with extended order and arithmetic conventions for the infinities.
- **PMA-1.24** (definition) — Complex number as an ordered pair (a, b) of reals, with equality, addition, and multiplication defined componentwise.
- **PMA-1.25** (theorem) — ℂ with these operations satisfies the field axioms. Deps: PMA-1.12, PMA-1.24, PMA-1.18.
- **PMA-1.26** (theorem) — (a, 0) + (b, 0) = (a + b, 0) and (a, 0)(b, 0) = (ab, 0): ℝ embeds as a subfield of ℂ. Deps: PMA-1.24.
- **PMA-1.27** (definition) — i = (0, 1).
- **PMA-1.28** (theorem) — i² = −1. Deps: PMA-1.24, PMA-1.27.
- **PMA-1.29** (theorem) — (a, b) = a + bi for real a, b. Deps: PMA-1.26–PMA-1.28.
- **PMA-1.30** (definition) — Conjugate z̄ of z = a + bi; real part Re(z) and imaginary part Im(z).
- **PMA-1.31** (theorem) — Conjugate of a sum/product; z + z̄ = 2Re(z), z − z̄ = 2iIm(z); zz̄ is real and nonnegative (positive unless z = 0). Deps: PMA-1.30.
- **PMA-1.32** (definition) — Absolute value |z| = √(zz̄) (nonnegative square root). Deps: PMA-1.21, PMA-1.31.
- **PMA-1.33** (theorem) — Modulus properties: positivity, |z̄| = |z|, |zw| = |z||w|, |Re z| ≤ |z|, triangle inequality |z + w| ≤ |z| + |w|. Deps: PMA-1.32.
- **PMA-1.34** (notation) — Summation notation Σ for finite sums of complex numbers.
- **PMA-1.35** (theorem) — Schwarz (Cauchy–Schwarz) inequality for finite complex sequences. Deps: PMA-1.31.
- **PMA-1.36** (definition) — ℝᵏ: k-tuples of reals with vector addition, scalar multiplication, inner product, and norm; euclidean k-space.
- **PMA-1.37** (theorem) — Norm properties in ℝᵏ: nonnegativity, definiteness, homogeneity, Cauchy–Schwarz form |x·y| ≤ |x||y|, triangle inequality, |x − z| ≤ |x − y| + |y − z|. Deps: PMA-1.35, PMA-1.36.
- **PMA-1.38** (remarks) — Theorem 1.37 lets ℝᵏ be viewed as a metric space (Chapter 2); ℝ¹ is the real line, ℝ² the plane/complex plane.

## Supporting material (not numbered nodes)

- **Appendix, Steps 1–9** (unnumbered): the Dedekind-cut construction of ℝ — definition of cuts, order on cuts, LUB property of the cut set, addition and its axioms, multiplication on positive cuts extended to all cuts, embedding r ↦ r* of ℚ, and uniqueness up to isomorphism. This is the proof body of Theorem 1.19.
- **Exercises 1–18**: end-of-chapter exercises (not inventoried).

## Count by type

| Type | Count | Nodes |
|---|---|---|
| Definition | 15 | 1.3, 1.4, 1.5, 1.6, 1.7, 1.8, 1.10, 1.12, 1.17, 1.23, 1.24, 1.27, 1.30, 1.32, 1.36 |
| Theorem | 12 | 1.11, 1.19, 1.20, 1.21, 1.25, 1.26, 1.28, 1.29, 1.31, 1.33, 1.35, 1.37 |
| Proposition | 4 | 1.14, 1.15, 1.16, 1.18 |
| Example | 2 | 1.1, 1.9 |
| Remarks | 3 | 1.2, 1.13, 1.38 |
| Notation | 1 | 1.34 |
| Discussion | 1 | 1.22 |
| **Total** | **38** | 1.1–1.38, including standalone Remark 1.2 |
