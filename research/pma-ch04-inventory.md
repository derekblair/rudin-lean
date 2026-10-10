# PMA Chapter 4 Inventory — Continuity (3rd ed.)

Source: `/home/derekblair/sources/pma3.pdf`, verified 2026-10-09. Printed pp.83–98 are PDF pp.92–107. Scope: all 34 numbered items, including all three worked-example nodes, all three substantive numbered remarks, and nearby unnumbered consequences folded into their numbered parent. Exercises are excluded. Every entry below is a brief statement paraphrase; no proof text is reproduced.

Unless otherwise stated, `X,Y,Z` are metric spaces, `E⊆X`, and a function on `E` has its domain restricted to `E`. Function limits at `p` use points of `E` different from `p`, with `p` an ambient accumulation point of `E`; `p` need not belong to `E`. Continuity at `p∈E` uses all sufficiently close domain points, including `p`. Euclidean spaces carry their usual metric, and monotonicity is non-strict. One-sided limits in 4.25–4.31 are finite limits, before the extended-real definitions in 4.32–4.34.

## Numbered nodes

- **PMA-4.1** (definition, pp.83–84) — `lim_{x→p,x∈E} f(x)=q` means `∀ε>0,∃δ>0,∀x∈E,0<d_X(x,p)<δ⇒d_Y(f(x),q)<ε`; `p` is a limit point of `E`, may lie outside `E`, and the limit need not equal `f(p)` when `p∈E`. Deps: 2.18, 3.1.
- **PMA-4.2** (theorem/corollary, p.84) — The function limit at an accumulation point `p` equals `q` iff every sequence `p_n∈E\{p}` tending to `p` has `f(p_n)→q`; a function limit, when it exists, is unique. Deps: 3.2, 4.1.
- **PMA-4.3** (definition, p.85) — Complex functions on `E` have pointwise sum, difference, product, and quotient, the quotient only where its denominator is nonzero; constants have a fixed value, real function inequalities are pointwise, and Euclidean-valued functions have pointwise vector sum, inner product, and multiplication by a fixed real scalar. Deps: 1.36, 2.2.
- **PMA-4.4** (theorem/remark, p.85) — At an accumulation point of `E`, limits of complex functions preserve sums, products, and quotients with nonzero denominator limit; for Euclidean-valued functions the corresponding vector-sum and inner-product limits hold. Deps: 3.3–3.4, 4.1–4.3.
- **PMA-4.5** (definition/consequence, pp.85–86) — Continuity of `f:E→Y` at `p∈E` means `∀ε>0,∃δ>0,∀x∈E,d_X(x,p)<δ⇒d_Y(f(x),f(p))<ε`; continuity on `E` means continuity at every domain point, and every function is continuous at an isolated domain point. Deps: 2.18.
- **PMA-4.6** (theorem, p.86) — At a domain point `p∈E` that is also an accumulation point of `E`, continuity at `p` is equivalent to the punctured function limit equaling `f(p)`. Deps: 4.1, 4.5.
- **PMA-4.7** (theorem/definition, p.86) — Composition is `(g∘f)(x)=g(f(x))`; if `f:E→Y` is continuous at `p∈E` and `g:f(E)→Z` is continuous at `f(p)`, then their composition is continuous at `p`. Deps: 4.5.
- **PMA-4.8** (theorem/corollary, pp.86–87) — A map `f:X→Y` is continuous iff the inverse image of every open subset of `Y` is open in `X`, equivalently iff the inverse image of every closed subset of `Y` is closed in `X`. Deps: 2.2, 2.19, 4.5.
- **PMA-4.9** (theorem, p.87) — Sums and products of continuous complex functions on `X` are continuous; their quotient is continuous when the denominator is nowhere zero. Deps: 4.4, 4.6.
- **PMA-4.10** (theorem, pp.87–88) — A map `f:X→ℝ^k` is continuous iff each coordinate function is continuous; sums and inner products of continuous Euclidean-valued maps are continuous. Deps: 4.9.
- **PMA-4.11** (examples, p.88) — Euclidean coordinate projections and the norm are 1-Lipschitz and continuous; monomials with nonnegative integer exponents, finite complex-coefficient polynomials, and their rational quotients where the denominator is nonzero are continuous; the norm of any continuous Euclidean-valued map is continuous. Deps: 4.7, 4.9–4.10.
- **PMA-4.12** (remark, pp.88–89) — Continuity of a function on `E⊆X` depends only on the induced metric on its domain: continuity at a domain point and continuity on `E` agree with continuity of the corresponding map from the metric subspace `E`. Deps: 2.16, 4.5.
- **PMA-4.13** (definition, p.89) — A function `f:E→ℝ^k` is bounded iff some real `M` satisfies `‖f(x)‖<M` for every `x∈E`. Deps: 1.36.
- **PMA-4.14** (theorem, p.89) — The image of a compact metric space under a continuous map into a metric space is compact. Deps: 2.32, 4.8.
- **PMA-4.15** (theorem, p.89) — A continuous map from a compact metric space into Euclidean space has a closed and bounded image, and is therefore bounded. Deps: 2.41, 4.13–4.14.
- **PMA-4.16** (theorem, pp.89–90) — A continuous real function on a nonempty compact metric space attains the supremum and infimum of its range, equivalently its maximum and minimum. Deps: 2.28, 4.15.
- **PMA-4.17** (theorem, p.90) — A continuous bijection from a compact metric space onto a metric space has a continuous inverse. Deps: 2.34–2.35, 4.8, 4.14.
- **PMA-4.18** (definition/consequence, p.90) — Uniform continuity of `f:X→Y` means `∀ε>0,∃δ>0,∀p,q∈X,d_X(p,q)<δ⇒d_Y(f(p),f(q))<ε`, with one `δ` for all domain points; uniform continuity implies continuity. Deps: 4.5.
- **PMA-4.19** (theorem, p.91) — A continuous map from a compact metric space into a metric space is uniformly continuous. Deps: 2.32, 4.5, 4.18.
- **PMA-4.20** (theorem/example, pp.91–92) — Every noncompact subset `E⊆ℝ` supports a continuous unbounded real function and a continuous bounded real function with no attained maximum; if `E` is also bounded, it supports a continuous real function that is not uniformly continuous; every map from the integer subspace of `ℝ` into any metric space is uniformly continuous. Deps: 2.41, 4.13, 4.18.
- **PMA-4.21** (example, p.93) — `t↦(cos t,sin t)` is a continuous bijection from `[0,2π)` onto the unit circle; its inverse is discontinuous at `(1,0)`, the domain is noncompact, and the target circle is compact. Deps: 2.41, 4.17; trigonometric facts are supplied by Mathlib and later discussed in Chapter 8.
- **PMA-4.22** (theorem, p.93) — A continuous map sends every connected subset of its metric domain to a connected subset of its metric codomain. Deps: 2.45, 4.8.
- **PMA-4.23** (theorem, p.93) — For `a<b`, a continuous real function on `[a,b]` attains each value strictly between `f(a)` and `f(b)` at a point of `(a,b)`, for either ordering of the endpoint values. Deps: 2.47, 4.22.
- **PMA-4.24** (remark, p.93) — The intermediate-value property does not imply continuity: the function in 4.27(d) attains every value strictly between any two endpoint values at an interior point, but is discontinuous at zero. Deps: 4.23, 4.27(d).
- **PMA-4.25** (definition/consequence, p.94) — For a metric-valued `f` on `(a,b)`, a right limit at `a≤x<b` equals `q` iff every sequence in `(x,b)` tending to `x` has images tending to `q`, and the left limit at `a<x<b` is defined using `(a,x)`; at an interior point the two-sided limit exists iff both one-sided limits exist and agree, with that common value. Deps: 4.2.
- **PMA-4.26** (definition/classification, p.94) — A metric-valued function's discontinuity at an interior interval point is of the first kind, or simple, iff both ordinary one-sided limits exist, and otherwise of the second kind; a simple discontinuity either has unequal one-sided limits or has equal one-sided limits different from the function value. Deps: 4.5, 4.25.
- **PMA-4.27** (examples, pp.94–95) — (a) `1` on rationals and `0` on irrationals has neither finite one-sided limit anywhere and is discontinuous of the second kind everywhere; (b) `x` on rationals and `0` on irrationals is continuous exactly at zero and has neither one-sided limit elsewhere; (c) on `(-3,1)`, the pieces `x+2` for `x<-2`, `-x-2` for `-2≤x<0`, and `x+2` for `0≤x` give a simple jump at zero and continuity elsewhere; (d) `sin(1/x)` for `x≠0`, with value zero at zero, is continuous away from zero and has neither one-sided limit at zero, hence a second-kind discontinuity there. Deps: 1.20, 4.5, 4.7, 4.25–4.26; sine continuity is supplied by Mathlib and later discussed in Chapter 8.
- **PMA-4.28** (definition, p.95) — A real function on `(a,b)` is monotonically increasing iff `a<x<y<b⇒f(x)≤f(y)`, decreasing iff the inequality reverses, and monotonic iff either condition holds. Deps: 1.5.
- **PMA-4.29** (theorem, pp.95–96) — An increasing real function has finite one-sided limits at every interior point, with `sup_{a<t<x}f(t)=f(x−)≤f(x)≤f(x+)=inf_{x<t<b}f(t)` and `f(x+)≤f(y−)` when `a<x<y<b`; decreasing functions satisfy the reversed inequalities with infimum/supremum exchanged. Deps: 1.19, 4.25, 4.28.
- **PMA-4.30** (theorem, pp.96–97) — The set of discontinuities in `(a,b)` of any monotonic real function is at most countable. Deps: 1.20, 2.8, 4.26, 4.29.
- **PMA-4.31** (remark/construction, p.97) — Every countable `E⊆(a,b)`, including dense sets, is exactly the discontinuity set of an increasing function; for distinct enumerated points `x_n∈E` and positive summable weights `c_n`, `f(x)=∑_{x_n<x}c_n` is increasing, left-continuous, continuous off `E`, and has jump `f(x_n+)−f(x_n−)=c_n`; replacing `<` by `≤` gives a right-continuous function with the same jumps and discontinuity set. Deps: 3.45, 3.55, 4.25, 4.28–4.30.
- **PMA-4.32** (definition, p.98) — Real traces of neighborhoods of `+∞` are rays `(c,+∞)`, and of `−∞` are rays `(-∞,c)`, for real `c`; finite-point neighborhoods remain ordinary open intervals around the point. Deps: 1.23, 2.18.
- **PMA-4.33** (definition/reference, p.98) — For a real function on `E⊆ℝ` and extended-real approach/target points `x,A`, the extended limit requires images of sufficiently close domain points different from `x` to lie in each neighborhood of `A`; the approach filter must be nontrivial, and for finite `x,A` this agrees with 4.1. Deps: 4.1, 4.32; see the punctured-domain fidelity correction below.
- **PMA-4.34** (theorem, p.98) — Extended function limits are unique and preserve sum, product, and quotient whenever the corresponding extended-real operation is defined, excluding opposite infinite summands, zero times infinity, infinity divided by infinity, and division by zero. Deps: 1.23, 4.33.

## Fidelity conventions and source corrections

- Punctured function limits require an accumulation point, or equivalently a nontrivial punctured approach filter. This is explicit in 4.1 and underlies uniqueness in 4.2 and 4.34; continuity at isolated domain points in 4.5 remains meaningful and automatic.
- The rendered text of 4.33 literally asks only for `V∩E≠∅` while testing points `t≠x`. That condition permits vacuous limits at isolated `x∈E`, contradicting its own finite-limit comparison and 4.34(a). Its introductory phrase that it extends 4.1 retains the intended accumulation-point condition: every approach neighborhood must meet the **punctured** domain. Formalization must record this correction instead of prove a false uniqueness assertion under a vacuous filter.
- Node 4.16 needs a nonempty compact domain; the book leaves this implicit. Compactness alone admits the empty space, which has no points attaining an extremum.
- Continuous maps on subsets are compared with `ContinuousWithinAt`/`ContinuousOn` and the subtype formulation in 4.12. Function-limit comparators use `Tendsto` on the restricted punctured neighborhood filter; a limit statement must not silently become continuity or impose `p∈E`.
- The quotient domain is restricted to nonzero denominators in 4.3. In 4.4 and 4.34 the permitted nonzero denominator limit ensures eventual nonvanishing; totalized Lean division alone must not justify a forbidden source case.
- Rudin's connectedness includes the empty set, as formalized in Chapter 2; 4.22 therefore compares with `IsPreconnected`, without adding a nonempty-set hypothesis.
- The endpoint inequalities in 4.23 and 4.24 are strict for the intermediate value, and the conclusion is an interior point. Node 4.24 depends on the later example 4.27(d); integrate that example first while retaining the original identifiers.
- One-sided limits and discontinuity kinds in 4.25–4.26 retain a general metric codomain. The source includes a right approach at `x=a`, although the function is defined only on `(a,b)`; its left-limit definition and the two-sided comparison concern interior points. Allowing a left approach at `x=b` is a valid optional generalization, not an explicit source clause. First-kind real discontinuities require **finite** one-sided limits.
- Node 4.27(c) includes `x=-2` in its middle piece and `x=0` in its last piece; the one-sided limits at zero are `-2` and `2`, respectively. Node 4.27(b) is the rational-point identity function, not a constant rational branch.
- A countable set in 4.31 can be empty, finite, or infinite. The exact weighted construction may use an injective family indexed by an arbitrary countable type, with positive summable weights, rather than assume every countable set has an injective enumeration by all of `ℕ`. Repeated point indices would change the stated jump formula to the sum of all weights at that point.
- The source's extended-real arithmetic is partial. Mathlib `EReal` operations are totalized, so 4.34 must include explicit admissibility guards for every forbidden case rather than infer the unguarded theorem from totalized operations.
- OCR headings were checked against rendered pages: `42`, `49`, `411`, `4.2` (remark), and `4.9` (monotonic theorem) mean 4.2, 4.9, 4.11, 4.12, and 4.29, respectively. The last numbered main-text item is 4.34; the exercises beginning on printed p.98 are excluded.

## Count by numbered type

| Type | Count |
| --- | ---: |
| Definitions | 10 |
| Theorems | 18 |
| Worked examples | 3 |
| Substantive numbered remarks | 3 |
| **Total** | **34** |

## Formalization order

`PMA-4.1`, `PMA-4.2`, `PMA-4.3`, `PMA-4.4`, `PMA-4.5`, `PMA-4.6`, `PMA-4.7`, `PMA-4.8`, `PMA-4.9`, `PMA-4.10`, `PMA-4.11`, `PMA-4.12`, `PMA-4.13`, `PMA-4.14`, `PMA-4.15`, `PMA-4.16`, `PMA-4.17`, `PMA-4.18`, `PMA-4.19`, `PMA-4.20`, `PMA-4.21`, `PMA-4.22`, `PMA-4.23`, `PMA-4.25`, `PMA-4.26`, `PMA-4.27`, `PMA-4.24`, `PMA-4.28`, `PMA-4.29`, `PMA-4.30`, `PMA-4.31`, `PMA-4.32`, `PMA-4.33`, `PMA-4.34`.

Dependencies on trigonometric results discussed later in Chapter 8 may be supplied directly by pinned Mathlib references.
