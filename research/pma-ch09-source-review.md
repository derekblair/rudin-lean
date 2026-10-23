# PMA Chapter 9 independent source review

Reviewer: `ch8_fidelity`, 2026-10-23. Source: the existing authorized read-only third-edition PDF `/home/derekblair/projects/math/references/sources/pma3.pdf`. Printed pp.204-238 correspond to PDF pp.213-247. Printed p.239 (PDF p.248) was inspected to establish the exercise boundary. Every chapter page was rendered in memory with `pdftoppm` and visually inspected under the PDF skill. No PDF copy, rendered page file, extracted proof text, or extended source exposition was saved. The companion `pma-ch09-inventory.md` contains brief mathematical paraphrases only.

`PROGRAM.md` and the repository progress/queue conventions were read. The parent coordinates the new user-authorized Chapter 9 lane on the existing branch, local commits only; this independent reviewer performs no build, Lean/lake invocation, git mutation, or production-proof edit. This source review is not evidence of kernel verification.

## Census and page mapping

There are **43 consecutive numbered items**, including definitions, remarks, preliminaries, notation, discussions, and worked examples. The final item is **9.43**, an improper Gaussian cosine-transform example; 9.42 is differentiation of a Riemann-Stieltjes integral. Any census ending at 9.42 is incomplete. Exercises begin on printed p.239 and are excluded.

| Printed pages | Numbered items beginning there | Section |
|---|---|---|
| 204 | 9.1 | Linear transformations |
| 205 | 9.2 | Linear transformations |
| 206 | 9.3, 9.4 | Linear transformations |
| 207 | 9.5, 9.6 | Linear transformations |
| 208 | 9.7 | Linear transformations |
| 209 | 9.8 | Linear transformations |
| 210 | 9.9 | Matrices |
| 211 | 9.10 | Differentiation |
| 212 | 9.11 | Differentiation |
| 213 | 9.12, 9.13 | Differentiation |
| 214 | 9.14, 9.15 | Differentiation |
| 215 | 9.16, 9.17 | Differentiation |
| 216 | 9.18 | Differentiation |
| 218 | 9.19 | Differentiation |
| 219 | 9.20, 9.21 | Differentiation |
| 220 | 9.22, 9.23 | Contraction principle |
| 221 | 9.24 | Inverse function theorem |
| 223 | 9.25 | Inverse function theorem |
| 224 | 9.26, 9.27, 9.28 | Implicit function theorem |
| 227 | 9.29 | Implicit function example |
| 228 | 9.30, 9.31 | Rank theorem |
| 229 | 9.32 | Rank theorem |
| 232 | 9.33, 9.34 | Determinants |
| 233 | 9.35, 9.36 | Determinants |
| 234 | 9.37, 9.38 | Determinants and Jacobians |
| 235 | 9.39, 9.40, 9.41 | Higher derivatives |
| 236 | 9.42 | Differentiation of integrals |
| 237 | 9.43 | Improper-integral example |

## Fidelity requirements for review

1. **Euclidean norms and arbitrary bases.** The book uses real Euclidean spaces. Pure algebra can be generalized safely, but the exact operator-norm and gradient assertions must specialize to the Euclidean norm and inner product. The `Fin n -> R` default sup norm is not the book's norm; a suitable `EuclideanSpace` or proved isometry/norm bridge is needed. Matrix discussion 9.9 covers arbitrary bases, while its square-sum norm bound uses standard Euclidean bases.
2. **Definitions must have their mathematical content.** Merely introducing aliases for `Submodule`, `LinearMap`, `Basis`, or `HasFDerivAt` does not cover all attached properties. Check basis coordinate uniqueness, basis extension, matrix correspondence, range spans, and operator-norm leastness separately. Dimension zero is explicit in 9.1, and the rank theorem expressly allows zero dimensions and rank zero.
3. **Actual local derivative hypotheses.** Sections 9.11-9.21 work on open domains. An ambient function can represent the source function, but proof and contract must depend only on values near the relevant domain point. In 9.21, existence and continuity of coordinate partials must imply total differentiability, not be supplemented by a premise assuming that conclusion already.
4. **Attached nonimplications.** Sections 9.16, 9.25, and 9.39 expressly warn that weaker hypotheses fail to imply continuity/differentiability, global injectivity, or equality of mixed partials. The named exercises are out of scope, but concrete witnesses or equivalent formal nonimplication statements cover the warnings without importing exercise proofs.
5. **Inverse function regularity.** The numbered 9.24 conclusion includes a `C^1` inverse and its derivative formula throughout the local inverse domain. Its following remark separately weakens the input regularity to differentiability on the domain plus derivative continuity at the distinguished point, yielding a differentiable local inverse and formula. Proving only the usual full-`C^1` version leaves that remark uncovered; claiming a `C^1` inverse under the weaker assumption would overstate it.
6. **Implicit function orientation and uniqueness.** In 9.26-9.29 the solved variables are the first block `x` of dimension `n`, the parameter block `y` has dimension `m`, and `f` takes values in dimension `n`. The derivative is `-A_x^-1 A_y`, in this order. The conclusion supplies the function, local uniqueness, `C^1` regularity, base-point value, and graph identity, rather than assuming an already existing implicit function. The component equations and exact numerical example are attached scope.
7. **Rank theorem strength.** Section 9.32 treats arbitrary constant rank, not only injective or surjective derivatives. It quantifies over any projection onto the range at the base point and gives the graph form with the actual derivative `A`. The auxiliary domain `A(V)` is open in the range subspace, not necessarily in the whole output space. Include invertible local coordinate changes, rank zero, graph parametrization, and level-set conclusions. This differs from merely stating an unnamed constant-rank normal form without a proved bridge.
8. **Determinant convention.** Section 9.33 starts with a sign-product on all index tuples, not only permutations. If Mathlib's determinant is used, prove that formula or a directly equivalent all-tuple formula, including repeated-index zeros and sign under transposition. Distinguish column index from row index, and retain arbitrary-basis determinant invariance in 9.37.
9. **Order and strength of mixed partials.** The source convention is `D_ij = D_i after D_j`. The rectangular mean-value theorem 9.40 only assumes existence of `D_1` and `D_21`; it allows signed nonzero side increments. The stronger 9.41 criterion assumes `D_1`, `D_2`, and `D_21` on the open set, with continuity of `D_21` at one point only; existence of `D_12` at that point is a conclusion. A `C^2` Schwarz theorem alone is strictly weaker coverage.
10. **Native integration and existence.** Section 9.42 concerns the Chapter 6 Riemann-Stieltjes integral for arbitrary increasing integrator, including constants and discontinuous ones, and derives integrability of the parameter derivative slice. The key continuity is uniform in the integration variable at one parameter, not global joint continuity; joint continuity is only the attached sufficient condition. Section 9.43 requires absolute convergence and improper-integral limits, as well as differentiability, the differential equation, and the explicit value. Bare totalized Bochner integrals require a bridge to these source notions.

## Source qualifications

- The contraction theorem's fixed-point existence presumes a nonempty space, consistent with choosing an arbitrary starting point. Lean permits empty metric spaces; an explicit nonemptiness hypothesis is necessary and faithful, not a loss of generality relative to the source convention. A contraction constant may be normalized to the interval `[0,1)` without changing the property.
- In 9.40, the signed expression `h*k` remains correct for negative side increments. The source's informal comparison with geometric area should not be encoded as `area = h*k` without sign qualifications.
- In 9.42, the derivative expression in the uniform hypothesis presupposes local existence, which must be explicit in a formal statement. Since the parameter is interior, the uniform condition may be written with a sufficiently small neighborhood contained in `(c,d)`.
- In 9.43, the intermediate integration-by-parts expression divides by `t`; any separately exported version needs `t != 0`. The final differential equation and closed form hold for every real `t`, including zero. The formula at zero uses Gaussian normalization referenced to 8.21. Because the authorized earlier source files are frozen and that numbered node remains pending, a new local bridge is needed; the reference does not license marking 8.21 complete.

## Review status

The full 43-node source inventory is established independently of Chapter 9 implementation. Exact Lean contract acceptance, independent boundary clients, source hashes, compilation, and recursive axiom verification remain separate gates. No production theorem is marked accepted by this inventory alone.
