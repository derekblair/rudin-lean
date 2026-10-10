# Chapter 5 hostile review A

**PASS for PMA 5.1–5.6 and 5.13–5.19 in the exact candidate below. No confirmed
blocking or nonblocking mathematical defect was found.** This is a new adversarial
review, not a relabeling of earlier fidelity reports. It is not a production
build result or a whole-chapter PROVED stamp.

Reviewer: the middle-node agent. I did not author the thirteen reviewed nodes.
I authored 5.7–5.12, so those nodes are excluded from this semantic verdict and
are assigned to another reviewer. I previously reviewed the separate Taylor
and oscillation drafts; this pass reread the actual assembled definitions,
contracts, proof helpers, source bridges, and probes and added new attacks.

Source scope is the independently accepted `research/pma-ch05-inventory.md`
and `evidence/pma-ch05-source-review.md`. This review does not claim a fresh
page-by-page extraction from the book. No copyrighted book text was copied.
Pinned Lean: 4.34.1; Mathlib:
`d13f23b723b8a846827a245b89c10fc7d3f11612`.

## Exact reviewed artifacts

| File | SHA256 |
|---|---|
| `rudin/Rudin/PMA/Chapter05.lean` | `55acec19c187d4ae0d6bfc37c78ee32df5711a997f3d4e0aeea876eb876904cb` |
| `rudin/Rudin/PMA/Chapter05Probes.lean` | `a59995311bfe25b74920cee0aef6ed6ed3674c4568374058c141c1fcb0f96093` |
| `rudin/Rudin/PMA/Chapter05Audit.lean` | `d8dbffc66740e026638a4c0bba1dbcacfb69594b706c92116aef9435fa18a0d9` |
| `rudin/Rudin.lean` | `ecb07140e6e5bdb8e69b82312225fcdddd761e37588f0e53871e64be0c5ca73e` |

All 26 entries of `evidence/ch06-inherited-ch05-hashes.json` still match after
review. Acceptance is invalid for changed mathematical bytes until rereviewed.

## Adversarial findings by node

Line locations refer to the reviewed main chapter.

| Node / location | Attack and result |
|---|---|
| 5.1, lines 22–71; proofs 118–280 | Checked all fourteen contract conjuncts. Domain membership and Chapter 4's explicit accumulation condition exclude isolated-set and open-endpoint false positives. The punctured `Ioo`/`Icc` equality handles both endpoints separately under `a<b`; ordinary interior and one-sided endpoint comparators are exact. Uniqueness is established from the nonvacuous source limit, not asserted for arbitrary library within-derivatives. Differentiability-on includes the domain-subset condition. |
| 5.2, lines 73–76 and 282–287 | Continuity is relative to the same domain and retains endpoint values. The proof obtains actual `HasDerivWithinAt` plus membership from the source predicate. No interior-only restriction appears. |
| 5.3, lines 78–89 and 289–316 | Sum and product derivatives have the correct coefficients. Quotient needs only `g(x)≠0`; it restricts the domain to nonzero denominator points and proves equality of punctured approach filters. Continuity supplies a local nonzero neighborhood, retaining accumulation; no global nonvanishing or totalized-division shortcut replaces the source domain. |
| 5.4, lines 91–107 and 318–366 | All six clauses are present. Integer exponents use `x≠0 ∨ 0≤n`; zero is excluded exactly for negative powers. A separate exponent-zero clause gives derivative zero at zero. Polynomial derivatives and rational quotient formulas are actual finite values, with the rational function restricted only where its denominator vanishes. |
| 5.5, lines 109–116 and 368–374 | Outer derivatives are relative to a containing interval `J`, not a global two-sided derivative. The range map gives the within-chain rule at both inner and outer endpoints. Redundant continuity/interval hypotheses do not strengthen the accepted source statement. The canonical absolute-value endpoint probe demonstrates applicability when the outer total extension has a cusp. |
| 5.6, lines 387–542 | All nine conjuncts are proved: both zero values, linear continuity, both off-zero formulas, failure of the linear derivative at zero, quadratic differentiability everywhere, quadratic zero derivative, and discontinuity of its actual derivative. The non-differentiability argument invokes the independently proved no-side-limit result for the sine quotient. Arbitrarily small positive witnesses with derivative −1 contradict continuity at the genuine value zero. Totalized formulas do not extend the off-zero derivative to zero; the boundary counterexample rejects precisely that mistake. |
| 5.13, lines 752–1100 | All four approaches are nontrivial; targets range over all `EReal`. The zero/zero branch allows arbitrary target filters, and its comap bridge covers ±∞ without inventing a finite limit. Infinite-denominator branches contain no limit or boundedness premise on the numerator. The convex-tail anchor proof uses only a fixed finite numerator value at the anchor. The negative-denominator branch negates numerator and denominator together, preserving the ratio and target. Eventual denominator nonvanishing is an output. Source interval filters cover bounded intervals, half-lines and both infinities with no endpoint derivative premise. |
| 5.14, lines 1127–1168 | All four clauses are checked. Successor existence requires predecessor existence throughout a relative neighborhood and differentiability of its actual iterated value. For points of the domain, neighborhood membership includes the point and recovers every predecessor. This blocks totalized derivative values from manufacturing higher derivatives at a cusp. Arbitrary-set generality does not claim uniqueness on isolated sets; source applications use nondegenerate intervals. |
| 5.15, lines 1170–1340 | All three clauses are present: Lagrange equality, absolute bound, and order-one MVT. Highest predecessor existence is explicit on `Icc`; its continuity is the only highest-order continuity assumption. The proof derives `ContDiffOn` only through `n−1`. Subinterval coefficient transport uses unique differentiability on both intervals; the nth derivative transfers using actual differentiability at the interior witness, not nth continuity. `uIoo` allows either point order; the signed `(β−α)^n` is retained. The canonical reversed cubic probe checks the odd negative sign. Order-one hypotheses are equivalent to closed continuity plus open differentiability, without endpoint derivatives. |
| 5.16, lines 1351–1432; bridge 1691–1700 | All six clauses are checked. Input scalars are real; complex output is not confused with complex analytic differentiation. The norm quotient uses real scalar inverse; the final bridge equates its punctured closed-cell approach to the source interior approach at endpoints. Complex real/imaginary and Euclidean coordinate comparators reconstruct the same derivative. The continuity/sum clause can recover continuity from one derivative by choosing the second function equal to the first; it imposes no additional meaningful hypothesis. Complex product/quotient and real Euclidean inner-product coefficients are correct. |
| 5.17, lines 1434–1465 | Euler form, both endpoint values, actual velocity and unit norm are explicit. The failed MVT equality uses positive interval length and nonzero velocity norm, not an empty witness interval or a preassumed failure. |
| 5.18, lines 1467–1606 | The phase is literally `I/(x:ℂ)^2`; velocity is `1+(2*x−2*I/x)*phase`. All seven interval assertions and four limits are retained, including nonzero `g` and `g'`, both lower norm bounds and the derivative-ratio bound. The derivative is ultimately a real-input derivative (`comp_ofReal`). Quotient rewriting is performed only eventually at positive nonzero inputs. Limit one for `f/g` and zero for `f'/g'` are distinct under the nontrivial approach filter; a separate theorem explicitly rejects the false zero limit for the function ratio. |
| 5.19, lines 1608–1659 | Existential norm inequality, arbitrary uniform bound, and finite supremum consequence all remain. No bound is a premise of the existential theorem and no endpoint derivative is assumed. Scalar projection plus Cauchy–Schwarz yields the existential point; the zero displacement case is separate. `BddAbove` guards the real supremum, avoiding totalized `sSup` on unbounded ranges. The inventory's unbounded extended-supremum case is the trivial +∞ bound, not falsely represented by a real supremum. |

The source bridges use the actual Chapter 4 definitions, inspected during this
pass: `FunctionLimitOn` includes accumulation, one-sided limits have the correct
endpoint inequalities, and `ExtendedLimitOn` includes extended accumulation.
Pinned Mathlib's four zero/zero l'Hôpital interfaces and
`taylor_mean_remainder_lagrange` were inspected directly. The latter requires
continuity through the predecessor order and differentiability of that
predecessor on the interior; no hidden nth-continuity requirement enters.

## Fresh validation and probes

- `./lake-local env lean Rudin/PMA/Chapter05.lean`: exit 0. This checks the actual
  assembled source, not merely cached theorem signatures. Its intermediate
  5.13 audit checked 171 declarations and allowed only the standard three axioms.
- `./lake-local env lean Rudin/PMA/Chapter05Audit.lean`: exit 0; recursive audit
  checked 267 chapter declarations and separately the nine standalone probes,
  allowing only `propext`, `Classical.choice`, and `Quot.sound`.
- `python3 -B scripts/check_chapter.py 5`: exit 0, 19/19, zero queued; source and
  metadata checks passed. This is coverage/token evidence, not semantic proof.
- Six new theorem probes compiled together through `lean --stdin` and passed
  their own recursive axiom audit: six declarations, standard axioms only.

The new probes instantiate the reviewed public interfaces:

1. `1/x → 0` at +∞ through 5.13 with numerator constantly one. This exercises the
   infinite-denominator branch when the numerator does not tend to zero.
2. `x²/(-x) → -∞` at +∞ through 5.13. This exercises a negative infinite
   denominator and a negative infinite target together.
3. `x/x² → +∞` at 0+ through the zero/zero branch. This checks that its target
   is not restricted to a finite real value.
4. The quadratic oscillation satisfies order-one Taylor hypotheses on `[-1,1]`
   although its first derivative is discontinuous at zero. Thus highest-derivative
   continuity is not accidentally hidden in that hypothesis.
5. Complex relative continuity follows from just one given derivative via the
   continuity/sum contract; its second-function parameter creates no narrowing.
6. At `x=1/2`, the complex counterexample has nonzero denominator and derivative,
   and derivative-ratio norm at most `1/3`, checking a concrete nonvacuous case.

Early versions of these temporary probes had function/instance elaboration,
filter-unfolding and universe errors. Those failed runs were rejected by the
axiom audit; they were not retained as evidence of a successful theorem. The
corrected six-probe run exited 0. No probe or source file was written, and no
review-source edit was needed.

## Limits and integration gate

This review finds no confirmed P0/P1/P2/P3 issue in the assigned nodes. Finite
probes are not an exhaustive proof of fidelity; the per-conjunct source comparison
and actual Lean proofs supply the main evidence. Mathlib reuse follows the
accepted scope and does not enforce the book's original proof-dependency order.

Whole-chapter hostile acceptance still requires review B for 5.7–5.12. Production
integration must match the exact four hashes above and pass production build,
coverage and recursive axiom checks. No production mutation, commit, push,
network operation, session control, software installation, or credential access
was performed in this review. Only this new evidence file was created.
