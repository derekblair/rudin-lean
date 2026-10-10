# Independent semantic review: PMA 5.14–5.15

**Verdict: ACCEPTED for the isolated draft. No semantic correction or remaining blocker.**

Reviewer: fresh middle-node agent, which did not author the Taylor implementation. Reviewed actual definitions, contracts, all proof helpers, and boundary probes in `rudin/Chapter05TaylorDraft.lean` against the accepted `research/pma-ch05-inventory.md` and `evidence/pma-ch05-source-review.md`. Also inspected the pinned Mathlib statement and proof interface for `taylor_mean_remainder_lagrange`. This is a review against the independently accepted source inventory, not a new extraction of copyrighted source pages.

Reviewed source SHA-256: `b294ca03411cd208e5d9afc5e23fe9ceadd213c1333552edba3a917da8abb737`.

## Statement fidelity

- **5.14 actual existence (lines 16–31).** At order zero the value is the original function. Successor existence requires predecessor existence throughout a relative neighborhood and differentiability of that predecessor at the point. This is substantive extra information beyond a totalized `iteratedDerivWithin` value. At a point of the domain, `HigherExistsWithin.predecessor` and `.lower` correctly recover every lower-order existence assertion; the neighborhood includes the point. Relative neighborhoods provide one-sided endpoint semantics on nondegenerate closed intervals.
- **No totalized-value false positive.** The recursion requires differentiability, not equality to an arbitrary library derivative value. The existing cusp probe rejects first derivative existence for absolute value at zero inside `[-1,1]`. An additional independent probe also rejected second derivative existence there through the lower-order implication.
- **5.15 hypotheses (lines 58–61).** Order `n−1` exists across `[a,b]` and is continuous there; order `n` exists on `(a,b)`. Making predecessor existence explicit expresses the source's implicit meaning of a derivative function, rather than adding a differentiability assumption beyond that source meaning. There is no order-`n` continuity premise. `higherExists_contDiffOn` derives lower continuity from derivative existence, obtaining `ContDiffOn` only through order `n−1`.
- **Original-domain endpoint coefficients.** The Taylor polynomial is the sum for `0 ≤ k < n`, with coefficient `iteratedDerivWithin k f (Icc a b) α`, displacement `(β−α)^k`, and factorial denominator. Every coefficient remains a derivative on the original interval. Its existence follows from the explicit order-`n−1` hypothesis and `.lower`.
- **Subinterval transport (lines 108–148).** The proof establishes unique differentiability on both the original nondegenerate interval and the nondegenerate interval between `α` and `β`. Orders through `n−1` transfer using the derived `ContDiffOn` hypothesis. Order `n` transfers using differentiability of the predecessor at the interior witness, not continuity of order `n`. The witness lies in `(a,b)` even when one or both chosen points are original endpoints.
- **Either point order and sign.** The only ordering restriction on `α,β` is inequality; `uIoo α β` means strictly between them in either order. The signed factor `(β−α)^n` remains intact in the equality. A separate independent order-three specialization at `α=1`, `β=0` verified that the remainder appears with a minus sign.
- **Attached consequences.** The contract includes the absolute remainder bound with a derivative bound only between the selected points and the `n=1` mean-value identity. The existing `taylorHypotheses_one_iff` proves that order-one hypotheses are exactly continuity on the closed interval plus differentiability on its open interior, so endpoint differentiability is not hidden in the base case. No unnecessary positivity premise on `M` is introduced: the bound on the nonempty interior already entails nonnegativity.

## Independent validation

`./lake-local env lean Chapter05TaylorDraft.lean` passed with exit 0. An independent stdin compilation of the unchanged source plus all-declaration axiom commands and the three additional probes below also passed with exit 0. All **18 named declarations** recursively depend only on `propext`, `Classical.choice`, and `Quot.sound`.

The additional probes were compiled in memory; the reviewed source was not modified:

1. `HigherExistsWithin abs (Icc 0 1) 1 0` holds, validating a genuine one-sided endpoint derivative despite the total extension's cusp.
2. `¬ HigherExistsWithin abs (Icc (-1) 1) 2 0`, validating lower-order rejection of a totalized higher derivative.
3. For arbitrary `f` satisfying `TaylorHypotheses f 0 1 3`, there is `x∈(0,1)` such that `f 0 = TaylorPolynomialValue f 0 1 3 1 0 - iteratedDerivWithin 3 f (Icc 0 1) x / 6`, validating reverse orientation and an odd-order sign.

## Scope and integration limits

The generic higher-existence predicate also accepts arbitrary sets, but derivative uniqueness on arbitrary isolated sets is not claimed. The intended source application and Taylor theorem use `a<b` and points in the closed interval, where the actual relative derivatives are unique. This generalization creates no weakening of the book-interval claims.

The proof imports pinned Mathlib and does not enforce the book's original proof-dependency order. No accepted mathematical scope from 5.14 or 5.15 is omitted. Complete chapter integration, source-difference-quotient bridge use, and the final integrated build remain the root's gate. This review changed only this evidence file; no Taylor source, shared checkout, book, sessions, global configuration, commits, or remote state was changed.
