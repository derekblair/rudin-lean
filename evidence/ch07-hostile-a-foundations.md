# Additional hostile gate A: PMA 7.1 and 7.7–7.9

Verdict: **ACCEPT; no finding**. This is a fresh adversarial supplement to the earlier fidelity review and to the main A reviewer, who authored this cluster. I authored none of Basic or Foundations. I read the entire actual Basic and 184-line Foundations modules, including all contract conjuncts and proofs, against the accepted inventory.

## Exact scope and snapshots

- `rudin/Rudin/PMA/Chapter07/Basic.lean`: SHA256 `b6b8b58999ad0025fd3ab28bc0ba3a4df5a07cc395158b99a14c05055bfa2b1a`.
- `rudin/Rudin/PMA/Chapter07/Foundations.lean`: `941938d68a48db2a4e0ab70ba0b39d51828fc91602a4583ab449f8ad1c4d5742`.
- Accepted inventory: `research/pma-ch07-inventory.md`, `f8e87ad7ccb765bfd4407e251958c5378552b209d32eca60a75e13e0ca9da0f0`.
- Persisted fresh client: `rudin/Chapter07FoundationsHostileProbe.lean`, `3b7be894331abe9419b7a2907945e4758bedeb77543d061c48d6c7eb8c5de2ea`.

Fresh source compilation and the final client both passed with exit 0 and no warnings:

```sh
./lake-local env lean Rudin/PMA/Chapter07/Foundations.lean
./lake-local env lean Chapter07FoundationsHostileProbe.lean
```

The client verifies all four principal declarations are kernel theorems and recursively audits all 43 visible Chapter07/client declarations. Only `propext`, `Classical.choice`, and `Quot.sound` occur. This count covers the imported scope, not the entire final chapter. Source scans found no placeholders, custom axioms, unsafe implementations, or alternate proof bodies.

## Attacks on actual definitions and quantifiers

**Totalized limits and ordered series (7.1/7.7).** Pointwise convergence is actual `Tendsto` at each point. The existence equivalence constructs a limit function from numerical limits and proves convergence to it; it does not name an unconstrained totalized operator. The series definitions use Chapter 3 `SeriesHasSum` and `PartialSums` with `Finset.range N`, preserving order. They are not unconditional `Summable` assertions. The uniform epsilon clause has one eventual index before all domain points, and the non-strict error bound is proved equivalent to the usual strict formulation by tolerance shrinking.

**Existence and completeness (7.8).** The Cauchy direction concludes existence of a uniformly convergent function sequence limit, rather than assuming a pointwise limit in advance. Completeness is explicit and applies in particular to complex values. The proof obtains pointwise Cauchy limits, chooses values on the set, assigns zero outside it, and uses the uniform Cauchy condition to upgrade pointwise convergence. No topology or nonemptiness of the domain is added. The reverse implication has the full two-index condition.

**Infinite and empty suprema (7.9).** `UniformError` is an extended nonnegative supremum over the subtype of the domain. Its definition allows infinity and gives zero on the empty domain. The real-supremum comparator separately requires `BddAbove` of the actual error image; its proof handles the empty set and nonnegativity before using `toReal`. No bound on all initial sequence errors is smuggled into the equivalence. The proof of uniform convergence iff error tends to zero directly compares eventual epsilon estimates; it does not depend circularly on the wrapper under review.

## Nine fresh adversarial probes

1. The sequence whose first member is the unbounded real identity and all subsequent members are zero converges uniformly on all of `ℝ`.
2. Its first `UniformError` is exactly infinity, proved by evaluating the supposed finite bound at that bound plus one.
3. Nevertheless its extended error sequence tends to zero by the actual 7.9 theorem. This directly attacks an illicit “every error is bounded” strengthening.
4. The moving complex indicator `F n x = if n=x then 1 else 0` on `ℕ` converges pointwise to zero.
5. The same sequence fails uniform convergence, by choosing the moving point after the proposed eventual index.
6. It also fails the actual two-index uniform Cauchy condition, with indices `N` and `N+1` and point `N`.
7. The actual Cauchy criterion produces a uniform limit on the empty domain for any complex sequence.
8. The bounded real-supremum comparator gives both zero error and zero `toReal` error on the empty domain.
9. A purely imaginary constant error has supremum one, preventing a real-part-only interpretation of the complex norm.

The first client iteration needed explicit universe instantiation for the independent conjuncts of `pma7_9` and an explicit type for an indexed-supremum inequality; those were client elaboration repairs, not source findings. The final file is warning-free and contains no placeholder. No reviewed source or protected/production file was modified. The assessment covers these four nodes only and makes no hostile-review claim for the Calculus module I authored.
