# Independent final-source review: PMA 5.7–5.12

**Verdict: ACCEPTED. No mathematical statement or proof correction is required for the six reviewed nodes.**

Reviewed file: `rudin/Chapter05MiddleDraft.lean`, SHA-256 `dc609125c4364b857f0c6d1d64088ab4094c1f561bc5b55ee1d3fdc523ecc2b0`. Reviewer: the separate Taylor subagent, which did not author or edit the reviewed file. The review reads actual contracts and proofs against `research/pma-ch05-inventory.md`, `evidence/pma-ch05-source-review.md`, the copied Chapter 4 definitions, and the invoked pinned Mathlib signatures. It does not rely on the author's design report as proof of acceptance.

## Statement and proof fidelity

| Node | Independent assessment |
| --- | --- |
| 5.7 | Both definitions use a strictly positive metric radius and non-strict function-value inequalities. They are proved equivalent to the reference neighborhood-filter local extrema. The metric-space domain itself supplies the source domain; no continuity assumption is introduced. |
| 5.8 | `x ∈ Ioo a b` ensures both nondegeneracy and that the interval is a neighborhood of the point. The derivative and extremum are initially relative to the closed interval; their conversion to ordinary local objects is justified by that neighborhood. Both minimum and maximum cases prove the derivative value is zero. |
| 5.9 | Closed-interval continuity and ordinary derivative witnesses only on the open interval imply the cross-multiplied Cauchy identity. There is no endpoint derivative or nonzero-derivative premise and no division that might discard constant cases. The reference theorem's reversed equation is correctly reversed back. |
| 5.10 | The hypotheses likewise impose no endpoint derivative premise. The reference slope identity is multiplied by the nonzero interval length, giving the exact source equality and a strictly interior witness. |
| 5.11 | The hypotheses concern differentiability only on the open interval. Continuity there is derived, with no endpoint continuity added. Nonnegative derivatives give non-strict monotonicity, nonpositive derivatives give non-strict antitonicity, and zero derivatives yield equality for every pair of points, regardless of their ordering. |
| 5.12 | Differentiability on the closed interval remains `HasDerivWithinAt`, with an explicitly supplied derivative-value function. Darboux attainment covers both strict endpoint-value orderings and has an interior witness. Both finite one-sided limit equalities are included, and the actual Chapter 4 first-kind predicate is excluded. No derivative-continuity assumption is added. |

### Endpoint and discontinuity details

The copied Chapter 4 `LeftLimitOn a b f' x l` requires `a < x ≤ b` and convergence through `(a,x)`. Hence the left-limit assertion in the 5.12 contract includes the right endpoint `x=b`. `RightLimitOn` requires `a ≤ x < b`, so the right-limit assertion includes `x=a`. The strict inequality on the available side prevents a vacuous neighborhood from supplying arbitrary finite limits.

The one-sided helpers first identify the supplied derivative values with ordinary `deriv f` only at genuinely interior nearby points. They then apply the appropriate finite-derivative-limit extension theorem. Continuity of `f` at the target follows from its existing relative derivative; it is not a new premise. Finally, derivative uniqueness on `[a,x]` or `[x,b]`, made nondegenerate by the one-sided-limit predicate, identifies the limiting value with `f' x`. The helpers therefore apply at source endpoints without claiming that the chosen total extension is two-sided differentiable there.

Chapter 4's `FirstKindDiscontinuityOn` is deliberately an interior two-sided classification. Its definition requires an actual discontinuity and both finite side limits; it includes both jumps and removable discontinuities. For interior points, the final conjunct uses the proved side-limit equalities and Chapter 4's continuity equivalence to rule out that full predicate. At endpoints, finite side limits differing from the endpoint derivative are ruled out by the preceding conjuncts, so endpoint jump/removable cases are not silently omitted. These assertions do not claim that finite side limits always exist or that derivatives are always continuous.

The permitted second-kind phenomenon is an integration obligation supplied by the accepted 5.6(b) example, as specified in the inventory. It is not separately reconstructed in this middle file. Acceptance of these six nodes does not certify completion of 5.6(b).

## Independent verification

Fresh command from the isolated root:

```text
./lake-local env lean Chapter05MiddleDraft.lean
```

Result: exit 0, no diagnostics. Independently fed the unchanged full source plus a `#print axioms` command for each declaration to `./lake-local env lean --stdin`. All **19 declarations** passed; each reports only `[propext, Classical.choice, Quot.sound]`. This includes both local-extremum definitions, six contracts, six node theorems, two finite-side-limit helpers, and three probes. A text inspection found no proof placeholders, custom axioms, native decision procedures, unsafe declarations, or local checker-option overrides.

The pinned Mathlib Darboux signatures match the supplied relative derivative hypotheses. The finite-derivative-limit extension signatures require differentiability near the point, continuity of the original function at the point, and convergence of its derivative; those obligations are explicitly discharged. The imported proof environment does not enforce Rudin's book-order dependency graph, and this acceptance does not claim it does.

## Probe adequacy and one optional improvement

The identity-on-`[0,1]` endpoint minimum probe correctly shows that the interior restriction in Fermat's theorem cannot be dropped. The absolute-value endpoint probe correctly distinguishes relative endpoint differentiability from two-sided differentiability of the total extension. The MVT application to absolute value checks that the proved theorem is usable without a two-sided endpoint derivative.

There is one limited coverage point: absolute value on `[0,1]` still has a finite right derivative at zero. Therefore the probe named `middle_probe_MVT_without_endpoint_differentiability` should be described as testing absence of **two-sided** endpoint differentiability, not absence of the source's one-sided endpoint derivative. The current design report makes this qualification correctly. An optional stronger boundary probe could apply the theorem to square root on `[0,1]` and show that no finite right derivative exists at zero. This is not a statement/proof defect or an acceptance blocker: the actual 5.9 and 5.10 contracts visibly contain no endpoint derivative assumption of either kind, and the checked proofs introduce none.

No middle-source edits were made. Only this independent review report was written. Integration and a complete chapter build remain the parent task's responsibility.
