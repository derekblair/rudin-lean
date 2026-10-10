# Independent final-source review: PMA 5.1–5.5

**Verdict: ACCEPTED. No mathematical statement or proof correction is required for the five reviewed nodes.**

Reviewed file: `rudin/Chapter05OpeningDraft.lean`, SHA-256 `879ab85337e9e2a697459b7b834a3003201a1ef023580f5baa18abf9ef19bc44`. Reviewer: the separate Taylor subagent, which did not author or edit this source. The review compares the actual definitions, every contract conjunct, and the final proofs with the accepted Chapter 5 inventory and independent source inventory review. It also reads the relevant copied Chapter 4 definitions and pinned Mathlib rule signatures. The copyrighted book was neither copied nor reproduced.

## PMA 5.1: Definitions and all fourteen contract conjuncts

`DifferenceQuotient f x t` has the correct orientation `(f t − f x)/(t − x)`. Its value at `t=x` is irrelevant because every limit used for derivatives is punctured. `HasDomainDerivative S f x d` requires both membership `x ∈ S` and Chapter 4's `FunctionLimitOn`; the latter explicitly requires `Chapter02.IsLimitPoint x S`. Thus neither isolated points nor an empty approach filter can certify an arbitrary derivative. The comparison with `HasDerivWithinAt` keeps this accumulation requirement instead of discarding it.

`DomainDifferentiableAt` means existence of an actual derivative witness, not a statement about a totalized library derivative value. `DomainDifferentiableOn S A f` records `A ⊆ S` and differentiability at each point of `A` using the original domain `S`. Restricting the set of points where differentiability is requested therefore does not accidentally change approach directions.

The contract's conjuncts were checked individually:

1. The general reference equivalence has domain membership, accumulation, and the relative Mathlib derivative.
2. On a nondegenerate closed interval and for every point of it, the derivative is equivalent to the source limit through the open interior `(a,b)`.
3. At an interior point, it agrees with the ordinary derivative.
4. At the left endpoint, it agrees with the right derivative.
5. At the right endpoint, it agrees with the left derivative.
6. The right derivative agrees with the derivative within `[x,+∞)` when the right side is available.
7. The left derivative agrees with the derivative within `(−∞,x]` when the left side is available.
8. At an interior point, existence of the derivative with value `d` is equivalent to both side derivatives having that same value.
9. Derivative values are unique.
10. Differentiability is equivalent to existence of a unique derivative value.
11. On the closed interval, differentiability agrees with the reference relative differentiability predicate.
12. The corresponding on-a-subset comparison retains the original interval as the derivative domain.
13. The totalized `derivWithin` value is identified with the source derivative only under actual derivative existence and interval uniqueness.
14. Neither endpoint is differentiable as a point of an original open-interval domain, because that point is absent from the domain.

The important source-filter bridge is proved, not assumed: `interval_punctured_Ioo_eq_Icc` handles the left endpoint, right endpoint, and interior separately. Removing the current endpoint and ignoring the remote endpoint makes the two local punctured filters equal. The source limit's accumulation condition is transferred through this equality. This avoids substituting a two-sided endpoint derivative or using an endpoint outside the original domain.

The separate right/left derivative predicates carry Chapter 4's side-availability bounds (`a ≤ x < b` or `a < x ≤ b`). Their interval interpretation is supplied by the endpoint and interior bridges. They are not declarations that an original open-domain function has a defined endpoint value.

## PMA 5.2–5.5

| Node | Independent assessment |
| --- | --- |
| 5.2 | Actual relative differentiability implies the copied Chapter 4 relative continuity predicate. The proof preserves domain membership and includes both endpoints. No global continuity conclusion is substituted. |
| 5.3 | Sum and product values have the correct formulas. The quotient requires `g x ≠ 0` only at the point. Its domain is exactly `S ∩ {t | g t ≠ 0}`. Within-domain continuity of `g` supplies local nonvanishing; explicit equality of punctured filters transfers accumulation to the quotient domain. The derivative formula is `(g x * df − f x * dg)/(g x)^2`. No global denominator condition is introduced, and totalized division outside the quotient domain is not used to enlarge the source claim. |
| 5.4 | Constants and identity have their expected derivatives. Integer powers include every integer, with domain `{x | x ≠ 0 ∨ 0 ≤ n}`: negative powers exclude zero, while nonnegative powers include zero. The domain is proved open, which supplies accumulation. The separate zero-exponent clause proves the constant-one derivative directly at every point, including zero, so source interpretation does not depend on an undefined negative intermediate power. Polynomial and rational formulas are explicit; rational functions are restricted exactly to nonzero denominator values. |
| 5.5 | The original inner interval is nondegenerate, the evaluation point belongs to it, the outer domain is order-connected, and it contains the entire inner image. Source continuity of the inner function is retained. Both derivative assumptions are domain-relative, including the outer derivative at a boundary point of its interval. The result is the composition derivative `dg * df` on the original inner interval. |

The chain proof invokes `HasDerivWithinAt.comp` with the actual `MapsTo` premise. It does not replace the outer derivative with `HasDerivAt` or require the outer function to be globally differentiable. Some source assumptions (global inner continuity and order-connectedness of the outer domain) are redundant for the stronger general relative-chain rule used in the proof; leaving them unused does not weaken or strengthen the stated source theorem.

For integer powers, the general symbolic formula at `n=0` is evaluated in Lean's totalized field operations, but the additional constant-one clause proves and states the intended value zero independently. Negative exponents remain excluded at zero by domain membership, so totalization does not authorize a source-forbidden negative power there.

## Independent verification and probe scope

Fresh command from the isolated root:

```text
./lake-local env lean Chapter05OpeningDraft.lean
```

Result: exit 0, no diagnostics. Independently fed the unchanged full source plus `#print axioms` for every declaration into `./lake-local env lean --stdin`; all **38 declarations** passed and reported only `[propext, Classical.choice, Quot.sound]`. The actual source contains no placeholders, custom axioms, or native decision procedures. The pinned integer-power and relative-chain-rule signatures match the hypotheses supplied by their proofs.

This final draft contains extensive reference-equivalence and domain-filter proofs but no separately named boundary-probe suite. The parent owns those integration probes. Useful checks to retain are: rejection of derivatives on singleton/empty domains; exclusion of open-interval endpoints; the zero power at zero; negative-power domain rejection at zero; a quotient whose denominator vanishes elsewhere; and a chain-rule instance whose outer total extension is not two-sided differentiable at its interval endpoint. This report certifies the actual definitions, contracts, and proofs, not the yet-unreviewed integration probe suite.

The formalizations use total functions together with explicit original domains, a standard representation of partial textbook domains. Imported Mathlib supplies reference results through its full dependency environment, so the proof dependencies do not enforce textbook chapter order. No accepted mathematical scope from 5.1–5.5 is omitted or queued.

No opening-source edits were made. Only this independent review file was written. Final chapter integration and its aggregate build remain the parent task's responsibility.
