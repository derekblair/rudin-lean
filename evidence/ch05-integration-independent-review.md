# Chapter 5 integration bridge and standalone probes: independent review

**Verdict: PASS.** The root-authored vector source bridge is sufficient, and all nine final standalone probes make relevant, nonvacuous assertions about the accepted Chapter 5 scope. No correction is requested.

Reviewer: `/root/vectors`, acting independently on the root's integration bridge and probe file. This review edited only this evidence document. It did not modify any Lean source, shared checkout, Git state, configuration, dependency, or session.

## Reviewed sources and stable hashes

| File | SHA-256 |
| --- | --- |
| `rudin/Chapter05Integration.lean` | `93b2e6db417ea6f2236bd6956bb9c1efad7a2f62b55b2685f1405d0e0179d861` |
| `rudin/Rudin/PMA/Chapter05Probes.lean` | `a59995311bfe25b74920cee0aef6ed6ed3674c4568374058c141c1fcb0f96093` |
| `rudin/Rudin/PMA/Chapter05.lean` | `55acec19c187d4ae0d6bfc37c78ee32df5711a997f3d4e0aeea876eb876904cb` |

The final integrated Chapter 5 hash identifies the dependency used during this review; it is not a claim of a new independent full review of all nineteen nodes. The bridge is present verbatim at the end of that integrated chapter. All three hashes were checked before and after the independent compilation and remained unchanged.

## Source-approach bridge

`vectorDerivativeWithin_source_iff` compares `VectorDerivativeWithin f v a b x` directly with convergence to zero of the norm of the real scalar difference quotient minus `v`, taken through `Ioo a b \ {x}`. Its assumptions are exactly `a < b` and `x ∈ Icc a b`.

Its use of `interval_punctured_Ioo_eq_Icc hab hx` is sufficient: this equality concerns the input filter alone, so it applies unchanged to the vector norm-limit function for every real normed codomain. The proof preserves the value `f x`, the proposed derivative `v`, the puncture, and the one-sided approach at either endpoint. It neither strengthens the source approach to a two-sided limit at endpoints nor removes the nondegeneracy/domain-membership guards. In combination with the existing `vectorDerivativeWithin_iff`, the source interior-approach definition is formally equivalent to the reference within-derivative under the stated guards. This closes the integration obligation noted in the preceding vector review.

## Nine semantic probes

| Declaration | Scope issue checked | Review result |
| --- | --- | --- |
| `open_endpoints_excluded` | An open-domain function has no endpoint derivative merely because a total function extension exists. | Both endpoint exclusions follow from required domain membership; valid even if the open interval is empty. |
| `singleton_derivative_rejected` | A vacuous library within-derivative on an isolated set must not count as a source derivative. | Uses the required limit-point condition and the nontrivial punctured filter, so this is a substantive rejection. |
| `zero_integer_power_at_zero` | The integer zero-power case must retain the derivative of a constant at zero. | Extracts the applicable 5.4 conjunct and proves the source derivative with value zero. |
| `negative_integer_power_excludes_zero` | Negative-power domains must exclude zero. | Tests the explicit integer-power domain at exponent −1. |
| `chain_rule_outer_endpoint_abs` | The outer function need only have the appropriate relative endpoint derivative. | Applies the actual chain-rule contract to absolute value restricted to `[0,1]`, while also proving its failure of ordinary two-sided differentiability at zero. This detects an accidentally overstrong outer hypothesis. |
| `mvt_without_oneSided_endpoint_derivative` | Mean value needs no endpoint derivative. | Produces a genuine interior MVT witness for the continuous oscillatory example, then rules out every finite one-sided source derivative at zero using the nonexistence of the right limit of the oscillating difference quotient. The second conjunct is stronger and more pertinent than merely denying two-sided differentiability. |
| `derivative_secondKind_discontinuity` | Darboux's corollary must allow discontinuities of the second kind. | Combines an everywhere differentiable example's discontinuous derivative with the proved absence of first-kind discontinuities; the resulting claim uses the explicit Chapter 4 second-kind definition. |
| `reversed_third_order_remainder` | Reversing Taylor's expansion/evaluation points must retain the sign of an odd power. | Specializes the actual Taylor theorem to order 3, expansion point 1 and evaluation point 0, and obtains the negative third-derivative term divided by 6 with an interior witness. It retains the source differentiability hypotheses without adding continuity of the third derivative. |
| `higher_order_cusp_rejected` | Iterated totalized derivatives must not imply actual higher derivative existence. | Rejects order 2 for absolute value at its interior cusp by propagating the existence predicate to order 1 and invoking the checked first-order cusp failure. |

The reviewed statements are successful boundary/scope checks, not general-purpose tests mirroring proof implementation. They deliberately exercise restrictions and extensions that could otherwise be lost in a superficially compiling translation.

## Independent kernel checks

From the isolated workspace root, after the root announced final source stability:

```text
./lake-local env lean Rudin/PMA/Chapter05Probes.lean
Exit code: 0
Output: none
Warnings: 0
```

A separate `./lake-local env lean --stdin` invocation imported the final probe module and ran `#print axioms` for the integrated `vectorDerivativeWithin_source_iff` and each of the nine probe declarations. It exited with code 0. Every recursive dependency report contained exactly:

```text
[propext, Classical.choice, Quot.sound]
```

Thus the ten declarations inspected in this review contain no forbidden axiom in their transitive proof dependencies. The root's reported whole-project build and 267-declaration chapter audit are separate evidence; this review independently establishes the specific bridge/probe compile, semantics, and axiom checks above.

No blocker remains within this review's scope. Production integration, commits, and publication permissions are outside this review.
