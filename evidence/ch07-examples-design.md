# Chapter 7 opening examples: contract and proof record

Owned draft: `rudin/Chapter07ExamplesDraft.lean`; numbered scope PMA-7.2 through PMA-7.6.

The complete contracts were typechecked without diagnostics before proof implementation. Typed-only SHA-256: `a032fb853ddd9ed9522de164b834fb7f7e2c3f1ead2f361b50f8e08d168e5f58`.

Root independently accepted that exact file against the accepted source inventory on 2026-10-10, confirming all numerical, limit, domain, derivative, and native integral assertions, together with the positive-index shifts. The primary source inventor then independently read every definition and conjunct and accepted the same hash without corrections. Proof implementation begins after both acceptances.

Positive source indices are encoded by `n+1` and `m+1`; the geometric series in 7.3 starts at zero. Iterated limits use `limUnder` only alongside the full existence assertions for their inner limits. Native `Chapter06.RIntegrable` and `Chapter06.RIntegral` are used for all ordinary integration claims. Both the divergent squared-spike variant and the finite linear-spike variant are present. Shared spike definitions will be supplied by the foundation owner in `Chapter07.Basic` without duplicating or changing the accepted formulas.

No implementation proof is counted complete by this contract record. Per-node proof work and compilation/axiom evidence will be appended as it is obtained. Protected Chapter 5/6 sources and the root import file remain outside this ownership.

Pinned proof routes checked while the second review is pending:

- 7.2: reduce one ratio to a constant divided by a denominator tending to infinity and the other to one minus that ratio. `Filter.Tendsto.limUnder_eq` then justifies the iterated-limit expressions from the actual inner-limit theorems.
- 7.3: `hasSum_geometric_of_lt_one` supplies the geometric sum away from zero; at zero every term vanishes. Pass from genuine `HasSum` to the source's ordered partial-sum limit. The punctured limit at zero equals one while the actual value is zero.
- 7.4: use `Real.sin_eq_zero_iff`, `Real.sin_eq_zero_iff_cos_eq`, and decay of powers of a number with absolute value below one for the inner limit. `Nat.dvd_factorial` supplies eventual integral multiples for a rational input. Rational and irrational density give discontinuity and exact lower/upper native sums; zero-width cells carry zero weight.
- 7.5: the reciprocal square-root bound gives global uniform convergence, the elementary derivative formula is exact, and its value at zero tends to infinity.
- 7.6: `tendsto_pow_const_mul_const_pow_of_lt_one` gives pointwise decay (zero is handled separately). Polynomial antiderivatives and native `pma6_21` yield the exact two integral formulas. Their elementary numerical limits then produce the two failures of interchange. No measure-integral identification is needed.

## Verified first chunk

Actual proof work began at 16:56 UTC on 2026-10-10 after both type acceptances. PMA-7.2, 7.3, 7.5 and 7.6 were completed and published at approximately 17:04 UTC in `rudin/Rudin/PMA/Chapter07/Examples.lean`, SHA-256 `a25907d75b1bae77638eaaea291888989f6d9f319f0d2cea71ee74c9a25f9bd5`.

The isolated module build passed (8,946 jobs), with no diagnostics from this source. A separate source compilation printed transitive axiom dependencies for all 23 theorem declarations; every set was exactly `propext`, `Classical.choice`, `Quot.sound`. No new axiom, proof placeholder, or changed integral definition is used. Root authorized publication of this safe chunk without waiting for 7.4. It imports only the shared Basic definitions and the protected Chapter 6 module and does not depend on Chapter 7 Continuity.

PMA-7.4 was separated into `rudin/Chapter07RationalDraft.lean`, initially SHA-256 `795cbbc7f5bbf6bcca9f23ad63c9d42880e9c9c5dae87cd8be0fe0e3a14b467d`. This retained exactly the previously accepted definitions and contract and imported the verified Examples module. Focused work on that node began at 17:04 UTC.

## Completed rational-indicator chunk

PMA-7.4 was completed by 17:08 UTC and published as `rudin/Rudin/PMA/Chapter07/RationalIndicator.lean`, SHA-256 `edcdd11545100cbd19fb90d3382d5baf8a5a7b34907ca7afdf44560ad53fbe3d` (206 lines, identical to its final draft). The native Darboux proof explicitly handles duplicate partition points: positive-length cells have infimum zero and supremum one, while zero-length cells have zero integrator weight. Its exact sums prove nonintegrability for every a<b. The two function-limit steps and the actual iterated limit are all proved, as is discontinuity at every real point.

The canonical module build passed (8,947 jobs), with no source diagnostics. A separate source compilation audited all 12 theorem declarations: exactly the three permitted axioms in each case. The final two-module forbidden-token scan found no `sorry`, `admit`, `native_decide`, `axiom`, or `unsafe`. Combined delivered size is 507 lines and 35 theorem declarations for the five numbered examples.

All five implementation nodes are now complete and ready for the separate independent proof/hostile acceptance gate. No resistant node was queued; the approximately twelve-minute post-acceptance implementation window completed the entire assigned scope. The canonical modules are authoritative; the original all-in-one Examples draft is retained only as a work record and is not an additional import.
