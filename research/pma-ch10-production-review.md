# Chapter 10 production verification — work in progress

The complete source inventory contains 51 numbered nodes. Integration proceeds
in book order; later proof drafts do not count as completed nodes.

## Opening native integration section: 10.1–10.4

The five production modules are `Integration`, `IntegrationProofs`,
`IntegrationMeasure`, `SimplexSlices`, and `Simplex`. Their independently accepted
exact hashes appear in `evidence/ch10-reviewed-production-manifest.json`.
The four accepted contract texts and hashes appear in
`evidence/ch10-accepted-contract-snapshot.json`. The independent reviewer authored
none of these production modules. Source and semantic review are recorded in
`pma-ch10-source-review.md`.

The formalization retains successive Chapter 6 Riemann integrals, proves native
slice existence and continuity, and derives their equality with measure
integrals. Coordinate permutations, zero dimensions, degenerate cells, and
real and complex compact supports are included. Simplex integration has a
separate proof: its extension by zero need not be continuous, and every fiber's
Riemann integrability is proved, including collapsed boundary fibers.

`IntegrationProbes` and `SimplexProbes` provide six independently authored
public assertions. They exercise a degenerate cell, zero-dimensional evaluation,
unequal exchanged intervals, purely imaginary compact support, a retained
nonzero simplex boundary value next to zero exterior values, and a collapsed
fiber whose existing native integral is zero.

The opening audit checks four actual principal theorem declarations and four
contract comparisons. It recursively audits 147 Chapter10 declarations, including
the 14-declaration probe subset, against only `propext`, `Classical.choice`, and
`Quot.sound`. The default target imports the audit. Exact byte/contract and
source guards are reproducible with `scripts/verify_chapter10.py`; the ordinary
chapter metadata check is `scripts/check_chapter.py 10 --partial` while the
chapter remains in progress. All 82 Chapter1–9 source files and the three pinned
project files must remain unchanged from baseline
`ee4e530a943c5642a0bac8a6435bcaea36ecf0ce`.

Raw gates: `evidence/ch10-section1-{source-check,audit,default-build}.log` and
`evidence/ch10-section1-integrity.json`. Builds are serialized on the shared host.
No push, installation, merge, PR, pin change or other-branch edit is authorized.
Further section evidence will be appended as those sections pass their gates.

## Primitive maps and local factorization: 10.5–10.7

`Primitive.lean` preserves the independently accepted full source contract and
proof bytes. Besides differentiation and the exact prefix projection spans,
the factorization constructs a nonzero derivative pivot, an actual local inverse,
and a smaller neighborhood contained in the original domain. The lists have
exactly n primitive factors and n−1 flip-or-identity factors in the written order.
Three independent clients exercise dimension one with no flips and the plane
flip with a zero diagonal pivot, including its actual two-primitive factorization.

The cumulative gate checks seven principal theorems/contracts and 215 recursively
audited declarations, including the 17-declaration probe subset. Only the three
permitted axioms occur. The default build succeeds with 9019 jobs. Raw logs and
integrity receipts use `evidence/ch10-section2-*`; reviewed manifests now contain
six production modules and seven accepted contracts. Earlier source and pin
preservation checks remain in force.
