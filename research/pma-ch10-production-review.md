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

## Finite partitions of unity: 10.8

`Partition.lean` supplies a finite continuous partition subordinate to an arbitrary
open cover, with closed supports and the global compact-support decomposition.
Two independent clients cover the empty compact set and a two-set cover of a
nonempty compact interval. The canonical manifest now records seven reviewed
production modules and eight accepted contracts.

The cumulative audit checks eight actual principal theorems and contract
comparisons, and 219 recursively audited declarations including the 19-declaration
probe subset. Only the three permitted axioms occur. The default build succeeds
with 9021 jobs. Raw logs and integrity receipts use `evidence/ch10-section3-*`.
All 82 earlier chapter sources and the three pinned project files are preserved.

## Native change of variables: 10.9

`ChangeOfVariables.lean` retains the independently reviewed exact source contract
and proof. The transformed integrand is zero outside the original open domain,
continuous globally, and compactly supported inside that domain. The proof
constructs the inverse's continuity and uses the absolute coordinate Jacobian.
Two independent reflection clients test negative orientation and a proper open
domain, including the zero exterior value.

The cumulative gate checks nine principal theorems/contracts and 244 recursively
audited declarations, including the 26-declaration probe subset; the thirteen
independently authored boundary assertions compile. Only the three permitted
axioms occur. The default build succeeds with 9023 jobs. Eight production modules
and nine contracts are recorded in the canonical manifests. Raw evidence uses
`evidence/ch10-section4-*`; earlier chapter sources and pins remain unchanged.

## Surfaces, forms, separation, and wedge multiplication: 10.10–10.17

The next fourteen reviewed modules develop actual cell/simplex parametrizations,
continuous and differentiable coefficients, and the native integral of derivative
minors. The worked examples retain endpoint values, the signed ellipse integrals,
and the spherical-coordinate Jacobian, volume, surjectivity, and interior
injectivity. Standard expansions and the Chapter9 tuple sign agree. Separation
uses nonzero native integrals on actual detecting surfaces; it does not define
functional equality to be coefficient equality. Wedge multiplication retains the
shared-index zero, cross-inversion parity, and graded commutativity.

Eight further independent boundary assertions exercise zero-dimensional
integration, an admissible noninjective surface, a repeated-coordinate zero,
standard coefficient cancellation, an actual detecting surface, a nonsorted
wedge sign, identified sphere boundary points versus interior injectivity, and
positive native volume with a degenerate boundary Jacobian. The cumulative total
is twenty-one authored assertions.

The production audit checks seventeen actual principal theorems and seventeen
accepted-contract comparisons. It recursively audits 643 declarations including
the 42-declaration probe subset, with only the three permitted axioms. The
default build succeeds with 9040 jobs. Canonical records cover 22 production
modules and seventeen contracts. Raw gates use `evidence/ch10-section5-*`; all
earlier chapter sources and pinned project files remain unchanged.

## Exterior differentiation and exact one-forms: 10.18–10.20

`CoordinateDifferentiation`, `ExteriorDerivative`, `ExactOneForms`, and
`ExteriorDerivativeRules` preserve their independently accepted compiled bytes.
Differentiation is defined on actual coordinate coefficients, gives the source's
left-wedge formula, and satisfies the C1 graded product rule and C2 d²=0. The
curve theorem retains both native integral existence and the endpoint value;
the ellipse supplies the nonexact x dy witness.

Three independent clients evaluate df on a tangent with mixed signs, compute
33 along a nonlinear curve on [-1,2], and check the odd-degree product rule
under C1 assumptions alone. Canonical records contain 26 production modules
and twenty contracts. The cumulative assertion count is twenty-four.

The cumulative gate checks twenty principal theorems/contracts and 708
recursively audited declarations, including the 55-declaration probe subset.
Only the three permitted axioms occur. The default build succeeds with 9045
jobs. Raw gates use `evidence/ch10-section6-*`; source and exact-byte checks
continue to preserve all earlier chapter files and project pins.

## Pullbacks and native surface identities: 10.21–10.25

Eight additional reviewed modules implement pullback through the actual
derivative-induced exterior-algebra map. Coefficient regularity, the source's
ordered coordinate formula, contravariant composition, and the derivative
identity retain C1 forms and C2 maps. Surface composition restricts its open
parameter neighborhood to the target preimage; no injectivity, rank, or
nonzero-dimension assumption is introduced. Both native surface-integral
identities include actual integrability on their original parameter domains.

Five independent clients test constant-map behavior by degree, the C1 closed-form
case on restricted domains, a zero-dimensional identity surface, a compact curve
whose ambient extension leaves its target set, and noncommuting map composition.
There are twenty-nine cumulative authored assertions. Canonical records contain
34 production modules and twenty-five accepted contracts.

The audit checks twenty-five actual principal theorem declarations and contract
comparisons, and 807 recursively audited declarations including the 79-declaration
probe subset. Only the three permitted axioms occur. The default build succeeds
with 9054 jobs. Raw gates use `evidence/ch10-section7-*`. Exact source, prior
chapter, and pin-preservation checks remain in force.
