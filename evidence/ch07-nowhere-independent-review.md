# Independent final review of PMA 7.18

**Verdict: ACCEPTED.** The complete 223-line canonical implementation was read,
its exact statement checked against the accepted Chapter 7 inventory, and five
fresh kernel clients plus recursive axiom audits passed. No unresolved finding.

Reviewer: `ch6_production`, independent of the root author's Nowhere proofs.
Reviewed file: `rudin/Rudin/PMA/Chapter07/Nowhere.lean`.
SHA256: `6d04835c41bda7f4315fc7ac3e65c32b1ccc1e778b8ea145a424193d7d406612`.
The same hash was rechecked after the kernel clients. The reviewer changed no
Nowhere source, production file, shared metadata, dependency, or configuration.

## Statement and source fidelity

`pma7_18_contract` explicitly requires a function `ℝ → ℝ`, global `Continuous`,
and failure of `DifferentiableAt ℝ` at every real point. `pma7_18` supplies that
exact existential conjunction. It has no extra premise, restricted interval,
exceptional set, almost-everywhere qualifier, or implication from an inconsistent
hypothesis. The accepted inventory permits a verified witness other than the
particular construction used in the book. Thus the periodic tent series is a
faithful proof choice, not a weakened theorem.

The tent is the norm on `AddCircle 2`; its nonnegativity, bound one, continuity,
Lipschitz bound and period-two shifts are proved using exact library interfaces.
The centered representative and signed half-step lemmas cover all real inputs,
including endpoints and breakpoints; there is no unstated generic-point premise.
The geometric coefficient bound establishes summability and global continuity
of the infinite series through `continuous_tsum`.

The high-frequency tail cancels exactly for the selected step: at indices above
`m`, the argument shift is an integer multiple of period two. The finite-sum
reduction is justified by actual summability, not by a totalized arbitrary tsum.
The lower-frequency contributions are bounded by the finite geometric sum of
`3^k`; the selected last term contributes exactly `3^m` times the absolute step.
The resulting lower bound on differences holds for a strictly nonzero step of
size `(1/2)/4^m` at every input. Assuming differentiability gives a local Big-O
bound on function increments. The proof chooses an index making the step small
enough for that bound and the lower difference ratio large enough to contradict
it. This argument does not require a preselected direction of the signed step,
a derivative value, or derivative continuity.

## Independent executable checks

Ran from the isolated root:
`./lake-local env lean Chapter07NowhereReviewProbe.lean`.
Exit code **0**, no warnings or errors. The independent client imports only the
canonical Nowhere module and the inherited Chapter 1 audit infrastructure.
Its five proved checks are:

- the exact global existence assertion, directly specialized from `pma7_18`;
- rejection of every candidate `HasDerivAt` value at every real point;
- failure of differentiability at `-1000000`, `1000000`, zero and `1/3`;
- the concrete origin normalization `nowhereWitness 0 = 0`;
- the explicit nonzero property of every chosen small difference step.

The same run recursively audited **40 Chapter 7 namespace declarations** imported
by this isolated client, including private/compiler-generated declarations, and
all **five client declarations**. Only `propext`, `Classical.choice` and
`Quot.sound` occur. `#print axioms pma7_18` independently reported precisely those
three. A comment/string-stripped scan found no `sorry`, `admit`, `native_decide`,
`sorryAx`, or `axiom` token in the reviewed source.

This is an independent statement/proof-source review and kernel-client check.
It is separate from the later chapter-wide hostile gate and does not certify any
other Chapter 7 node or production integration. No book text was copied.
