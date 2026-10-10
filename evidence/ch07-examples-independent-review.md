# Independent final review: PMA 7.2–7.6

Verdict: **ACCEPT** for the exact canonical source bytes below. Reviewer: `ch6_production`, independent of these modules' author. The complete 301-line Examples and 206-line RationalIndicator sources were read against the accepted `research/pma-ch07-inventory.md`, including contracts and every proof. Neither reviewed source was edited.

- `Rudin/PMA/Chapter07/Examples.lean`: SHA256 `a25907d75b1bae77638eaaea291888989f6d9f319f0d2cea71ee74c9a25f9bd5`.
- `Rudin/PMA/Chapter07/RationalIndicator.lean`: SHA256 `edcdd11545100cbd19fb90d3382d5baf8a5a7b34907ca7afdf44560ad53fbe3d`.

## Fidelity

7.2 proves actual inner convergence in both directions, then both unequal iterated limits. The positive source indices are explicitly represented by successor indices. 7.3 preserves the zero-based series, global term continuity, the exact ordered Chapter 3 series sum at every real point (including zero), and discontinuity of its sum. 7.5 gives uniform convergence on the entire real line, the exact derivatives, zero derivative of the limit, and derivative divergence at zero.

7.6 includes both scaling variants and both closed endpoints. Integrability and values use the preserved native Chapter 6 Riemann integral, via the native fundamental theorem and scalar linearity. The quadratic integral diverges and the linear integral converges to one half; the limiting zero function has native integral zero. There is no silent measure-integral substitution.

7.4 proves each cosine power continuous, actual inner and outer limits, and the iterated-limit statement. The rational indicator is discontinuous at every real point and fails native Riemann integrability on every nondegenerate closed interval. The lower/upper sum proof covers arbitrary permitted partitions: rational and irrational density handle positive-length cells, while repeated adjacent partition points contribute zero weight. Thus no unjustified strict-partition assumption enters the native gap criterion. The rational denominator eventually divides the factorial; irrational values never meet the integer grid. All hypotheses and conclusions match the accepted inventory; no result is obtained from a premise equivalent to its conclusion.

## Independent kernel checks

Both canonical sources were also freshly compiled directly with the pinned local Lean toolchain, each with exit zero and no warnings or diagnostics. Logs: `ch07-independent-source-examples.log` and `ch07-independent-source-rationalindicator.log`.

Fresh external client `rudin/Chapter07ExamplesReviewProbe.lean` compiled successfully with no warnings. Ten named probes exercise the equal-index ratio, the geometric series at source index zero, the first sine derivative, both first native spike integrals, the closed right endpoint, impossibility of a zero limit for the finite integral variant, indicator values at integers, discontinuity at zero, sums for arbitrary native partitions, and failure of native integrability on [-2,3].

`evidence/ch07-examples-independent-client.log` records recursive audits of all 92 imported Chapter 7 declarations and all 10 independent client declarations. Every dependency is among `propext`, `Classical.choice`, and `Quot.sound`; the five principal theorems were also checked individually. No `sorry`, `admit`, custom `axiom`, `unsafe`, `implemented_by`, or `extern` occurs in either reviewed canonical source. An earlier client-only arithmetic normalization error was corrected before this passing run; it changed no canonical source.

This is a final source-fidelity and proof review for these five nodes, not a claim of complete Chapter 7 integration or production verification. No production writes, pushes, dependency changes, or book copies were performed.
