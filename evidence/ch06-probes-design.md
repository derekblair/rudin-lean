# Chapter 6 canonical fidelity probes

The canonical file is `rudin/Rudin/PMA/Chapter06Probes.lean`, in namespace `Rudin.PMA.Chapter06.FidelityProbes`. It imports frozen chapter modules directly so it does not depend on aggregator integration.

The thirteen standalone theorem probes exercise:

1. An arbitrary bounded integrand against a concrete constant integrator, with no continuity assumption.
2. The discontinuous source step against zero mass, including its proved discontinuity.
3. The same function/integrator shared jump on a singleton interval, where the integral is zero.
4. Rejection of a reversed interval despite the empty family of native partitions.
5. The source step's exact values on both sides and at its jump.
6. A persistent unit Darboux gap for every partition when integrand and integrator share that step.
7. Ordinary integrability of that discontinuous monotone step.
8. Ordinary integrability of its discontinuous antitone negative.
9. An explicit four-node partition with two repeated endpoints, compared with the two-node partition for arbitrary bounded integrands and monotone integrators.
10. Retention of the full right jump at the left endpoint under the source raw-increment convention.
11. Correct zero/one mass allocation and integral additivity when splitting at that jump.
12. Correct primitive derivatives at both endpoints despite a different, discontinuous extension outside the source interval.
13. Existence and value one when a right-valued integrand jump is paired with the source left-valued integrator jump: the partition through zero has exactly equal lower and upper sums. This distinguishes the native refinement criterion from an unrestricted mesh-limit convention and prevents an overbroad claim that every shared discontinuity blocks integrability.

These are theorem instantiations at adversarial boundary cases, not restatements of the defining iff contracts. The suite targets the accepted distinction between native Darboux integration, unrestricted mesh limits, and normalized Stieltjes measures. No derivative or integral backend is substituted, and no proof source outside the assigned probe file is changed.

Verification completed on 2026-10-10:

- `./lake-local env lean Rudin/PMA/Chapter06Probes.lean` exited 0 with no diagnostics.
- A second independent Lean invocation compiled the same source via stdin and printed the transitive axiom dependencies of all thirteen theorem declarations. Every result was exactly the standard set `propext`, `Classical.choice`, `Quot.sound`; no custom axiom or placeholder was present.
- Source scan found no `sorry`, `admit`, `native_decide`, custom `axiom`, `unsafe`, or `opaque` declaration.
- Stable source SHA-256: `4f68e96188e2ac11fb3729cb345ff8a1c21640eba7f5cf1a8a7007f3bd58d9c9`.

Vector zero-dimensional, complex, derivative-density, and nonlinear substitution adversarial cases are separately covered by the independently compiled hostile-C probe suite; this canonical file concentrates on the native partition and jump boundaries.
