# Chapter 7 canonical probe design and provenance

`rudin/Rudin/PMA/Chapter07Probes.lean` contains **51 standalone boundary assertions plus seven supporting Algebra theorems**: 58 explicit theorem declarations in total. Its recursive namespace audit sees 67 declarations, including definitions and generated declarations. This 67 is a subset of the chapter-wide 392, never an additional count. The 33 accepted-contract type comparisons in `Chapter07Audit.lean` are a distinct type-fidelity check, not 33 more boundary probes.

The nine source clients and exact hashes are in [the provenance manifest](ch07-probes-manifest.json). They were independently compiled before assembly. Canonical assembly changes only imports, namespace wrappers and standalone diagnostic commands; the mathematical declaration bodies are retained. Independent integration review re-compares the transplanted bodies and compiles the canonical probes and audit afresh.

| Group | Assertions | Supporting theorems | Principal boundaries |
|---|---:|---:|---|
| Nowhere | 5 | 0 | All real points, distant points, no derivative value, witness at zero, arbitrarily small nonzero steps |
| Examples | 10 | 0 | Double limits, index-zero geometric term, native spike integrals and endpoint, rational indicator discontinuity and nonintegrability |
| MTest | 2 | 0 | Empty-domain majorant signs and complex conditional uniform convergence |
| NoSubsequence | 2 | 0 | No uniform subsequence and a bad point for every strict subsequence |
| Calculus | 2 | 0 | Zero integrator mass and existence of the complex differentiable uniform limit |
| Continuity | 8 | 0 | External accumulation point, isolated-point rejection, noncompact Dini example, empty/singleton norms, completeness without compactness |
| Equicontinuity | 6 | 0 | Empty/countable sets without topology, global uniform equicontinuity, early sequence member, empty Ascoli, moving peaks |
| Foundations | 10 | 0 | Empty domains, infinite initial supremum, completeness requirement, imaginary values and ordered series |
| Algebra | 6 | 7 | Genuinely nonunital real/complex interpolation, absence of a common bound, exact zero-radius normalization, singleton and empty compact cases, conjugation obstruction |
| Total | 51 | 7 | |

Algebra's seven supporting theorems are the six `eventuallyZero_*` structural lemmas and `no_common_bound`. Its other six theorem declarations are the standalone boundary assertions. These probes supplement direct source review; they do not assert exhaustive countermodel coverage. Additional hostile-review clients remain in their own reports and are not double-counted here.
