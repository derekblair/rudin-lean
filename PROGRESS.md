# Progress

Formalized node counts per chapter include definitions, theorems, propositions,
worked examples, notation, and mathematical content of remarks/discussions.
Unnumbered corollaries and Remark 1.2 are folded into their nearest nodes.
All completed nodes have zero proof placeholders.

| Chapter | Title | Nodes formalized |
|---|---|---|
| 01 | The Real and Complex Number Systems | 37 / 37 |
| 02 | Basic Topology | 47 / 47 |
| 03 | Numerical Sequences and Series | 55 / 55 |
| 04 | Continuity | 34 / 34 |
| 05 | Differentiation | 19 / 19 |
| 06 | The Riemann-Stieltjes Integral | 27 / 27 |
| 07 | Sequences and Series of Functions | 33 / 33 |
| 08 | Some Special Functions | 6 / 22 |
| 09 | Functions of Several Variables | 38 / 43 |
| 10 | Integration of Differential Forms | 0 |
| 11 | The Lebesgue Theory | 0 |

Chapter 1 is complete. Each target has its own local `PMA-1.x done` commit,
with a passing build. The final build includes independent boundary probes and
an audit of 210 chapter declarations and 23 probe declarations against the
three permitted axioms.
The chapter source, inventory, and queue are checked by
`python3 scripts/check_chapter01.py`. Detailed fidelity evidence is in
`research/pma-ch01-checks.md` and `research/pma-ch01-fidelity.md`.

Chapter 2 is complete: 47 / 47 nodes, each with a local `PMA-2.x done`
commit and passing build. Final verification compiles 13 independent
boundary probes and audits 289 namespace declarations (275 chapter
declarations plus 14 probe declarations including compiler-generated code).
Only the three permitted axioms occur. Run
`python3 scripts/check_chapter.py 2`; fidelity evidence is in
`research/pma-ch02-checks.md` and `research/pma-ch02-fidelity.md`.

Chapter 3 is complete: 55 / 55 nodes, each with a local `PMA-3.x done`
commit and passing default build. All source definitions and statements were
independently reviewed; final verification includes 14 authored boundary probes
and a recursive audit of 604 chapter/probe declarations against the three
permitted axioms. Run `python3 scripts/check_chapter.py 3`; fidelity evidence is
in `research/pma-ch03-checks.md` and `research/pma-ch03-fidelity.md`.

Chapter 4 is complete: 34 / 34 nodes, each with a local `PMA-4.x done`
commit and passing default build. All definitions and every contract conjunct
were independently reviewed before proof. Final verification includes 18 authored
boundary probes and a recursive audit of 275 chapter/probe declarations against
the three permitted axioms. Independent actual-source comparison confirms all
79 distinct reviewed definitions/contracts and all 34 principal proof signatures.
Run `python3 scripts/check_chapter.py 4`; fidelity evidence is in
`research/pma-ch04-checks.md`, `research/pma-ch04-fidelity.md`, and
`research/pma-ch04-production-review.md`.

Chapter 5 local integration: 19/19 numbered nodes have been added from the
independently and adversarially reviewed candidate. The opening 5.1–5.5
section is grouped to preserve reviewed declaration order; later nodes
are integrated individually. Each section commit requires a passing default
build, source check, and recursive axiom audit. Final standalone probe and
production verification evidence is recorded when the chapter closes.

Chapter 5 final verification is complete: 19/19, zero queued nodes, nine
standalone probes, and 267 recursively audited declarations using only the
three standard axioms. Exact final code hashes match both hostile reviews.
See `research/pma-ch05-production-review.md` and production verification logs.

Chapter 6 local integration: 27/27 accepted numbered nodes.
Completed nodes: 6.1, 6.2, 6.3, 6.4, 6.5, 6.6, 6.7, 6.8, 6.9, 6.10, 6.11, 6.12, 6.13, 6.14, 6.15, 6.16, 6.17, 6.18, 6.19, 6.20, 6.21, 6.22, 6.23, 6.24, 6.25, 6.26, 6.27.
Section commits preserve frozen reviewed modules and follow their actual import
dependencies. Each section requires the default build, kernel theorem checks,
source checks and a recursive axiom audit. Unintegrated nodes are pending
integration; none is being labeled a resistant mathematical node.

Chapter 6 production verification is complete: all 27 nodes and their accepted
attached consequences, both explicit complex bridges, 13 authored standalone
probes and 457 recursively audited declarations (including 25 probe-namespace
declarations). Only the three permitted axioms occur. Final source is byte-for-byte
identical to the independently reviewed and hostile-reviewed candidate.
See `research/pma-ch06-production-review.md`. Chapter 7 integration status is recorded below; Chapter 8 local work is recorded at the end.

Chapter 7 local integration: 33/33 accepted numbered nodes.
Completed nodes: 7.1, 7.2, 7.3, 7.4, 7.5, 7.6, 7.7, 7.8, 7.9, 7.10, 7.11, 7.12, 7.13, 7.14, 7.15, 7.16, 7.17, 7.18, 7.19, 7.20, 7.21, 7.22, 7.23, 7.24, 7.25, 7.26, 7.27, 7.28, 7.29, 7.30, 7.31, 7.32, 7.33.
Frozen modules are committed in their actual dependency order; node groups may be nonnumeric. Every local commit requires the default build, exact principal coverage, accepted-contract comparisons, source checks and recursive permitted-axiom audits. Pending integration is not a resistant proof node.

Chapter 7 production verification is complete: 33 nodes and all accepted attached consequences, 33 accepted-contract comparisons, 51 boundary assertions with 7 probe support theorems, and 392 recursively audited declarations including the 67-declaration probe namespace subset. Only the three standard axioms occur. All 15 canonical files match the independently reviewed candidate and both complete hostile-review coverage sets. Explicit pinned-library forward dependencies do not count as later-chapter completion. See `research/pma-ch07-production-review.md`. Chapter 8 work is separately isolated on its authorized local branch; Chapters 9–11 remain pending.

Chapter 8 local lane: the power-series section covers numbered nodes 8.1–8.5,
with the requested addition, Cauchy multiplication, and native termwise integration
supplements. The complete source inventory has 22 numbered items. The brief’s
numeric topic ranges differ from the third edition: exponential/logarithmic
functions and attached real powers belong to 8.6. Verification and independent
source review are recorded in `research/pma-ch08-checks.md`. The first section has 11 independent clients and a recursive permitted-axiom
audit of 74 declarations (13 in the probe subset), with 5 actual principal
theorems and contract comparisons. The default build is a pre-commit gate.
Later nodes remain pending; none has been classified as a resistant proof node.

Chapter 8 lane final scope: 6/22 numbered nodes (8.1–8.6), including the
exponential/logarithmic development and positive-base real powers. All 6 principal
theorems and contract comparisons pass; 16 independent clients compile; the
fresh recursive audit checks 103 declarations, including the 18-declaration
probe subset, against only the three permitted axioms. Both section commits
require passing default builds. Nodes 8.7–8.22 are unattempted and pending;
there are no needs-insight entries. See `research/pma-ch08-production-review.md`
and `evidence/ch08-final-manifest.json`.

Chapter 9 local lane: 38/43 numbered nodes, through PMA-9.38, on the user-authorized
branch `ch8-codex-20261022`. Independent exact source/contract and proof review,
boundary clients, actual principal lookup, recursive standard-axiom audits and
source/default-build gates precede each local section commit. All 57 Chapter 1–8
source files remain unchanged. The Chapter 8 pending scope is unaffected.
See Chapter 9 review and evidence files for exact scope and verification.
