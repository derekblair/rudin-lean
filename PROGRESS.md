# Progress

Formalized node counts per chapter include definitions, theorems, propositions,
worked examples, notation, and mathematical content of remarks/discussions.
Unnumbered corollaries are folded into their nearest nodes. Numbered Remark 1.2
has its own node and proved midpoint theorem.
All completed nodes have zero proof placeholders. Historical audit counts below
refer to their recorded chapter-completion gates; the later review-finding
repairs are listed separately.

| Chapter | Title | Nodes formalized |
|---|---|---|
| 01 | The Real and Complex Number Systems | 38 / 38 |
| 02 | Basic Topology | 47 / 47 |
| 03 | Numerical Sequences and Series | 55 / 55 |
| 04 | Continuity | 34 / 34 |
| 05 | Differentiation | 19 / 19 |
| 06 | The Riemann-Stieltjes Integral | 27 / 27 |
| 07 | Sequences and Series of Functions | 33 / 33 |
| 08 | Some Special Functions | 22 / 22 |
| 09 | Functions of Several Variables | 43 / 43 |
| 10 | Integration of Differential Forms | 50 / 51 |
| 11 | The Lebesgue Theory | 0 |

Chapter 1 is complete: 38 / 38 nodes, including the standalone 1.2 rational
midpoint theorem added by merged PR #3. The original 37-node completion had
individual `PMA-1.x done` commits, independent boundary probes, and an audit of
210 chapter declarations and 23 probe declarations. The current audit additionally
uses the module-ownership coverage repair from PR #5, including generated
declarations outside chapter namespaces; only the three permitted axioms are allowed.
The chapter source, inventory, and queue are checked by
`python3 scripts/check_chapter01.py`. Detailed fidelity evidence is in
`research/pma-ch01-checks.md` and `research/pma-ch01-fidelity.md`.

Chapter 2 is complete: 47 / 47 nodes, each with a local `PMA-2.x done`
commit and passing build. The original verification compiled 13 independent
boundary probes and audited 289 namespace declarations (275 chapter
declarations plus 14 probe declarations including compiler-generated code).
Only the three permitted axioms occur. Run
`python3 scripts/check_chapter.py 2`; fidelity evidence is in
`research/pma-ch02-checks.md` and `research/pma-ch02-fidelity.md`.

Chapter 3 is complete: 55 / 55 nodes, each with a local `PMA-3.x done`
commit and passing default build. All source definitions and statements were
independently reviewed; the original verification included 14 authored boundary probes
and a recursive audit of 604 chapter/probe declarations against the three
permitted axioms. Run `python3 scripts/check_chapter.py 3`; fidelity evidence is
in `research/pma-ch03-checks.md` and `research/pma-ch03-fidelity.md`.

Chapter 4 is complete: 34 / 34 nodes, each with a local `PMA-4.x done`
commit and passing default build. All definitions and every contract conjunct
were independently reviewed before proof. The original verification included 18 authored
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

Chapter 6 original production verification completed with all 27 nodes and their accepted
attached consequences, both explicit complex bridges, 13 authored standalone
probes and 457 recursively audited declarations (including 25 probe-namespace
declarations). Only the three permitted axioms occurred. At that gate the source
was byte-for-byte identical to the independently reviewed and hostile-reviewed
candidate; PR #5 subsequently repaired 6.18 as listed below.
See `research/pma-ch06-production-review.md`. Later chapter status and merged
review-finding repairs are recorded below.

Chapter 7 local integration: 33/33 accepted numbered nodes.
Completed nodes: 7.1, 7.2, 7.3, 7.4, 7.5, 7.6, 7.7, 7.8, 7.9, 7.10, 7.11, 7.12, 7.13, 7.14, 7.15, 7.16, 7.17, 7.18, 7.19, 7.20, 7.21, 7.22, 7.23, 7.24, 7.25, 7.26, 7.27, 7.28, 7.29, 7.30, 7.31, 7.32, 7.33.
Frozen modules are committed in their actual dependency order; node groups may be nonnumeric. Every local commit requires the default build, exact principal coverage, accepted-contract comparisons, source checks and recursive permitted-axiom audits. Pending integration is not a resistant proof node.

Chapter 7 original production verification completed with 33 nodes and all accepted attached consequences, 33 accepted-contract comparisons, 51 boundary assertions with 7 probe support theorems, and 392 recursively audited declarations including the 67-declaration probe namespace subset. Only the three standard axioms occur. At that gate all 15 canonical files matched the independently reviewed candidate and both complete hostile-review coverage sets; PR #5 subsequently documented the 7.28 deviation as listed below. Explicit pinned-library forward dependencies do not count as later-chapter completion. See `research/pma-ch07-production-review.md`. The merged Chapter 8/9 completion and Chapter 10 integration are recorded below.

Chapter 8 is complete: 22 / 22 nodes, merged in PR #6. All 22 principal theorem
contracts and their attached claims are covered by the production modules,
probes, and recursive axiom audit. The final recorded chapter audit covers 532
declarations, including 18 probe declarations, using only the three permitted
axioms. See `research/ch08-complete-inventory.md` and
`evidence/ch08-final-coverage-review.md`. The explicit relative-coefficient
integrability premise in 8.10–8.12 remains a disclosed source clarification.

Chapter 9 is complete: 43 / 43 nodes, merged in PRs #4 and #8. The first half
covers 9.1–9.22; the second half covers 9.23–9.43, including their attached
claims. See `evidence/ch09-a-coverage.md`, `evidence/ch09-b-coverage.md`, and
`research/pma-ch09-b-inventory.md`. Chapter 10 builds on these merged modules.

All eight review findings are closed by merged PRs #3 and #5. Closure includes
explicitly disclosing source deviations where the printed statement requires
correction; it does not claim to prove a false source statement.

| Finding | Merged resolution |
|---|---|
| 1.2 | Standalone rational midpoint theorem and numbered node. |
| 1.21 | Root-uniqueness comment now accurately records the positive-root restriction and printed omission. |
| 3.18(a) | Arbitrary real sequences containing all rationals are covered, allowing irrational terms and repetitions. |
| 3.36 | The false full-test dominance claim is explicitly identified, with a formal counterexample and the valid convergence-criterion result retained. |
| 4.33 | The nonvacuous accumulation hypothesis and its role in uniqueness are explicitly documented. |
| 6.18 | Cumulative atomic mass includes closed endpoint support, with the required mass/integral relation and endpoint probes. |
| 7.28 | The nonempty-algebra premise and empty-domain obstruction are explicitly disclosed and formalized. |
| Audit coverage (F8) | Module-owned declarations, including generated declarations outside the chapter namespace and probe declarations, receive transitive axiom checks. |

Chapter 10 integration covers all numbered items 10.1–10.51, with 50 / 51 nodes
complete. The sole incomplete node is 10.43: both forward identities and the
C² scalar-potential converse are proved, and the existing C¹ vector-potential
theorem is explicitly labeled as weaker. The final C² vector-potential clause
remains stated in `pma10_43_contract` but unproved. There is no principal
`pma10_43`, proof placeholder, or axiom for that clause; the second-half audit
checks that the principal theorem is absent. Its separate research ticket is
`research/pma-ch10-b-43-blocker.md`. The integration preserves that boundary
and does not attempt the missing proof. Chapter 11 remains pending in this
checkout.

The live-tree integration build passes with 9,177 jobs. Its combined gate checks
all 51 contracts, 50 principals and 25 probe modules, and transitively audits
2,306 Chapter 10 declarations across 148 modules using only `propext`,
`Classical.choice` and `Quot.sound`. The separate outer Chapter10Audit module
is also audited. All 253 project Lean sources pass the placeholder scan.
See `evidence/ch10-integration-validation.json`, the integration build/audit
logs, and `research/pma-ch10-integration-inventory.md` for the complete record.
