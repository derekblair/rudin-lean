# Chapter 9 final production review — 2026-10-23

Chapter 9 is complete: **43/43 numbered nodes, PMA-9.1–PMA-9.43**, in book order,
with no needs-insight entries. Scope includes the numbered definitions, remarks,
worked examples and accepted attached consequences from printed pp.204–238 of
the third edition. Exercises, beginning on p.239, remain outside the programme.
The independent inventory and page mapping are in `pma-ch09-inventory.md` and
`pma-ch09-source-review.md`.

## Independent acceptance and exact production identity

`evidence/ch09-accepted-contract-snapshot.json` records all 43 accepted contract
texts and hashes. The final production manifest compares every exact text with
its production definition. Lean separately checks all 43 principal constants
are actual theorem declarations and typechecks each against its contract.
These comparisons supplement the independent source review; they do not by
themselves establish fidelity to the book.

`evidence/ch09-reviewed-production-manifest.json` covers all **13 production
proof/helper modules**, including definitions, helper statements and proof bodies.
All 13 current hashes match the independently accepted hashes. The
`ch8_fidelity` reviewer independently accepted 11 modules. That reviewer authored
`C1Partials.lean` and `MathlibPartialBridge.lean`, so the root independently
reviewed those two; their acceptance is in `pma-ch09-root-review.md`. The root's
contraction/inverse/implicit proofs were accepted by the other reviewer. The
worked implicit example also has an additional independent review in
`evidence/ch09-implicit-example-hostile-review.md`.

No source theorem was weakened to pass compilation. In particular:

- 9.21 derives total differentiability from continuous coordinate partials.
- 9.24 retains both the C1 inverse and the weaker derivative-continuity-at-base
  version. 9.28 solves the first variable block and retains all-solution uniqueness.
- 9.32 retains the actual base derivative, any prescribed possibly oblique
  projection, rank zero, relative openness, both coordinate regularities,
  graph, image bijection, level sets and kernel dimension.
- 9.33 uses the literal all-tuple sign-product determinant and proves the
  permutation-sum bridge, including repeated tuples and empty dimension.
- 9.41 derives existence of the missing mixed partial using continuity of only
  the given mixed partial at the one point; its C2 consequence is separate.
- 9.42 uses the native Riemann–Stieltjes integral and arbitrary monotone
  integrators. Derivative-slice integrability is a conclusion.
- 9.43 supplies native compact integrability, independently moving improper
  endpoints, absolute convergence, parameter derivative, ODE and closed form.

## Boundary clients and kernel verification

All **10 probe modules compile**. There are **42 independently authored boundary
assertions**, plus **2 supplementary assertions and 3 public setup lemmas** in
`RankObliqueProbes.lean`, which was written by the Rank author. This distinction
is deliberate: its full rank-one oblique-projection client received independent
semantic review, but is not counted as independently authored. That review
accepted SHA256 `fc7be1f891f9741d53d3d6a649da0c0965b2686bf01454ea57232959ddc31200`.
There are also 6 private support theorems and 4 probe definitions. The exact
47-public-theorem census is in `evidence/ch09-final-probe-inventory.json`.

The independent clients exercise zero dimensions, empty domains, derivative
nonuniqueness exclusions, partial-derivative counterexamples, negative
contraction constants on singletons, noninjective open maps, first-block
implicit solutions, repeated determinant tuples, a nonzero constant rank-zero
map, signed rectangle increments, discontinuous Stieltjes integrators,
singleton intervals, and native improper-integral convergence.

Final commands, all successful and run sequentially:

1. `PYTHONDONTWRITEBYTECODE=1 python3 scripts/check_chapter.py 9`
2. In `rudin/`: `lake build Rudin.PMA.Chapter09Audit`
3. In `rudin/`: `lake build`

The audit finds **43 principal theorems and 43 contract comparisons**. It
recursively checks **470 Chapter09 namespace declarations**, including the
**70-declaration FidelityProbes subset**, against only `propext`,
`Classical.choice`, and `Quot.sound`. The 70 are included in 470, not additional.
Private declarations, generated code and the Mathlib partial-derivative wrapper
are included by namespace collection and recursive dependency traversal.
The default target imports the audit, so these gates are part of ordinary builds.
The final default build reports success with 9009 jobs. Existing style/linter
warnings remain nonfatal; this is not a warning-free build claim.

The strict source guard checks all 25 Chapter09 Lean files and finds no `sorry`,
`admit`, `sorryAx`, `native_decide`, custom `axiom`, `unsafe` or `implemented_by`
declarations. `evidence/ch09-final-integrity.json` records the source and
preservation checks; `evidence/ch09-final-manifest.json` records the exact 43
contract hashes, 25 integrated source hashes and audit counts. Final raw logs
are `evidence/ch09-final-{source-check,audit,default-build}.log`; each individual
module/client also has its compile log.

## Section gates and preserved scope

| Book-order section | Cumulative principals/contracts | Audited declarations | Probe subset |
|---|---:|---:|---:|
| 9.1–9.9 | 9 | 61 | 9 |
| 9.10–9.21 | 21 | 171 | 17 |
| 9.22–9.29 | 29 | 240 | 30 |
| 9.30–9.38 | 38 | 364 | 55 |
| 9.39–9.43 | 43 | 470 | 70 |

Every section has a successful source check, cumulative audit, exact manifest
comparison and default build before its local commit. All builds in this lane
were serialized on the shared host. The branch is `ch8-codex-20261022`; the
Chapter 9 starting commit is `ddee6018dc400f45841f25e2897668932a9100d1`.
The task-directory `CH9-LOG.md` records the exact resulting commit list.

All **57 Chapter 1–8 source files** are byte-identical to that starting commit.
`lean-toolchain`, `lakefile.toml` and `lake-manifest.json` are also unchanged.
Chapter 8 remains **6/22**, and Chapters 10–11 remain pending. The user explicitly
authorized proceeding to Chapter 9 on this branch. Pinned Mathlib supplies
forward library dependencies, including Gaussian normalization; this does not
complete the pending Chapter 8 Gaussian node. See
`pma-ch09-calculus-dependencies.md` for the native integral bridges and library
boundary. The landscape check records overlapping prior work and makes no
novelty claim.

## Final independent reconciliation

After the final gates, `ch8_fidelity` independently rechecked all 25 integrated
source hashes, all 13 accepted production hashes, all 43 contract texts/hashes,
the book-order index, every audit/probe import, and the successful final logs.
The reviewer also byte-compared the 57 preserved sources and three pin files
against the starting commit, and reconciled PROGRESS/PROGRAM/QUEUE and the
probe-authorship counts. The read-only review found no discrepancy; it made
no source edits and ran no Lean/Lake build.

No install, push, PR, merge, toolchain change or other-branch edit was performed.
