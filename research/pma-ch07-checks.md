# Chapter 7 production checks status

All 33 nodes and accepted attached consequences are integrated locally. The 15 canonical source hashes match the independently and hostile-reviewed candidate; fresh production source, default build, exact principal, contract and recursive axiom gates pass. See `pma-ch07-production-review.md` and `evidence/ch07-production-verification.json`.

## Historical isolated checks record

The record below is retained unchanged. Its isolated commands and pending-production wording are historical and superseded in this checkout by the production evidence above.

# PMA Chapter 7 verification

The isolated Chapter 7 candidate has **33 / 33 accepted nodes proved**, with all attached assertions included and no queued mathematical case. Independent semantic and hostile coverage is recorded in [the fidelity map](pma-ch07-fidelity.md). Final integration status and exact artifact hashes are recorded in [the verification manifest](../evidence/ch07-verification.json) and [independent integration review](../evidence/ch07-integration-independent-review.md).

## Kernel and source gates

- `./lake-local build`: **PASS**, 8,976 jobs, no warnings or errors; [final build log](../evidence/ch07-final-build.log).
- The default root import includes the Chapter 7 index, canonical probes and audit. All **33 principal names are actual kernel theorem declarations**, with **33 accepted-contract comparisons** under `autoImplicit false`.
- Recursive transitive axiom audit: **392 Chapter 7 declarations**, including the **67-declaration probe subset**. Only `propext`, `Classical.choice`, and `Quot.sound` occur. Namespace auditing includes private/generated names after normalization.
- Canonical probes: **51 boundary assertions and seven support theorems**, not 58 independent assertions; [design](../evidence/ch07-probes-design.md), [provenance](../evidence/ch07-probes-manifest.json).
- `python scripts/check_chapter01.py` and `python scripts/check_chapter.py N` for N=2…7: **PASS**; [source-check log](../evidence/ch07-final-source-checks.log). The accepted index, node order, progress, queue, and canonical source restrictions pass. No proof placeholders, custom axioms, `native_decide` or unsafe proof escape is allowed.
- Fifteen final Lean source files are frozen in [the code hash manifest](../evidence/ch07-final-code-hashes.json). All eleven support modules still match their independent-review snapshots.

## Preservation and production boundary

`python scripts/check_chapter07_preservation.py` passes: all **26 protected Chapter 5 files**, **60 protected Chapter 6 files**, and **127 tracked production files** match their baselines. Production Git status is clean; HEAD remains `cc4328264872054cb72115dfcb3e025b1695ed5c` on `codex/pma-ch05-integration`; `main` remains `97758281a2802ea1700c9b84164c05a2cc64313d`. See [preservation log](../evidence/ch07-preservation-check.log).

Chapter 6 was integrated in fourteen verified local commits, preserving all seventeen Chapter 5 commits and their evidence. [The Chapter 6 production result](../evidence/ch07-ch06-production-result.md) lists every exact commit and its successful build gates. Chapter 7 has **not** been integrated into production or committed. There were no pushes, new interactive sessions, software installations, credential access or disabled safeguards.

The local toolchain remains Lean 4.34.1, Lake 5, with Mathlib pinned at `d13f23b723b8a846827a245b89c10fc7d3f11612`. The existing local dependency snapshot and `lake-local` wrapper were used; no download was needed. A read-only comparison checks all nine original dependency checkouts are clean at their pinned revisions and all 10,038 copied tracked files match byte for byte with independent inodes. Git metadata, `.github` directories and Python caches were intentionally excluded from the original snapshot. The isolated tree has no symlinks, Git metadata or PDFs. See [dependency check](../evidence/ch07-dependency-check.log). The original book was read locally in memory for inventory/review only; it was not copied, committed, uploaded or reproduced.

## Remaining work

Chapter 7 production integration and incremental local commits are the next separate authorized phase. Chapters 8–11 remain unimplemented: special functions; several-variable differential calculus; differential forms and their integration; and Lebesgue theory. Each needs its own complete source inventory, independently accepted contracts, proofs, fidelity/hostile review and chapter build/axiom/probe gates. Dependencies run through the completed convergence/calculus/approximation interfaces; Chapter 9 supplies Chapter 10's differential machinery, while Chapter 11 supplies measure/integration results currently accessed explicitly from Mathlib where needed. Exercises remain excluded. No mathematical node is blocked or silently skipped.
