# Chapter 7 independent integration review

Reviewer: `/root/oscillation`; date: 2026-10-10. Scope: integration wiring, actual principal types, inventory coverage, recursive axiom checking, probe inclusion, and preservation. This is **not** a fresh whole-chapter source-fidelity or hostile review. The reviewer authored Algebra; its mathematical fidelity therefore requires the separate non-author review.

**Final verdict: PASS for the frozen Chapter 7 integration described below. No integration blocker remains.** The source/proof fidelity and two hostile coverage sets are separate non-author reviews; their exact-source coverage and evidence wiring were checked here, without claiming to repeat their semantic work.

## Independently completed checks

- Read the accepted 33-node inventory and independently accepted scope report. Read the complete canonical chapter index: it imports all eleven support modules and lists exactly PMA-7.1 through PMA-7.33 in book order, once each, pointing to actual principal proof names.
- Read `Rudin.lean` and `lakefile.toml`. The default target is `Rudin`; its import chain includes `Chapter07` and `Chapter07Audit`. Thus chapter coverage and the axiom gate are part of the default build, not detached scratch checks.
- Independently ran `python3 scripts/check_chapter.py 7`: exit 0, `33/33 completed, 0 queued; source and metadata checks pass`. Read the checker and its comment/string-stripping implementation. This is a structural/source-token check, not a proof of statement fidelity. It checks inventory identities/order, queue/progress consistency, and forbidden tokens in the index, support modules, and canonical probes when present.
- Independently compared all eleven canonical support files against `evidence/ch07-frozen-support-hashes.json`: all match. These hashes are recorded below.
- Independently compiled all 33 principal theorem/contract comparisons through the full `import Rudin` path: exit 0, no warnings or errors. Persisted and separately compiled `rudin/Chapter07PrincipalTypeProbe.lean`, SHA256 `ee3ab17adf278ed1f46bce3f026590613db240bf287e5c9fcdbb747d1d5fbf28`, using `autoImplicit false`. Exactly 33 comparisons use the actual accepted contracts. Node 7.20 intentionally uses `PMA7_20_Contract`; the other 32 use `pma7_N_contract`. These comparisons are type checks, **not** 33 mathematical boundary probes.
- Read the shared `checkNamespaceAxioms` implementation in `Chapter01Audit`. It traverses all environment declarations after normalizing private names and macro scopes, collects **transitive** axiom dependencies, and rejects every axiom outside `propext`, `Classical.choice`, and `Quot.sound`. The Chapter 7 audit targets the chapter namespace and separately verifies that all 33 principal names refer to theorems. Before the final probe additions, the recorded default build passed 8,975 jobs and audited 322 chapter declarations; the final count is to be checked below.
- Independently ran `python3 scripts/check_chapter07_preservation.py`: exit 0. It confirmed 26 inherited Chapter 5 files and 60 inherited Chapter 6 files unchanged. Production remained clean at `cc4328264872054cb72115dfcb3e025b1695ed5c`, with all 127 baseline tracked files matching exact hashes. Read the checker: it uses read-only Git inspection and hashing; no production mutation occurred.
- Read the progress/queue status: 33 principal proofs were counted, while final whole-chapter verification was explicitly withheld until the fidelity, hostile, build, audit, and probe gates finish. This correctly distinguishes proof existence from final verification.

## Frozen support snapshot

All paths below are beneath `rudin/Rudin/PMA/Chapter07/`.

| File | SHA256 |
|---|---|
| Algebra.lean | `44ebf1128a6a4f6409b4784c648ccecaf804a1ab354c406c02dcde638fde65c2` |
| Basic.lean | `b6b8b58999ad0025fd3ab28bc0ba3a4df5a07cc395158b99a14c05055bfa2b1a` |
| Calculus.lean | `0bc805601a65a1261e944ae9d180b3cb0344c0d9484fc766f1d3df6c3411580d` |
| Continuity.lean | `8dae8b99a9de2d8b996c47e62ad3ae5396efb503b36a686374f0349a4efa1977` |
| Equicontinuity.lean | `baffc08a75f000487493d784939d9b9af42f7c3b4441a52d73a6664aa9ec6ff0` |
| Examples.lean | `a25907d75b1bae77638eaaea291888989f6d9f319f0d2cea71ee74c9a25f9bd5` |
| Foundations.lean | `941938d68a48db2a4e0ab70ba0b39d51828fc91602a4583ab449f8ad1c4d5742` |
| MTest.lean | `c364dc78a12a188264c39c24f8dfd5da1edc699491442d18cf78b2565aef3e05` |
| NoSubsequence.lean | `a0f5e92e41fe61bbda351ab4a0497ef621ec7f3ceb7f136f742dfaca2c69f7b6` |
| Nowhere.lean | `6d04835c41bda7f4315fc7ac3e65c32b1ccc1e778b8ea145a424193d7d406612` |
| RationalIndicator.lean | `edcdd11545100cbd19fb90d3382d5baf8a5a7b34907ca7afdf44560ad53fbe3d` |

## Final canonical wiring and fresh verification

After the root's frozen-ready notification, read all 505 lines of canonical `Chapter07Probes.lean` and all 56 lines of `Chapter07Audit.lean`. The audit imports the probes, and `Rudin.lean` imports the audit. There is no detached probe gate. The canonical audit now persists the 33 accepted-contract comparisons with `autoImplicit false`, including the actual `PMA7_20_Contract` name. The node-existence check additionally rejects missing or non-theorem principal names.

Independently reran all of the following on the final code, with exit 0 and no warnings/errors:

```text
./lake-local env lean Rudin/PMA/Chapter07Probes.lean
./lake-local env lean Rudin/PMA/Chapter07Audit.lean
./lake-local build
python3 scripts/check_chapter.py 7
python3 scripts/check_chapter07_preservation.py
```

The fresh independent default build completed **8,976 jobs**. Fresh direct audit compilation and the default build both confirmed:

```text
PMA Chapter 7 coverage: 33 principal theorems and 33 accepted-contract type comparisons.
Axiom audit for Rudin.PMA.Chapter07: checked 392 declarations; only propext, Classical.choice, and Quot.sound.
Axiom audit for Rudin.PMA.Chapter07.FidelityProbes: checked 67 declarations; only propext, Classical.choice, and Quot.sound.
```

The **67 probe-namespace declarations are a subset of 392**, not an additional count. The canonical probe source has **58 explicit theorem declarations: 51 boundary assertions and seven Algebra supporting lemmas**. The supporting lemmas are the six `eventuallyZero_*` structural facts and `no_common_bound`. Its nine groups have 5, 10, 2, 2, 2, 8, 6, 10, and 6 boundary assertions respectively. The 33 contract comparisons are a separate type check and are not counted as boundary assertions. Probes supplement direct source review; they do not establish exhaustive countermodel coverage.

Compared every transplanted mathematical declaration body with its original independent client. All nine groups match after ignoring namespace/import/open wrappers, comments/whitespace, and standalone diagnostic commands. The original per-client audit commands are consolidated in the canonical audit. No theorem statement or proof body changed. Independently verified all nine client hashes and all 58 theorem names against `ch07-probes-manifest.json`.

The final manifest exhausts exactly the eleven support modules plus index, probes, audit, and root import file. Every entry matches its file. The four integration-file hashes are:

| File | SHA256 |
|---|---|
| `rudin/Rudin/PMA/Chapter07.lean` | `c84a119e20c57e2629f69ab024b36f607e105b2b9ec5f7b7ab2be1273647df9b` |
| `rudin/Rudin/PMA/Chapter07Probes.lean` | `3f8ab677255b71a28bb0f31823efd0af5e767eff7f508529cf2d9286203375e0` |
| `rudin/Rudin/PMA/Chapter07Audit.lean` | `338546f35755b21968ca88666203755db29c35f45905674e274f2c1700223326` |
| `rudin/Rudin.lean` | `5ade2dc30215b4ecdb012c49abe73cb696ed307dd91b01dfa614f1cbee91af1e` |

`evidence/ch07-final-code-hashes.json` has SHA256 `fdc39ab851a15cf3ba3a09c0307ee7b16d266250acd2122b76c9488e37a02701`. Support hashes remain exactly those listed above. An additional comment-aware scan of the four integration sources found no forbidden proof placeholder, custom axiom, `native_decide`, `unsafe`, or `implemented_by` token.

## Final evidence, status, and preservation review

Read the reconciled `PROGRAM.md`, `PROGRESS.md`, `QUEUE.md`, `research/pma-ch07-checks.md`, `research/pma-ch07-fidelity.md`, `evidence/ch07-probes-design.md`, both final manifests, and `evidence/ch07-verification.json`. The stale Chapter 6 isolated-only statements were corrected: production is recorded at the actual Chapter 6 commit, Chapter 7 remains isolated, and Chapters 8–11 remain future scope. The documents correctly distinguish the 33 proved nodes, final review gates, native integral semantics, explicit forward Mathlib dependencies, and lack of Chapter 7 production integration or publication. No exercises or later chapters are falsely counted as completed.

The fidelity map lists all 33 nodes exactly once and points to nine final non-author acceptance records. Verified the exact hashes of all **14 source/fidelity/hostile review records** in the verification manifest, as well as its **15 code** and **nine ancillary evidence** hash entries. Checked all four hostile reports and their scopes: A has 29 non-foundation nodes plus four foundations; B has 28 non-example nodes plus five examples. Each set covers 1–33 exactly once, and each node's two hostile reviewers differ from its author. This checks evidence coverage, not a new hostile verdict by this reviewer.

The last independent source check again passed **33/33, zero queued**. The last preservation check again confirmed **26 unchanged Chapter 5 files, 60 unchanged Chapter 6 files, and 127 exact production files**, with production clean at `cc4328264872054cb72115dfcb3e025b1695ed5c`. Lean remains 4.34.1 and Mathlib remains pinned to `d13f23b723b8a846827a245b89c10fc7d3f11612`.

At the moment of inspection, the verification JSON truthfully awaited this final integration verdict and the prose said the review was closing. This PASS permits the root to replace only those pending status fields and refresh affected evidence hashes, followed by the promised source/preservation recheck; no code changes are covered by that administrative update. No mathematical or integration defect remains in the reviewed snapshot. Production integration/commits and publication remain separate authorization boundaries.

This review wrote only this report and the requested standalone principal-type client. It did not edit any canonical proof module, production file, protected historical evidence, Git state, credential, configuration, book file, or existing session.
