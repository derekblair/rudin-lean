# Independent Chapter 6 integration review

**Verdict: ACCEPTED for the canonical assembly, coverage audit, support-source scan, preservation checks, and fidelity evidence mapping.** No missing principal theorem, complex bridge, module import, or changed reviewed proof was found. The final hostile-gate outcomes and validation manifest were also checked and agree with the frozen source; see the closing section below.

Reviewer: `remaining_scope`. Review date: 2026-10-10. Workspace: `/home/derekblair/Documents/Codex/2026-10-10/task/rudin-ch05-isolated`. This is an integration review, not a repeat of all mathematical proof reviews. The reviewer authored the earlier scalar integrability and endpoint drafts, but did not author the canonical aggregation, kernel audit, preservation checker, or standalone probe suite being assessed here. Those authored proofs have separate independent reviews linked by the fidelity record. No Lean, checker, research, production, dependency, or configuration file was modified for this review; only this evidence document was written.

## Canonical declaration and import coverage

`rudin/Rudin/PMA/Chapter06.lean:1` imports all fifteen support modules, each exactly once. Its 27 book-order node markers agree with the accepted inventory. An independent scan located exactly one actual `theorem` declaration for each principal `pma6_1` through `pma6_27` and each of `pma6_23_complex` and `pma6_25_complex`; proposition-valued contract definitions were not counted. The only new principal wrapper in the aggregator, at line 46, supplies both exact-union common refinement and repeated-point invariance from their completed proofs.

| Principal nodes | Canonical theorem locations |
|---|---|
| 6.1, 6.2 | `Chapter06/Definitions.lean:41`, `:50` |
| 6.3 | `Chapter06.lean:46` |
| 6.4 | `Chapter06/Refinement.lean:243` |
| 6.5, 6.6, 6.7 | `Chapter06/Criterion.lean:19`, `:65`, `:126` |
| 6.8, 6.11, 6.13 | `Chapter06/Integrability.lean:178`, `:508`, `:543` |
| 6.9 | `Chapter06/Monotone.lean:70` |
| 6.10 | `Chapter06/Exceptional.lean:110` |
| 6.12 | `Chapter06/Properties.lean:10` |
| 6.14, 6.15, 6.16 | `Chapter06/Jump.lean:69`, `:225`, `:325` |
| 6.17, 6.19, 6.20, 6.21, 6.22 | `Chapter06/Calculus.lean:463`, `:492`, `:583`, `:120`, `:608` |
| 6.18 | `Chapter06/Moment.lean:28` |
| 6.23, 6.24, 6.25 | `Chapter06/Vector.lean:206`, `:179`, `:269` |
| 6.26, 6.27 | `Chapter06/Curve.lean:173`, `:325` |
| Complex 6.23, 6.25 | `Chapter06/Vector.lean:340`, `:346` |

Locations in this table are relative to `rudin/Rudin/PMA/`. All local Rudin imports in the aggregator, its support modules, audit, and probes resolve to actual source files. The fourteen assembled support modules other than Basic are byte-for-byte identical to their corresponding final drafts (Definitions corresponds to Chapter06BasicDraft); Basic retains its independently reviewed final SHA256. No proof alteration was hidden by moving source into canonical modules.

## Kernel audit and standalone probes

`Chapter06Audit.lean:7` looks up every principal and both explicit complex bridges in the Lean environment and requires `.thmInfo`, so comments and unproved contracts cannot satisfy this gate. Lines 21–22 run the inherited recursive axiom audit on the chapter namespace and the fidelity-probe namespace. `Chapter01Audit.lean:18` uses `privateToUserName` to include private helpers and `collectAxioms` for transitive dependencies; only `propext`, `Classical.choice`, and `Quot.sound` are allowed. The chapter namespace check already includes the child probe namespace, so the reported declaration counts should not be added as disjoint totals.

The canonical thirteen-probe source was read in full, including the final repaired concrete sum normalization. Its frozen hash is `4f68e96188e2ac11fb3729cb345ff8a1c21640eba7f5cf1a8a7007f3bd58d9c9`. It covers arbitrary bounded discontinuous integrands at zero mass, singleton and reversed intervals, actual step values, the persistent shared-step gap, monotone and antitone discontinuous ordinary integrands, repeated endpoints, raw endpoint jump mass and its allocation under splitting, relative endpoint derivatives, and the opposite-value shared-jump example that remains integrable. These are substantive specializations of the native semantics. The thirteen theorem count is distinct from all generated/helper declarations counted by the namespace audit.

`rudin/Rudin.lean:12` imports Chapter06Audit. Its sole difference from the accepted Chapter 5 production root is that added import; the production root remains at its accepted hash `ecb07140e6e5bdb8e69b82312225fcdddd761e37588f0e53871e64be0c5ca73e`.

The final default-build log, `evidence/ch06-final-build.log`, was inspected: it records the probe module, audit, and root module building successfully, all 27 principal theorems plus both complex bridges being found, 457 chapter-namespace declarations and 25 probe-namespace declarations using only the allowed axioms, and successful completion of 8963 jobs. This reviewer did not rerun that build; the log records the parent's final build. The probe author separately reports a clean source compile and all thirteen transitive axiom checks in `evidence/ch06-probes-design.md`.

## Checkers and fidelity claims

Both checkers were read before this reviewer ran them with `python3 -B`; both exited zero:

- `scripts/check_chapter.py 6`: 27/27 nodes, zero queued, source and metadata checks pass. Its support scan recursively includes every `.lean` file under `Chapter06/`, plus the aggregator and standalone probes; it strips comments and strings before checking prohibited proof/declaration tokens. Its marker count is a source/metadata check, not independent proof completion; the kernel audit above provides actual declaration and axiom coverage. A missing standalone probe is skipped by this source checker, but the mandatory audit import independently prevents that omission in the assembled build. The audit file is not itself in the token scan; its complete 22-line source was directly inspected here.
- `scripts/check_chapter06_preservation.py`: all 26 protected Chapter 5 files and 21 unrelated original production snapshot files match, dependency/toolchain pins are unchanged, and inspected source files have independent inodes. The recursive no-PDF/no-symlink/no-Git-metadata check applies to the isolated `rudin/` tree. Production has the expected clean local branch `codex/pma-ch05-integration`, HEAD `8f8d71a5122c0dbfdfa277ad746c34fa46f7eb2b`, unchanged `main`, and exactly 17 commits since the recorded original HEAD. Its Git operations are read-only and set `GIT_OPTIONAL_LOCKS=0`. This reviewer did not run a production build or change production files.

All twelve review filenames cited by `research/pma-ch06-fidelity.md` exist under `evidence/`, and their stated scope matches the table. In particular, the split/properties review closes the scalar review's deliberately excluded 6.12(c)/wrapper; the final calculus review closes the earlier calculus snapshot's omitted 6.20/6.22; the vector review includes the explicit complex bridges. Earlier partial snapshots are not being relabeled as whole-chapter acceptance. The source-independent inventory review supplies the 27-node source scope; the final compiled theorem lookup supplies completion. Native closed-cell Darboux semantics, raw integrator values, ordered interval guards, and the separate hostile gate are described consistently.

## Frozen source and checker hashes

Hashes below identify bytes read for this integration review. Hashes of final closing evidence are handled separately to avoid confusing mutable completion records with frozen proof source.

| File relative to isolated root | SHA256 |
|---|---|
| `rudin/Rudin.lean` | `a8c7df04d0c3761a9a9004dc477a2c0d1e664ca1c526caea408c367fcf67aab8` |
| `rudin/Rudin/PMA/Chapter06.lean` | `845f356f126f288456cf210526ecb29523776bff6f6cfe89a4ebba369747a373` |
| `rudin/Rudin/PMA/Chapter06Audit.lean` | `a1f606949d6368a1b1ba25dcafd00600ffa35921c1e357bfba8f256c53fe2d77` |
| `rudin/Rudin/PMA/Chapter06Probes.lean` | `4f68e96188e2ac11fb3729cb345ff8a1c21640eba7f5cf1a8a7007f3bd58d9c9` |
| `rudin/Rudin/PMA/Chapter06/Basic.lean` | `5192b99092c0fc7da7109b1e3ffd90446db62c73845b935172643456b46a3915` |
| `rudin/Rudin/PMA/Chapter06/Calculus.lean` | `ac36c016490bd347b592af764c1c6e5f544a6cd09ad7aac0c59a4c79da6c3c18` |
| `rudin/Rudin/PMA/Chapter06/Criterion.lean` | `e88daabe91d0ddd9145c79ff4aecbfd5c054b30fd27ea86c0a1b7743e3488715` |
| `rudin/Rudin/PMA/Chapter06/Curve.lean` | `0fcd03a02ba4b7c7a57a647b14befac8b93fa006238ed13abc910849362d1b50` |
| `rudin/Rudin/PMA/Chapter06/Definitions.lean` | `13adade605f2cff6904a9b5d24f06057595d0c760abc140dfd7831608c5ccf81` |
| `rudin/Rudin/PMA/Chapter06/Endpoint.lean` | `b4518141434d43a5d28f97944ba85b9af1c98cff1b19c910bddc2d4a70fe3e4b` |
| `rudin/Rudin/PMA/Chapter06/Exceptional.lean` | `f611a715e8c85e43989fa9a196ceb7d93b55b40b9b3674dfd3bb98398fdfabfa` |
| `rudin/Rudin/PMA/Chapter06/Integrability.lean` | `001823e4c51a56b9c0d0afbe13801a757200178eac396081dec3b7abb91d5cec` |
| `rudin/Rudin/PMA/Chapter06/Jump.lean` | `ab56704088a99d95c29755f2ada3c7a491ea55af5f24be7cf19b51283e96c47a` |
| `rudin/Rudin/PMA/Chapter06/Moment.lean` | `21ccfad2cbbc3cbd0726a62a190f6092fd2b376690233dd340435b38bb89deb5` |
| `rudin/Rudin/PMA/Chapter06/Monotone.lean` | `93a69abdd3e242baa92eace347b551042157da49b4a83078e06abd469d832598` |
| `rudin/Rudin/PMA/Chapter06/Properties.lean` | `a50ff1516880bd4110cb95e7b81baf44a64980ca2400aa1e377f2b093e8634c1` |
| `rudin/Rudin/PMA/Chapter06/Refinement.lean` | `d1590f0b5df2fec5986358b6d84c255a4535a90df0ac70b8bc5f4bbec9c6fcb0` |
| `rudin/Rudin/PMA/Chapter06/Split.lean` | `d235d56777fc5e5a25db12e834769fd2192273d55a9d5921ceb80b857499a888` |
| `rudin/Rudin/PMA/Chapter06/Vector.lean` | `1830138b9712dc5c6bd97293c0396df8160da84c25be76f55f0069dc3962ff98` |
| `scripts/check_chapter.py` | `0f035c5241e86639d31fceb2420c1e954abc0c85786ff864c265ca92d3aed179` |
| `scripts/check_chapter01.py` | `72367f15e807185764b8a0d5606c17e4ef0fb2f396f7688cc2dfa7c35cd950ae` |
| `scripts/check_chapter06_preservation.py` | `6e21ae6941095a07b65f147da33791ee7921b3fd9c673e90ad269ee9b91504ac` |
| `research/pma-ch06-inventory.md` | `5e2ead64c3941180f1b3cf4bd8d086c980e40b19df36363c046d3b463f24a68f` |
| `research/pma-ch06-fidelity.md` | `e4b8c8d6cd3f208449c0a9d1ca525d1d15564c2fef18c647728aee9b3d43a448` |

## Final closing evidence

**Final integration QA: PASS, with no remaining blocker.** The final manifest status is `PASS: isolated proof, fidelity, hostile, integration, coverage and axiom gates complete`. All three hostile reports now explicitly pass. Their recorded node sets partition nodes 1–27 exactly once. Hostile A's final report hash is `ed7183e406d1d9a00fb0987ac8e6b238fc9769faf5913b4c9fa322566e0826ae`, matching the manifest and the parent's announced frozen report. The earlier pending-A state was accurate during the review and is now resolved.

All **19 code hashes and 31 artifact hashes** in the final `evidence/ch06-verification.json` were recomputed from disk and match. The 19-entry fixed map in `evidence/ch06-final-code-hashes.json` equals the manifest's code map exactly. No proof code changed during closing metadata updates. The toolchain string and Mathlib revision match the pinned files. Both baseline/final build success lines and job counts match their logs; neither log contains a warning or error diagnostic. The source-check log records 37+47+55+34+19+27 = 219 completed numbered nodes across Chapters 1–6. The final preservation log agrees with this reviewer's independent checker run.

`PROGRAM.md`, `PROGRESS.md`, `QUEUE.md`, `README-ISOLATED.md`, and `research/pma-ch06-checks.md` consistently record verified isolated Chapter 6 proof completion and the passing additional hostile gate, while retaining the unperformed Chapter 6 production integration/commit boundary. Chapter 5's separately authorized production result remains unchanged. Chapters 7–11 are the remaining uninventoried program scope. No closing metadata link points to an absent required review or validation artifact.

Final closing artifact hashes:

- `research/pma-ch06-checks.md`: `76c01b0f7e10c187fa8ea98fa61e78e83d275c5b520a589dd3d977033e138da8`.
- `evidence/ch06-verification.json`: `848ca41a1c033749f2fbaaeb3ea8ae6541a32acd5beca99148353a18436aeedf`.
- `evidence/ch06-final-code-hashes.json`: `08bb0e83eeeebd2bd23287a2e77d94b936d77b8e48d913d370daf2cb2cd09843`.

The manifest references this review by path without hashing it; this intentionally avoids a circular manifest/review hash dependency. This review certifies the recorded isolated assembly and factual evidence mapping, and does not imply Chapter 6 production integration, commits, or pushes.
