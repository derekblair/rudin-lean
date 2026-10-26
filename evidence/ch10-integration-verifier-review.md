# Independent Chapter 10 verifier and manifest review

Date: 2026-10-25. Scope: `scripts/verify_ch10_integration.py`, `evidence/ch10-integration-manifest.json`, their actual live inputs, and the relationship to the separate Lean integration audit. This review made no repository edits and started no Lean build.

## Verdict

The current verifier is a meaningful source/provenance gate for the assembled integration. No new blocking defect was found. The only actual invocation failure is the already-known stale hash of `rudin/Rudin/PMA/Chapter10.lean` after its documentation wording change. Refresh that reviewed hash and rerun the real command before recording PASS. This review simulated that single hash refresh in memory; all other gates passed.

A source-check PASS is explicitly not a proof certificate. The script correctly says the separate full live-tree `lake build` and Lean integration audit must pass. This review does not claim to have run them.

## Independent manifest verification

I independently compared each provenance record with `git show <source_commit>:<path>`, hashed those exact bytes, and compared each preserved-main record with baseline `f7f4e813348d0fb8ddc3b6645f794448266b44b9`.

- 152 integration file records and 104 preserved-main/pin records.
- No duplicate paths within either list and no overlap between lists.
- All 149 Chapter10 source files have integration hash records.
- All 253 live project Lean source files are covered by one of the hash lists.
- The three additional hash records are `rudin/lakefile.toml`, `rudin/lake-manifest.json`, and `rudin/lean-toolchain`.
- All recorded source commits/source hashes match the exact Git objects.
- All 104 preserved-main/pin hashes match the baseline Git tree.
- Every record marked `preserved byte-for-byte` has equal current and source hashes.
- Decisions currently count 135 byte-preserved files, 12 adapted files, and 5 integration wiring/audit/compatibility files.
- The adapted list includes the Chapter10 aggregate, nine other production/import adaptations, SecondHalfAudit, and Chapter10Audit; the full path list is in the manifest and integration report.

The current sole live-bytes mismatch is the known Chapter10 aggregate documentation update. No other provenance mismatch was found.

## Gate coverage assessed

1. **Hash protection:** Existing reviewed integration files and all preserved earlier-chapter/pin files must exist and have the expected SHA-256. This checks actual bytes, not modification times or build caches.
2. **Executable placeholder scan:** All 253 live project Lean sources are scanned after the existing nested-comment/string stripping function. Executable `sorry`, `admit`, `native_decide`, `sorryAx`, and custom `axiom` tokens are rejected. This avoids treating the documented incomplete clause in comments as a proof placeholder.
3. **Chapter10 inventory:** The actual Chapter10 file set must equal the manifest's 149-file set; the script requires exactly 25 probe modules.
4. **Numbered source coverage:** Exactly 50 principal theorem/lemma declarations with IDs 1–51 excluding 43, and exactly 51 numbered contract definitions. Duplicate principal/contract entries change the length and fail. All three retained 10.43 partial theorem names must be present.
5. **Live-tree dependency closure:** The graph is traversed from Rudin using actual source files, unresolved local imports fail, and every Chapter10 file must be in that closure. Required Chapter08, Chapter09 first/second-half, and Chapter10 integration audits must be reachable.
6. **Coverage disclosure:** PROGRESS must say Chapter10 50/51 and QUEUE must explicitly retain PMA-10.43.
7. **Separate Lean audit:** The actual IntegrationAudit typechecks the complete four-part 10.43 contract using `Iff.rfl`, the forward/scalar/C1 statements, all 51 definition anchors, 50 theorem anchors, supplementary first-half anchors, and 25 imported probe modules. It rejects any `pma10_43` declaration. Its transitive audit uses module ownership, including private/generated declarations, rather than relying on source-name regexes.

The source checker does not attempt to infer theorem semantics from text, which is appropriate: those obligations are covered by the exact-byte provenance and the Lean contract/type audits.

## In-memory rejection probes

Using Python mocks of file reads, without modifying repository files, and normalizing only the known pending aggregate hash in the in-memory manifest:

| Probe | Result |
|---|---|
| Known pending hash refreshed; no source mutation | Exit 0; 149 modules, 25 probes, 51 contracts, 50 principals, 253 sources, 152 + 104 matching hashes |
| Inject executable `sorry` in Chapter10 Integration source | Exit 1 with forbidden-token diagnostic |
| Rename actual `pma10_42` principal | Exit 1 with missing principal coverage diagnostic |
| Rename actual `pma10_43_contract` | Exit 1 with missing full-contract diagnostic |
| Remove root import of Chapter10 IntegrationAudit | Exit 1 with unreachable Chapter10 module diagnostics |
| Replace that root edge with a nonexistent Rudin module | Exit 1 with explicit unresolved live-tree import diagnostic |
| Change PROGRESS to claim 51/51 | Exit 1 with completion-count diagnostic |

The real unmodified command was also run and exited 1 solely at the known aggregate hash. That expected failure demonstrates the byte gate detects the documentation change instead of silently passing it.

## Bounded limitations, not current blockers

- The checker trusts the reviewed manifest's `source_commit`, `source_sha256`, decision labels, and path-list structure; it does not re-query Git or explicitly reject duplicate hash records. This review independently validated all of those fields and list properties for the actual manifest. If the script is intended as a reusable future provenance generator/checker, structural equality and uniqueness checks would make accidental manifest omissions easier to detect.
- The import parser recognizes the repository's current single-module `import Rudin.X` lines. I checked every current Rudin import line: none is outside that supported syntax. It is not a general Lean parser for future multiline/multi-module imports.
- Principal/contract regexes recognize the current explicit `theorem pma10_N :` and `def pma10_N_contract :` style. The Lean environment checks provide the authoritative declaration-kind and type checks.
- PROGRESS and QUEUE checks ensure the required visible indicators; they do not semantically review prose. The exact incomplete state is separately preserved in code and the original blocker note, and was reviewed independently.
- An untracked `scripts/__pycache__/check_chapter01.cpython-314.pyc` exists after Python imports. It is not a source or evidence artifact and should not be included in the commit. The in-memory probes used `PYTHONDONTWRITEBYTECODE=1`.

No verifier or manifest edit was made by this review. Root owns the pending manifest refresh, real final source-check PASS, live build/audit results, and report/PR publication.
