# Independent Chapter 8/9 root-build wiring review

Date: 2026-10-25. Base reviewed: origin/main f7f4e813348d0fb8ddc3b6645f794448266b44b9. No build was run by this review, avoiding contention with the root agent's verification.

## Actual baseline gap

`rudin/lakefile.toml` declares `defaultTargets = ["Rudin"]` and a `lean_lib` named Rudin without a custom `globs` field. The pinned local Lake source at `~/.elan/toolchains/leanprover--lean4---v4.34.1/src/lean/lake/Lake/Config/LeanLibConfig.lean` explicitly defaults roots to `#[name]` and globs to `roots.map Glob.one` (lines 36 and 46). Therefore the default build covers the root module and its recursive import closure, not every `.lean` file in the library directory.

A source-import graph traversal of the baseline shows:

| Scope | Reachable from Rudin | Missing |
|---|---:|---|
| Chapter08 directory | 25 / 26 | GammaAudit only |
| Chapter09 directory | 0 / 24 | Every Chapter09 directory module |

`Rudin.lean` imports Chapter08 and Chapter09. Chapter08 imports all production modules plus Chapter08Audit, which imports both probe modules. Chapter09 is still a comment-only stub. Its very fast build is consistent with this; a successful build of that stub says nothing about the merged Chapter09 modules.

## Required import decisions

- Keep the merged Chapter08 aggregate and production modules.
- Make `Chapter09.FirstHalfAudit` and `Chapter09.SecondHalfAudit` reachable from Rudin. They transitively cover all Chapter09 production modules. This brings Chapter09 reachability to 22/24 files; only redundant `DeterminantsAudit` and `IntegralsAudit` remain outside.
- To include all existing diagnostics as well, also import `Chapter09.DeterminantsAudit`, `Chapter09.IntegralsAudit`, and `Chapter08.GammaAudit`. With these five additional roots, all 26 Chapter08 directory files and all 24 Chapter09 directory files are reachable.
- Root chose to add these imports directly in `Rudin.lean`, preserving the Chapter09 stub bytes. This is dependency/build wiring, not a mathematical change.
- For Chapter10, keep the first-half aggregator/audit environment isolated if preserving the source lane's first-half audit: that audit expressly forbids principal theorems 10.27–10.51 in its own import environment. Root can import the first-half audit, second-half audit, and new integration audit separately in `Rudin.lean` without making Chapter10 import its second half.

## Audit API incompatibility found and repaired

Merged `AxiomAudit.lean` provides `checkModuleAxioms`, not the old `checkNamespaceAxioms`. Baseline Chapter08Audit and GammaAudit still called the removed function. This is a real API mismatch independent of Chapter10 mathematics.

With explicit root delegation, this review changed only the following audit files:

1. `rudin/Rudin/PMA/Chapter08Audit.lean`: replaced its two obsolete namespace audit calls with module-ownership audits for every imported Chapter08 child module, the separately named Chapter08Probes module, and the current Chapter08Audit module. All 22 original contract comparisons and all 22 principal-theorem lookups remain byte-identical.
2. `rudin/Rudin/PMA/Chapter08/GammaAudit.lean`: replaced its obsolete namespace call with module-ownership audits of imported Chapter08 child modules plus the current GammaAudit module. All six original contract comparisons remain byte-identical.

Why iterate imported child modules instead of auditing `Chapter08` directly? `checkModuleAxioms` requires the requested module itself to be imported/current. The Chapter08 aggregate imports Chapter08Audit, so importing it back would create a cycle; its child modules are already present. Iteration avoids that cycle and checks the true source ownership, including generated declarations outside the expected namespace. `allowEmpty := true` permits import-only modules, while the preserved principal/contract checks independently establish the substantive coverage. The current audit module is checked explicitly to include comparator declarations.

`git diff --check` passed after these edits. Root owns the compile result.

Chapter09 audits contain no obsolete `checkNamespaceAxioms` calls. FirstHalfAudit uses its own recursive namespace filter; InverseAudit defines Chapter09Audit.check, reused by the other audits. A fresh root integration module-ownership audit can cover their outside-namespace generated declarations without altering those merged files.

## Independent integration verifier requirements

1. Traverse the final Rudin import graph and compare it with all Chapter10 production/probe source files, plus the complete merged Chapter08/09 files. Report any deliberately excluded diagnostic, and require zero unresolved local `Rudin.*` imports.
2. Run the default `lake build` from this working clone's `rudin/` directory, with the current live source tree and pinned dependencies. Record command, exit status, job count, log, and source fingerprint. A prerequisite-complete external snapshot is not this certificate.
3. Typecheck 50 principal `pma10_N` theorems against their contracts, for every N in 1–51 except 43. Require all 51 `pma10_N_contract` definitions to exist; retain the five supplementary first-half theorem anchors and the extra 10.26 orientation comparison.
4. Explicitly require the absence of a principal `pma10_43`, and the presence of its forward, scalar-converse, and explicitly weaker C1 vector-potential theorems. Keep the full C2 contract and the existing blocker note. Do not replace the full contract with the weaker theorem's type.
5. Perform the independent transitive axiom audit by module ownership over all Chapter10 imported production/probe/audit modules, including private, generated, and out-of-namespace declarations; collect dependencies transitively and reject every axiom outside propext, Classical.choice, Quot.sound. Namespace-only enumeration does not close F8's class of omission.
6. Include any restored prerequisite modules and newly written bridge declarations in axiom checks; earlier-chapter module ownership checks can additionally demonstrate that the integration retains the merged audit policy.
7. Scan production Lean sources for executable `sorry`, `admit`, `sorryAx`, `native_decide`, and custom `axiom` tokens after stripping nested comments and strings. Report both scan scope and zero count; comments documenting the intentionally unproved 10.43 clause are not placeholders.
8. Compare final source hashes to exact lane commits and the recovered prerequisite commit, list all byte-identical modules, and enumerate every adaptation by path and reason. Preserve the merged Chapter08/09 proof files unless an explicitly documented minimal API/layout repair is necessary.
9. Re-run Chapter1 metadata checker (38/38); require full source inventory 10.1–10.51 with exactly the documented 10.43 incompleteness. Ensure PR/report counts distinguish 50 complete nodes from 51 represented contracts.

These checks address the discovered root gap and source-lane snapshot limitation without attempting any new 10.43 mathematics.
