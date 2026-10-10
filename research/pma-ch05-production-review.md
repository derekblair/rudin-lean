# Chapter 5 production review and verification

Hostile review gate: **PASS for all nineteen nodes in the exact candidate**.
Review A covers 5.1–5.6 and 5.13–5.19; review B covers 5.7–5.12.
Each reviewer is independent of the nodes reviewed. Reports: [A](../evidence/ch05-hostile-review-a.md), [B](../evidence/ch05-hostile-review-b.md).

Production verification: **PASS, 19/19 nodes, zero queued**.

Base: `97758281a2802ea1700c9b84164c05a2cc64313d`; branch: `codex/pma-ch05-integration`. Local commits only; no push or remote update.

| Final reviewed artifact | SHA256 |
|---|---|
| `rudin/Rudin/PMA/Chapter05.lean` | `55acec19c187d4ae0d6bfc37c78ee32df5711a997f3d4e0aeea876eb876904cb` |
| `rudin/Rudin/PMA/Chapter05Probes.lean` | `a59995311bfe25b74920cee0aef6ed6ed3674c4568374058c141c1fcb0f96093` |
| `rudin/Rudin/PMA/Chapter05Audit.lean` | `d8dbffc66740e026638a4c0bba1dbcacfb69594b706c92116aef9435fa18a0d9` |
| `rudin/Rudin.lean` | `ecb07140e6e5bdb8e69b82312225fcdddd761e37588f0e53871e64be0c5ca73e` |

The main module retains its historical isolated-preparation header verbatim
to preserve the reviewed bytes. This production report supersedes that
header and the historical authorization blockers in copied evidence.
Earlier isolated reviews/logs/JSON retain their original scope and dates;
they are not represented as production or hostile-review results.

All original untracked research was preserved in the preparation commit.
Proof history groups 5.1–5.5 because their contracts precede the proofs,
then has one commit for each of 5.6–5.19. A final commit adds the vector
source bridge, nine standalone probes, default audit import and results.
This is current integration history, not a reconstruction of past authorship.

Production commands use the existing pinned Lean 4.34.1 binary with working
directory `rudin/`: `lake --no-cache build`, followed by `lake --no-cache env lean --stdin`
for the recursive namespace audit. At repository root use
`python3 -B scripts/check_chapter.py 5` (`--partial` during prefixes).
No isolated local-package overrides, dependency copies, installs, fetches,
session changes, credentials, book files, or Chapter 6 edits were integrated.

The final build includes the canonical Chapter 5 probes and recursive audit.
The audit checks 267 declarations, including nine standalone probes, with
only `propext`, `Classical.choice`, and `Quot.sound`. All four final code
hashes match the hostile-reviewed candidate exactly. Detailed per-commit
records and build output are in `../evidence/ch05-production-verification.json`
and `../evidence/ch05-production-build.log`.
