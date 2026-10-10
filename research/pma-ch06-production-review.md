# Chapter 6 production integration review

Status: Verified candidate accepted; local integration is in progress.

Branch: `codex/pma-ch05-integration`. Starting Chapter 5 commit: `8f8d71a5122c0dbfdfa277ad746c34fa46f7eb2b`.
The original main remains `97758281a2802ea1700c9b84164c05a2cc64313d`. No push or other remote write is authorized or performed.

## Scope and semantic gates

The verified candidate covers all 27 accepted main-text nodes and attached consequences. Exercises
are excluded. Native closed-cell Darboux semantics and the source endpoint/jump
conventions are retained. The explicit complex bridges and native polygonal
curve length are part of the accepted scope.

Independent source-fidelity records are mapped by `pma-ch06-fidelity.md`.
The separate hostile reviews A/B/C cover every node and accepted consequence.
The initial full production candidate matched all 19 reviewed code hashes, and
the final integration must match them again. Those semantic
acceptances apply through exact source identity; this is a hash-identity check,
not a claim that the mathematical reviews were rerun. A new production default
build, kernel-node lookup, source check, and recursive axiom audit are run here.

## Honest commit sequence

Preparation is followed by complete frozen modules in dependency order:

1. definitions: 6.1, 6.2 (`Basic`, `Definitions`).
2. refinement: 6.3, 6.4 (`Refinement`).
3. criterion: 6.5, 6.6, 6.7 (`Criterion`).
4. integrability: 6.8, 6.11, 6.13 (`Integrability`).
5. monotone: 6.9 (`Monotone`).
6. properties: 6.12 (`Split`, `Properties`).
7. jumps: 6.14, 6.15, 6.16 (`Jump`).
8. finite-discontinuities: 6.10 (`Endpoint`, `Exceptional`).
9. calculus: 6.17, 6.19, 6.20, 6.21, 6.22 (`Calculus`).
10. moments: 6.18 (`Moment`).
11. vectors: 6.23, 6.24, 6.25 (`Vector`).
12. curves: 6.26, 6.27 (`Curve`).

The final commit adds standalone probes, the mandatory chapter audit, exact
canonical aggregator/root import, production metadata and validation records.
This grouping preserves the reviewed declaration order rather than fabricating
individual node histories. A passing default build, node/source checks and
recursive axiom audit precede every actual commit.

## Preservation and evidence

All pre-existing Chapter 5 code and chapter-specific evidence remain byte-for-byte
unchanged; its 17 commits remain ancestors. The only modified pre-existing files
are the Chapter 6 scaffold, root audit import, shared program/progress/queue/readme
metadata and the recursively extended chapter source checker. Chapter 7 remains
the production scaffold; no isolated Chapter 7 work is integrated.

The `evidence/ch06-*` isolated reports and logs retain their historical paths,
commands and pending-integration wording. That wording is superseded for this
production checkout by this report and `evidence/ch06-production-verification.json`.
The production build logs are separately recorded in `evidence/ch06-production-build.log`.
No book, credentials, dependency caches, draft files, isolated runner, or session
state is copied into Git. No installation, global configuration or session control
action is part of this integration.
