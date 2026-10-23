# Rudin Formalization Program

**Goal:** Complete Lean 4 + Mathlib formalization of Walter Rudin's *Principles of Mathematical Analysis* (3rd ed.) — every definition, every theorem, zero sorrys — at https://github.com/derekblair/rudin-lean. Then *Real and Complex Analysis*, then *Functional Analysis*, novelty increasing at each step.

**Status:** Chapter 1 complete: 37 / 37 requested nodes (2026-10-09), zero proof placeholders, standard axioms only. Chapter 2 complete: 47 / 47 nodes, zero proof placeholders, standard axioms only. Chapter 3 complete: 55 / 55 nodes, zero proof placeholders, standard axioms only. Chapter 4 complete: 34 / 34 nodes, zero proof placeholders, standard axioms only. Chapter 5 complete: 19 / 19 nodes, zero proof placeholders, standard axioms only, with independent hostile review and production verification. Chapter 6 complete: 27 / 27 nodes and all accepted attached consequences, independent fidelity/hostile review and exact production verification complete. Chapter 7 complete: 33 / 33 nodes and all accepted attached consequences, independent fidelity/two hostile review sets, and exact production verification complete. The isolated Chapter 8 lane covers power series 8.1–8.5 and exponential/logarithmic functions with real powers at 8.6; nodes 8.7–8.22 remain pending. Chapter 9 is complete: 43 / 43 nodes with independent source/proof review, zero proof placeholders, standard axioms only and passing production gates. Chapter 10 is active, with its opening integration section tracked below; Chapter 11 remains pending. The user-authorized Chapter 9 exception to dependency order is recorded below.

## The book (3rd ed.)

1. The Real and Complex Number Systems
2. Basic Topology
3. Numerical Sequences and Series
4. Continuity
5. Differentiation
6. The Riemann-Stieltjes Integral
7. Sequences and Series of Functions
8. Some Special Functions
9. Functions of Several Variables
10. Integration of Differential Forms
11. The Lebesgue Theory

## Node scheme

One node per numbered item in Rudin's text (Definition, Theorem, Proposition, Lemma, Corollary), keyed by **Rudin's own numbering**: `PMA-1.19` = Chapter 1, Theorem 1.19. Examples with proofs become nodes too (`PMA-1.12-ex`). Exercises are out of scope for v1 (revisit after the main text is done).

## Toolchain (pinned)

- Lean `leanprover/lean4:v4.34.1` via elan; Mathlib pinned to the same rev as `~/math-proofs` (see lake-manifest). Never float the toolchain mid-book — API churn rots the corpus.
- `lake exe cache get` for oleans; never build Mathlib from source.
- Current authorized run (2026-10-10): use the existing approved local executor and pinned toolchain. Keep approval and sandbox safeguards enabled. Chapter 7 integration continues the existing Chapter 5/6 local branch with local commits only; no push, new interactive session, installation, or remote execution is authorized by this run.

## Per-node pipeline

1. **Extract** the informal statement (brief — theorem statements only, never proof text).
2. **Formalize** the statement in Lean 4 + Mathlib.
3. **Fidelity check** (the hard part — a compiling statement that says the wrong thing is worse than no statement):
   - *Syntax check:* it typechecks.
   - *Consistency check:* back-translate to English via a second model and compare against Rudin's statement; spot-check, 100% on definitions, sampling on routine theorems.
   - *Reference-equivalence:* where Mathlib already contains the result, a comparator confirms our statement matches Mathlib's (same technique as Anthropic's FLT run).
   - *Prove-or-disprove probe:* on a sample, attempt to prove the negation — catches misformalizations without a reference.
4. **Prove.** Automation first (`aesop`, `simp`, `linarith`, `ring`, `field_simp`, …), escalate to manual tactic proofs. No `sorry`, no `admit`, no `native_decide`. Axioms: exactly `propext`, `Classical.choice`, `Quot.sound` — audit per chapter like the Spivak repo did.
5. **Commit** per section; `lake build` must pass on every commit.
6. **Stuck nodes** go to `QUEUE.md` (the needs-insight queue) with what's blocking — never silently skipped.

## Calibration

Measure on Chapter 1's opening theorems before committing to pace estimates: **tokens per target node** and **wall-clock per node**, split by statement-formalization vs proof. Benchmarks for context: RepoProver ~$294/target (multi-agent, ~50% tokens on aborted runs); Anthropic FLT ~203k output tokens per intermediate theorem. Our cost basis is subscription Codex, so we track tokens and time, not dollars. Full benchmark notes: `research/cost-benchmarks-2026-10-09.md`.

## Layout

```
rudin-lean/
  Rudin/PMA/Chapter01.lean … Chapter11.lean
  Rudin.lean                      -- imports all chapters
  QUEUE.md                        -- stuck nodes, what's blocking
  PROGRESS.md                     -- per-chapter counts (nodes done / total)
  research/                       -- landscape, candidates, benchmarks
```

## Rules

- Lean is the checker. A node isn't done until `lake build` passes with zero sorrys.
- Copyright: theorem statements only, brief. Never reproduce Rudin's proof text or extended exposition — in chat, files, or commits.
- Before starting each chapter, re-verify no one else has formalized it (landscape moves fast; Meta's ATLAS book list is not public).
- Exercises deferred to v1-complete. Corollaries/remarks folded into the nearest node.

## Current Chapter 5 production gate

Before integration, independent hostile reviews must accept the exact candidate
for every node, with reviewers independent of their assigned authorship. Preserve
those bytes in production, then require source checks, recursive axiom audits,
and the default build before every section commit. A final production review
records hashes and evidence. Existing fidelity reviews alone do not satisfy this
additional gate. No separate `PROVED` stamp is defined by this program.

## Current Chapter 6 production gate

Continue on the authorized local branch after preserving the completed Chapter 5
history and evidence. Chapter 6 source must match the final independently reviewed
and hostile-reviewed candidate. Require a fresh production default build, actual
principal theorem lookup, source checks and recursive axiom audit before every
section commit. Preserve all approved code bytes; group nodes by their real module
dependencies. Chapter 7 integration is governed by the later production gate below. No push or remote write is authorized.

## Current Chapter 7 production gate

Integrate the independently accepted frozen Chapter 7 candidate on the existing local branch. Preserve all Chapter 5/6 history and chapter-specific evidence. Require a fresh default production build, exact principal coverage, accepted-contract comparisons, source checks and recursive axiom audit before every dependency-respecting section commit. Final code must match all 15 reviewed hashes. Existing semantic acceptance is carried by byte identity, with fresh production kernel gates. Chapter 8 work stays isolated. No push, new interactive session, install, credential access or safeguard change is authorized.

## Current Chapter 8 local lane

The 2026-10-22 brief authorizes this checkout on `ch8-codex-20261022`, with
local section commits only. No push, PR, merge, installation, or pin change.
Follow the third edition’s actual numbering: power series 8.1–8.5, then
exponential/logarithmic functions with attached real powers at 8.6. Independent
source/contract review, actual principal theorem lookup, contract type comparisons,
independent boundary clients, source checks and recursive permitted-axiom audits
precede completion. Run the default build before each section commit. Keep all
project build invocations sequential on the shared host. Unattempted later nodes
are pending, not needs-insight entries. Preserve Chapters 1–7 source unchanged.

## Current Chapter 9 local lane

The user on 2026-10-23 explicitly authorized Chapter 9 on `ch8-codex-20261022`,
despite the remaining Chapter 8 nodes. This is an authorized exception to the
general chapter dependency order, not a claim that Chapter 8 is complete.
Follow book order within Chapter 9; retain zero placeholders, independent source
and exact-contract review, independent boundary clients, actual principal lookup,
recursive permitted-axiom audits, source checks and a default build before every
local section commit. No push, PR, merge, installation or toolchain change.
Keep all project builds sequential and preserve Chapters 1–8 source unchanged.

## Current Chapter 10 local lane

The user's new Chapter 10 instruction authorizes this checkout on the same
`ch8-codex-20261022` branch, local commits only. Follow the third edition's
numbered nodes in book order, including accepted attached consequences. Require
independent source/contract/proof review, exact reviewed hashes, independent
boundary clients, actual theorem lookup, recursive permitted-axiom audits,
source checks and a default build before every section commit. No push, PR,
merge, install, pin change or other-branch edit. All Lean/Lake invocations are
sequential; preserve Chapters 1–9 sources. Chapter 8 remains 6/22; the explicit
new chapter instruction authorizes this continuation without claiming its
pending nodes complete.
