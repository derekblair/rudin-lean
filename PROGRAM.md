# Rudin Formalization Program

**Goal:** Complete Lean 4 + Mathlib formalization of Walter Rudin's *Principles of Mathematical Analysis* (3rd ed.) — every definition, every theorem, zero sorrys — at https://github.com/derekblair/rudin-lean. Then *Real and Complex Analysis*, then *Functional Analysis*, novelty increasing at each step.

**Status:** Chapter 1 complete: 37 / 37 requested nodes (2026-10-09), zero proof placeholders, standard axioms only. Chapter 2 complete: 47 / 47 nodes, zero proof placeholders, standard axioms only. Chapter 3 complete: 55 / 55 nodes, zero proof placeholders, standard axioms only. Chapter 4 complete: 34 / 34 nodes, zero proof placeholders, standard axioms only. Chapters 5–11 are pending. Dependency order: 1 → 11.

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
- Machine: **bakkie** (standing Lean machine). All agent work via Codex `gpt-6-astra`, `ultra` effort, yolo, in tmux, per Derek's standing rule. Nothing runs on this VM.

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
