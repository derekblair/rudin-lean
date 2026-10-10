# rudin-lean

Complete Lean 4 + Mathlib formalization of Walter Rudin's *Principles of
Mathematical Analysis* (3rd edition) — every definition, every theorem,
zero `sorry`s.

## Goal

A permanent, machine-checked corpus of Baby Rudin on GitHub: each
theorem-sized node formalized in Lean 4 with dependency edges explicit in
the module structure, so every later lemma builds on verified earlier ones.

## Layout

- `rudin/` — the Lake project (what `lake build` builds)
  - `rudin/Rudin.lean` — root module, imports all eleven chapters
  - `rudin/Rudin/PMA/Chapter01.lean` … `Chapter11.lean` — one file per chapter
- `QUEUE.md` — the needs-insight queue: statements that resisted automation,
  waiting for a mathematician's idea. Tracked here, never as `sorry` in code.
- `PROGRESS.md` — per-chapter formalized node counts.

## Pipeline

1. **Statement** — transcribe the informal statement from the book.
2. **Fidelity checks** — the formal statement must say what the book says:
   back-translation (formal → informal via a second model, compared against
   the source) and reference-equivalence against Mathlib's own statements
   where they exist. A syntactically valid Lean statement of the wrong
   theorem is worse than a compile error.
3. **Proof** — automation first (`aesop`, `simp`, Mathlib lemmas); stuck items
   go to `QUEUE.md`.
4. **Check** — `lake build` passes with zero `sorry`s.

## Ground rules

- Toolchain pinned: `leanprover/lean4:v4.34.1` — never float it.
- Mathlib pinned to a fixed commit (see `rudin/lake-manifest.json`) — never float it.
- Axioms: `propext`, `Classical.choice`, `Quot.sound` only (Lean's standard three).
- Oleons via `lake exe cache get`; never build Mathlib from source.

## Status

Chapter 1: all 37 requested nodes complete with zero proof placeholders.
Chapter 2: all 47 numbered nodes complete. Chapters 3–11 follow in order.
The default `lake build` compiles boundary probes and audits completed chapter
declarations for the three permitted axioms. See `PROGRESS.md` and the
chapter-specific verification logs under `research/`.

Run `python3 scripts/check_chapter.py N` for a completed chapter’s
source/coverage/metadata checks,
and run `lake build` from `rudin/` for Lean verification.
