# Chapter 5 production verification

Production: 19/19 accepted nodes, zero queued; default build and recursive audit
pass, with nine standalone probes and 267 declarations allowing only the three
standard axioms. Both fresh hostile reviews passed for the exact integrated
source. See [production review](pma-ch05-production-review.md).

At repository root run `python3 -B scripts/check_chapter.py 5`; from `rudin/`,
using the pinned Lean 4.34.1 toolchain, run `lake --no-cache build`.

## Historical isolated preparation report

The material below is retained as historical evidence. Its commands apply only
to `/home/derekblair/Documents/Codex/2026-10-10/task/rudin-ch05-isolated`,
not to this production checkout. Its pending-integration statements are
superseded by the production review above.

# Chapter 5 isolated verification

All nineteen accepted inventory nodes are proved in the assembled
`rudin/Rudin/PMA/Chapter05.lean`. No mathematical node is queued, no accepted
conjunct was dropped, and no proof placeholder or custom axiom was introduced.
Production integration, commits and publication remain pending separately.

## Evidence

- Source baseline: `97758281a2802ea1700c9b84164c05a2cc64313d`.
- Lean 4.34.1; Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.
- All nine dependency revisions were checked before copying; their original
  tracked sources were subsequently confirmed clean. No installation or fetch.
- Baseline default build: 8,944 jobs; inherited Chapters 1–4 audits passed.
- First twelve integrated nodes: 8,945 jobs; 105 audited declarations passed.
- All nineteen integrated nodes: 8,945 jobs; 258 audited declarations passed.
- Final default build including standalone probes: **8,946 jobs**, success with
  no warnings/errors. Recursive audit checks **267 declarations**, including
  the **nine standalone integration probes**, allowing only `propext`,
  `Classical.choice`, and `Quot.sound`.
- Source/coverage/metadata check: **19/19 completed, zero queued**.
- All seven assembly inputs match their recorded hashes and are preserved in
  the assembled source after moving imports and removing diagnostic print/check
  commands. No declaration or proof body is changed by assembly.
- Shared-checkout HEAD and all 25 recorded source hashes remain unchanged;
  no shared source inodes, dependency symlinks, Git metadata or PDFs occur in
  the isolated Lake project.

Commands from the isolated root:

```sh
./lake-local build
python3 -B scripts/check_chapter.py 5
python3 -B scripts/check_isolation.py
```

Logs and exact source hashes are in `../evidence/ch05-final-build.log`,
`../evidence/ch05-assembly.json` and `../evidence/snapshot-provenance.json`.

## Independent semantic acceptance

| Nodes | Scope checked | Fresh final review |
| --- | --- | --- |
| 5.1–5.5 | Source quotient limits; nonvacuity; endpoints; arithmetic; integer powers; local quotient domain; relative outer chain rule | `../evidence/ch05-opening-independent-review.md` |
| 5.6 | Both complete oscillatory examples, including actual derivative discontinuity | `../evidence/ch05-oscillation-independent-review.md` |
| 5.7–5.12 | Metric extrema; interior Fermat; both MVTs; open-interval monotonicity; both Darboux orders; no simple discontinuities | `../evidence/ch05-middle-independent-review.md` |
| 5.13 | Four endpoint approaches, arbitrary extended targets, zero/zero, both infinite-denominator signs, eventual nonvanishing | `../evidence/ch05-lhopital-independent-review.md` |
| 5.14–5.15 | Actual recursive existence; original-interval endpoint coefficients; both Taylor orientations; no highest-derivative continuity premise | `../evidence/ch05-taylor-independent-review.md` |
| 5.16–5.19 | Real-parameter complex/vector derivatives; exact counterexamples; norm estimates; existential vector MVT and consequences | `../evidence/ch05-vector-independent-review.md` |

The vector source comparator explicitly proves equivalence between the norm
limit over the punctured closed interval and Rudin's punctured open-interior
approach, including one-sided endpoint derivatives. It uses the opening
codomain-independent filter equality. The final integration review is recorded
in `../evidence/ch05-integration-independent-review.md`.

## Boundary probes

Standalone probes reject open-domain endpoint derivatives, reject singleton
derivative vacuity, verify exponent zero at zero and exclude negative powers
there, exercise an outer endpoint chain rule for absolute value, prove MVT
without even a finite one-sided endpoint derivative, identify a derivative's
second-kind discontinuity, preserve a reversed odd-order Taylor sign, and
reject higher-order existence at a lower-order cusp. Additional authored probes
are included in the chapter and all are covered by its recursive audit.

## Semantic and operational limits

The scope is the accepted nineteen numbered main-text items with attached
consequences, excluding exercises. Final reviews compare Lean with the already
independently accepted source inventory; they do not repeat a full book-page
extraction. The original book remains local and was not copied into this work.
Pinned Mathlib supplies prior mathematics, including trigonometry, so these
proofs do not enforce the book's historical proof-dependency order. The
infinite-denominator l'Hopital cases use a new formal convex-tail Cauchy-MVT
argument; no numerator-limit assumption was added. Every completed statement is
kernel checked, not a claim of novel mathematics.

This workspace has independent dependency copies and local path overrides;
those overrides are execution infrastructure, not a change to the preserved
revision pins. No production writes, commits, pushes, global configuration
changes, new interactive sessions, session-control actions or credential access
were used. Ownership confirmation remains the integration prerequisite.
