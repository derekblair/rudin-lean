# Progress

Formalized node counts per chapter include definitions, theorems, propositions,
worked examples, notation, and mathematical content of remarks/discussions.
Unnumbered corollaries and Remark 1.2 are folded into their nearest nodes.
All completed nodes have zero proof placeholders.

| Chapter | Title | Nodes formalized |
|---|---|---|
| 01 | The Real and Complex Number Systems | 37 / 37 |
| 02 | Basic Topology | 5 / 47 |
| 03 | Numerical Sequences and Series | 0 |
| 04 | Continuity | 0 |
| 05 | Differentiation | 0 |
| 06 | The Riemann-Stieltjes Integral | 0 |
| 07 | Sequences and Series of Functions | 0 |
| 08 | Some Special Functions | 0 |
| 09 | Functions of Several Variables | 0 |
| 10 | Integration of Differential Forms | 0 |
| 11 | The Lebesgue Theory | 0 |

Chapter 1 is complete. Each target has its own local `PMA-1.x done` commit,
with a passing build. The final build includes independent boundary probes and
an audit of 210 chapter declarations and 23 probe declarations against the
three permitted axioms.
The chapter source, inventory, and queue are checked by
`python3 scripts/check_chapter01.py`. Detailed fidelity evidence is in
`research/pma-ch01-checks.md` and `research/pma-ch01-fidelity.md`.
