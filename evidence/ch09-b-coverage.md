# Chapter 9 B coverage

All 21 nodes assigned to this lane are complete. The full 43-node source
inventory and agreed split are in `research/pma-ch09-b-inventory.md`.
Namespace: `Rudin.PMA.Chapter09`. Import: `Rudin.PMA.Chapter09.SecondHalf`.

| Node | Module | Kernel anchors / coverage |
|---|---|---|
| 9.23 | Inverse | `pma9_23`, `pma9_23_iterates`: unique fixed point and convergent iteration |
| 9.24 | Inverse | `pma9_24`, `pma9_24_inverse_derivative`: open local inverse, C1 inverse, derivative |
| 9.25 | Inverse | `pma9_25`: open image of every open subset of the domain |
| 9.26 | Implicit | `pma9_26_x`, `pma9_26_y`, `pma9_26`: both blocks and reconstruction |
| 9.27 | Implicit | `pma9_27`: unique linear solution and its formula |
| 9.28 | Implicit | `pma9_28`: unique C1 graph, base point, and derivative formula |
| 9.29 | Implicit | `pma9_29` and explicit f/A/B/D declarations: full worked example |
| 9.30 | Determinants | null space, range, cardinal/finite rank; full-rank and zero-rank consequences |
| 9.31 | Determinants | projection definition; unique splitting, prescribed range, infinitely many projections |
| 9.32 | Rank; RankGeometry | `pma9_32`: graph normal form; graph image, projection bijection, level sets, kernel dimension |
| 9.33 | Determinants | exact integer tuple sign and all-tuples determinant; proved Mathlib equivalence |
| 9.34 | Determinants | identity, both column linearity laws, column swap, equal columns |
| 9.35 | Determinants | `pma9_35`: determinant of a product |
| 9.36 | Determinants | `pma9_36`, `pma9_36_matrix`: invertibility iff nonzero determinant |
| 9.37 | Determinants | basis-change intertwining and basis-independent determinant |
| 9.38 | Determinants | Jacobian definition, actual coordinate partials, inverse/implicit nonsingularity criteria |
| 9.39 | HigherDerivatives | scalar and mapping C2 definitions, actual coordinate-slice derivatives |
| 9.40 | HigherDerivatives | `pma9_40`: rectangle MVT for either sign of each side length |
| 9.41 | HigherDerivatives | `pma9_41`: weak mixed-partial theorem; corollary and native C2 bridge |
| 9.42 | Integrals | `pma9_42`: native Riemann–Stieltjes integral, integrable derivative and differentiated integral |
| 9.43 | Integrals | both integrals, absolute convergence, quotient estimate, derivative, ODE, closed form, initial value, divided identity and improper limits |

`SecondHalfAudit.lean` checks 50 actual theorem constants and 13 actual
definition constants covering every row, and recursively audits all Chapter 9
declarations in its import closure. Supporting results are included in that
recursive audit. There are no remaining nodes, proof holes, or custom axioms.

No first-half node is duplicated. First-half modules are obtained only through
Git rebases onto `origin/lane/rudin-ch09-a`. Shared chapter aggregators,
PROGRESS.md, and README files are not edited by this lane.
