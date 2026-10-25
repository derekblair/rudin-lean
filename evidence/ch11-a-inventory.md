# Chapter 11 source inventory and lane boundary

Source: locally supplied PMA third-edition PDF, printed pp. 300–332 (PDF pages
309–341). All 45 numbered main-text nodes are consecutive, 11.1–11.45.
For the odd total, the first lane owns the first 23 nodes (11.1–11.23);
the second lane owns 11.24–11.45. Unnumbered corollaries belong to their
preceding numbered theorem. Exercises are not numbered chapter nodes.

| Node | Kind / brief topic | Lane |
|---|---|---|
| 11.1 | Definition: rings and sigma-rings of sets; intersection closure | A |
| 11.2 | Definition: extended-real set functions, additivity; basic identities | A |
| 11.3 | Theorem: continuity along increasing sets in a ring | A |
| 11.4 | Definition: intervals, elementary sets, volume; properties (12)–(15) | A |
| 11.5 | Definition: regular additive elementary-set functions | A |
| 11.6 | Examples: volume and Stieltjes content are regular | A |
| 11.7 | Definition: outer measure by open elementary coverings | A |
| 11.8 | Theorem: extension to elementary sets and subadditivity | A |
| 11.9 | Definition: symmetric difference, distance, finite/general measurability | A |
| 11.10 | Theorem: measurable sets form a sigma-ring; countable additivity | A |
| 11.11 | Remarks: open/closed/Borel sets, regularity, null sets, Cantor example | A |
| 11.12 | Definition: measure spaces and measurable spaces; examples | A |
| 11.13 | Definition: measurable extended-real functions | A |
| 11.14 | Example: continuous functions are measurable | A |
| 11.15 | Theorem: four equivalent level-set criteria | A |
| 11.16 | Theorem: absolute values are measurable | A |
| 11.17 | Theorem: suprema and limsups; infima, liminfs, extrema and limits | A |
| 11.18 | Theorem: continuous functions of two measurable real functions | A |
| 11.19 | Definition: simple functions and characteristic functions | A |
| 11.20 | Theorem: simple approximation, measurable/monotone/uniform variants | A |
| 11.21 | Definition: nonnegative Lebesgue integral via simple functions | A |
| 11.22 | Definition: extended signed integral and integrability | A |
| 11.23 | Remarks: six elementary integral properties | A |
| 11.24 | Theorem: integral as countably additive set function; null difference corollary | B |
| 11.25 | Remarks: almost-everywhere equivalence and finiteness | B |
| 11.26 | Theorem: absolute integrability and integral bound | B |
| 11.27 | Theorem: domination implies integrability | B |
| 11.28 | Theorem: monotone convergence | B |
| 11.29 | Theorem: additivity of the integral | B |
| 11.30 | Theorem: integrate nonnegative series termwise | B |
| 11.31 | Theorem: Fatou inequality | B |
| 11.32 | Theorem: dominated convergence; bounded convergence corollary | B |
| 11.33 | Theorem: comparison with Riemann integration and continuity criterion | B |
| 11.34 | Definition: square integrability and its norm | B |
| 11.35 | Theorem: Schwarz inequality | B |
| 11.36 | Theorem: triangle inequality in L2 | B |
| 11.37 | Remark: quotient metric on L2 | B |
| 11.38 | Theorem: continuous functions dense in interval L2 | B |
| 11.39 | Definition: orthonormal functions and Fourier coefficients | B |
| 11.40 | Theorem: Fourier convergence in L2 and Parseval; uniqueness corollary | B |
| 11.41 | Definition: convergence and Cauchy sequences in L2 | B |
| 11.42 | Theorem: completeness of L2 | B |
| 11.43 | Theorem: Riesz–Fischer | B |
| 11.44 | Definition: complete orthonormal systems | B |
| 11.45 | Theorem: Parseval for complete orthonormal systems | B |

Prior-art check: starting main commit 87344489d0a8ce7fe00a37ef846a72fc70d33735;
Chapter11.lean has only the scaffold from e179c39. All listed PRs (#1 and #2)
concern Chapter 8 and are merged. The additional remote ch8-codex-20261022
branch likewise has no Chapter 11 implementation. No prior Chapter 11 work
was overwritten. Imports for this lane will live under Rudin.PMA.Chapter11.
