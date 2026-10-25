# Chapter 9 source inventory and lane boundary

Source: PMA, third edition, local PDF `/root/sources/pma3.pdf`, printed pages
204–238 (PDF pages 213–247). Inventoried directly from the PDF, 2026-10-25.
There are 43 consecutive numbered nodes. OCR renders 9.3 as `93` and 9.31
as `9,31`; both are included. Exercises begin on printed page 239 and are
outside the numbered-node scope.

The agreed order split assigns the first 22 nodes (9.1–9.22) to
`lane/rudin-ch09-a`; this lane owns the remaining 21 (9.23–9.43).

| Node | Kind | Brief subject | Lane |
|---|---|---|---|
| 9.1 | Definitions | Linear combinations, independence, bases, dimension | A |
| 9.2 | Theorem | Spanning sets bound independent sets; dimension of real coordinate space | A |
| 9.3 | Theorem | Bases and extending independent sets | A |
| 9.4 | Definitions | Linear transformations and invertibility | A |
| 9.5 | Theorem | Invertibility and bases in finite dimension | A |
| 9.6 | Definitions | Operator spaces and operator norm | A |
| 9.7 | Theorem | Boundedness and norm inequalities for linear operators | A |
| 9.8 | Theorem | Openness of invertibility and continuity of inversion | A |
| 9.9 | Matrices | Matrix representation, composition, coordinates | A |
| 9.10 | Preliminaries | Linear approximation and uniqueness | A |
| 9.11 | Definition | Differentiability and derivative | A |
| 9.12 | Theorem | Differentiability implies continuity | A |
| 9.13 | Remarks | Derivatives of affine maps and domain locality | A |
| 9.14 | Example | Linear derivatives and scalar derivatives | A |
| 9.15 | Theorem | Chain rule | A |
| 9.16 | Definitions | Partial derivatives | A |
| 9.17 | Theorem | Derivative matrix and directional derivatives | A |
| 9.18 | Example | Differentiation along curves and gradient | A |
| 9.19 | Theorem | Derivative bound implies Lipschitz bound on a convex open set | A |
| 9.20 | Definition | Continuously differentiable maps | A |
| 9.21 | Theorem | Continuous partial derivatives characterize C1 maps | A |
| 9.22 | Definition | Contractions of metric spaces | A |
| 9.23 | Theorem | Contraction fixed point existence and uniqueness | B |
| 9.24 | Theorem | Local C1 inverse and derivative of inverse | B |
| 9.25 | Theorem | Invertible derivatives imply an open mapping | B |
| 9.26 | Notation | Product coordinates and splitting a linear map | B |
| 9.27 | Theorem | Solving a linear implicit equation | B |
| 9.28 | Theorem | C1 implicit function and its derivative | B |
| 9.29 | Example | Explicit five-to-two dimensional implicit function calculation | B |
| 9.30 | Definitions | Null space, range, rank and elementary consequences | B |
| 9.31 | Projections | Idempotence, unique decomposition, prescribed range | B |
| 9.32 | Theorem | Constant rank local graph form and level sets | B |
| 9.33 | Definition | Tuple sign and determinant | B |
| 9.34 | Theorem | Identity, column linearity, alternation and repeated columns | B |
| 9.35 | Theorem | Multiplicativity of determinant | B |
| 9.36 | Theorem | Determinant detects invertibility | B |
| 9.37 | Remark | Basis independence of determinant | B |
| 9.38 | Definition | Jacobian and nonsingularity hypotheses | B |
| 9.39 | Definition | Higher partial derivatives and C2 | B |
| 9.40 | Theorem | Rectangular mixed difference mean value theorem | B |
| 9.41 | Theorem | Equality of mixed partials under one-point continuity; C2 corollary | B |
| 9.42 | Theorem | Differentiation under a Riemann–Stieltjes integral | B |
| 9.43 | Example | Gaussian cosine transform and its derivative | B |

## Prior work reconciliation

At start, origin/main was `87344489d0a8ce7fe00a37ef846a72fc70d33735`.
`Rudin/PMA/Chapter09.lean` contained only introductory documentation, no
formalized nodes. The remote branches and all PRs were inspected; no prior
Chapter 9 implementation or PR existed. Lane A was concurrently starting
from the same commit. Its stable import is `Rudin.PMA.Chapter09.FirstHalf`.

This inventory is a scope list, not a completion claim. Completion and exact
remaining proof obligations are recorded in the lane report.
