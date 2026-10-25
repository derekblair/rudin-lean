# Chapter 9 source inventory and lane split

Source: PMA third edition, printed pp. 204–239, inspected from `/root/sources/pma3.pdf`. There are 43 main-text numbered nodes, 9.1–9.43. Exercises are outside this scope.

The first half (rounding up) is **9.1–9.22**, owned by `lane/rudin-ch09-a`. The second half is **9.23–9.43**, owned by `lane/rudin-ch09-b`. Numbered exposition and attached consequences are retained in the inventory.

| Node | Kind | Brief subject | Lane |
|---|---|---|---|
| 9.1 | Definitions | vector spaces, span, independence, dimension, bases | a |
| 9.2 | Theorem | dimension bound; dimension of Euclidean space | a |
| 9.3 | Theorem | basis criteria, cardinality, extension | a |
| 9.4 | Definitions | linear transformations and inverses | a |
| 9.5 | Theorem | injectivity iff surjectivity in finite dimension | a |
| 9.6 | Definitions | linear-map operations and operator norm | a |
| 9.7 | Theorem | boundedness, uniform continuity, norm laws | a |
| 9.8 | Theorem | stability of invertibility; open invertible set and continuous inversion | a |
| 9.9 | Matrices | basis matrices, products, norm bound, parameter continuity | a |
| 9.10 | Preliminaries | one-dimensional derivatives as linear maps | a |
| 9.11 | Definition | Fréchet differentiability | a |
| 9.12 | Theorem | uniqueness of derivative | a |
| 9.13 | Remarks | linear remainder, derivative as a map, differentiability implies continuity | a |
| 9.14 | Example | the derivative of a linear map is the map itself | a |
| 9.15 | Theorem | chain rule | a |
| 9.16 | Partial derivatives | coordinate partial derivative definition | a |
| 9.17 | Theorem | Jacobian entries and derivative action | a |
| 9.18 | Example | curve chain rule, gradient, directional derivatives and their maximum | a |
| 9.19 | Theorem | mean-value bound on convex sets; zero derivative implies constancy | a |
| 9.20 | Definition | continuous differentiability | a |
| 9.21 | Theorem | continuous differentiability iff continuous partial derivatives | a |
| 9.22 | Definition | contraction | a |
| 9.23 | Theorem | unique fixed point of a contraction | b |
| 9.24 | Theorem | inverse function theorem | b |
| 9.25 | Theorem | local diffeomorphisms are open | b |
| 9.26 | Notation | product variables and partial linear maps | b |
| 9.27 | Theorem | linear implicit-function equation | b |
| 9.28 | Theorem | implicit function theorem | b |
| 9.29 | Example | explicit implicit-function derivative | b |
| 9.30 | Definitions | kernel, range and rank | b |
| 9.31 | Projections | unique decomposition; projection onto a subspace | b |
| 9.32 | Theorem | constant rank theorem | b |
| 9.33 | Definition | determinant | b |
| 9.34 | Theorem | elementary determinant properties | b |
| 9.35 | Theorem | determinant of a product | b |
| 9.36 | Theorem | invertibility iff determinant is nonzero | b |
| 9.37 | Remark | basis independence of determinant | b |
| 9.38 | Jacobians | Jacobian determinant | b |
| 9.39 | Definition | second partial derivatives and C² | b |
| 9.40 | Theorem | rectangle second-difference mean-value theorem | b |
| 9.41 | Theorem | equality of mixed partials | b |
| 9.42 | Theorem | differentiation under a Stieltjes integral | b |
| 9.43 | Example | Gaussian cosine integral | b |

## Reconciliation and import boundary

At baseline `87344489d0a8ce7fe00a37ef846a72fc70d33735`, `Chapter09.lean` contains only a chapter comment. Remote branch and PR inventory found no previous Chapter 9 implementation. Existing landed Chapters 1–8 are preserved.

Stable first-half import: `Rudin.PMA.Chapter09.FirstHalf`. Declarations use namespace `Rudin.PMA.Chapter09`. The second lane may import this module without circular dependency on the eventual chapter aggregate.
