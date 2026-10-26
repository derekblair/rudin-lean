# Chapter 10 inventory and lane boundary

Source: the supplied PMA third-edition PDF, printed pages 245–288
(PDF pages 254–297). Every numbered item is included, including remarks,
properties, and worked examples. Exercises are outside the programme scope.

There are **51 nodes**. Splitting by order with the extra node assigned to the
first half gives **lane A: 10.1–10.26**, **lane B: 10.27–10.51**. The second
lane should import `Rudin.PMA.Chapter10` from this branch. This inventory is a
scope record, not a claim that the nodes are proved.

| Node | Kind | Printed page | Brief content |
|---|---|---:|---|
| 10.1 | Definition | 245 | Iterated cell integration and intermediate continuity |
| 10.2 | Theorem | 246 | Independence of integration order |
| 10.3 | Definition | 246 | Closed support; enclosing-cell-independent whole-space integral |
| 10.4 | Example | 247 | Simplex zero extension; iterated integrability and order independence |
| 10.5 | Definition and properties | 248 | Primitive maps, derivative, Jacobian, invertibility |
| 10.6 | Definition | 249 | Coordinate flips and initial-coordinate projections |
| 10.7 | Theorem | 249 | Local primitive-map and flip factorization |
| 10.8 | Theorem and corollary | 251 | Finite subordinate partition of unity; function decomposition |
| 10.9 | Theorem | 252 | Change of variables with absolute Jacobian |
| 10.10 | Definition | 254 | Parametrized surfaces with C¹ neighborhood extensions |
| 10.11 | Definition | 254 | Differential forms through surface integration; regularity; 0-forms |
| 10.12 | Three examples | 254 | Exact line integral, ellipse integrals, spherical volume integral |
| 10.13 | Properties | 256 | Operational equality, linearity, antisymmetry, repeated-index vanishing |
| 10.14 | Definition and properties | 257 | Increasing indices, basic forms, signed standard presentation |
| 10.15 | Theorem | 258 | Uniqueness of standard coefficients from surface integrals |
| 10.16 | Definition and properties | 258 | Basic wedge products, inversion signs, associativity |
| 10.17 | Definition and properties | 259 | General wedge product, distributivity, associativity, 0-forms |
| 10.18 | Definition | 260 | Exterior derivative |
| 10.19 | Example | 260 | Endpoint formula for exact 1-forms; a nonexact 1-form |
| 10.20 | Two-part theorem | 261 | Graded Leibniz rule; exterior derivative squared vanishes |
| 10.21 | Definition | 262 | Pullback of differential forms |
| 10.22 | Three-part theorem | 263 | Pullback preserves addition, wedge products, exterior derivative |
| 10.23 | Theorem | 264 | Pullback composition law |
| 10.24 | Theorem | 264 | Surface integral via pullback to parameter domain |
| 10.25 | Theorem | 265 | Integration over a composed surface |
| 10.26 | Definition and properties | 266–267 | Affine simplexes, orientation, signed 0-simplex integration |
| 10.27 | Theorem | 267 | Vertex permutation and integration sign |
| 10.28 | Definition | 268 | Affine chains and additive integration |
| 10.29 | Definition | 269 | Alternating simplex boundary |
| 10.30 | Definition | 269 | Differentiable simplexes and chains |
| 10.31 | Definition and examples | 270 | Positively oriented boundaries and square triangulation |
| 10.32 | Example | 272 | Sphere parametrization has zero boundary |
| 10.33 | Theorem | 272 | Generalized Stokes theorem |
| 10.34 | Definition | 275 | Exact and closed forms |
| 10.35 | Four remarks | 275 | Closedness, boundary dependence, boundary squared vanishes |
| 10.36 | Example | 277 | Closed nonexact angular form on punctured plane |
| 10.37 | Example | 277 | Closed nonexact radial flux form on punctured space |
| 10.38 | Theorem | 278 | Coordinate primitive on an open convex set |
| 10.39 | Theorem | 278 | Poincaré lemma |
| 10.40 | Theorem | 280 | Exactness under a C² diffeomorphism |
| 10.41 | Remark | 280 | Triangulations and alternative parameter domains |
| 10.42 | Definitions | 281 | Vector fields, gradient, curl, divergence |
| 10.43 | Theorem | 281 | Vector differential identities and converse potentials |
| 10.44 | Definition and property | 282 | Volume form and positive parametrizations |
| 10.45 | Theorem | 282 | Green's theorem and area formulas |
| 10.46 | Definition and properties | 283 | Surface normals, area, tangent planes, orientation |
| 10.47 | Example | 285 | Solid torus volume and area |
| 10.48 | Definition and identity | 286 | Tangential arc-length interpretation of 1-forms |
| 10.49 | Definition and identity | 287 | Normal area interpretation of 2-forms |
| 10.50 | Theorem | 287 | Classical Stokes theorem |
| 10.51 | Theorem | 288 | Divergence theorem |

## Fidelity obligations

For 10.1–10.4, a measure-integral backend alone does not prove the printed
iterated-integral statements: agreement, intermediate continuity, and the
simplex zero-extension argument must be accounted for. Support means closed
support (`tsupport`). For 10.8 include the unnumbered corollary. For 10.12
include all three examples. For 10.15, equality means equality on every
surface integral; coefficient extensionality alone does not suffice.
For 10.22(c), the map has class C². Node 10.26 includes its continuation
through printed page 267; orientation is a relation and signed 0-simplexes
must be included.

## Prior work inspected

At baseline `87344489d0a8ce7fe00a37ef846a72fc70d33735`, Chapter 10 is an
empty documentation stub. The initial branch-name/PR inspection missed work
inside the cross-chapter branch `ch8-codex-20261022`; its initial conclusion
that there was no earlier Chapter 10 implementation was incorrect.

Following the user's correction, a full fetch identified commit
`bb50a2079f8e189d8e282e2521bbadb64f4f98eb`, which supplies prior proofs for
all 26 first-half nodes. The lane reuses those sources, with exact-byte hashes
in `evidence/ch10-a-reconciliation-manifest.json`, rather than replacing them
with the independent drafts started before that discovery. The prior inventory
also has 51 nodes. The second lane's fetched inventory explicitly adopts this
lane's ceiling-first split.

The prior proof dependency graph includes Chapter 8–9 files absent from this
lane. These other-lane files are left untouched; an isolated snapshot inside
this lane permits verification with the exact earlier prerequisites. The
standalone lane build and snapshot build are reported separately.

The toolchain is Lean 4.34.1; Mathlib remains pinned to
`d13f23b723b8a846827a245b89c10fc7d3f11612`.
