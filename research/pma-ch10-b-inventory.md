# Chapter 10 second-half source inventory

Source: Walter Rudin, *Principles of Mathematical Analysis*, third edition,
Chapter 10, consulted in `/root/sources/pma3.pdf`. The chapter's exposition runs
from printed page 245 through printed page 288 (PDF pages 254–297); the exercises
begin on printed page 288. Summaries below are original, brief descriptions.

There are **51 consecutive numbered exposition nodes, 10.1–10.51**. There are no
missing or repeated node numbers. A reference to 10.20 at the beginning of a
line on printed page 263 is a cross-reference, not another node. The unnumbered
corollary following 10.8 belongs to 10.8. Numbered chapter exercises are not
additional exposition nodes.

## Split by node order

For the odd total, the reconciled split uses the **ceiling-first choice**, as
recorded by the first-half lane in commit `47f1bdb`:

- First half, `rudin-ch10-a`: the first 26 nodes, **10.1–10.26**.
- Second half, `rudin-ch10-b`: the final 25 nodes, **10.27–10.51**.

This is a split by node count, not by page count or mathematical difficulty. The
chosen convention assigns 10.26 to the first half. This supersedes the initial
floor-first working assumption; the second lane must not duplicate 10.26.

## Full numbered-node list

| Node | Printed page(s) | Kind | Brief mathematical content |
| --- | --- | --- | --- |
| 10.1 | 245–246 | Definition | Integrate a continuous function over a rectangular cell by successive one-dimensional integrations. |
| 10.2 | 246 | Theorem | The resulting cell integral is independent of coordinate integration order. |
| 10.3 | 246–247 | Definition | Define closed support and the integral of a compactly supported continuous function using an enclosing cell; independence of the enclosing cell. |
| 10.4 | 247–248 | Example | Integrate a continuous function on the standard simplex by extension by zero; establish existence and order independence. |
| 10.5 | 248 | Definition and calculation | Primitive maps alter at most one coordinate; calculate their derivative and Jacobian and characterize derivative invertibility. |
| 10.6 | 249 | Definition | Define coordinate flips and initial-coordinate projections. |
| 10.7 | 249–250 | Theorem | Locally factor a C¹ map fixing the origin with invertible derivative into primitive maps and coordinate flips. |
| 10.8 | 251 | Theorem and unnumbered corollary | A compact set admits a finite continuous partition of unity subordinate to an open cover; decompose supported functions accordingly. |
| 10.9 | 252–253 | Theorem | Change of variables for a compactly supported continuous function under an injective C¹ map with nonzero Jacobian, using the absolute Jacobian. |
| 10.10 | 254 | Definition | A k-surface is a C¹ parametrization from a compact cell or standard simplex; regularity on a compact domain means extension to an open neighborhood. |
| 10.11 | 254 | Definition | Differential forms act on parametrized surfaces through coefficient functions and Jacobian minors; define coefficient regularity and zero-forms. |
| 10.12 | 254–255 | Three examples | Compute the endpoint formula for x dy + y dx, the ellipse integrals of x dy and y dx, and the unit-ball volume integral in spherical coordinates. |
| 10.13 | 256 | Elementary properties | Equality and linear operations are detected by all surface integrals; swapping coordinate differentials changes sign, repeats vanish, and degree above dimension vanishes. |
| 10.14 | 257 | Definition and examples | Increasing coordinate indices give basic forms and a standard presentation; count basic forms and perform representative reorderings. |
| 10.15 | 258 | Theorem | A form that integrates to zero on every surface has all standard-presentation coefficients zero. |
| 10.16 | 258–259 | Product construction | Concatenate basic indices, compute signs by inversions, obtain zero for overlapping indices, and establish associativity. |
| 10.17 | 259–260 | Definition and properties | Extend wedge multiplication to forms; establish distributivity and associativity, including multiplication by zero-forms. |
| 10.18 | 260 | Definition | Define the exterior derivative from coefficient partial derivatives. |
| 10.19 | 260–261 | Example | Integrating df along a C¹ curve gives the endpoint difference; x dy cannot be the differential of a global zero-form. |
| 10.20 | 261–262 | Theorem | The exterior derivative satisfies the graded product rule and has square zero on C² forms. |
| 10.21 | 262 | Definition | Define pullback of a form under a C¹ map by substituting component differentials. |
| 10.22 | 263 | Theorem | Pullback preserves addition and wedge products; pullback by a C² map commutes with exterior differentiation of C¹ forms. |
| 10.23 | 264 | Theorem | Pullback respects composition of C¹ maps. |
| 10.24 | 264–265 | Theorem | A surface integral equals integration of its pulled-back form on the identity parameter surface. |
| 10.25 | 265–266 | Theorem | Integrating a form on a composed surface equals integrating its pullback on the original surface. |
| 10.26 | 266–267 | Definitions and orientation convention | Define affine maps, standard and vertex-parametrized affine simplexes, orientation under vertex permutations, determinant orientation in equal dimensions, and signed zero-simplexes. |
| 10.27 | 267–268 | Theorem | Reordering simplex vertices changes integration by the sign of the permutation. |
| 10.28 | 268–269 | Definition and interpretation | Define finite affine chains and their integrals; interpret chain sums as sums of integration functionals, including orientation cancellation. |
| 10.29 | 269 | Definition and examples | Define the boundary as the alternating sum of vertex-deletion faces and give triangle and face-parametrization formulas. |
| 10.30 | 269–270 | Definitions | Push affine simplexes through C² maps, form C² chains, and define simplex and chain boundaries by pushforward and linearity. |
| 10.31 | 270–271 | Definition and discussion | Define positive boundaries of orientation-preserving simplex images and finite unions with disjoint interiors; assert parametrization independence and work out the square decomposition and boundary cancellation. |
| 10.32 | 272 | Example | The standard latitude–longitude parametrization of the unit sphere has zero boundary as an integration functional, by cancellation of meridians and constant curves. |
| 10.33 | 272–275 | Theorem | Stokes' theorem: a C¹ form integrated on the boundary of a C² chain equals its exterior derivative integrated on that chain. |
| 10.34 | 275 | Definitions and implication | Define exact and closed forms and state that exact C¹ forms are closed. |
| 10.35 | 275–276 | Four remarks | Characterize closed one-forms by equality of mixed coefficient derivatives; derive integral invariance and vanishing for exact/closed forms; establish that a boundary has zero boundary. |
| 10.36 | 277 | Example | The angular one-form on the punctured plane is closed, has circle integral 2π, is not exact, and detects a circle that cannot bound a C² chain there. |
| 10.37 | 277 | Example | The radial flux two-form on punctured three-space is closed, has sphere integral 4π, is not exact, and detects a sphere that cannot bound a C² chain there. |
| 10.38 | 278 | Theorem | On a convex open set, a C¹ function independent of all coordinates after p has a C¹ antiderivative in coordinate p with the same later-coordinate independence. |
| 10.39 | 278–279 | Theorem | Poincaré's lemma: closed C¹ forms of positive degree on convex open sets are exact. |
| 10.40 | 280 | Theorem | Exactness of all closed forms of a fixed positive degree is invariant under C² diffeomorphisms; apply this to sets C²-equivalent to convex open sets. |
| 10.41 | 280 | Remark | Cells can be triangulated and treated as chains; discuss the relationship between this representation and simplex-based Stokes theory. |
| 10.42 | 281 | Definitions and correspondences | Associate one- and two-forms with vector fields in three-space; define gradient, curl, and divergence and identify every such form with a field. |
| 10.43 | 281–282 | Theorem | Curl of a gradient and divergence of a curl vanish under the stated C² hypotheses; for C¹ fields on sets C²-equivalent to convex sets, assert a C² scalar or vector potential in the respective converses. |
| 10.44 | 282 | Definition and interpretation | The top coordinate form is the volume element; orientation-preserving change of variables identifies its integral with ordinary volume integration. |
| 10.45 | 282–283 | Theorem and applications | Green's theorem for the positive boundary construction of 10.31; derive the boundary formulas for enclosed area. |
| 10.46 | 283–285 | Definitions and geometric properties | Define the normal from Jacobian minors and the area integral; prove orthogonality, the positive determinant identity, and the tangent-parallelogram area formula. |
| 10.47 | 285–286 | Example | Parametrize a solid torus with 0 < a < b; compute its Jacobian, volume 2π²a²b, surviving oriented boundary, outward normal, and surface area 4π²ab. |
| 10.48 | 286–287 | Integral representation | Rewrite the one-form integral as the integral of the tangential component against arc length, including a convention at zero velocity. |
| 10.49 | 287 | Integral representation | Rewrite the two-form integral as normal flux against surface area, including a convention where the parametrized normal vanishes. |
| 10.50 | 287–288 | Theorem | Vector Stokes formula equates curl flux over a C² surface with tangential circulation around its oriented boundary. |
| 10.51 | 288 | Theorem | The divergence theorem equates volume integration of divergence with outward flux over the positive boundary from 10.31. |

## Second-half fidelity requirements and dependencies

- **10.26 (first-half dependency):** Vertices need not be affinely independent. The map depends on the
  ordered vertices, while orientation equivalence does not assert equality of
  parametrizations. Signed zero-simplexes are a separate convention. A standard
  simplex consisting only of its vertices is insufficient: the full barycentric
  parameter set and its affine parametrization are required. Determinant-based
  orientation is asserted only for nondegenerate simplexes in the same ambient
  dimension.
- **10.27:** The sign relation concerns actual differential-form integrals,
  including coefficient evaluation at the parametrized point. An alternating
  abstract functional alone does not establish the analytic theorem. This node
  uses the first half's integration, change-of-variables, and pullback results.
- **10.28–10.30:** A chain can repeat simplexes. Addition of chains adds their
  integration functionals; it is not pointwise addition of parametrizations.
  Faces retain their order and signs. A C² parametrization extends to an open
  neighborhood, and its map need not be injective. The printed 10.30 definition
  uses C² maps, as does the later Stokes theorem; the scanned double prime must
  not be misread as a general superscript r.
- **10.31:** The discussion includes mathematical claims beyond a boundary
  definition: independence from a chosen positive parametrization, finite-union
  additivity with disjoint interiors, and the square's internal-edge cancellation.
  A completely arbitrary closed subset is not a permitted region; the positive
  boundary construction is part of the hypotheses in 10.45 and 10.51.
- **10.32:** Zero boundary means the integral of every continuous one-form on
  that boundary is zero. It is not equality to an empty list of parametrized
  curves. Both constant-boundary pieces and the reversed-meridian cancellation
  need justification.
- **10.33:** A faithful implementation must prove finite-dimensional Stokes
  for genuine forms and C² parametrized chains. Assuming the integration
  identity as a structure field or theorem hypothesis is not a proof of this
  node. The book reduces to a coordinate form on a standard simplex and then
  uses iterated integration and the fundamental theorem of calculus.
- **10.34–10.35:** Closedness is a differential condition and exactness requires
  an existing primitive. Do not replace exactness by closedness in a definition.
  The four parts of 10.35 include both implications for integrals and the
  boundary-of-boundary assertion. The regularity required when applying d² = 0
  or Stokes must be tracked rather than inferred from the names of predicates.
- **10.36–10.37:** These are explicit analytic and topological examples, not
  generic implications from an assumed nonzero period. The forms, domains,
  circle/sphere parametrizations, closedness, periods, and both nonexistence
  conclusions are all substantive parts. The denominators are x² + y² in the
  planar example and (x² + y² + z²)^(3/2) in the spatial example.
- **10.38–10.40:** These are genuine existence theorems. Convexity and openness
  are hypotheses in 10.38 and 10.39. The condition p ≤ n allows p = n, when the
  later-coordinate conditions are empty. A primitive postulated as an input
  does not establish 10.38 or 10.39. For 10.40, the map and its inverse are C²;
  the equality of their pullback compositions is supplied by 10.23.
- **10.41:** There is an explicit triangulation assertion. If only the
  surrounding expository commentary is recorded, the mathematical claim remains
  unformalized.
- **10.42–10.43:** Coordinate gradient/curl/divergence operators must be connected
  to the exterior derivative and the two vector-field/form correspondences.
  Both vanishing identities and both potential converses belong to 10.43; the
  converse depends on 10.39–10.40, not merely on d² = 0. The printed converse
  asserts C² regularity for both the scalar and vector potentials, despite
  assuming only C¹ regularity for the input field. A weaker regularity result
  must not silently stand in for this printed conclusion.
- **10.44–10.46:** Surface integration counts a parametrized surface, potentially
  with multiplicity. Surface area uses the norm of the normal; integration of
  a two-form retains orientation. In 10.46 the nondegenerate tangent-plane
  discussion assumes differential rank two. The algebraic normal formulas
  remain meaningful at lower rank, with zero normal.
- **10.47:** The torus map is injective only in the interior of the parameter
  cell. Several boundary faces coincide with opposite orientations, and the
  degenerate face has zero area contribution. Computing only the displayed
  constants does not cover these boundary and orientation claims.
- **10.48–10.49:** Unit tangent and unit normal live on the parameter domain;
  self-intersections need not give a unique such vector at an image point.
  The chosen fallback at a zero derivative/normal contributes zero to the
  corresponding weighted integral.
- **10.50–10.51:** These are specializations of proved Stokes and the established
  vector/form integration identities. The boundary must have the correct
  orientation. Neither is a tautological equality introduced by defining one
  side to be the other.

This inventory records source scope, not implementation completion. A node is
complete only when its substantive definitions and claims have been reconciled
with compiled, axiom-audited declarations; partial helper lemmas must be reported
as partial coverage.
