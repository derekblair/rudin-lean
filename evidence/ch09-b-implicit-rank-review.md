# Chapter 9 implicit and rank source review

Reviewed against the local PMA third-edition PDF, printed pages 224–231.
The explicit example on page 227 was also rendered and inspected visually;
the temporary page image is not retained in the repository.

## 9.26–9.29

`Implicit.lean` retains both block restrictions and their reconstruction identity,
solves the linear implicit equation uniquely with the stated negative inverse
formula, and proves the nonlinear local existence and uniqueness statement on
open sets. The implicit function is C1 throughout its neighborhood, takes the
required base-point value, solves the original equation there, and has the
asserted derivative. No premise assumes an inverse or a nonlinear implicit
solution exists.

The functions, base points, two-by-five derivative, two-by-two inverse, and all
six entries of the implicit derivative in 9.29 agree with the displayed example.

Representation changes are explicit: product vectors represent concatenated
coordinates, and the general theorems hold over real Banach spaces. This
includes every finite-dimensional coordinate case in the printed statements.

## 9.32

The main `pma9_32` statement in `Rank.lean` preserves the constant-rank hypothesis,
the derivative at the distinguished point, and the arbitrary projection with
that derivative's range. Intrinsic dimensions replace the separate natural
numbers n, m, r; the printed inequalities follow automatically for a linear map.

The returned open partial homeomorphism has the distinguished point in its
target U, U lies in the original domain, and both directions are C1. Its source
V is additionally convex. The image A(V) is open in the range of A. The function
phi is C1 there, takes its values in the kernel of P, and satisfies the exact
printed graph equation. The ambient-valued representation of phi together with
P(phi(y))=0 is documented at the node and is equivalent to a kernel-valued map.

The proof constructs the change of coordinates and uses the constant-rank
hypothesis to show that the derivative of the residual vanishes on ker(A).
`RankFactorization.lean` proves descent on convex fibers using a continuous
linear right inverse. There is no strengthened regularity hypothesis or assumed
factorization.

The attached geometric consequences in `RankGeometry.lean` express the local
image as an exact graph, make projection a bijection onto A(V), identify the
transformed level sets, transport intersections with affine translates of ker(A)
through H, and give the kernel dimension by rank-nullity.

## Validation

- `lake build Rudin.PMA.Chapter09.Implicit`: passed.
- `lake build Rudin.PMA.Chapter09.RankFactorization`: passed (3176 jobs before the
  latest first-half imports were integrated).
- Direct axiom checks of `pma9_26`, `pma9_27`, `pma9_28`, `pma9_29`,
  `rankSupport_factorization`, and `rankSupport_isOpen_image` passed: each depends
  only on `propext`, `Classical.choice`, and `Quot.sound`.
- `lake build Rudin.PMA.Chapter09.RankGeometry`: passed (8932 jobs), including
  the main rank theorem, factorization, and all geometric consequences after
  the updated first-half imports were integrated.
- Source scanning of the three modules owned/reviewed here found no proof holes,
  custom axioms, or native decision procedures.
- The integrating agent records the final build and recursive namespace audit
  after all dependency updates.
