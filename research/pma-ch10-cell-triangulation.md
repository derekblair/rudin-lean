# Chapter 10.41: cell triangulation API reconnaissance

Independent reviewer: ch8_fidelity. Read-only library research; no Lean/lake invocation or production implementation.

Printed p.280 (PDF289) asserts that every cell can be triangulated and thereby regarded as a chain. It does not display a general cubical boundary formula. A faithful statement needs an actual finite affine-simplex decomposition with coverage and native integral compatibility, and compatibility with the induced chain boundary. Explicit coordinate-side formulas are useful for later examples but are not a separate displayed clause of 10.41.

Targeted searches in pinned Mathlib/Analysis, Geometry and MeasureTheory found no existing geometric cube triangulation/decomposition theorem. The categorical occurrences of “triangulated” are unrelated. The following APIs support a direct staircase construction.

## Sorting and cumulative sums

`Mathlib/Data/Fin/Tuple/Sort.lean`:

- `Tuple.sort (f : Fin n → α) : Equiv.Perm (Fin n)` (line79), for a linearly ordered codomain.
- `Tuple.monotone_sort f : Monotone (f ∘ Tuple.sort f)` (line94).
- `Tuple.eq_sort_iff` (line161): a permutation equals `sort f` iff it makes f monotone and orders equal-value ties by index. When the coordinate values are distinct, the tie condition is vacuous. Thus strictly ordered chambers have unique sorting permutations.
- `Tuple.comp_sort_eq_comp_iff_monotone` (line176) identifies any monotone permutation of the values with the sorted values, useful when ties remain on shared faces.

`Mathlib/Algebra/BigOperators/Fin.lean:478–522` defines the additive `Fin.partialSum` via `to_additive` from partial products. Its type is `(Fin n → A) → Fin (n+1) → A`, including the initial zero. Available generated declarations are `partialSum_zero`, `partialSum_succ`, `partialSum_succ'`, `partialSum_init`, `partialSum_left_inv`, and `partialSum_right_inv`. For `g : Fin (n+1) → A`, the left inverse says the cumulative sums of increments `-g i.castSucc + g i.succ`, translated by `g 0`, recover g. The right inverse recovers each increment from adjacent cumulative sums. Apply with `g = Fin.cons 0 y` for sorted nonnegative coordinates y. These identities remove most manual telescoping work.

## Orientation and interiors

Let L be the lower-triangular matrix with entries one on and below the diagonal. Its image of the standard simplex is the chamber `0 ≤ x0 ≤ ... ≤ x(n-1) ≤ 1`. The native source domain remains the usual nonnegative-coordinate simplex with sum at most one.

- `Matrix.det_of_isLowerTriangular (M) (h)` in `LinearAlgebra/Matrix/Block.lean:397` gives the determinant as the diagonal product, hence det L=1. The matching upper-triangular theorem is at line390.
- `Matrix.det_submatrix_equiv_self (e) (A)` in `LinearAlgebra/Matrix/Determinant/Basic.lean:224` states `det (A.submatrix e e)=det A`.
- Orient each permuted chamber with a simultaneous row/column permutation (equivalently conjugate L by the coordinate permutation). This makes every determinant +1 while giving exactly the permuted image chamber: the compensating domain permutation preserves the standard simplex. It avoids separately changing vertex order according to the permutation sign.
- `Homeomorph.image_interior` in `Topology/Homeomorph/Defs.lean:309` identifies the interior of the image under the invertible affine chart. Strictly positive increments and sum strictly below one yield strict coordinate order. `Tuple.eq_sort_iff` then proves distinct chamber interiors disjoint. The frontier may belong to several closed pieces, as required.

## Native integral and cell transport

The existing PositiveRegion image-integral theorem can sum the positive unit-cube staircase pieces once their carrier union is the unit cube and their interiors are disjoint. It establishes equality of the actual native integrals through the already-reviewed measure bridge; this does not require another multidimensional integration theory.

For a general cell with lower endpoint a and upper endpoint b, use the actual affine map `x ↦ a + (b-a)*x` coordinatewise. For positive side lengths its determinant is the product of those lengths, and its image is the cell. The existing affine/C2 chain pushforward and native pullback theorem transfer both integration and boundary. Include dimension zero explicitly: there is one empty permutation and one point simplex.

For a degenerate cell, retain the same affine map and simplex family. Coverage still holds, but at least one diagonal factor is zero. The top-degree native integrand on every pushed-forward simplex is zero by the determinant formula, matching the existing zero integral of the degenerate cell. Its boundary compatibility follows from actual chain pushforward commuting with the boundary; it must not be discarded merely because the full-dimensional determinant vanishes. If an explicit side-face boundary functional is desired, paired collapsed faces cancel under that same map.

This note supplies proof architecture and exact pinned APIs, not a formal proof or a claim that an unproved triangulation theorem is already available.
