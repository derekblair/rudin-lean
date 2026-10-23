# Native simplex Stokes: pinned API and proposed proof interfaces

Source33 is the general C² parameterized k-chain theorem for a C¹ (k−1)-form
on an open set, k≥1. The parameter integral remains the actual native integral.
The source census is in `pma-ch10-inventory.md`. The initial sections record the pinned API research; the implementation status
at the end distinguishes compiled ingredients from the pending final assembly.

## Available pinned divergence theorems

`Mathlib/Analysis/BoxIntegral/DivergenceTheorem.lean:158` provides
`BoxIntegral.hasIntegral_GP_pderiv`: a coordinate derivative integrated over a
closed rectangular box equals upper-face minus lower-face integrals. The
integral is the GP gauge integral. Its vector sum version is
`hasIntegral_GP_divergence_of_forall_hasDerivWithinAt` at265.

The more direct measure bridge is
`Mathlib/MeasureTheory/Integral/DivergenceTheorem.lean:266`,
`MeasureTheory.integral_divergence_of_hasFDerivAt_off_countable`:

- endpoints `a ≤ b` in `Fin (d+1) → ℝ`;
- vector field continuous on `Icc a b`;
- actual Fréchet derivative on the open box outside a countable exceptional set;
- integrability of the divergence on the box;
- conclusion: its set integral is the sum of upper minus lower face integrals,
  using `Fin.insertNth` for each face.

The family-of-scalar-functions version has a trailing apostrophe and starts
at296. For C¹ coefficients the exceptional set is empty and compact continuity
supplies integrability. Existing native cell bridges can transport this result.
Neither theorem handles a simplex. Searches of the pinned analysis and measure
integral trees found no general simplex divergence/Stokes theorem. A box-only
wrapper would not discharge source33.

## Shortest native simplex route

Use the native fiber results already proved for10.4 and one-dimensional FTC.
For `f : Coord (d+1) → ℝ`, C¹ on an open neighborhood U of the standard simplex,
the essential scalar lemma should be:

```
simplexRIntegral (fun x => fderiv ℝ f x (Pi.single i 1)) =
  simplexRIntegral (fun u =>
    f (i.insertNth (1 - ∑ j, u j) u) - f (i.insertNth 0 u))
```

Both sides have explicit native recursive integrability from10.4 before any
measure rewriting. For the last coordinate, `simplex_slice_integrable_formula`
and `simplex_slice_eq_setIntegral` already identify every actual fiber. Apply
native6.21, or its already proved native-to-interval bridge followed by
`intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le`, on
`[0, 1 - ∑u_j]`. This includes the collapsed endpoint `sum u = 1`.
Outside the lower-dimensional simplex, the zero-extension fiber vanishes.
`integral_cell_snoc` and `simplexRIntegral_eq_integral` then assemble the fiber
identity. Other coordinates follow by the proved coordinate-permutation
invariance in10.4 and the linear chain rule.

A convenient intermediate API is a simplex Fubini formula with the upper bound
`1 - sum u`; prove it first for continuous functions on the closed simplex.
The existing Tietze extension is only an auxiliary device: the resulting
formula is independent of the extension on every admissible fiber.

## Upper face and orientation bridge

Each scalar coordinate FTC has its own parametrization of the upper face
`sum x_i = 1`. Combining them into the single ordered face0 requires invariance
under permutations of **simplex vertices**, which includes swapping the origin
with a coordinate vertex. Existing10.4 coordinate-permutation invariance alone
is insufficient for this step.

A reusable native helper can accept a differentiable injective affine map A,
`A '' standardSimplex d = standardSimplex d`, and absolute derivative determinant
one, and conclude `simplexRIntegral (f ∘ A) = simplexRIntegral f` for continuous
f on the simplex. The exact pinned bridge is
`MeasureTheory.integral_image_eq_integral_abs_det_fderiv_smul` in
`MeasureTheory/Function/Jacobian.lean:1213`; it requires only a measurable set,
`HasFDerivWithinAt` at every point, and `InjOn`. The integrability companion is
at1199. Thus no compact-support extension is needed. The native existence
conclusion is still obtained independently by10.4 and continuity of A.

The chain API should expose vertex-face maps and their derivative matrices,
plus affine vertex-permutation determinant signs. This supports both orientation
well-definedness in26–30 and the top-face reconciliation in33. Coordinate-face
minors give the usual signs; the top face0 map with ordered vertices
`e0,e1,...` can be written `u ↦ Fin.cons (1 - sum u) u`.

## Proposed module boundary

1. `SimplexFTC`: scalar fiber/Fubini and coordinate-derivative integral lemma;
   independent of chains and exterior algebra.
2. A geometry helper in the chain lane: native invariance under affine vertex
   permutations and the signed face-minor identities.
3. `SimplexStokes`: standard parameter simplex, coefficient expansion of a
   C¹ form of degree d in dimension d+1, scalar FTC plus signed faces.
4. General C² simplex: use22 to commute d with pullback and25 for actual native
   integral naturality. The restricted pullback is C¹ on a genuine open
   parameter neighborhood. No injectivity assumption is introduced.
5. Finite ℤ-chains: extend by finite integral linearity and boundary additivity;
   the k=1 case retains zero-dimensional face evaluations and reproduces19.

All claims about APIs above were read from the pinned local sources. No Lean,
lake, installation, or git operation was run by this research lane.


## Implementation status

The proposed scalar and transport boundaries have now been implemented.
`SimplexFTC.lean` proves direct arbitrary-coordinate disintegration, not merely
a last-coordinate special case, and both native recursive integrability
conclusions precede its measure calculation. This module is compiled and has
independent mathematical acceptance. The general affine change-of-variables
helper and `simplexRIntegral_vertexPermutation` are also compiled.

`StokesCoefficients.lean` and `StandardSimplexSurface.lean` are compiled. The full
standard-simplex proof is drafted in `SimplexStokes.lean`, using the signed
coordinate-face evaluations in `SimplexFormFaces.lean`. It includes dimension
one and both zero-dimensional faces. The final assembly is frozen for the
independent proof review and serialized compiler gate. General C² pullback
transport and integer-chain linearity remain in root's separate
`StokesTransport.lean`; the standard coefficient calculation introduces no
injectivity premise on the source simplex.
