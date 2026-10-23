# Needs insight: PMA 10.43, C2 vector-potential converse

Chapter: 10. Statement reference: printed pp.281–282, theorem10.43(b′), fourth conjunct of `Rudin.PMA.Chapter10.pma10_43_contract` in `VectorPotentials.lean`.

## Exact outstanding statement

For open sets `U,E ⊆ Euclidean 3`, with `U` convex and an actual `C2DomainEquivalence U E`, every `C1` field `F` on `E` satisfying `divergence F = 0` on `E` has a vector potential `G` of class **C2** on `E`, with `curl G = F` there. Empty, unbounded, and nonrectangular domains remain allowed. The printed C2 conclusion has been independently checked against the source scan.

## What is proved

The root-owned compiler gate has passed the full C1 Poincaré lemma10.39, its C2-domain transport10.40, and the following separate results in `VectorPotentials.lean`:

- Both forward identities, `curl (gradient u) = 0` and `divergence (curl G) = 0`, for C2 input.
- The full scalar converse, including a C2 scalar potential from a C1 curl-free field.
- The exact gradient/curl and exterior-derivative equivalences.
- `vectorPotential_c1_of_equivalent_convex`, which constructs a **C1** vector potential from the hypotheses above.

The exact four-clause source contract remains unchanged. There is no theorem named `pma10_43`, no placeholder proof, and no axiom asserting the missing regularity. The separately named C1 vector result is not counted as completion of the C2 source clause.

## What was tried

1. The explicit radial homotopy constructs a C1 primitive and verifies its exterior derivative by coefficientwise integration and the fundamental theorem of calculus. Joint C1 regularity supplies exactly the C1 coefficient estimate proved in10.39; differentiating a second time would require further control that is absent from the premise.
2. The scalar upgrade succeeds because every first partial of a scalar potential is a component of the prescribed C1 field. `PotentialRegularity.lean` formalizes this in arbitrary finite dimension. A curl equation determines only antisymmetric combinations of a vector potential's first derivatives, so this argument does not give its complete C1 derivative.
3. Raw radial regularity cannot simply be upgraded: a closed form `h(x) dx∧dy`, with a C1 but non-C2 function `h`, can give a radial primitive whose coefficients remain only C1. Such an example does not rule out a different C2 primitive.
4. The primary Hölder/Hodge and divergence references examined give gains for positive noninteger Hölder exponents or Dini hypotheses. The C0/Lipschitz counterexamples examined do not by themselves establish failure at the distinct C1/C2 endpoint. Details and links are in [the independent regularity investigation](pma-ch10-potential-regularity.md).
5. Reduction to a planar divergence equation was checked: apply the missing assertion to `F(x,y,z)=(0,0,f(x,y))`. A C2 curl potential would yield a C2 planar vector field `(G₂,-G₁)` with divergence equal to any prescribed C1 `f`. No proof or counterexample for this exact endpoint has been established here.

## What is missing

A valid argument establishing the exact C1-to-C2 curl-potential regularity, or a rigorous counterexample resolving the printed assertion. A sufficient positive route is local C2 solvability on balls, followed by a proved globalization using local potentials, scalar gauges, and a smooth partition of unity; the existing global C1 potential supplies the topological part. Neither a Hölder premise on the input nor a C1 conclusion may silently replace the source statement.

Status: **needs insight**, rather than a compiler or API failure. This entry does not claim that the printed theorem is false. The completed partial results remain available for subsequent work, and the source node remains incomplete until the fourth conjunct is resolved.
