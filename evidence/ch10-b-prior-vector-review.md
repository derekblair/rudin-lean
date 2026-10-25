# Independent review of recovered PMA 10.42–10.51

Date: 2026-10-25. Reviewed the recovered lane sources against printed
pp. 281–288 of `/root/sources/pma3.pdf`, with a visual check of the regularity
symbols in 10.43, 10.44, and 10.46. The source specifies C² potentials in both
converses of 10.43, C¹ parametrizations in 10.44, and C¹ surfaces in 10.46.

The 18 production modules examined below are byte-identical to their versions
in recovered commit `bb50a2079f8e189d8e282e2521bbadb64f4f98eb` at review time.
No implementation was edited, no new proof was substituted, and no build was
started by this reviewer. The root-owned build and recursive axiom audit are
separate verification gates; this document is not their result.

## Coverage and principal proof semantics

| Node | Principal declaration and assessment |
|---|---|
| 10.42 | `VectorFields.pma10_42` proves the coordinate definitions, both vector/form reconstruction directions, their injectivity on the domain, and continuity of gradient/curl/divergence with the printed hypotheses. The 2-form basis uses the correct cyclic signs: `(dy∧dz, dz∧dx, dx∧dy)`. |
| 10.43 | **Incomplete.** `pma10_43_forward` proves both identities for C² inputs; `pma10_43_scalar_converse` proves the full C² scalar-potential conclusion from a C¹ curl-free field. The separately named vector-potential result yields only C¹. There is no theorem `pma10_43`. |
| 10.44 | `VolumeElements.pma10_44` proves the density/Jacobian integrand identity and the equality with ordinary volume integration on the actual image of an injective, positively parametrized surface. The constant density gives actual ambient image volume. The proof uses the measure change-of-variables theorem only after proving native parameter integrability and its integral bridge. |
| 10.45 | `PlanarGreen.pma10_45` derives Green's identity from the actual chain Stokes theorem, with the correct sign `D₁β − D₂α`. It includes both the symmetric half-integral area formula and the `x dy` area formula, with existence of the required native integrals. |
| 10.46 | `AreaElements.pma10_46` covers the three Jacobian minors, area density and its integrability, tangent affine image, normal orthogonality, determinant `‖N‖²`, rank-two/nonzero-normal equivalence, rank-deficient cases, and the affine rectangle/unit-square area formulas. These are derived from the actual derivative and Euclidean cross product. |
| 10.47 | `TorusProof.pma10_47` covers the literal source parametrization, injectivity in the cell interior, image equal to the explicit solid-torus set, Jacobian and its sign, native and ordinary image volumes, the actual boundary's integration-functional equality with the outer torus, unit normal, outwardness, surface area, and the top-point computation. The boundary proof cancels the two periodic face pairs and proves that the radius-zero face integrates every continuous 2-form to zero. |
| 10.48 | `Circulation.pma10_48` proves equality of the 1-form integral, coordinate sum, velocity inner product, and weighted unit-tangent integral. It includes zero-speed fallback independence, integrability, and the Chapter 6 curve-length bridge on cell intervals. The tangent is parameter-indexed, as the source requires. |
| 10.49 | `Flux.pma10_49` proves equality of the 2-form integral, derivative-normal inner product, and weighted unit-normal integral. It includes rank-deficient points and arbitrary unit fallback at zero normal, with no unjustified continuity assumption on the normalized field. |
| 10.50 | `ClassicalStokes.pma10_50` specializes the actual surface/chain Stokes theorem using the proved derivative identity for the vector 1-form. Both sides are then identified with the normal-component and tangent-component native integrals, including integer boundary signs and integrability. |
| 10.51 | `DivergenceTheorem.pma10_51` identifies the ordinary volume integral with the density-form chain integral and applies general Stokes. It then expands actual boundary flux into signed normal-component integrals and proves independence of the admissible decomposition. |

The source-level result of this review is coverage of **10.42 and 10.44–10.51**,
subject to the independent compilation/audit gate, and partial coverage of
10.43. These are substantive proofs, rather than contracts supplied as
hypotheses or definitions of the desired equality.

## Exact unresolved obligation in 10.43

The fourth conjunct of `VectorPotentials.lean:16`, `pma10_43_contract`, requires:
for open `U,E ⊆ ℝ³`, convex `U`, a genuine `C2DomainEquivalence U E`, and a C¹
field `F` on `E` with zero divergence, there exists a **C²** field `G` on `E`
whose curl equals `F` there. No boundedness, rectangular-domain, global
regularity, or positive-Hölder assumption is part of that contract.

`vectorPotential_c1_of_equivalent_convex` obtains an exact 2-form from the
proved Poincaré/domain-transport result, extracts its primitive 1-form as a
vector field, and proves `curl G = F`. Its primitive regularity is exactly C¹.
This is a useful theorem but does not entail the fourth conjunct.

`PotentialRegularity.lean` legitimately upgrades the scalar primitive: all
first coordinate partials of the scalar function equal prescribed C¹
components, so its entire Fréchet derivative is C¹ and the scalar function
is C². A curl equation prescribes only antisymmetric combinations of vector
derivatives. The same proof does not upgrade the vector potential. Pulling
back a 1-form through a merely C² domain map also introduces first
derivatives of that map, so a C² output cannot be inferred by relabeling the
existing transport proof.

The earlier notes were inspected directly with `git show`:

* `bb50a20:research/pma-ch10-43-needs-insight.md`;
* `bb50a20:research/pma-ch10-potential-regularity.md`.

Their description agrees with the code. They distinguish failure of the
particular radial construction to gain a derivative from nonexistence of a
different C² potential, and explicitly do not claim a counterexample. Their
reduction to planar divergence is valid: a potential for
`F(x,y,z)=(0,0,f(x,y))`, restricted to `z=0`, would give a C² planar field
`(G₂,-G₁)` with divergence `f` for arbitrary C¹ `f`.

This is a **genuine unresolved mathematical regularity obligation**, not a
compiler inconvenience or a missing general Stokes/Poincaré API. Neither the
current source nor this review resolves that endpoint. The exact C² clause
must remain outstanding; the C¹ theorem must not count as completion or as a
silent repair of the book.

## Source scope and representation differences

No strengthened premise narrowing the printed cases was found in these
completed nodes. The following explicit modeling choices and extensions
should nevertheless be retained in the final fidelity report:

* **All nodes:** vector fields/forms are total ambient functions with
  regularity and equality restricted to the stated set. There is no hidden
  smoothness requirement outside that set. Native iterated parameter
  integrals remain in the definitions; ordinary measure integrals are
  reached through proved bridges.
* **10.42:** the contract additionally proves uniqueness of both vector/form
  correspondences and records regularity preservation. This strengthens
  the conclusion without restricting the source data.
* **10.43:** only the separate C¹ vector-potential theorem is weaker than
  the printed conclusion. Its comment and the exact unchanged contract
  explicitly flag this; the principal source node is left incomplete.
* **10.44:** the theorem includes dimension zero and arbitrary ambient sets
  when openness is unnecessary. Its nontrivial image-volume clause retains
  injectivity on the complete parameter domain and positive Jacobian there.
* **10.45 and 10.51:** `PositiveRegion` means a finite union of injective C²
  simplex images with Jacobian positive in the simplex interior and pairwise
  disjoint image interiors. This matches the admissible regions of 10.31;
  it is not a theorem for every closed set with an arbitrary topological
  boundary. Boundary degeneracy is allowed. Integer coefficients encode
  orientation/multiplicity of the boundary chain, not arbitrary signed
  multiplicities of the region's volume.
* **10.46:** degenerate rectangles and every derivative rank are handled
  explicitly. Area is the source's parametrized area integral, and the
  affine rectangle computation uses that area. No additional theorem about
  Hausdorff measure of an immersed image or convergence of arbitrary tangent
  approximations is claimed.
* **10.47:** the torus is additionally identified by an explicit inequality,
  and its ordinary image volume is proved. Outwardness is formalized by
  leaving that solid set after any normal displacement `0 < s < b-a`.
  This expresses local outwardness; it does not impose the false stronger
  requirement that every positive normal ray stay outside forever.
* **10.48:** the interval `[0,1]` is generalized to all admitted one-dimensional
  cell/simplex parameter domains, with the length bridge on cells. The
  field need only be continuous on the curve image, and any unit fallback
  is allowed at zero velocity. These are extensions, not restrictions.
* **10.49:** continuity only on the surface image suffices, and arbitrary
  unit fallbacks are proved harmless at zero normal. The normal remains
  parameter-indexed; no injectivity or immersion is assumed.
* **10.50:** the source's C² cell and simplex surfaces are both handled via
  their actual triangulated boundary chains. Neither immersion nor
  nonvanishing curl/normal/velocity is introduced as an extra hypothesis.

## Axiom/source inspection and provenance

The reviewed production files were `VectorFields`, `VectorFormDerivatives`,
`VectorPotentials`, `PotentialRegularity`, `VolumeElements`, `PlanarGreen`,
`AreaElements`, `Torus`, `TorusCalculus`, `TorusGeometry`, `TorusVolume`,
`TorusBoundary`, `TorusProof`, `CellImageVolume`, `Circulation`, `Flux`,
`ClassicalStokes`, and `DivergenceTheorem`.

All 18 were compared byte-for-byte with the prior commit. A lexical scan
after stripping nested block comments and line comments found no `sorry`,
`admit`, `axiom`, `unsafe`, or `sorryAx` token. In particular, defining the
unproved proposition `pma10_43_contract` is not asserting that proposition.
The source contains no hidden proof or axiom of the missing conjunct.

Selected reviewed hashes:

* `VectorPotentials.lean`: `d7c1a926415911e523a70a29c0957bc63dc271b981f86c04dcbcb11ee37f4c84`.
* `PotentialRegularity.lean`: `7670f6c309da576976eb65205078fed0dd0fec9c70ff3f1c5cb37c1cde3d52d7`.
* `TorusProof.lean`: `0131a917bca7234f878412237feac7e577d328805ff7e74ff28ada11bd936880`.
* `DivergenceTheorem.lean`: `e5b4644a2239a6ddead2d3220e5ae763ce58f9ab62d390c26245c389e5efa15d`.

The complete reconciliation manifest records all file hashes. This lexical
inspection is not a transitive axiom audit; the root-owned audit must still
verify the compiled declarations against the three allowed axioms.
