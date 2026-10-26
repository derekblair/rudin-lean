import Rudin.PMA.Chapter10
import Rudin.PMA.Chapter10.SimplexOrientation
import Rudin.PMA.Chapter10.ChainMaps
import Rudin.PMA.Chapter10.BoundaryDefinitions
import Rudin.PMA.Chapter10.SphereBoundary
import Rudin.PMA.Chapter10.ClosedFormConsequences
import Rudin.PMA.Chapter10.PuncturedPlane
import Rudin.PMA.Chapter10.PuncturedSphere
import Rudin.PMA.Chapter10.ConvexPrimitives
import Rudin.PMA.Chapter10.Poincare
import Rudin.PMA.Chapter10.DiffeomorphicExactness
import Rudin.PMA.Chapter10.CellTriangulation
import Rudin.PMA.Chapter10.VectorFields
import Rudin.PMA.Chapter10.VectorPotentials
import Rudin.PMA.Chapter10.VolumeElements
import Rudin.PMA.Chapter10.PlanarGreen
import Rudin.PMA.Chapter10.AreaElements
import Rudin.PMA.Chapter10.TorusProof
import Rudin.PMA.Chapter10.Circulation
import Rudin.PMA.Chapter10.Flux
import Rudin.PMA.Chapter10.ClassicalStokes
import Rudin.PMA.Chapter10.DivergenceTheorem

/-!
# PMA Chapter 10, second half: 10.27–10.51

Forms and vector fields are ambient functions, with all regularity and
equality hypotheses restricted to the stated domains. Native parameter
integration is retained and related to measure integration by proved bridges.

The first-half module supplies nodes 10.1–10.26. The implementation imported
here is recovered without mathematical changes from commit
`bb50a2079f8e189d8e282e2521bbadb64f4f98eb`; the lane reconciliation manifest
records exact file hashes.

Nodes 10.27–10.42 and 10.44–10.51 have principal theorems in their respective
modules. Node 10.43 retains its exact printed contract and separately proved
partial results in `VectorPotentials.lean`. Its C² vector-potential converse
remains unproved and is not counted as a completed node.
-/

/-! ### PMA-10.27
Principal proof: `Rudin.PMA.Chapter10.pma10_27`.
Representation: positive-dimensional vertex permutations and signed zero-simplexes use the first-half orientation interfaces; zero-dimensional parameter integration is also supported.
-/

/-! ### PMA-10.28
Principal proof: `Rudin.PMA.Chapter10.pma10_28`.
Representation: chains are finitely supported integer combinations. Equality of their integration functionals is kept separate from equality of formal chains.
-/

/-! ### PMA-10.29
Principal proof: `Rudin.PMA.Chapter10.pma10_29`.
-/

/-! ### PMA-10.30
Principal proof: `Rudin.PMA.Chapter10.pma10_30`.
Representation: a differentiable simplex stores its actual parameter map and neighborhood C² regularity; its affine-simplex pushforward representation is proved.
-/

/-! ### PMA-10.31
Principal proof: `Rudin.PMA.Chapter10.pma10_31`.
Proof-order note: positive-boundary independence uses proved Stokes and approximation to cover continuous test forms. This does not add a smoothness assumption to the source claim.
-/

/-! ### PMA-10.32
Principal proof: `Rudin.PMA.Chapter10.pma10_32`.
-/

/-! ### PMA-10.33
Principal proof: `Rudin.PMA.Chapter10.pma10_33`.
-/

/-! ### PMA-10.34
Principal proof: `Rudin.PMA.Chapter10.pma10_34`.
Convention outside the positive-degree source definition: `IsExactOn E 0 ω` is false. The source assertion concerns positive-degree forms and does not require a C² primitive.
-/

/-! ### PMA-10.35
Principal proof: `Rudin.PMA.Chapter10.pma10_35`.
-/

/-! ### PMA-10.36
Principal proof: `Rudin.PMA.Chapter10.pma10_36`.
Representation: the original circle is retained and related to a normalized simplex chain by equality for every continuous test form.
-/

/-! ### PMA-10.37
Principal proof: `Rudin.PMA.Chapter10.pma10_37`.
Representation: the original spherical rectangle is retained and related to a simplex chain by equality for every continuous test form; the norm-cubed denominator is proved equal to the printed real-power expression.
-/

/-! ### PMA-10.38
Principal proof: `Rudin.PMA.Chapter10.pma10_38`.
-/

/-! ### PMA-10.39
Principal proof: `Rudin.PMA.Chapter10.pma10_39`.
Proof-method note: radial homotopy replaces coordinate induction; the conclusion still gives a C¹ primitive from a closed C¹ form.
-/

/-! ### PMA-10.40
Principal proof: `Rudin.PMA.Chapter10.pma10_40`.
Scope extension: the contract permits different ambient dimensions and every positive degree. Equal ambient dimensions and the printed degree range are included as specializations.
-/

/-! ### PMA-10.41
Principal proof: `Rudin.PMA.Chapter10.pma10_41`.
Scope extension: the cell triangulation also handles dimension zero and collapsed sides.
-/

/-! ### PMA-10.42
Principal proof: `Rudin.PMA.Chapter10.pma10_42`.
Scope extension: uniqueness of both vector/form correspondences and regularity preservation are proved in addition to the printed correspondences.
-/

/-! PMA-10.43 remains incomplete. `pma10_43_forward` and
`pma10_43_scalar_converse` retain the printed conclusions. The separately
named `vectorPotential_c1_of_equivalent_convex` has weaker C¹ output and
is not a proof of the required C² vector converse. The exact contract in
`VectorPotentials.lean` is unchanged. -/

/-! ### PMA-10.44
Principal proof: `Rudin.PMA.Chapter10.pma10_44`.
Scope extension: the definitions include dimension zero and do not require an open ambient set when unused. The image-volume theorem retains injectivity and positivity of the Jacobian.
-/

/-! ### PMA-10.45
Principal proof: `Rudin.PMA.Chapter10.pma10_45`.
Region convention: `PositiveRegion` is the admissible finite union from 10.31, with its induced oriented chain boundary; it does not mean every closed set.
-/

/-! ### PMA-10.46
Principal proof: `Rudin.PMA.Chapter10.pma10_46`.
Scope extension: degenerate rectangles and all derivative ranks are included. Area means the printed parametrized integral, not an unproved identification with Hausdorff measure.
-/

/-! ### PMA-10.47
Principal proof: `Rudin.PMA.Chapter10.pma10_47`.
Representation: outwardness means leaving the explicit solid torus for sufficiently small positive normal displacements. The explicit solid-set description and ordinary image-volume identity add conclusions.
-/

/-! ### PMA-10.48
Principal proof: `Rudin.PMA.Chapter10.pma10_48`.
Scope extension: all admitted curve parameter intervals are allowed, continuity is needed only on the curve image, and any unit fallback at zero velocity is permitted.
-/

/-! ### PMA-10.49
Principal proof: `Rudin.PMA.Chapter10.pma10_49`.
Scope extension: continuity is needed only on the surface image, and any unit fallback at zero normal is permitted. Normals are indexed by parameter points.
-/

/-! ### PMA-10.50
Principal proof: `Rudin.PMA.Chapter10.pma10_50`.
Representation: both cell and simplex surfaces use their actual induced chain boundaries. No immersion or injectivity hypothesis is added.
-/

/-! ### PMA-10.51
Principal proof: `Rudin.PMA.Chapter10.pma10_51`.
Region convention: the admissible `PositiveRegion` and its induced outward boundary are the construction of 10.31; the theorem also proves independence of the chosen admissible decomposition.
-/
