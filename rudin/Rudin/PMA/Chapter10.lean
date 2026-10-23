import Rudin.PMA.Chapter10.Simplex
import Rudin.PMA.Chapter10.Primitive
import Rudin.PMA.Chapter10.Partition
import Rudin.PMA.Chapter10.ChangeOfVariables
import Rudin.PMA.Chapter10.SphereExamples
import Rudin.PMA.Chapter10.FormSeparation
import Rudin.PMA.Chapter10.WedgeProducts
import Rudin.PMA.Chapter10.ExactOneForms
import Rudin.PMA.Chapter10.ExteriorDerivativeRules
import Rudin.PMA.Chapter10.PullbackDefinitions
import Rudin.PMA.Chapter10.PullbackDifferentiation
import Rudin.PMA.Chapter10.SurfacePullbacks
import Rudin.PMA.Chapter10.SimplexOrientation
import Rudin.PMA.Chapter10.ChainMaps
import Rudin.PMA.Chapter10.BoundaryDefinitions
import Rudin.PMA.Chapter10.SphereBoundary
import Rudin.PMA.Chapter10.ClosedFormConsequences
import Rudin.PMA.Chapter10.Poincare
import Rudin.PMA.Chapter10.DiffeomorphicExactness
import Rudin.PMA.Chapter10.CellTriangulation
import Rudin.PMA.Chapter10.VectorFields

import Rudin.PMA.Chapter10.PuncturedPlane
import Rudin.PMA.Chapter10.PuncturedSphere
import Rudin.PMA.Chapter10.ConvexPrimitives

/-!
# PMA Chapter 10: Integration of Differential Forms

Book-order integration is in progress. The full source inventory has 51 nodes;
only the numbered markers below are counted as completed. Independent source
review and kernel evidence are recorded in research/pma-ch10-* and evidence/ch10-*.
-/

namespace Rudin.PMA.Chapter10

/-! ### PMA-10.1
Principal proof: `pma10_1`. Definitions: `Chapter10/Integration.lean`; proofs: `Chapter10/IntegrationMeasure.lean`.
-/

/-! ### PMA-10.2
Principal proof: `pma10_2`. Definitions: `Chapter10/Integration.lean`; proofs: `Chapter10/IntegrationMeasure.lean`.
-/

/-! ### PMA-10.3
Principal proof: `pma10_3`. Definitions: `Chapter10/Integration.lean`; proofs: `Chapter10/IntegrationMeasure.lean`.
-/

/-! ### PMA-10.4
Principal proof: `pma10_4`. Definitions: `Chapter10/Integration.lean`; proofs: `Chapter10/Simplex.lean`.
-/

/-! ### PMA-10.5
Principal proof: `pma10_5`. Definitions and proofs: `Chapter10/Primitive.lean`.
-/

/-! ### PMA-10.6
Principal proof: `pma10_6`. Definitions and proofs: `Chapter10/Primitive.lean`.
-/

/-! ### PMA-10.7
Principal proof: `pma10_7`. Definitions and proofs: `Chapter10/Primitive.lean`.
-/

/-! ### PMA-10.8
Principal proof: `pma10_8`. Definitions and proofs: `Chapter10/Partition.lean`.
-/

/-! ### PMA-10.9
Principal proof: `pma10_9`. Definitions and proofs: `Chapter10/ChangeOfVariables.lean`.
-/

/-! ### PMA-10.10
Principal proof: `pma10_10`. Definitions and proofs: `Chapter10/SurfaceDomains.lean`.
-/

/-! ### PMA-10.11
Principal proof: `pma10_11`. Definitions and proofs: `Chapter10/FormDefinitions.lean`.
-/

/-! ### PMA-10.12
Principal proof: `pma10_12`. Definitions and proofs: `Chapter10/SphereExamples.lean`.
-/

/-! ### PMA-10.13
Principal proof: `pma10_13`. Definitions and proofs: `Chapter10/FormOperations.lean`.
-/

/-! ### PMA-10.14
Principal proof: `pma10_14`. Definitions and proofs: `Chapter10/StandardForms.lean`.
-/

/-! ### PMA-10.15
Principal proof: `pma10_15`. Definitions and proofs: `Chapter10/FormSeparation.lean`.
-/

/-! ### PMA-10.16
Principal proof: `pma10_16`. Definitions and proofs: `Chapter10/WedgeProducts.lean`.
-/

/-! ### PMA-10.17
Principal proof: `pma10_17`. Definitions and proofs: `Chapter10/WedgeProducts.lean`.
-/

/-! ### PMA-10.18
Principal proof: `pma10_18`. Definitions and proofs: `Chapter10/ExteriorDerivative.lean`.
-/

/-! ### PMA-10.19
Principal proof: `pma10_19`. Definitions and proofs: `Chapter10/ExactOneForms.lean`.
-/

/-! ### PMA-10.20
Principal proof: `pma10_20`. Definitions and proofs: `Chapter10/ExteriorDerivativeRules.lean`.
-/

/-! ### PMA-10.21
Principal proof: `pma10_21`. Definitions: `Chapter10/Pullbacks.lean`; proofs: `Chapter10/PullbackDefinitions.lean`.
-/

/-! ### PMA-10.22
Principal proof: `pma10_22`. Definitions: `Chapter10/Pullbacks.lean`; proofs: `Chapter10/PullbackDifferentiation.lean`.
-/

/-! ### PMA-10.23
Principal proof: `pma10_23`. Definitions: `Chapter10/Pullbacks.lean`; proofs: `Chapter10/SurfacePullbacks.lean`.
-/

/-! ### PMA-10.24
Principal proof: `pma10_24`. Definitions: `Chapter10/Pullbacks.lean`; proofs: `Chapter10/SurfacePullbacks.lean`.
-/

/-! ### PMA-10.25
Principal proof: `pma10_25`. Definitions: `Chapter10/Pullbacks.lean`; proofs: `Chapter10/SurfacePullbacks.lean`.
-/

/-! ### PMA-10.26
Principal proof: `pma10_26`. Definitions and proofs: `Chapter10/AffineSimplices.lean`.
-/

/-! ### PMA-10.27
Principal proof: `pma10_27`. Definitions and proofs: `Chapter10/SimplexOrientation.lean`.
-/

/-! ### PMA-10.28
Principal proof: `pma10_28`. Definitions and proofs: `Chapter10/AffineChains.lean`.
-/

/-! ### PMA-10.29
Principal proof: `pma10_29`. Definitions and proofs: `Chapter10/SimplexBoundaries.lean`.
-/

/-! ### PMA-10.30
Principal proof: `pma10_30`. Definitions and proofs: `Chapter10/ChainMaps.lean`.
-/

/-! ### PMA-10.31
Principal proof: `pma10_31`. Definitions and proofs: `Chapter10/BoundaryDefinitions.lean`.
-/

/-! ### PMA-10.32
Principal proof: `pma10_32`. Definitions and proofs: `Chapter10/SphereBoundary.lean`.
-/

/-! ### PMA-10.33
Principal proof: `pma10_33`. Definitions and proofs: `Chapter10/ChainStokes.lean`.
-/

/-! ### PMA-10.34
Principal proof: `pma10_34`. Definitions and proofs: `Chapter10/ClosedExact.lean`.
-/

/-! ### PMA-10.35
Principal proof: `pma10_35`. Definitions and proofs: `Chapter10/ClosedFormConsequences.lean`.
-/

/-! ### PMA-10.36
Principal proof: `pma10_36`. Definitions and proofs: `Chapter10/PuncturedPlane.lean`.
-/

/-! ### PMA-10.37
Principal proof: `pma10_37`. Definitions and proofs: `Chapter10/PuncturedSphere.lean`.
-/

/-! ### PMA-10.38
Principal proof: `pma10_38`. Definitions and proofs: `Chapter10/ConvexPrimitives.lean`.
-/

/-! ### PMA-10.39
Principal proof: `pma10_39`. Definitions and proofs: `Chapter10/Poincare.lean`.
-/

/-! ### PMA-10.40
Principal proof: `pma10_40`. Definitions and proofs: `Chapter10/DiffeomorphicExactness.lean`.
-/

/-! ### PMA-10.41
Principal proof: `pma10_41`. Definitions and proofs: `Chapter10/CellTriangulation.lean`.
-/

/-! ### PMA-10.42
Principal proof: `pma10_42`. Definitions and proofs: `Chapter10/VectorFields.lean`.
-/

end Rudin.PMA.Chapter10
