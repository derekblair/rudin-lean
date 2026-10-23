import Rudin.PMA.Chapter10
import Rudin.PMA.Chapter10.IntegrationProbes
import Rudin.PMA.Chapter10.SimplexProbes
import Rudin.PMA.Chapter10.PrimitiveProbes
import Rudin.PMA.Chapter10.PartitionProbes
import Rudin.PMA.Chapter10.ChangeOfVariablesProbes
import Rudin.PMA.Chapter10.FormProbes
import Rudin.PMA.Chapter10.FormAlgebraProbes
import Rudin.PMA.Chapter10.SphereExampleProbes
import Rudin.PMA.Chapter10.ExteriorDerivativeProbes
import Rudin.PMA.Chapter10.PullbackProbes
import Rudin.PMA.Chapter10.SimplexChainProbes
import Rudin.PMA.Chapter10.BoundaryExamplesProbes
import Rudin.PMA.Chapter10.PositiveBoundaryProbes
import Rudin.PMA.Chapter10.StokesProbes
import Rudin.PMA.Chapter10.ClosedFormProbes
import Rudin.PMA.Chapter10.PuncturedProbes
import Rudin.PMA.Chapter10.ConvexPrimitiveProbes
import Rudin.PMA.Chapter10.ConvexExactnessProbes
import Rudin.PMA.Chapter10.CellTriangulationProbes
import Rudin.PMA.Chapter10.VectorFieldProbes
import Rudin.PMA.Chapter10.ScalarPotentialProbes
import Rudin.PMA.Chapter10.VolumeAreaProbes
import Rudin.PMA.Chapter10.TorusProbes
import Rudin.PMA.Chapter10.VectorIntegrationProbes
import Rudin.PMA.Chapter10.ClassicalCalculusProbes
import Rudin.PMA.Chapter01Audit

set_option autoImplicit false
open Rudin.PMA.Chapter10
namespace Rudin.PMA.Chapter10.ContractComparators
example : pma10_1_contract := pma10_1
example : pma10_2_contract := pma10_2
example : pma10_3_contract := pma10_3
example : pma10_4_contract := pma10_4
example : pma10_5_contract := pma10_5
example : pma10_6_contract := pma10_6
example : pma10_7_contract := pma10_7
example : pma10_8_contract := pma10_8
example : pma10_9_contract := pma10_9
example : pma10_10_contract := pma10_10
example : pma10_11_contract := pma10_11
example : pma10_12_contract := pma10_12
example : pma10_13_contract := pma10_13
example : pma10_14_contract := pma10_14
example : pma10_15_contract := pma10_15
example : pma10_16_contract := pma10_16
example : pma10_17_contract := pma10_17
example : pma10_18_contract := pma10_18
example : pma10_19_contract := pma10_19
example : pma10_20_contract := pma10_20
example : pma10_21_contract := pma10_21
example : pma10_22_contract := pma10_22
example : pma10_23_contract := pma10_23
example : pma10_24_contract := pma10_24
example : pma10_25_contract := pma10_25
example : pma10_26_contract := pma10_26
example : pma10_27_contract := pma10_27
example : pma10_28_contract := pma10_28
example : pma10_29_contract := pma10_29
example : pma10_30_contract := pma10_30
example : pma10_31_contract := pma10_31
example : pma10_32_contract := pma10_32
example : pma10_33_contract := pma10_33
example : pma10_34_contract := pma10_34
example : pma10_35_contract := pma10_35
example : pma10_36_contract := pma10_36
example : pma10_37_contract := pma10_37
example : pma10_38_contract := pma10_38
example : pma10_39_contract := pma10_39
example : pma10_40_contract := pma10_40
example : pma10_41_contract := pma10_41
example : pma10_42_contract := pma10_42
example : pma10_44_contract := pma10_44
example : pma10_45_contract := pma10_45
example : pma10_46_contract := pma10_46
example : pma10_47_contract := pma10_47
example : pma10_48_contract := pma10_48
example : pma10_49_contract := pma10_49
example : pma10_50_contract := pma10_50
example : pma10_51_contract := pma10_51
end Rudin.PMA.Chapter10.ContractComparators

run_cmd do
  let env ← Lean.getEnv
  for i in [1, 2, 3, 4, 5, 6, 7, 8, 9, 10,
    11, 12, 13, 14, 15, 16, 17, 18, 19, 20,
    21, 22, 23, 24, 25, 26, 27, 28, 29, 30,
    31, 32, 33, 34, 35, 36, 37, 38, 39, 40,
    41, 42, 44, 45, 46, 47, 48, 49, 50, 51] do
    let n := Lean.Name.str `Rudin.PMA.Chapter10 ("pma10_" ++ toString i)
    match env.find? n with
    | some (.thmInfo _) => pure ()
    | _ => throwError "Missing completed Chapter 10 proof: {n}"
  if (env.find? `Rudin.PMA.Chapter10.pma10_43).isSome then
    throwError "Queued PMA-10.43 must not have a principal theorem"
  Lean.logInfo "PMA Chapter 10 coverage: 50 principal theorems and 50 contract type comparisons."

run_cmd Rudin.PMA.Audit.checkNamespaceAxioms `Rudin.PMA.Chapter10
run_cmd Rudin.PMA.Audit.checkNamespaceAxioms `Rudin.PMA.Chapter10.FidelityProbes
