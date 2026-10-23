import Rudin.PMA.Chapter10
import Rudin.PMA.Chapter10.IntegrationProbes
import Rudin.PMA.Chapter10.SimplexProbes
import Rudin.PMA.Chapter10.PrimitiveProbes
import Rudin.PMA.Chapter10.PartitionProbes
import Rudin.PMA.Chapter10.ChangeOfVariablesProbes
import Rudin.PMA.Chapter10.FormProbes
import Rudin.PMA.Chapter10.FormAlgebraProbes
import Rudin.PMA.Chapter10.SphereExampleProbes
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
end Rudin.PMA.Chapter10.ContractComparators

run_cmd do
  let env ← Lean.getEnv
  for i in List.range 17 do
    let n := Lean.Name.str `Rudin.PMA.Chapter10 ("pma10_" ++ toString (i + 1))
    match env.find? n with
    | some (.thmInfo _) => pure ()
    | _ => throwError "Missing completed Chapter 10 proof: {n}"
  Lean.logInfo "PMA Chapter 10 coverage: 17 principal theorems and 17 contract type comparisons."

run_cmd Rudin.PMA.Audit.checkNamespaceAxioms `Rudin.PMA.Chapter10
run_cmd Rudin.PMA.Audit.checkNamespaceAxioms `Rudin.PMA.Chapter10.FidelityProbes
