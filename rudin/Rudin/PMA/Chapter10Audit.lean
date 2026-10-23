import Rudin.PMA.Chapter10
import Rudin.PMA.Chapter10.IntegrationProbes
import Rudin.PMA.Chapter10.SimplexProbes
import Rudin.PMA.Chapter10.PrimitiveProbes
import Rudin.PMA.Chapter10.PartitionProbes
import Rudin.PMA.Chapter10.ChangeOfVariablesProbes
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
end Rudin.PMA.Chapter10.ContractComparators

run_cmd do
  let env ← Lean.getEnv
  for i in List.range 9 do
    let n := Lean.Name.str `Rudin.PMA.Chapter10 ("pma10_" ++ toString (i + 1))
    match env.find? n with
    | some (.thmInfo _) => pure ()
    | _ => throwError "Missing completed Chapter 10 proof: {n}"
  Lean.logInfo "PMA Chapter 10 coverage: 9 principal theorems and 9 contract type comparisons."

run_cmd Rudin.PMA.Audit.checkNamespaceAxioms `Rudin.PMA.Chapter10
run_cmd Rudin.PMA.Audit.checkNamespaceAxioms `Rudin.PMA.Chapter10.FidelityProbes
