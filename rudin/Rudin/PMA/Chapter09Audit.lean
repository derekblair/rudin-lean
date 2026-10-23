import Rudin.PMA.Chapter09
import Rudin.PMA.Chapter09.LinearProbes
import Rudin.PMA.Chapter01Audit

set_option autoImplicit false
open Rudin.PMA.Chapter09
namespace Rudin.PMA.Chapter09.ContractComparators
example : pma9_1_contract := pma9_1
example : pma9_2_contract := pma9_2
example : pma9_3_contract := pma9_3
example : pma9_4_contract := pma9_4
example : pma9_5_contract := pma9_5
example : pma9_6_contract := pma9_6
example : pma9_7_contract := pma9_7
example : pma9_8_contract := pma9_8
example : pma9_9_contract := pma9_9
end Rudin.PMA.Chapter09.ContractComparators

run_cmd do
  let env ← Lean.getEnv
  for i in List.range 9 do
    let n := Lean.Name.str `Rudin.PMA.Chapter09 ("pma9_" ++ toString (i + 1))
    match env.find? n with
    | some (.thmInfo _) => pure ()
    | _ => throwError "Missing completed Chapter 9 proof: {n}"
  Lean.logInfo "PMA Chapter 9 coverage: 9 principal theorems and 9 contract type comparisons."

run_cmd Rudin.PMA.Audit.checkNamespaceAxioms `Rudin.PMA.Chapter09
run_cmd Rudin.PMA.Audit.checkNamespaceAxioms `Rudin.PMA.Chapter09.FidelityProbes
