import Rudin.PMA.Chapter09
import Rudin.PMA.Chapter09.LinearProbes
import Rudin.PMA.Chapter09.DifferentiationProbes
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
example : pma9_10_contract := pma9_10
example : pma9_11_contract := pma9_11
example : pma9_12_contract := pma9_12
example : pma9_13_contract := pma9_13
example : pma9_14_contract := pma9_14
example : pma9_15_contract := pma9_15
example : pma9_16_contract := pma9_16
example : pma9_17_contract := pma9_17
example : pma9_18_contract := pma9_18
example : pma9_19_contract := pma9_19
example : pma9_20_contract := pma9_20
example : pma9_21_contract := pma9_21
end Rudin.PMA.Chapter09.ContractComparators

run_cmd do
  let env ← Lean.getEnv
  for i in List.range 21 do
    let n := Lean.Name.str `Rudin.PMA.Chapter09 ("pma9_" ++ toString (i + 1))
    match env.find? n with
    | some (.thmInfo _) => pure ()
    | _ => throwError "Missing completed Chapter 9 proof: {n}"
  Lean.logInfo "PMA Chapter 9 coverage: 21 principal theorems and 21 contract type comparisons."

run_cmd Rudin.PMA.Audit.checkNamespaceAxioms `Rudin.PMA.Chapter09
run_cmd Rudin.PMA.Audit.checkNamespaceAxioms `Rudin.PMA.Chapter09.FidelityProbes
