import Rudin.PMA.Chapter08
import Rudin.PMA.Chapter08Probes
import Rudin.PMA.Chapter08.ExponentialProbes
import Rudin.PMA.Chapter01Audit

set_option autoImplicit false
open Rudin.PMA.Chapter08

namespace Rudin.PMA.Chapter08.ContractComparators
example : pma8_1_contract := pma8_1
example : pma8_2_contract := pma8_2
example : pma8_3_contract := pma8_3
example : pma8_4_contract := pma8_4
example : pma8_5_contract := pma8_5
example : pma8_6_contract := pma8_6
example : pma8_7_contract := pma8_7
example : pma8_8_contract := pma8_8
end Rudin.PMA.Chapter08.ContractComparators

run_cmd do
  let env ← Lean.getEnv
  for i in List.range 8 do
    let n := Lean.Name.str `Rudin.PMA.Chapter08 ("pma8_" ++ toString (i + 1))
    match env.find? n with
    | some (.thmInfo _) => pure ()
    | _ => throwError "Missing completed Chapter 8 proof: {n}"
  Lean.logInfo "PMA Chapter 8 coverage: 8 principal theorems and 8 contract type comparisons."

run_cmd Rudin.PMA.Audit.checkNamespaceAxioms `Rudin.PMA.Chapter08
run_cmd Rudin.PMA.Audit.checkNamespaceAxioms `Rudin.PMA.Chapter08.FidelityProbes
