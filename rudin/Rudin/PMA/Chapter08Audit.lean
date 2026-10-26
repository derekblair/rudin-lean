import Rudin.PMA.Chapter08
import Rudin.PMA.Chapter08Probes
import Rudin.PMA.Chapter08.ExponentialProbes
import Rudin.PMA.Chapter08.GammaAudit
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
example : pma8_9_contract := pma8_9
example : pma8_10_contract := pma8_10
example : pma8_11_contract := pma8_11
example : pma8_12_contract := pma8_12
example : pma8_13_contract := pma8_13
example : pma8_14_contract := pma8_14
example : pma8_15_contract := pma8_15
example : pma8_16_contract := pma8_16
example : pma8_17_contract := pma8_17
example : pma8_18_contract := pma8_18
example : pma8_19_contract := pma8_19
example : pma8_20_contract := pma8_20
example : pma8_21_contract := pma8_21
example : pma8_22_contract := pma8_22
end Rudin.PMA.Chapter08.ContractComparators

run_cmd do
  let env ← Lean.getEnv
  for i in List.range 22 do
    let n := Lean.Name.str `Rudin.PMA.Chapter08 ("pma8_" ++ toString (i + 1))
    match env.find? n with
    | some (.thmInfo _) => pure ()
    | _ => throwError "Missing completed Chapter 8 proof: {n}"
  Lean.logInfo "PMA Chapter 8 coverage: 22 principal theorems and 22 contract type comparisons."

run_cmd Rudin.PMA.Audit.checkModuleAxioms `Rudin.PMA.Chapter08
run_cmd Rudin.PMA.Audit.checkModuleAxioms `Rudin.PMA.Chapter08Probes

run_cmd Rudin.PMA.Audit.checkModuleAxioms `Rudin.PMA.Chapter08Audit (allowEmpty := true)
