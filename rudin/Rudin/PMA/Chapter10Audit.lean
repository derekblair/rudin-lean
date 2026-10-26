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
import Rudin.PMA.AxiomAudit

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
example : pma10_26_relativeOrientation_contract := pma10_26_relativeOrientation
end Rudin.PMA.Chapter10.ContractComparators

run_cmd do
  let env ← Lean.getEnv
  for i in List.range 26 do
    let n := Lean.Name.str `Rudin.PMA.Chapter10 ("pma10_" ++ toString (i + 1))
    match env.find? n with
    | some (.thmInfo _) => pure ()
    | _ => throwError "Missing Chapter 10 first-half proof: {n}"
  for i in List.range 25 do
    let n := Lean.Name.str `Rudin.PMA.Chapter10 ("pma10_" ++ toString (i + 27))
    if (env.find? n).isSome then
      throwError "Second-half principal unexpectedly imported by first-half lane: {n}"
  for n in [`Rudin.PMA.Chapter10.pma10_8_complex_corollary,
    `Rudin.PMA.Chapter10.pma10_12_geometry,
    `Rudin.PMA.Chapter10.pma10_19_xdy_derivative,
    `Rudin.PMA.Chapter10.pma10_19_dxdy_not_formEqOn_zero,
    `Rudin.PMA.Chapter10.pma10_26_relativeOrientation] do
    match env.find? n with
    | some (.thmInfo _) => pure ()
    | _ => throwError "Missing supplementary first-half proof: {n}"
  Lean.logInfo "PMA Chapter 10 first-half coverage: 26 principal theorems and 26 contract type comparisons."
  Lean.logInfo "Supplementary coverage: 5 theorem declarations and 1 additional contract comparison; no second-half principal imported."

-- Audit by source-module ownership, including private and generated declarations.
run_cmd Rudin.PMA.Audit.checkModuleAxioms `Rudin.PMA.Chapter10
