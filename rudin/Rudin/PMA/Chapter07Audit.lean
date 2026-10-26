import Rudin.PMA.Chapter07
import Rudin.PMA.Chapter07Probes
import Rudin.PMA.Chapter01Audit

set_option autoImplicit false
open Rudin.PMA.Chapter07

/-! Durable accepted-contract type comparisons; these are not boundary probes. -/
namespace Rudin.PMA.Chapter07.ContractComparators
example : pma7_1_contract := pma7_1
example : pma7_2_contract := pma7_2
example : pma7_3_contract := pma7_3
example : pma7_4_contract := pma7_4
example : pma7_5_contract := pma7_5
example : pma7_6_contract := pma7_6
example : pma7_7_contract := pma7_7
example : pma7_8_contract := pma7_8
example : pma7_9_contract := pma7_9
example : pma7_10_contract := pma7_10
example : pma7_11_contract := pma7_11
example : pma7_12_contract := pma7_12
example : pma7_13_contract := pma7_13
example : pma7_14_contract := pma7_14
example : pma7_15_contract := pma7_15
example : pma7_16_contract := pma7_16
example : pma7_17_contract := pma7_17
example : pma7_18_contract := pma7_18
example : pma7_19_contract := pma7_19
example : PMA7_20_Contract := pma7_20
example : pma7_21_contract := pma7_21
example : pma7_22_contract := pma7_22
example : pma7_23_contract := pma7_23
example : pma7_24_contract := pma7_24
example : pma7_25_contract := pma7_25
example : pma7_26_contract := pma7_26
example : pma7_27_contract := pma7_27
example : pma7_28_contract := pma7_28
example : pma7_29_contract := pma7_29
example : pma7_30_contract := pma7_30
example : pma7_31_contract := pma7_31
example : pma7_32_contract := pma7_32
example : pma7_33_contract := pma7_33
end Rudin.PMA.Chapter07.ContractComparators

/-! Kernel proof-declaration coverage and recursive transitive axiom checks. -/
run_cmd do
  let env ← Lean.getEnv
  for i in List.range 33 do
    let n := Lean.Name.str `Rudin.PMA.Chapter07 ("pma7_" ++ toString (i + 1))
    match env.find? n with
    | some (.thmInfo _) => pure ()
    | _ => throwError "Missing completed Chapter 7 proof: {n}"
  Lean.logInfo "PMA Chapter 7 coverage: 33 principal theorems and 33 accepted-contract type comparisons."

-- Require an anchor from each declaration-bearing chapter module.
run_cmd Rudin.PMA.Audit.checkModuleAxioms `Rudin.PMA.Chapter07 #[
    `Rudin.PMA.Chapter07.IsFunctionAlgebra,
    `Rudin.PMA.Chapter07.PointwiseConvergesOn,
    `Rudin.PMA.Chapter07.pma7_16_contract,
    `Rudin.PMA.Chapter07.pma7_11_contract,
    `Rudin.PMA.Chapter07.PointwiseBoundedOn,
    `Rudin.PMA.Chapter07.doubleRatio,
    `Rudin.PMA.Chapter07.pma7_1_contract,
    `Rudin.PMA.Chapter07.pma7_10_contract,
    `Rudin.PMA.Chapter07.sineSequence,
    `Rudin.PMA.Chapter07.pma7_18_contract,
    `Rudin.PMA.Chapter07.factorialCosinePower]
run_cmd Rudin.PMA.Audit.checkModuleAxioms `Rudin.PMA.Chapter07Probes #[
    `Rudin.PMA.Chapter07.FidelityProbes.Nowhere.all_real_points]

run_cmd Rudin.PMA.Audit.checkModuleAxioms `Rudin.PMA.Chapter07Audit (allowEmpty := true)
