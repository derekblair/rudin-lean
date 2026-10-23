import Rudin.PMA.Chapter09
import Rudin.PMA.Chapter09.LinearProbes
import Rudin.PMA.Chapter09.DifferentiationProbes
import Rudin.PMA.Chapter09.FixedPointProbes
import Rudin.PMA.Chapter09.InverseProbes
import Rudin.PMA.Chapter09.ImplicitProbes
import Rudin.PMA.Chapter09.AlgebraProbes
import Rudin.PMA.Chapter09.RankObliqueProbes
import Rudin.PMA.Chapter09.DeterminantProbes
import Rudin.PMA.Chapter09.HigherDerivativeProbes
import Rudin.PMA.Chapter09.ParameterIntegralProbes
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
example : pma9_22_contract := pma9_22
example : pma9_23_contract := pma9_23
example : pma9_24_contract := pma9_24
example : pma9_25_contract := pma9_25
example : pma9_26_contract := pma9_26
example : pma9_27_contract := pma9_27
example : pma9_28_contract := pma9_28
example : pma9_29_contract := pma9_29
example : pma9_30_contract := pma9_30
example : pma9_31_contract := pma9_31
example : pma9_32_contract := pma9_32
example : pma9_33_contract := pma9_33
example : pma9_34_contract := pma9_34
example : pma9_35_contract := pma9_35
example : pma9_36_contract := pma9_36
example : pma9_37_contract := pma9_37
example : pma9_38_contract := pma9_38
example : pma9_39_contract := pma9_39
example : pma9_40_contract := pma9_40
example : pma9_41_contract := pma9_41
example : pma9_42_contract := pma9_42
example : pma9_43_contract := pma9_43
end Rudin.PMA.Chapter09.ContractComparators

run_cmd do
  let env ← Lean.getEnv
  for i in List.range 43 do
    let n := Lean.Name.str `Rudin.PMA.Chapter09 ("pma9_" ++ toString (i + 1))
    match env.find? n with
    | some (.thmInfo _) => pure ()
    | _ => throwError "Missing completed Chapter 9 proof: {n}"
  Lean.logInfo "PMA Chapter 9 coverage: 43 principal theorems and 43 contract type comparisons."

run_cmd Rudin.PMA.Audit.checkNamespaceAxioms `Rudin.PMA.Chapter09
run_cmd Rudin.PMA.Audit.checkNamespaceAxioms `Rudin.PMA.Chapter09.FidelityProbes
