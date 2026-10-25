import Rudin.PMA.Chapter08.PowerSeriesCompatibility
import Rudin.PMA.Chapter08.Abel
import Rudin.PMA.Chapter08.DoubleSeries
import Rudin.PMA.Chapter08.Taylor
import Rudin.PMA.Chapter08.Operations
import Rudin.PMA.Chapter08.Exponential
import Rudin.PMA.Chapter08.Trigonometric
import Rudin.PMA.Chapter08.AlgebraicCompleteness
import Rudin.PMA.Chapter08.Orthogonality
import Rudin.PMA.Chapter08.IntegralAlgebra
import Rudin.PMA.Chapter08.GammaConsequences
import Rudin.PMA.Chapter08.GammaStirling
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
example : pma8_11_contract := pma8_11
example : pma8_12_contract := pma8_12
example : pma8_15_contract := pma8_15
example : pma8_17_contract := pma8_17
example : pma8_18_contract := pma8_18
example : pma8_19_contract := pma8_19
example : pma8_20_contract := pma8_20
example : pma8_21_contract := pma8_21
example : pma8_22_contract := pma8_22
end Rudin.PMA.Chapter08.ContractComparators

run_cmd do
  let env ← Lean.getEnv
  for i in [1, 2, 3, 4, 5, 6, 7, 8, 11, 12, 15, 17, 18, 19, 20, 21, 22] do
    let n := Lean.Name.str `Rudin.PMA.Chapter08 ("pma8_" ++ toString i)
    match env.find? n with
    | some (.thmInfo _) => pure ()
    | _ => throwError "Missing completed Chapter 8 proof: {n}"
  Lean.logInfo "PMA Chapter 8 coverage: 17 principal theorems and 17 contract type comparisons."

run_cmd Rudin.PMA.Audit.checkNamespaceAxioms `Rudin.PMA.Chapter08
run_cmd Rudin.PMA.Audit.checkNamespaceAxioms `Rudin.PMA.Chapter08.FidelityProbes
