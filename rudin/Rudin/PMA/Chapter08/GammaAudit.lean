import Rudin.PMA.Chapter08.GammaConsequences
import Rudin.PMA.Chapter08.GammaStirling
import Rudin.PMA.Chapter01Audit

open Rudin.PMA.Chapter08

example : pma8_17_contract := pma8_17
example : pma8_18_contract := pma8_18
example : pma8_19_contract := pma8_19
example : pma8_20_contract := pma8_20
example : pma8_21_contract := pma8_21
example : pma8_22_contract := pma8_22

run_cmd Rudin.PMA.Audit.checkNamespaceAxioms `Rudin.PMA.Chapter08
