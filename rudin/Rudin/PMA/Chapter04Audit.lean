import Rudin.PMA.Chapter04
import Rudin.PMA.Chapter04Probes
import Rudin.PMA.Chapter01Audit

run_cmd Rudin.PMA.Audit.checkModuleAxioms `Rudin.PMA.Chapter04 #[
    `Rudin.PMA.Chapter04.FunctionLimitOn]
run_cmd Rudin.PMA.Audit.checkModuleAxioms `Rudin.PMA.Chapter04Probes #[
    `Rudin.PMA.Chapter04.FidelityProbes.singleton_continuous_but_no_limit]

run_cmd Rudin.PMA.Audit.checkModuleAxioms `Rudin.PMA.Chapter04Audit (allowEmpty := true)
