import Rudin.PMA.Chapter02
import Rudin.PMA.Chapter02Probes
import Rudin.PMA.Chapter01Audit

run_cmd Rudin.PMA.Audit.checkModuleAxioms `Rudin.PMA.Chapter02 #[
    `Rudin.PMA.Chapter02.PMAMapping]
run_cmd Rudin.PMA.Audit.checkModuleAxioms `Rudin.PMA.Chapter02Probes #[
    `Rudin.PMA.Chapter02.FidelityProbes.finite_at_most_but_not_countably_infinite]

run_cmd Rudin.PMA.Audit.checkModuleAxioms `Rudin.PMA.Chapter02Audit (allowEmpty := true)
