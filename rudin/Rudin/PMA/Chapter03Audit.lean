import Rudin.PMA.Chapter03
import Rudin.PMA.Chapter03Probes
import Rudin.PMA.Chapter01Audit

run_cmd Rudin.PMA.Audit.checkModuleAxioms `Rudin.PMA.Chapter03 #[
    `Rudin.PMA.Chapter03.ConvergesTo]
run_cmd Rudin.PMA.Audit.checkModuleAxioms `Rudin.PMA.Chapter03Probes #[
    `Rudin.PMA.Chapter03.FidelityProbes.probe_empty_diameter]

run_cmd Rudin.PMA.Audit.checkModuleAxioms `Rudin.PMA.Chapter03Audit (allowEmpty := true)
