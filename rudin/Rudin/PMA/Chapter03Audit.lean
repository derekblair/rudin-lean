import Rudin.PMA.Chapter03
import Rudin.PMA.Chapter03Probes
import Rudin.PMA.Chapter01Audit

run_cmd Rudin.PMA.Audit.checkModuleAxioms `Rudin.PMA.Chapter03
run_cmd Rudin.PMA.Audit.checkModuleAxioms `Rudin.PMA.Chapter03Probes

run_cmd Rudin.PMA.Audit.checkModuleAxioms `Rudin.PMA.Chapter03Audit (allowEmpty := true)
