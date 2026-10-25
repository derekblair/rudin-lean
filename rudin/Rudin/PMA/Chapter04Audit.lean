import Rudin.PMA.Chapter04
import Rudin.PMA.Chapter04Probes
import Rudin.PMA.Chapter01Audit

run_cmd Rudin.PMA.Audit.checkModuleAxioms `Rudin.PMA.Chapter04
run_cmd Rudin.PMA.Audit.checkModuleAxioms `Rudin.PMA.Chapter04Probes

run_cmd Rudin.PMA.Audit.checkModuleAxioms `Rudin.PMA.Chapter04Audit (allowEmpty := true)
