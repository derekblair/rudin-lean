import Rudin.PMA.Chapter02
import Rudin.PMA.Chapter02Probes
import Rudin.PMA.Chapter01Audit

run_cmd Rudin.PMA.Audit.checkModuleAxioms `Rudin.PMA.Chapter02
run_cmd Rudin.PMA.Audit.checkModuleAxioms `Rudin.PMA.Chapter02Probes

run_cmd Rudin.PMA.Audit.checkModuleAxioms `Rudin.PMA.Chapter02Audit (allowEmpty := true)
