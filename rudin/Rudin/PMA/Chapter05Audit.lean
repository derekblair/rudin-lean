import Rudin.PMA.Chapter05
import Rudin.PMA.Chapter05Probes
import Rudin.PMA.Chapter01Audit

/-! Recursive axiom audit, including private and generated chapter declarations. -/
run_cmd Rudin.PMA.Audit.checkModuleAxioms `Rudin.PMA.Chapter05 #[
    `Rudin.PMA.Chapter05.DifferenceQuotient]
run_cmd Rudin.PMA.Audit.checkModuleAxioms `Rudin.PMA.Chapter05Probes #[
    `Rudin.PMA.Chapter05.FidelityProbes.open_endpoints_excluded]

run_cmd Rudin.PMA.Audit.checkModuleAxioms `Rudin.PMA.Chapter05Audit (allowEmpty := true)
