import Rudin.PMA.Chapter05
import Rudin.PMA.Chapter05Probes
import Rudin.PMA.Chapter01Audit

/-! Recursive axiom audit, including private and generated chapter declarations. -/
run_cmd Rudin.PMA.Audit.checkNamespaceAxioms `Rudin.PMA.Chapter05
run_cmd Rudin.PMA.Audit.checkNamespaceAxioms `Rudin.PMA.Chapter05.FidelityProbes
