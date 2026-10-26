import Rudin.PMA.Chapter01
import Rudin.PMA.Chapter01Probes
import Rudin.PMA.AxiomAudit

/-!
This module checks every declaration owned by the chapter and probe modules,
including declarations generated outside their namespaces. Importing it makes
the axiom check part of `lake build`.
-/

-- Regression coverage: Lean generates this equation outside the chapter namespace.
run_cmd Rudin.PMA.Audit.checkModuleAxioms `Rudin.PMA.Chapter01 #[
    `PiLp.equivOfUnique.eq_1,
    `Rudin.PMA.Chapter01.rationalBelowSqrtTwo]
run_cmd Rudin.PMA.Audit.checkModuleAxioms `Rudin.PMA.Chapter01Probes #[
    `Rudin.PMA.Chapter01Probes.rational_gap_nonvacuous]

run_cmd Rudin.PMA.Audit.checkModuleAxioms `Rudin.PMA.AxiomAudit #[
    `Rudin.PMA.Audit.checkModuleAxioms,
    `Rudin.PMA.Audit.declarationModule]

run_cmd Rudin.PMA.Audit.checkModuleAxioms `Rudin.PMA.Chapter01Audit (allowEmpty := true)
