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

-- Retain main's imported-module sweep alongside the required coverage checks.
run_cmd do
  let env ← Lean.getEnv
  let required : Array Lean.Name := #[
    `Rudin.PMA.Chapter08.continuous_native_integral_eq,
    `Rudin.PMA.Chapter08.trigonometricBetaIntegrand,
    `Rudin.PMA.Chapter08.stirlingMainLog]
  for moduleName in env.header.moduleNames do
    if (`Rudin.PMA.Chapter08).isPrefixOf moduleName then
      Rudin.PMA.Audit.checkModuleAxioms moduleName
        (required.filter fun name =>
          moduleName.isPrefixOf (Rudin.PMA.Audit.declarationModule env name))
        (allowEmpty := true)

run_cmd Rudin.PMA.Audit.checkModuleAxioms `Rudin.PMA.Chapter08.Gamma #[
    `Real.GammaSeq.eq_1,
    `Rudin.PMA.Chapter08.continuous_native_integral_eq]
run_cmd Rudin.PMA.Audit.checkModuleAxioms `Rudin.PMA.Chapter08.GammaConsequences #[
    `Rudin.PMA.Chapter08.trigonometricBetaIntegrand]
run_cmd Rudin.PMA.Audit.checkModuleAxioms `Rudin.PMA.Chapter08.GammaStirling #[
    `Rudin.PMA.Chapter08.stirlingMainLog]

run_cmd Rudin.PMA.Audit.checkModuleAxioms `Rudin.PMA.Chapter08.GammaAudit (allowEmpty := true)
