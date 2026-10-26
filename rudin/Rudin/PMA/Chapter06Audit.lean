import Rudin.PMA.Chapter06
import Rudin.PMA.Chapter06Probes
import Rudin.PMA.Chapter01Audit

/-! Verify proof declarations for every inventory node, then audit all imported
chapter declarations, including private helpers and compiler-generated code. -/
run_cmd do
  let env ← Lean.getEnv
  for i in List.range 27 do
    let n := Lean.Name.str `Rudin.PMA.Chapter06 ("pma6_" ++ toString (i + 1))
    match env.find? n with
    | some (.thmInfo _) => pure ()
    | _ => throwError "Missing completed Chapter 6 proof: {n}"
  for n in [`Rudin.PMA.Chapter06.pma6_23_complex,
      `Rudin.PMA.Chapter06.pma6_25_complex] do
    match env.find? n with
    | some (.thmInfo _) => pure ()
    | _ => throwError "Missing complex specialization: {n}"
  Lean.logInfo "PMA Chapter 6 coverage: 27 principal theorems and both explicit complex bridges."

-- Regression coverage: Lean generates this equation outside the chapter namespace.
-- Each declaration-bearing chapter module also has a required anchor.
run_cmd Rudin.PMA.Audit.checkModuleAxioms `Rudin.PMA.Chapter06 #[
    `NNReal.mk.eq_1,
    `Rudin.PMA.Chapter06.pma6_3,
    `Rudin.PMA.Chapter06.Partition,
    `Rudin.PMA.Chapter06.pma6_17_contract,
    `Rudin.PMA.Chapter06.lowerSum_le_upperSum_other,
    `Rudin.PMA.Chapter06.CurveOn,
    `Rudin.PMA.Chapter06.pma6_1_contract,
    `Rudin.PMA.Chapter06.endpoint_local_gap_lt,
    `Rudin.PMA.Chapter06.finite_exceptional_open_of_base,
    `Rudin.PMA.Chapter06.pma6_8_contract,
    `Rudin.PMA.Chapter06.UnitStep,
    `Rudin.PMA.Chapter06.quadraticMoment_density,
    `Rudin.PMA.Chapter06.monotoneOn_boundedOn,
    `Rudin.PMA.Chapter06.pma6_12,
    `Rudin.PMA.Chapter06.Partition.Refines,
    `Rudin.PMA.Chapter06.splitLeftPartition,
    `Rudin.PMA.Chapter06.VectorRSIntegrable]
run_cmd Rudin.PMA.Audit.checkModuleAxioms `Rudin.PMA.Chapter06Probes #[
    `Rudin.PMA.Chapter06.FidelityProbes.zero_mass_arbitrary_bounded]

run_cmd Rudin.PMA.Audit.checkModuleAxioms `Rudin.PMA.Chapter06Audit (allowEmpty := true)
