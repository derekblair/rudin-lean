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

run_cmd Rudin.PMA.Audit.checkNamespaceAxioms `Rudin.PMA.Chapter06
run_cmd Rudin.PMA.Audit.checkNamespaceAxioms `Rudin.PMA.Chapter06.FidelityProbes
