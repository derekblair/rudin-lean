import Rudin.PMA.Chapter01
import Rudin.PMA.Chapter01Probes
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/-!
This module checks every declaration in the chapter namespace, including private
helpers, generated instances, constructors, and recursion equations. Importing
it makes the axiom check part of `lake build`.
-/

open Lean Elab Command

namespace Rudin.PMA.Audit

/-- Inspect the transitive axiom dependencies of all declarations in a namespace. -/
def checkNamespaceAxioms (namespacePrefix : Name) : CommandElabM Unit := do
  let env ← getEnv
  let names ← env.constants.foldM (init := #[]) fun names rawName _ => do
    let userName := privateToUserName rawName.eraseMacroScopes
    return if namespacePrefix.isPrefixOf userName then names.push rawName else names
  if names.isEmpty then
    throwError "Axiom audit found no declarations under {namespacePrefix}."
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in names do
    let axioms ← collectAxioms name
    let forbidden := axioms.filter fun ax => !allowed.contains ax
    if !forbidden.isEmpty then
      throwError "Forbidden axioms in {name}: {forbidden}. Only propext, Classical.choice, and Quot.sound are permitted."
  logInfo m!"Axiom audit for {namespacePrefix}: checked {names.size} declarations; only propext, Classical.choice, and Quot.sound."

end Rudin.PMA.Audit

run_cmd Rudin.PMA.Audit.checkNamespaceAxioms `Rudin.PMA.Chapter01
run_cmd Rudin.PMA.Audit.checkNamespaceAxioms `Rudin.PMA.Chapter01Probes
