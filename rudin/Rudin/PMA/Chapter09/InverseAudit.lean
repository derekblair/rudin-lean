import Rudin.PMA.Chapter09.Inverse
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/-! The checker recursively checks every Chapter 9 declaration in this import
closure, including definitions and private/generated declarations. -/
open Lean Elab Command

namespace Rudin.PMA.Chapter09Audit
/-- Recursive axiom check over all declarations under the Chapter 9 namespace. -/
def check : CommandElabM Unit := do
  let env ← getEnv
  let names ← env.constants.foldM (init := #[]) fun names rawName _ => do
    let userName := privateToUserName rawName.eraseMacroScopes
    return if (`Rudin.PMA.Chapter09).isPrefixOf userName then names.push rawName else names
  if names.isEmpty then throwError "No Chapter 9 declarations found."
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in names do
    let axioms ← collectAxioms name
    let forbidden := axioms.filter fun ax => !allowed.contains ax
    if !forbidden.isEmpty then throwError "Forbidden axioms in {name}: {forbidden}"
  logInfo m!"Chapter 9 axiom audit: {names.size} declarations; only propext, Classical.choice, Quot.sound."
end Rudin.PMA.Chapter09Audit

run_cmd Rudin.PMA.Chapter09Audit.check

#print axioms Rudin.PMA.Chapter09.pma9_23
#print axioms Rudin.PMA.Chapter09.pma9_23_iterates
#print axioms Rudin.PMA.Chapter09.pma9_24
#print axioms Rudin.PMA.Chapter09.pma9_24_inverse_derivative
#print axioms Rudin.PMA.Chapter09.pma9_25
