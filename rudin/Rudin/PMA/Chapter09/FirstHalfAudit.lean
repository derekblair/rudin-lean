import Rudin.PMA.Chapter09.FirstHalf
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/-! Recursive axiom audit of every first-half chapter declaration, including
private helpers, definitions and generated equations. -/
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let names ← env.constants.foldM (init := #[]) fun names rawName _ => do
    let userName := privateToUserName rawName.eraseMacroScopes
    return if (`Rudin.PMA.Chapter09).isPrefixOf userName then names.push rawName else names
  if names.isEmpty then throwError "No first-half declarations found."
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in names do
    let axioms ← collectAxioms name
    let forbidden := axioms.filter fun ax => !allowed.contains ax
    if !forbidden.isEmpty then
      throwError "Forbidden axioms in {name}: {forbidden}"
  logInfo m!"Chapter 9 first-half axiom audit: {names.size} declarations; only propext, Classical.choice, Quot.sound."
