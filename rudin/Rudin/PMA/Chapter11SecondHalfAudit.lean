import Rudin.PMA.Chapter11SecondHalf
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/-! Recursive axiom audit for every declaration introduced by the second half,
including private helpers and generated definitions. This deliberately checks
actual declarations rather than inferring completion from theorem names. -/

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let names ← env.constants.foldM (init := #[]) fun names rawName _ => do
    let userName := privateToUserName rawName.eraseMacroScopes
    return if (`Rudin.PMA.Chapter11.SecondHalf).isPrefixOf userName then
      names.push rawName else names
  if names.isEmpty then
    throwError "No Chapter 11 second-half declarations found."
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut used : Array Name := #[]
  for name in names do
    let axioms ← collectAxioms name
    for ax in axioms do
      unless used.contains ax do used := used.push ax
    let forbidden := axioms.filter fun ax => !allowed.contains ax
    unless forbidden.isEmpty do
      throwError "Forbidden axioms in {name}: {forbidden}."
  logInfo m!"Chapter 11 second-half axiom audit: {names.size} declarations; axioms used: {used}."
