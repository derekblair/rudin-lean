import Rudin.PMA.Chapter11
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/-!
# Chapter 11 axiom audit

Every declaration under the chapter namespace is checked recursively, including
private helpers and generated definitions. Imported results used by these proofs
are traversed as dependencies. This is an axiom check, not a claim that every
source node is complete; source coverage is recorded separately.
-/

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let names ← env.constants.foldM (init := #[]) fun names rawName _ => do
    let userName := privateToUserName rawName.eraseMacroScopes
    return if (`Rudin.PMA.Chapter11).isPrefixOf userName then names.push rawName else names
  if names.isEmpty then
    throwError "No Chapter 11 declarations found."
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut theoremCount : Nat := 0
  for name in names do
    let axioms ← collectAxioms name
    let forbidden := axioms.filter fun ax => !allowed.contains ax
    if !forbidden.isEmpty then
      throwError "Forbidden axioms in {name}: {forbidden}"
    match env.find? name with
    | some (.thmInfo _) => theoremCount := theoremCount + 1
    | _ => pure ()
  logInfo m!"Chapter 11 axiom audit PASS: {names.size} declarations ({theoremCount} theorems); only propext, Classical.choice, Quot.sound."
