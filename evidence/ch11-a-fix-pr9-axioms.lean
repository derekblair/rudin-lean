import Rudin.PMA.Chapter11
import Lean.Util.CollectAxioms
import Lean.Elab.Command

open Lean Elab Command

-- Fresh transitive audit, independent of the Chapter11Audit target.
run_cmd do
  let env ← getEnv
  let mut declarations : Nat := 0
  let mut theorems : Nat := 0
  let mut privateDeclarations : Nat := 0
  let mut used : Array Name := #[]
  let names ← env.constants.foldM (init := #[]) fun names name _ =>
    pure (names.push name)
  for name in names do
    let visibleName := privateToUserName name.eraseMacroScopes
    if (`Rudin.PMA.Chapter11).isPrefixOf visibleName then
      declarations := declarations + 1
      if name != visibleName then
        privateDeclarations := privateDeclarations + 1
      if (env.find? name) matches some (.thmInfo _) then
        theorems := theorems + 1
      let axioms ← collectAxioms name
      for ax in axioms do
        unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
          throwError "Forbidden transitive axiom {ax} in {name}"
        unless used.contains ax do
          used := used.push ax
      logInfo m!"{name}: {axioms}"
  if declarations == 0 then
    throwError "Empty audit"
  logInfo m!"Independent transitive audit PASS: {declarations} chapter declarations, {theorems} theorems, {privateDeclarations} private/generated-name declarations. Axioms encountered: {used}."
