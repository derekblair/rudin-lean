import Lean.Util.CollectAxioms
import Lean.Elab.Command

/-!
Module-based axiom auditing. Declaration namespaces do not identify their source
modules: elaboration can emit declarations such as `PiLp.equivOfUnique.eq_1`
while compiling a chapter. Use Lean's module ownership table instead, retaining
private declarations, generated instances, constructors, and equation lemmas.
-/

open Lean Elab Command

namespace Rudin.PMA.Audit

/-- The source module of an imported or current-module declaration. -/
def declarationModule (env : Environment) (name : Name) : Name :=
  match env.getModuleIdxFor? name with
  | some idx => env.header.moduleNames[idx]!
  | none => env.mainModule

/-- Check every declaration owned by a module or any of its submodules.

The module must be present, but it may be an import-only aggregate. Each selected
module is reported separately, including modules with no declarations. An empty
selection fails unless `allowEmpty` is explicitly enabled for audit-only modules. The
transitive dependencies of every declaration may use only the three standard
axioms below; any other axiom makes elaboration (and hence `lake build`) fail.
-/
def checkModuleAxioms (modulePrefix : Name)
    (requiredDeclarations : Array Name := #[]) (allowEmpty : Bool := false) : CommandElabM Unit := do
  let env := (← getEnv).setExporting false
  if env.mainModule != modulePrefix && (env.getModuleIdx? modulePrefix).isNone then
    throwError "Axiom audit module {modulePrefix} is not imported or current."
  let modules := (env.header.moduleNames.push env.mainModule).filter fun moduleName =>
    modulePrefix.isPrefixOf moduleName
  if modules.isEmpty then
    throwError "Axiom audit found no modules under {modulePrefix}."
  let names := env.constants.fold (init := #[]) fun names name _ =>
    if modulePrefix.isPrefixOf (declarationModule env name) then names.push name else names
  let names := names.qsort Name.lt
  if names.isEmpty && !allowEmpty then
    throwError "Axiom audit found no declarations in {modulePrefix} or its submodules."
  for name in requiredDeclarations do
    if !names.contains name then
      throwError "Axiom audit coverage regression: {name} is not owned by {modulePrefix} or its submodules."
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut used : NameSet := {}
  for name in names do
    let axioms ← collectAxioms name
    let forbidden := axioms.filter fun ax => !allowed.contains ax
    if !forbidden.isEmpty then
      throwError "Forbidden axioms in {name} (module {declarationModule env name}): {forbidden}. Only propext, Classical.choice, and Quot.sound are permitted."
    used := axioms.foldl (init := used) fun acc ax => acc.insert ax
    if requiredDeclarations.contains name then
      logInfo m!"Axiom audit coverage: {name} (module {declarationModule env name}); axioms used: {axioms}."
  for moduleName in modules.qsort Name.lt do
    let count := names.foldl (init := (0 : Nat)) fun n name =>
      if declarationModule env name == moduleName then n + 1 else n
    logInfo m!"Axiom audit module {moduleName}: checked {count} declarations."
  logInfo m!"Axiom audit for {modulePrefix}: checked {names.size} declarations in {modules.size} modules; axioms used: {used.toArray.qsort Name.lt}; no forbidden axioms."

end Rudin.PMA.Audit
