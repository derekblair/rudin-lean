import Rudin.PMA.Chapter10.SecondHalf
import Rudin.PMA.Chapter10.SimplexChainProbes
import Rudin.PMA.Chapter10.BoundaryExamplesProbes
import Rudin.PMA.Chapter10.PositiveBoundaryProbes
import Rudin.PMA.Chapter10.StokesProbes
import Rudin.PMA.Chapter10.ClosedFormProbes
import Rudin.PMA.Chapter10.PuncturedProbes
import Rudin.PMA.Chapter10.ConvexPrimitiveProbes
import Rudin.PMA.Chapter10.ConvexExactnessProbes
import Rudin.PMA.Chapter10.CellTriangulationProbes
import Rudin.PMA.Chapter10.VectorFieldProbes
import Rudin.PMA.Chapter10.ScalarPotentialProbes
import Rudin.PMA.Chapter10.VolumeAreaProbes
import Rudin.PMA.Chapter10.TorusProbes
import Rudin.PMA.Chapter10.VectorIntegrationProbes
import Rudin.PMA.Chapter10.ClassicalCalculusProbes
import Lean.Util.CollectAxioms
import Lean.Elab.Command

set_option autoImplicit false

/-! Checks recovered second-half contracts and recursively audits all imported
Chapter 10 declarations. Node 10.43 is explicitly incomplete. -/

open Rudin.PMA.Chapter10
namespace Rudin.PMA.Chapter10.SecondHalfContractComparators
example : pma10_27_contract := pma10_27
example : pma10_28_contract := pma10_28
example : pma10_29_contract := pma10_29
example : pma10_30_contract := pma10_30
example : pma10_31_contract := pma10_31
example : pma10_32_contract := pma10_32
example : pma10_33_contract := pma10_33
example : pma10_34_contract := pma10_34
example : pma10_35_contract := pma10_35
example : pma10_36_contract := pma10_36
example : pma10_37_contract := pma10_37
example : pma10_38_contract := pma10_38
example : pma10_39_contract := pma10_39
example : pma10_40_contract := pma10_40
example : pma10_41_contract := pma10_41
example : pma10_42_contract := pma10_42
example : pma10_44_contract := pma10_44
example : pma10_45_contract := pma10_45
example : pma10_46_contract := pma10_46
example : pma10_47_contract := pma10_47
example : pma10_48_contract := pma10_48
example : pma10_49_contract := pma10_49
example : pma10_50_contract := pma10_50
example : pma10_51_contract := pma10_51
end Rudin.PMA.Chapter10.SecondHalfContractComparators

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for i in [27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 44, 45, 46, 47, 48, 49, 50, 51] do
    let name := Lean.Name.str `Rudin.PMA.Chapter10 ("pma10_" ++ toString i)
    match env.find? name with
    | some (.thmInfo _) => pure ()
    | _ => throwError "Missing second-half principal theorem: {name}"
  if (env.find? `Rudin.PMA.Chapter10.pma10_43).isSome then
    throwError "Unresolved PMA 10.43 must not be marked complete."
  logInfo "Second-half coverage: 24 principal theorems and contract comparisons; 10.43 incomplete."
  let namespacePrefix := `Rudin.PMA.Chapter10
  let names ← env.constants.foldM (init := #[]) fun names name _ => do
    let userName := privateToUserName name.eraseMacroScopes
    return if namespacePrefix.isPrefixOf userName then names.push name else names
  if names.isEmpty then
    throwError "No Chapter 10 declarations found."
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in names do
    let axioms ← collectAxioms name
    let forbidden := axioms.filter fun ax => !allowed.contains ax
    unless forbidden.isEmpty do
      throwError "Forbidden axioms in {name}: {forbidden}."
  logInfo m!"Chapter 10 axiom audit: {names.size} declarations checked; only propext, Classical.choice, Quot.sound."
