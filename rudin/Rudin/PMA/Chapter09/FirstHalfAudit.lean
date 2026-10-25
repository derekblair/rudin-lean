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

/-! One checked principal theorem per numbered node. The coverage document
lists the additional definitions, assertions and corollaries at each node. -/
run_cmd do
  let env ← getEnv
  let required := #[
    `Rudin.PMA.Chapter09.pma9_1_vectorSpace_iff,
    `Rudin.PMA.Chapter09.pma9_2_dimension,
    `Rudin.PMA.Chapter09.pma9_3_c,
    `Rudin.PMA.Chapter09.pma9_4_basis_image,
    `Rudin.PMA.Chapter09.pma9_5,
    `Rudin.PMA.Chapter09.pma9_6_norm_eq_sup,
    `Rudin.PMA.Chapter09.pma9_7_a,
    `Rudin.PMA.Chapter09.pma9_8_a,
    `Rudin.PMA.Chapter09.pma9_9_frobenius_bound_sq,
    `Rudin.PMA.Chapter09.pma9_10_linear_derivative,
    `Rudin.PMA.Chapter09.pma9_11_iff_punctured_limit,
    `Rudin.PMA.Chapter09.pma9_12,
    `Rudin.PMA.Chapter09.pma9_13_continuous,
    `Rudin.PMA.Chapter09.pma9_14,
    `Rudin.PMA.Chapter09.pma9_15,
    `Rudin.PMA.Chapter09.pma9_16_iff_limit,
    `Rudin.PMA.Chapter09.pma9_17,
    `Rudin.PMA.Chapter09.pma9_18_maximum,
    `Rudin.PMA.Chapter09.pma9_19,
    `Rudin.PMA.Chapter09.pma9_20,
    `Rudin.PMA.Chapter09.pma9_21,
    `Rudin.PMA.Chapter09.pma9_22]
  for name in required do
    match env.find? name with
    | some (.thmInfo _) => pure ()
    | _ => throwError "Missing principal theorem: {name}"
  logInfo m!"Chapter 9 first-half coverage: {required.size} numbered nodes have kernel-checked principal theorems."

run_cmd do
  let env ← getEnv
  for name in #[`Rudin.PMA.Chapter09.pma9_16_partials_not_imply_continuity,
      `Rudin.PMA.Chapter09.pma9_16_continuous_partials_not_differentiable] do
    match env.find? name with
    | some (.thmInfo _) => pure ()
    | _ => throwError "Missing 9.16 counterexample: {name}"
  logInfo "Both attached 9.16 counterexample assertions are kernel-checked."
