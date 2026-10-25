import Rudin.PMA.Chapter11SecondHalf
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/-! Recursive axiom audit for every declaration introduced by the second half,
including private helpers and generated definitions. This deliberately checks
actual declarations rather than inferring completion from theorem names. -/

open Lean Elab Command

run_cmd do
  let groups : Array (String × Array String) := #[
    ("11.24", #["pma11_24_nonnegative", "pma11_24_integrable", "pma11_24_ereal",
      "pma11_24_corollary", "pma11_24_corollary_nonnegative", "pma11_24_corollary_ereal",
      "pma11_24_native_nonnegative", "pma11_24_native"]),
    ("11.25", #["AlmostEqualOn", "pma11_25_equivalence", "pma11_25_iff_null",
      "pma11_25_ereal_finite_ae", "pma11_25_ereal_representative",
      "pma11_25_ereal_integral_eq", "pma11_25_ereal_integral_congr", "pma11_25_native"]),
    ("11.26", #["pma11_26", "pma11_26_ereal", "pma11_26_native"]),
    ("11.27", #["pma11_27", "pma11_27_ereal", "pma11_27_native"]),
    ("11.28", #["pma11_28", "pma11_28_limit", "pma11_28_on", "pma11_28_native"]),
    ("11.29", #["pma11_29", "pma11_29_ereal", "pma11_29_native"]),
    ("11.30", #["pma11_30", "pma11_30_ae", "pma11_30_native"]),
    ("11.31", #["pma11_31", "pma11_31_ae", "pma11_31_native"]),
    ("11.32", #["pma11_32", "pma11_32_ereal", "pma11_32_bounded", "pma11_32_native",
      "pma11_32_native_extended_majorant"]),
    ("11.33", #["pma11_33", "pma11_33_comparison", "pma11_33_criterion",
      "pma11_33_indefinite_integral", "pma11_33_integral_derivative"]),
    ("11.34", #["SquareIntegrable", "l2Norm", "pma11_34", "norm_toL2"]),
    ("11.35", #["pma11_35"]),
    ("11.36", #["pma11_36"]),
    ("11.37", #["L2Space", "pma11_37_eq", "pma11_37_dist", "pma11_37_zero_iff",
      "pma11_37_metric"]),
    ("11.38", #["pma11_38"]),
    ("11.39", #["OrthonormalFunctions", "fourierCoefficient", "pma11_39",
      "pma11_39_bessel", "pma11_39_bestApproximation", "pma11_39_l1_fourier_integrand"]),
    ("11.40", #["trigCoefficient", "trigPartialSum", "pma11_40",
      "pma11_40_convergence", "pma11_40_parseval", "pma11_40_corollary",
      "pma11_40_uniqueness"]),
    ("11.41", #["L2Converges", "L2Cauchy", "pma11_41_converges", "pma11_41_cauchy"]),
    ("11.42", #["pma11_42", "pma11_42_functions"]),
    ("11.43", #["pma11_43", "pma11_43_functions"]),
    ("11.44", #["CompleteOrthonormal", "completeOrthonormalBasis"]),
    ("11.45", #["pma11_45", "pma11_45_expansion", "l2Coordinates"])]
  let env ← getEnv
  let mut count : Nat := 0
  for (node, declarations) in groups do
    for declaration in declarations do
      let name := Name.str `Rudin.PMA.Chapter11.SecondHalf declaration
      unless env.contains name do
        throwError "Missing declaration for PMA {node}: {name}."
      count := count + 1
  logInfo m!"Chapter 11 second-half coverage: {groups.size} numbered-node groups, {count} required declarations."

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
