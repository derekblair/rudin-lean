import Rudin.PMA.Chapter11
import Rudin.PMA.Chapter11SecondHalfAudit
import Rudin.PMA.AxiomAudit
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

/-! Declaration coverage of every numbered node; semantic fidelity is separately
reviewed against the source and documented in the coverage inventory. -/
run_cmd do
  let env ← getEnv
  let coverage : Array (Nat × Array Name) := #[
    (1, #[`SetRing, `SigmaRing, `pma11_1_inter, `pma11_1_iInter]),
    (2, #[`AdmissibleSetFunction, `AdditiveSetFunction, `CountablyAdditiveSetFunction,
      `pma11_2_empty, `pma11_2_finite_union, `pma11_2_inclusion_exclusion,
      `pma11_2_mono, `pma11_2_sdiff, `pma11_2_absolute_of_finite_total]),
    (3, #[`pma11_3]),
    (4, #[`IsInterval, `IsElementary, `pma11_4_empty_interval, `isSetRing_isElementary,
      `pma11_4_not_countable_union_closed, `IsElementary.disjoint_intervals,
      `pma11_4_interval_volume_real, `pma11_4_well_defined, `pma11_4_additive]),
    (5, #[`ContentRegular, `infiniteElementaryContent_empty,
      `infiniteElementaryContent_nonempty, `infiniteElementaryContent_regular,
      `infiniteElementaryContent_not_finite]),
    (6, #[`pma11_6a, `pma11_6b_real_interval_formulas, `pma11_6b_degenerate_intervals,
      `pma11_6b_regular, `volumeRegularContent, `stieltjesRegularContent]),
    (7, #[`RegularContent.outer, `RegularContent.outer_eq_iInf, `RegularContent.outer_mono]),
    (8, #[`RegularContent.outer_eq_content, `RegularContent.outer_iUnion_le]),
    (9, #[`RegularContent.setDistance, `RegularContent.SetConverges,
      `RegularContent.FinitelyMeasurable, `RegularContent.RudinMeasurable]),
    (10, #[`RegularContent.rudinMeasurable_sigmaRing,
      `RegularContent.rudinMeasurable_iUnion_measure,
      `RegularContent.finitelyMeasurable_iff, `volumeRegularContent_outer]),
    (11, #[`pma11_11a, `RegularContent.pma11_11b, `pma11_11c,
      `pma11_11c_borel_sigmaRing, `pma11_11c_borel_minimal, `RegularContent.pma11_11d,
      `RegularContent.pma11_11d_decomposition, `pma11_11_null_sigmaRing,
      `pma11_11_countable_null, `pma11_11_cantor, `pma11_11_cantor_stage_volume]),
    (12, #[`RingMeasureSpace, `RingMeasureSpace.IsMeasurable,
      `RingMeasureSpace.toMeasure_apply, `pma11_12_lebesgue,
      `pma11_12_counting, `pma11_12_probability]),
    (13, #[`MeasurableFunction, `pma11_13_iff_measurable]),
    (14, #[`pma11_14, `pma11_14_real]),
    (15, #[`pma11_15]),
    (16, #[`pma11_16]),
    (17, #[`pma11_17, `pma11_17_inf_liminf, `pma11_17_corollary_a,
      `pma11_17_positive_negative_parts, `pma11_17_corollary_b]),
    (18, #[`pma11_18, `pma11_18_add_mul]),
    (19, #[`IsSimple, `characteristic, `simple_eq_sum_characteristic,
      `simple_measurable_iff]),
    (20, #[`exists_simple_pointwise, `exists_measurable_simple_pointwise,
      `exists_simple_monotone, `exists_measurable_simple_monotone, `exists_simple_uniform,
      `exists_simple_monotone_uniform]),
    (21, #[`simpleIntegral, `simpleIntegral_eq_sum, `nonnegativeIntegral,
      `nonnegativeIntegral_eq_sup, `nonnegativeIntegral_simple]),
    (22, #[`IntegralDefined, `lebesgueIntegral, `LebesgueIntegrable,
      `LebesgueIntegrable.integral_finite, `integralDefined_integrable_iff]),
    (23, #[`lebesgueIntegrable_of_bounded, `lebesgueIntegral_bounds,
      `lebesgueIntegral_mono, `LebesgueIntegrable.const_mul,
      `lebesgueIntegral_null, `LebesgueIntegrable.mono_set])]
  for (node, names) in coverage do
    for relativeName in names do
      let name := `Rudin.PMA.Chapter11 ++ relativeName
      unless env.contains name do
        throwError "Missing declaration for numbered node 11.{node}: {name}"
  logInfo m!"Chapter 11 first-half declaration coverage PASS: {coverage.size} numbered nodes (11.1–11.23)."

-- Supplement the original checks with ownership coverage of every contributing module
-- in both halves, pinning one declaration from each of the 24 content modules.
run_cmd Rudin.PMA.Audit.checkModuleAxioms `Rudin.PMA.Chapter11 #[
    `Rudin.PMA.Chapter11.ContentRegular,
    `Rudin.PMA.Chapter11.pma11_11c_borel_sigmaRing,
    `Rudin.PMA.Chapter11.elementaryMeasureContent,
    `Rudin.PMA.Chapter11.SetRing,
    `Rudin.PMA.Chapter11.axisInterval,
    `Rudin.PMA.Chapter11.IsInterval.closed_inter_open,
    `Rudin.PMA.Chapter11.isSetRing_isElementary,
    `Rudin.PMA.Chapter11.simpleIntegral,
    `Rudin.PMA.Chapter11.MeasurableFunction,
    `Rudin.PMA.Chapter11.pma11_11_null_sigmaRing,
    `Rudin.PMA.Chapter11.RegularContent.exists_open_sdiff_lt,
    `Rudin.PMA.Chapter11.pma11_2_absolute_series,
    `Rudin.PMA.Chapter11.IsSimple,
    `Rudin.PMA.Chapter11.stieltjesEuclideanMeasure,
    `Rudin.PMA.Chapter11.SecondHalf.partitionStep_integral,
    `Rudin.PMA.Chapter11.SecondHalf.pma11_33_ae_continuous_of_riemann,
    `Rudin.PMA.Chapter11.SecondHalf.pma11_40_parseval,
    `Rudin.PMA.Chapter11.SecondHalf.pma11_45,
    `Rudin.PMA.Chapter11.SecondHalf.pma11_24_nonnegative,
    `Rudin.PMA.Chapter11.SecondHalf.pma11_34,
    `Rudin.PMA.Chapter11.SecondHalf.pma11_33_riemann_of_ae_continuous,
    `Rudin.PMA.Chapter11.SecondHalf.native_lebesgueIntegral_compat,
    `Rudin.PMA.Chapter11.SecondHalf.pma11_33_indefinite_integral,
    `Rudin.PMA.Chapter11.SecondHalf.pma11_33_comparison]
