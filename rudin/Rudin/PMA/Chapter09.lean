import Rudin.PMA.Chapter09.FirstHalfAudit
import Rudin.PMA.Chapter09.SecondHalfAudit
import Rudin.PMA.Chapter09.DeterminantsAudit
import Rudin.PMA.Chapter09.IntegralsAudit
import Rudin.PMA.AxiomAudit

/-!
# Rudin, *Principles of Mathematical Analysis* (3rd ed.)

## Chapter 9: Functions of Several Variables

Every definition, theorem, and corollary from this chapter is
formalized below in dependency order. Zero `sorry`s: anything
not yet proved is tracked in `QUEUE.md`, never as a `sorry` here.
-/

/-! Audit the whole imported chapter by module ownership, including generated
declarations outside the chapter namespace and the partial-audit helper.
Require an anchor from each declaration-bearing module and the generated
implicit-function lemma outside the chapter namespace. -/
run_cmd Rudin.PMA.Audit.checkModuleAxioms `Rudin.PMA.Chapter09 #[
    `ContDiffAt.implicitFunction.congr_simp,
    `Rudin.PMA.Chapter09.pma9_19,
    `Rudin.PMA.Chapter09.pma9_30_nullSpace,
    `Rudin.PMA.Chapter09.pma9_10_slope,
    `Rudin.PMA.Chapter09.pma9_16_discontinuous,
    `Rudin.PMA.Chapter09.coordinatePartial,
    `Rudin.PMA.Chapter09.pma9_26_x,
    `Rudin.PMA.Chapter09.rsIntegrable_uniformLimit_filter,
    `Rudin.PMA.Chapter09.pma9_23_withConstant,
    `Rudin.PMA.Chapter09Audit.check,
    `Rudin.PMA.Chapter09.pma9_1_vectorSpace,
    `Rudin.PMA.Chapter09.pma9_6_linearMaps,
    `Rudin.PMA.Chapter09.coordinateDerivative,
    `Rudin.PMA.Chapter09.pma9_16_continuousCounterexample,
    `Rudin.PMA.Chapter09.partial_hasDerivAt_update,
    `Rudin.PMA.Chapter09.pma9_32,
    `Rudin.PMA.Chapter09.rankSupport_constant_on_fibers,
    `Rudin.PMA.Chapter09.rankRangeProjection,
    `Rudin.PMA.Chapter09.rankSupport_ker_comp_eq]
