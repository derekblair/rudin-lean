import Rudin.Research.PMA1043Compatibility
import Rudin.PMA.AxiomAudit

/-! Explicit audit of the standalone compatibility research module. -/

run_cmd do
  Rudin.PMA.Audit.checkModuleAxioms `Rudin.Research.PMA1043Compatibility
    #[`Rudin.PMA.Chapter10.c2_planarDivergence_iff_compatibleColumns,
      `Rudin.PMA.Chapter10.canonical_columns_compatible_iff_constant]

#print axioms Rudin.PMA.Chapter10.planarGradient
#print axioms Rudin.PMA.Chapter10.planarGradient_apply
#print axioms Rudin.PMA.Chapter10.PlanarClosed
#print axioms Rudin.PMA.Chapter10.contDiff_planarGradient
#print axioms Rudin.PMA.Chapter10.planarClosed_planarGradient
#print axioms Rudin.PMA.Chapter10.horizontalField
#print axioms Rudin.PMA.Chapter10.contDiff_horizontalField
#print axioms Rudin.PMA.Chapter10.curl_horizontalField_eq_zero
#print axioms Rudin.PMA.Chapter10.planarClosed_has_c2_scalarPotential
#print axioms Rudin.PMA.Chapter10.PlanarCompatibleTrace
#print axioms Rudin.PMA.Chapter10.c2_planarDivergence_iff_compatibleTrace
#print axioms Rudin.PMA.Chapter10.c2_verticalPotential_iff_compatibleTrace
#print axioms Rudin.PMA.Chapter10.planarMatrixColumn
#print axioms Rudin.PMA.Chapter10.planarMatrixTrace
#print axioms Rudin.PMA.Chapter10.contDiff_planarMatrixTrace
#print axioms Rudin.PMA.Chapter10.planarDivergence_column_eq_partial_trace
#print axioms Rudin.PMA.Chapter10.PlanarCompatibleColumns
#print axioms Rudin.PMA.Chapter10.planar_constant_of_partials_zero
#print axioms Rudin.PMA.Chapter10.compatibleColumns_iff_compatibleTrace
#print axioms Rudin.PMA.Chapter10.c2_planarDivergence_iff_compatibleColumns
#print axioms Rudin.PMA.Chapter10.canonical_columns_compatible_iff_constant
