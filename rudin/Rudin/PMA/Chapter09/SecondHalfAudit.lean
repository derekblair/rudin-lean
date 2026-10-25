import Rudin.PMA.Chapter09.SecondHalf
import Rudin.PMA.Chapter09.InverseAudit

run_cmd Rudin.PMA.Chapter09Audit.check

#print axioms Rudin.PMA.Chapter09.pma9_28
#print axioms Rudin.PMA.Chapter09.pma9_29
#print axioms Rudin.PMA.Chapter09.pma9_32
#print axioms Rudin.PMA.Chapter09.pma9_33_det_eq
#print axioms Rudin.PMA.Chapter09.pma9_40
#print axioms Rudin.PMA.Chapter09.pma9_41

/-! Numbered-node coverage is checked against actual kernel declarations.
Definitions are checked as definitions; mathematical claims as theorem constants. -/
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let proofs : Array Name := #[
    `Rudin.PMA.Chapter09.pma9_23, `Rudin.PMA.Chapter09.pma9_24,
    `Rudin.PMA.Chapter09.pma9_24_inverse_derivative, `Rudin.PMA.Chapter09.pma9_25,
    `Rudin.PMA.Chapter09.pma9_26, `Rudin.PMA.Chapter09.pma9_27,
    `Rudin.PMA.Chapter09.pma9_28, `Rudin.PMA.Chapter09.pma9_29,
    `Rudin.PMA.Chapter09.pma9_30_full_rank, `Rudin.PMA.Chapter09.pma9_30_rank_zero,
    `Rudin.PMA.Chapter09.pma9_31_a, `Rudin.PMA.Chapter09.pma9_31_b,
    `Rudin.PMA.Chapter09.pma9_31_infinitely_many, `Rudin.PMA.Chapter09.pma9_32,
    `Rudin.PMA.Chapter09.pma9_32_graph_image, `Rudin.PMA.Chapter09.pma9_32_projection_bijOn,
    `Rudin.PMA.Chapter09.pma9_32_graph_reconstruct, `Rudin.PMA.Chapter09.pma9_32_level_eq_iff,
    `Rudin.PMA.Chapter09.pma9_32_level_image, `Rudin.PMA.Chapter09.pma9_32_kernel_dimension,
    `Rudin.PMA.Chapter09.pma9_33_det_eq, `Rudin.PMA.Chapter09.pma9_33_sign_swap,
    `Rudin.PMA.Chapter09.pma9_33_sign_values, `Rudin.PMA.Chapter09.pma9_34_a,
    `Rudin.PMA.Chapter09.pma9_34_b_add, `Rudin.PMA.Chapter09.pma9_34_b_smul,
    `Rudin.PMA.Chapter09.pma9_34_c, `Rudin.PMA.Chapter09.pma9_34_d,
    `Rudin.PMA.Chapter09.pma9_35, `Rudin.PMA.Chapter09.pma9_36,
    `Rudin.PMA.Chapter09.pma9_37_change_basis, `Rudin.PMA.Chapter09.pma9_37,
    `Rudin.PMA.Chapter09.pma9_38_nonzero_iff, `Rudin.PMA.Chapter09.pma9_38_partials,
    `Rudin.PMA.Chapter09.pma9_38_implicit, `Rudin.PMA.Chapter09.pma9_40,
    `Rudin.PMA.Chapter09.pma9_41, `Rudin.PMA.Chapter09.pma9_41_corollary,
    `Rudin.PMA.Chapter09.pma9_41_of_pma9_39]
  let definitions : Array Name := #[
    `Rudin.PMA.Chapter09.pma9_26_x, `Rudin.PMA.Chapter09.pma9_26_y,
    `Rudin.PMA.Chapter09.pma9_30_nullSpace, `Rudin.PMA.Chapter09.pma9_30_range,
    `Rudin.PMA.Chapter09.pma9_30_rank, `Rudin.PMA.Chapter09.pma9_31_isProjection,
    `Rudin.PMA.Chapter09.pma9_33_sign, `Rudin.PMA.Chapter09.pma9_33_det,
    `Rudin.PMA.Chapter09.pma9_38_jacobian, `Rudin.PMA.Chapter09.pma9_39,
    `Rudin.PMA.Chapter09.pma9_39_mapping]
  for name in proofs do
    match env.find? name with
    | some (.thmInfo _) => pure ()
    | _ => throwError "Missing kernel theorem: {name}"
  for name in definitions do
    match env.find? name with
    | some (.defnInfo _) => pure ()
    | _ => throwError "Missing kernel definition: {name}"
  logInfo m!"Second-half coverage check: {proofs.size} theorem anchors and {definitions.size} definition anchors."
