import NIH_LinkReference
import NIH_SelectedBinary
import NIH_LocalPacked
open Lean Elab Command
run_cmd do
 let env ← getEnv
 let wanted := ["active_mask_basis", "expand", "at_point", "boxed_at_point", "row", "copy_residual", "copy_tag_coordinate_dot", "copy_tag_coordinate_value", "finish_pattern_basis_values", "finish_selector_tensor_basis", "pattern_values", "pattern_values_windowed", "qm31_sum_products_up_to4", "selected_binary_weight", "external_linear_lazy", "external_linear_packed", "full_round", "full_round_m31_constants", "full_round_packed", "full_round_m31_constants_packed", "internal_linear_lazy", "internal_round", "interpolated_full_pair_packed", "interpolated_internal_pair", "leading_pair_packed", "semantic_round", "semantic_rounds", "claims", "verify_finish", "verify_observed", "circle_sample", "circle_validated"]
 for tail in wanted do
  let suffix := "." ++ tail
  let found := env.constants.toList.filterMap fun (n,_) =>
   if n.toString.startsWith "FIq_Native." && n.toString.endsWith suffix then some n.toString else none
  logInfo m!"NIH_DECL {tail}: {found}"
