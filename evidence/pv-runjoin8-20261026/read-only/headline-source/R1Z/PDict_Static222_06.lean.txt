import R1Z.PDict_Static222_05
set_option autoImplicit false
noncomputable section
namespace R1Z.PDict_Static222
open Aeneas Aeneas.Std ProverRwFull PDict_FormatterTypeMaps PDict_FormatterDictionaryMap
/-- Carrier transport candidate for `aspis_prover.state_only_hiding.sum_qm31_copy_inactive`. -/
theorem erase_96 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @aspis_prover.state_only_hiding.sum_qm31_copy_inactive (types base F) (selected base F ops) = @aspis_prover.state_only_hiding.sum_qm31_copy_inactive base ops := by
  delta aspis_prover.state_only_hiding.sum_qm31_copy_inactive
  try simp only [erase_95 base F ops]
  all_goals rfl
#print axioms erase_96

/-- Carrier transport candidate for `aspis_prover.state_only_hiding.balance_qm31_copy_inactive`. -/
theorem erase_97 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @aspis_prover.state_only_hiding.balance_qm31_copy_inactive (types base F) (selected base F ops) = @aspis_prover.state_only_hiding.balance_qm31_copy_inactive base ops := by
  delta aspis_prover.state_only_hiding.balance_qm31_copy_inactive
  try simp only [erase_96 base F ops]
  all_goals rfl
#print axioms erase_97

/-- Carrier transport candidate for `aspis_prover.state_only_hiding.sample_mask_g_loop.body`. -/
theorem erase_98 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @aspis_prover.state_only_hiding.sample_mask_g_loop.body (types base F) (selected base F ops) = @aspis_prover.state_only_hiding.sample_mask_g_loop.body base ops := by
  delta aspis_prover.state_only_hiding.sample_mask_g_loop.body
  try simp only [erase_92 base F ops, erase_97 base F ops]
  all_goals rfl
#print axioms erase_98

/-- Carrier transport candidate for `aspis_prover.state_only_hiding.sample_mask_g_loop`. -/
theorem erase_99 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @aspis_prover.state_only_hiding.sample_mask_g_loop (types base F) (selected base F ops) = @aspis_prover.state_only_hiding.sample_mask_g_loop base ops := by
  delta aspis_prover.state_only_hiding.sample_mask_g_loop
  try simp only [erase_98 base F ops]
  all_goals rfl
#print axioms erase_99

/-- Carrier transport candidate for `aspis_prover.state_only_hiding.sample_mask_g`. -/
theorem erase_100 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @aspis_prover.state_only_hiding.sample_mask_g (types base F) (selected base F ops) = @aspis_prover.state_only_hiding.sample_mask_g base ops := by
  delta aspis_prover.state_only_hiding.sample_mask_g
  try simp only [erase_99 base F ops]
  all_goals rfl
#print axioms erase_100

/-- Carrier transport candidate for `aspis_core.field.QM31.Insts.CoreCloneClone`. -/
theorem erase_101 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @aspis_core.field.QM31.Insts.CoreCloneClone (types base F) (selected base F ops) = @aspis_core.field.QM31.Insts.CoreCloneClone base ops := by
  delta aspis_core.field.QM31.Insts.CoreCloneClone
  all_goals rfl
#print axioms erase_101

/-- Carrier transport candidate for `aspis_prover.state_only_hiding.sample_mask_h1_padding_loop.body`. -/
theorem erase_102 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @aspis_prover.state_only_hiding.sample_mask_h1_padding_loop.body (types base F) (selected base F ops) = @aspis_prover.state_only_hiding.sample_mask_h1_padding_loop.body base ops := by
  delta aspis_prover.state_only_hiding.sample_mask_h1_padding_loop.body
  try simp only [erase_92 base F ops, erase_97 base F ops]
  all_goals rfl
#print axioms erase_102

/-- Carrier transport candidate for `aspis_prover.state_only_hiding.sample_mask_h1_padding_loop`. -/
theorem erase_103 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @aspis_prover.state_only_hiding.sample_mask_h1_padding_loop (types base F) (selected base F ops) = @aspis_prover.state_only_hiding.sample_mask_h1_padding_loop base ops := by
  delta aspis_prover.state_only_hiding.sample_mask_h1_padding_loop
  try simp only [erase_102 base F ops]
  all_goals rfl
#print axioms erase_103

/-- Carrier transport candidate for `aspis_prover.state_only_hiding.sample_mask_h1_padding`. -/
theorem erase_104 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @aspis_prover.state_only_hiding.sample_mask_h1_padding (types base F) (selected base F ops) = @aspis_prover.state_only_hiding.sample_mask_h1_padding base ops := by
  delta aspis_prover.state_only_hiding.sample_mask_h1_padding
  try simp only [erase_101 base F ops, erase_103 base F ops]
  all_goals rfl
#print axioms erase_104

/-- Carrier transport candidate for `aspis_prover.state_only_hiding.build_mask_material_for_layout`. -/
theorem erase_105 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @aspis_prover.state_only_hiding.build_mask_material_for_layout (types base F) (selected base F ops) = @aspis_prover.state_only_hiding.build_mask_material_for_layout base ops := by
  delta aspis_prover.state_only_hiding.build_mask_material_for_layout
  try simp only [erase_84 base F ops, erase_91 base F ops, erase_100 base F ops, erase_104 base F ops]
  all_goals rfl
#print axioms erase_105

/-- Carrier transport candidate for `aspis_prover.state_only_hiding.pool_v1_pair_forest_copy_active_rows`. -/
theorem erase_106 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @aspis_prover.state_only_hiding.pool_v1_pair_forest_copy_active_rows (types base F) (selected base F ops) = @aspis_prover.state_only_hiding.pool_v1_pair_forest_copy_active_rows base ops := by
  delta aspis_prover.state_only_hiding.pool_v1_pair_forest_copy_active_rows
  all_goals rfl
#print axioms erase_106

/-- Carrier transport candidate for `aspis_prover.state_only_hiding.build_pool_v1_pair_forest_mask_material_v1_from_entropy_ref`. -/
theorem erase_107 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @aspis_prover.state_only_hiding.build_pool_v1_pair_forest_mask_material_v1_from_entropy_ref (types base F) (selected base F ops) = @aspis_prover.state_only_hiding.build_pool_v1_pair_forest_mask_material_v1_from_entropy_ref base ops := by
  delta aspis_prover.state_only_hiding.build_pool_v1_pair_forest_mask_material_v1_from_entropy_ref
  try simp only [erase_105 base F ops, erase_106 base F ops]
  all_goals rfl
#print axioms erase_107

/-- Carrier transport candidate for `aspis_prover.state_only_entropy.StateOnlyAttemptSecrets.reserve_and_build_pool_v1_pair_forest_mask_material_v1`. -/
theorem erase_108 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @aspis_prover.state_only_entropy.StateOnlyAttemptSecrets.reserve_and_build_pool_v1_pair_forest_mask_material_v1 (types base F) (selected base F ops) = @aspis_prover.state_only_entropy.StateOnlyAttemptSecrets.reserve_and_build_pool_v1_pair_forest_mask_material_v1 base ops := by
  delta aspis_prover.state_only_entropy.StateOnlyAttemptSecrets.reserve_and_build_pool_v1_pair_forest_mask_material_v1
  try simp only [erase_62 base F ops, erase_107 base F ops, erase_64 base F ops]
  all_goals rfl
#print axioms erase_108

/-- Carrier transport candidate for `aspis_prover.state_only_hiding.apply_mask_cells_loop.body`. -/
theorem erase_109 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @aspis_prover.state_only_hiding.apply_mask_cells_loop.body (types base F) (selected base F ops) = @aspis_prover.state_only_hiding.apply_mask_cells_loop.body base ops := by
  delta aspis_prover.state_only_hiding.apply_mask_cells_loop.body
  all_goals rfl
#print axioms erase_109

/-- Carrier transport candidate for `aspis_prover.state_only_hiding.apply_mask_cells_loop`. -/
theorem erase_110 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @aspis_prover.state_only_hiding.apply_mask_cells_loop (types base F) (selected base F ops) = @aspis_prover.state_only_hiding.apply_mask_cells_loop base ops := by
  delta aspis_prover.state_only_hiding.apply_mask_cells_loop
  try simp only [erase_109 base F ops]
  all_goals rfl
#print axioms erase_110

/-- Carrier transport candidate for `aspis_prover.state_only_hiding.apply_mask_cells`. -/
theorem erase_111 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @aspis_prover.state_only_hiding.apply_mask_cells (types base F) (selected base F ops) = @aspis_prover.state_only_hiding.apply_mask_cells base ops := by
  delta aspis_prover.state_only_hiding.apply_mask_cells
  try simp only [erase_110 base F ops]
  all_goals rfl
#print axioms erase_111
end R1Z.PDict_Static222
