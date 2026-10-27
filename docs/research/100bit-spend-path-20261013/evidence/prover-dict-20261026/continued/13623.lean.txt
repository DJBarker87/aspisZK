import R1Z.PDict_FmtErase05
set_option autoImplicit false
noncomputable section
namespace R1Z.PDict_FmtErase
open Aeneas Aeneas.Std ProverRwFull
variable [ExternalTypes]

/-- Full symbolic source-function equality for `aspis_prover.state_only_hiding.sum_qm31_copy_inactive`. -/
theorem erase_96 (ops other : ExternalFuns) :
    @aspis_prover.state_only_hiding.sum_qm31_copy_inactive _ (replace ops other) = @aspis_prover.state_only_hiding.sum_qm31_copy_inactive _ ops := by
  delta aspis_prover.state_only_hiding.sum_qm31_copy_inactive
  try simp only [erase_95 ops other]
  all_goals rfl
#print axioms erase_96

/-- Full symbolic source-function equality for `aspis_prover.state_only_hiding.balance_qm31_copy_inactive`. -/
theorem erase_97 (ops other : ExternalFuns) :
    @aspis_prover.state_only_hiding.balance_qm31_copy_inactive _ (replace ops other) = @aspis_prover.state_only_hiding.balance_qm31_copy_inactive _ ops := by
  delta aspis_prover.state_only_hiding.balance_qm31_copy_inactive
  try simp only [erase_96 ops other]
  all_goals rfl
#print axioms erase_97

/-- Full symbolic source-function equality for `aspis_prover.state_only_hiding.sample_mask_g_loop.body`. -/
theorem erase_98 (ops other : ExternalFuns) :
    @aspis_prover.state_only_hiding.sample_mask_g_loop.body _ (replace ops other) = @aspis_prover.state_only_hiding.sample_mask_g_loop.body _ ops := by
  delta aspis_prover.state_only_hiding.sample_mask_g_loop.body
  try simp only [erase_92 ops other, erase_97 ops other]
  all_goals rfl
#print axioms erase_98

/-- Full symbolic source-function equality for `aspis_prover.state_only_hiding.sample_mask_g_loop`. -/
theorem erase_99 (ops other : ExternalFuns) :
    @aspis_prover.state_only_hiding.sample_mask_g_loop _ (replace ops other) = @aspis_prover.state_only_hiding.sample_mask_g_loop _ ops := by
  delta aspis_prover.state_only_hiding.sample_mask_g_loop
  try simp only [erase_98 ops other]
  all_goals rfl
#print axioms erase_99

/-- Full symbolic source-function equality for `aspis_prover.state_only_hiding.sample_mask_g`. -/
theorem erase_100 (ops other : ExternalFuns) :
    @aspis_prover.state_only_hiding.sample_mask_g _ (replace ops other) = @aspis_prover.state_only_hiding.sample_mask_g _ ops := by
  delta aspis_prover.state_only_hiding.sample_mask_g
  try simp only [erase_99 ops other]
  all_goals rfl
#print axioms erase_100

/-- Full symbolic source-function equality for `aspis_core.field.QM31.Insts.CoreCloneClone`. -/
theorem erase_101 (ops other : ExternalFuns) :
    @aspis_core.field.QM31.Insts.CoreCloneClone _ (replace ops other) = @aspis_core.field.QM31.Insts.CoreCloneClone _ ops := by
  delta aspis_core.field.QM31.Insts.CoreCloneClone
  all_goals rfl
#print axioms erase_101

/-- Full symbolic source-function equality for `aspis_prover.state_only_hiding.sample_mask_h1_padding_loop.body`. -/
theorem erase_102 (ops other : ExternalFuns) :
    @aspis_prover.state_only_hiding.sample_mask_h1_padding_loop.body _ (replace ops other) = @aspis_prover.state_only_hiding.sample_mask_h1_padding_loop.body _ ops := by
  delta aspis_prover.state_only_hiding.sample_mask_h1_padding_loop.body
  try simp only [erase_92 ops other, erase_97 ops other]
  all_goals rfl
#print axioms erase_102

/-- Full symbolic source-function equality for `aspis_prover.state_only_hiding.sample_mask_h1_padding_loop`. -/
theorem erase_103 (ops other : ExternalFuns) :
    @aspis_prover.state_only_hiding.sample_mask_h1_padding_loop _ (replace ops other) = @aspis_prover.state_only_hiding.sample_mask_h1_padding_loop _ ops := by
  delta aspis_prover.state_only_hiding.sample_mask_h1_padding_loop
  try simp only [erase_102 ops other]
  all_goals rfl
#print axioms erase_103

/-- Full symbolic source-function equality for `aspis_prover.state_only_hiding.sample_mask_h1_padding`. -/
theorem erase_104 (ops other : ExternalFuns) :
    @aspis_prover.state_only_hiding.sample_mask_h1_padding _ (replace ops other) = @aspis_prover.state_only_hiding.sample_mask_h1_padding _ ops := by
  delta aspis_prover.state_only_hiding.sample_mask_h1_padding
  try simp only [erase_101 ops other, erase_103 ops other]
  all_goals rfl
#print axioms erase_104

/-- Full symbolic source-function equality for `aspis_prover.state_only_hiding.build_mask_material_for_layout`. -/
theorem erase_105 (ops other : ExternalFuns) :
    @aspis_prover.state_only_hiding.build_mask_material_for_layout _ (replace ops other) = @aspis_prover.state_only_hiding.build_mask_material_for_layout _ ops := by
  delta aspis_prover.state_only_hiding.build_mask_material_for_layout
  try simp only [erase_84 ops other, erase_91 ops other, erase_100 ops other, erase_104 ops other]
  all_goals rfl
#print axioms erase_105

/-- Full symbolic source-function equality for `aspis_prover.state_only_hiding.pool_v1_pair_forest_copy_active_rows`. -/
theorem erase_106 (ops other : ExternalFuns) :
    @aspis_prover.state_only_hiding.pool_v1_pair_forest_copy_active_rows _ (replace ops other) = @aspis_prover.state_only_hiding.pool_v1_pair_forest_copy_active_rows _ ops := by
  delta aspis_prover.state_only_hiding.pool_v1_pair_forest_copy_active_rows
  all_goals rfl
#print axioms erase_106

/-- Full symbolic source-function equality for `aspis_prover.state_only_hiding.build_pool_v1_pair_forest_mask_material_v1_from_entropy_ref`. -/
theorem erase_107 (ops other : ExternalFuns) :
    @aspis_prover.state_only_hiding.build_pool_v1_pair_forest_mask_material_v1_from_entropy_ref _ (replace ops other) = @aspis_prover.state_only_hiding.build_pool_v1_pair_forest_mask_material_v1_from_entropy_ref _ ops := by
  delta aspis_prover.state_only_hiding.build_pool_v1_pair_forest_mask_material_v1_from_entropy_ref
  try simp only [erase_105 ops other, erase_106 ops other]
  all_goals rfl
#print axioms erase_107

/-- Full symbolic source-function equality for `aspis_prover.state_only_entropy.StateOnlyAttemptSecrets.reserve_and_build_pool_v1_pair_forest_mask_material_v1`. -/
theorem erase_108 (ops other : ExternalFuns) :
    @aspis_prover.state_only_entropy.StateOnlyAttemptSecrets.reserve_and_build_pool_v1_pair_forest_mask_material_v1 _ (replace ops other) = @aspis_prover.state_only_entropy.StateOnlyAttemptSecrets.reserve_and_build_pool_v1_pair_forest_mask_material_v1 _ ops := by
  delta aspis_prover.state_only_entropy.StateOnlyAttemptSecrets.reserve_and_build_pool_v1_pair_forest_mask_material_v1
  try simp only [erase_62 ops other, erase_107 ops other, erase_64 ops other]
  all_goals rfl
#print axioms erase_108

/-- Full symbolic source-function equality for `aspis_prover.state_only_hiding.apply_mask_cells_loop.body`. -/
theorem erase_109 (ops other : ExternalFuns) :
    @aspis_prover.state_only_hiding.apply_mask_cells_loop.body _ (replace ops other) = @aspis_prover.state_only_hiding.apply_mask_cells_loop.body _ ops := by
  delta aspis_prover.state_only_hiding.apply_mask_cells_loop.body
  all_goals rfl
#print axioms erase_109

/-- Full symbolic source-function equality for `aspis_prover.state_only_hiding.apply_mask_cells_loop`. -/
theorem erase_110 (ops other : ExternalFuns) :
    @aspis_prover.state_only_hiding.apply_mask_cells_loop _ (replace ops other) = @aspis_prover.state_only_hiding.apply_mask_cells_loop _ ops := by
  delta aspis_prover.state_only_hiding.apply_mask_cells_loop
  try simp only [erase_109 ops other]
  all_goals rfl
#print axioms erase_110

/-- Full symbolic source-function equality for `aspis_prover.state_only_hiding.apply_mask_cells`. -/
theorem erase_111 (ops other : ExternalFuns) :
    @aspis_prover.state_only_hiding.apply_mask_cells _ (replace ops other) = @aspis_prover.state_only_hiding.apply_mask_cells _ ops := by
  delta aspis_prover.state_only_hiding.apply_mask_cells
  try simp only [erase_110 ops other]
  all_goals rfl
#print axioms erase_111
end R1Z.PDict_FmtErase
