import R1Z.PDict_ReachErase06
set_option autoImplicit false
noncomputable section
namespace R1Z.PDict_ReachErase
open Aeneas Aeneas.Std ProverRwFull
variable [ExternalTypes]

/-- Full symbolic source-function equality for `aspis_prover.state_only_hiding.balance_mask_column`. -/
theorem erase_112 (ops other : ExternalFuns) :
    @aspis_prover.state_only_hiding.balance_mask_column _ (replace ops other) = @aspis_prover.state_only_hiding.balance_mask_column _ ops := by
  delta aspis_prover.state_only_hiding.balance_mask_column
  try simp only [erase_63 ops other, erase_89 ops other]
  all_goals rfl
#print axioms erase_112

/-- Full symbolic source-function equality for `aspis_prover.state_only_hiding.balance_mask_columns_from`. -/
theorem erase_113 (ops other : ExternalFuns) :
    @aspis_prover.state_only_hiding.balance_mask_columns_from _ (replace ops other) = @aspis_prover.state_only_hiding.balance_mask_columns_from _ ops := by
  delta aspis_prover.state_only_hiding.balance_mask_columns_from
  try simp only [erase_112 ops other]
  all_goals rfl
#print axioms erase_113

/-- Full symbolic source-function equality for `aspis_prover.state_only_hiding.balance_mask_columns`. -/
theorem erase_114 (ops other : ExternalFuns) :
    @aspis_prover.state_only_hiding.balance_mask_columns _ (replace ops other) = @aspis_prover.state_only_hiding.balance_mask_columns _ ops := by
  delta aspis_prover.state_only_hiding.balance_mask_columns
  try simp only [erase_113 ops other]
  all_goals rfl
#print axioms erase_114

/-- Full symbolic source-function equality for `aspis_prover.state_only_hiding.apply_mask_material_for_layout`. -/
theorem erase_115 (ops other : ExternalFuns) :
    @aspis_prover.state_only_hiding.apply_mask_material_for_layout _ (replace ops other) = @aspis_prover.state_only_hiding.apply_mask_material_for_layout _ ops := by
  delta aspis_prover.state_only_hiding.apply_mask_material_for_layout
  try simp only [erase_63 ops other, erase_111 ops other, erase_114 ops other]
  all_goals rfl
#print axioms erase_115

/-- Full symbolic source-function equality for `aspis_prover.state_only_hiding.apply_pool_v1_pair_forest_mask_material_v1`. -/
theorem erase_116 (ops other : ExternalFuns) :
    @aspis_prover.state_only_hiding.apply_pool_v1_pair_forest_mask_material_v1 _ (replace ops other) = @aspis_prover.state_only_hiding.apply_pool_v1_pair_forest_mask_material_v1 _ ops := by
  delta aspis_prover.state_only_hiding.apply_pool_v1_pair_forest_mask_material_v1
  try simp only [erase_115 ops other, erase_106 ops other]
  all_goals rfl
#print axioms erase_116

/-- Full symbolic source-function equality for `aspis_core.field.M31.Insts.CoreCloneClone`. -/
theorem erase_117 (ops other : ExternalFuns) :
    @aspis_core.field.M31.Insts.CoreCloneClone _ (replace ops other) = @aspis_core.field.M31.Insts.CoreCloneClone _ ops := by
  delta aspis_core.field.M31.Insts.CoreCloneClone
  all_goals rfl
#print axioms erase_117

/-- Full symbolic source-function equality for `aspis_core.field.M31.Insts.CoreMarkerCopy`. -/
theorem erase_118 (ops other : ExternalFuns) :
    @aspis_core.field.M31.Insts.CoreMarkerCopy _ (replace ops other) = @aspis_core.field.M31.Insts.CoreMarkerCopy _ ops := by
  delta aspis_core.field.M31.Insts.CoreMarkerCopy
  try simp only [erase_117 ops other]
  all_goals rfl
#print axioms erase_118

/-- Full symbolic source-function equality for `host_commitment.domain_next_level_loop.body`. -/
theorem erase_119 (ops other : ExternalFuns) :
    @host_commitment.domain_next_level_loop.body _ (replace ops other) = @host_commitment.domain_next_level_loop.body _ ops := by
  delta host_commitment.domain_next_level_loop.body
  all_goals rfl
#print axioms erase_119

/-- Full symbolic source-function equality for `host_commitment.domain_next_level_loop`. -/
theorem erase_120 (ops other : ExternalFuns) :
    @host_commitment.domain_next_level_loop _ (replace ops other) = @host_commitment.domain_next_level_loop _ ops := by
  delta host_commitment.domain_next_level_loop
  try simp only [erase_119 ops other]
  all_goals rfl
#print axioms erase_120

/-- Full symbolic source-function equality for `host_commitment.domain_next_level`. -/
theorem erase_121 (ops other : ExternalFuns) :
    @host_commitment.domain_next_level _ (replace ops other) = @host_commitment.domain_next_level _ ops := by
  delta host_commitment.domain_next_level
  try simp only [erase_118 ops other, erase_120 ops other]
  all_goals rfl
#print axioms erase_121

/-- Full symbolic source-function equality for `host_commitment.domain_append_levels`. -/
theorem erase_122 (ops other : ExternalFuns) :
    @host_commitment.domain_append_levels _ (replace ops other) = @host_commitment.domain_append_levels _ ops := by
  delta host_commitment.domain_append_levels
  try simp only [erase_121 ops other]
  all_goals rfl
#print axioms erase_122

/-- Full symbolic source-function equality for `host_commitment.domain_first_level_loop.body`. -/
theorem erase_123 (ops other : ExternalFuns) :
    @host_commitment.domain_first_level_loop.body _ (replace ops other) = @host_commitment.domain_first_level_loop.body _ ops := by
  delta host_commitment.domain_first_level_loop.body
  all_goals rfl
#print axioms erase_123

/-- Full symbolic source-function equality for `host_commitment.domain_first_level_loop`. -/
theorem erase_124 (ops other : ExternalFuns) :
    @host_commitment.domain_first_level_loop _ (replace ops other) = @host_commitment.domain_first_level_loop _ ops := by
  delta host_commitment.domain_first_level_loop
  try simp only [erase_123 ops other]
  all_goals rfl
#print axioms erase_124

/-- Full symbolic source-function equality for `host_commitment.domain_first_level`. -/
theorem erase_125 (ops other : ExternalFuns) :
    @host_commitment.domain_first_level _ (replace ops other) = @host_commitment.domain_first_level _ ops := by
  delta host_commitment.domain_first_level
  try simp only [erase_118 ops other, erase_124 ops other]
  all_goals rfl
#print axioms erase_125

/-- Full symbolic source-function equality for `aspis_core.r0.domain.Point.Insts.CoreCloneClone`. -/
theorem erase_126 (ops other : ExternalFuns) :
    @aspis_core.r0.domain.Point.Insts.CoreCloneClone _ (replace ops other) = @aspis_core.r0.domain.Point.Insts.CoreCloneClone _ ops := by
  delta aspis_core.r0.domain.Point.Insts.CoreCloneClone
  all_goals rfl
#print axioms erase_126

/-- Full symbolic source-function equality for `aspis_core.r0.domain.Point.Insts.CoreMarkerCopy`. -/
theorem erase_127 (ops other : ExternalFuns) :
    @aspis_core.r0.domain.Point.Insts.CoreMarkerCopy _ (replace ops other) = @aspis_core.r0.domain.Point.Insts.CoreMarkerCopy _ ops := by
  delta aspis_core.r0.domain.Point.Insts.CoreMarkerCopy
  try simp only [erase_126 ops other]
  all_goals rfl
#print axioms erase_127
end R1Z.PDict_ReachErase
