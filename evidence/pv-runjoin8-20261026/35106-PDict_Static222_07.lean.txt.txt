import R1Z.PDict_Static222_06
set_option autoImplicit false
noncomputable section
namespace R1Z.PDict_Static222
open Aeneas Aeneas.Std ProverRwFull PDict_FormatterTypeMaps PDict_FormatterDictionaryMap
/-- Carrier transport candidate for `aspis_prover.state_only_hiding.balance_mask_column`. -/
theorem erase_112 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @aspis_prover.state_only_hiding.balance_mask_column (types base F) (selected base F ops) = @aspis_prover.state_only_hiding.balance_mask_column base ops := by
  delta aspis_prover.state_only_hiding.balance_mask_column
  try simp only [erase_63 base F ops, erase_89 base F ops]
  all_goals rfl
#print axioms erase_112

/-- Carrier transport candidate for `aspis_prover.state_only_hiding.balance_mask_columns_from`. -/
theorem erase_113 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @aspis_prover.state_only_hiding.balance_mask_columns_from (types base F) (selected base F ops) = @aspis_prover.state_only_hiding.balance_mask_columns_from base ops := by
  delta aspis_prover.state_only_hiding.balance_mask_columns_from
  try simp only [erase_112 base F ops]
  all_goals rfl
#print axioms erase_113

/-- Carrier transport candidate for `aspis_prover.state_only_hiding.balance_mask_columns`. -/
theorem erase_114 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @aspis_prover.state_only_hiding.balance_mask_columns (types base F) (selected base F ops) = @aspis_prover.state_only_hiding.balance_mask_columns base ops := by
  delta aspis_prover.state_only_hiding.balance_mask_columns
  try simp only [erase_113 base F ops]
  all_goals rfl
#print axioms erase_114

/-- Carrier transport candidate for `aspis_prover.state_only_hiding.apply_mask_material_for_layout`. -/
theorem erase_115 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @aspis_prover.state_only_hiding.apply_mask_material_for_layout (types base F) (selected base F ops) = @aspis_prover.state_only_hiding.apply_mask_material_for_layout base ops := by
  delta aspis_prover.state_only_hiding.apply_mask_material_for_layout
  try simp only [erase_63 base F ops, erase_111 base F ops, erase_114 base F ops]
  all_goals rfl
#print axioms erase_115

/-- Carrier transport candidate for `aspis_prover.state_only_hiding.apply_pool_v1_pair_forest_mask_material_v1`. -/
theorem erase_116 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @aspis_prover.state_only_hiding.apply_pool_v1_pair_forest_mask_material_v1 (types base F) (selected base F ops) = @aspis_prover.state_only_hiding.apply_pool_v1_pair_forest_mask_material_v1 base ops := by
  delta aspis_prover.state_only_hiding.apply_pool_v1_pair_forest_mask_material_v1
  try simp only [erase_115 base F ops, erase_106 base F ops]
  all_goals rfl
#print axioms erase_116

/-- Carrier transport candidate for `aspis_core.field.M31.Insts.CoreCloneClone`. -/
theorem erase_117 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @aspis_core.field.M31.Insts.CoreCloneClone (types base F) (selected base F ops) = @aspis_core.field.M31.Insts.CoreCloneClone base ops := by
  delta aspis_core.field.M31.Insts.CoreCloneClone
  all_goals rfl
#print axioms erase_117

/-- Carrier transport candidate for `aspis_core.field.M31.Insts.CoreMarkerCopy`. -/
theorem erase_118 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @aspis_core.field.M31.Insts.CoreMarkerCopy (types base F) (selected base F ops) = @aspis_core.field.M31.Insts.CoreMarkerCopy base ops := by
  delta aspis_core.field.M31.Insts.CoreMarkerCopy
  try simp only [erase_117 base F ops]
  all_goals rfl
#print axioms erase_118

/-- Carrier transport candidate for `host_commitment.domain_next_level_loop.body`. -/
theorem erase_119 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @host_commitment.domain_next_level_loop.body (types base F) (selected base F ops) = @host_commitment.domain_next_level_loop.body base ops := by
  delta host_commitment.domain_next_level_loop.body
  all_goals rfl
#print axioms erase_119

/-- Carrier transport candidate for `host_commitment.domain_next_level_loop`. -/
theorem erase_120 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @host_commitment.domain_next_level_loop (types base F) (selected base F ops) = @host_commitment.domain_next_level_loop base ops := by
  delta host_commitment.domain_next_level_loop
  try simp only [erase_119 base F ops]
  all_goals rfl
#print axioms erase_120

/-- Carrier transport candidate for `host_commitment.domain_next_level`. -/
theorem erase_121 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @host_commitment.domain_next_level (types base F) (selected base F ops) = @host_commitment.domain_next_level base ops := by
  delta host_commitment.domain_next_level
  try simp only [erase_118 base F ops, erase_120 base F ops]
  all_goals rfl
#print axioms erase_121

/-- Carrier transport candidate for `host_commitment.domain_append_levels`. -/
theorem erase_122 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @host_commitment.domain_append_levels (types base F) (selected base F ops) = @host_commitment.domain_append_levels base ops := by
  delta host_commitment.domain_append_levels
  try simp only [erase_121 base F ops]
  all_goals rfl
#print axioms erase_122

/-- Carrier transport candidate for `host_commitment.domain_first_level_loop.body`. -/
theorem erase_123 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @host_commitment.domain_first_level_loop.body (types base F) (selected base F ops) = @host_commitment.domain_first_level_loop.body base ops := by
  delta host_commitment.domain_first_level_loop.body
  all_goals rfl
#print axioms erase_123

/-- Carrier transport candidate for `host_commitment.domain_first_level_loop`. -/
theorem erase_124 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @host_commitment.domain_first_level_loop (types base F) (selected base F ops) = @host_commitment.domain_first_level_loop base ops := by
  delta host_commitment.domain_first_level_loop
  try simp only [erase_123 base F ops]
  all_goals rfl
#print axioms erase_124

/-- Carrier transport candidate for `host_commitment.domain_first_level`. -/
theorem erase_125 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @host_commitment.domain_first_level (types base F) (selected base F ops) = @host_commitment.domain_first_level base ops := by
  delta host_commitment.domain_first_level
  try simp only [erase_118 base F ops, erase_124 base F ops]
  all_goals rfl
#print axioms erase_125

/-- Carrier transport candidate for `aspis_core.r0.domain.Point.Insts.CoreCloneClone`. -/
theorem erase_126 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @aspis_core.r0.domain.Point.Insts.CoreCloneClone (types base F) (selected base F ops) = @aspis_core.r0.domain.Point.Insts.CoreCloneClone base ops := by
  delta aspis_core.r0.domain.Point.Insts.CoreCloneClone
  all_goals rfl
#print axioms erase_126

/-- Carrier transport candidate for `aspis_core.r0.domain.Point.Insts.CoreMarkerCopy`. -/
theorem erase_127 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @aspis_core.r0.domain.Point.Insts.CoreMarkerCopy (types base F) (selected base F ops) = @aspis_core.r0.domain.Point.Insts.CoreMarkerCopy base ops := by
  delta aspis_core.r0.domain.Point.Insts.CoreMarkerCopy
  try simp only [erase_126 base F ops]
  all_goals rfl
#print axioms erase_127
end R1Z.PDict_Static222
