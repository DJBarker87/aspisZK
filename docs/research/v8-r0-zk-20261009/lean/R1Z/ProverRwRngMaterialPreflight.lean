import R1Z.ProverRwRngMaterialInvariant
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwRngMaterialPreflight
open Aeneas Aeneas.Std Result ProverRwRngMaterialBody
open aspis_prover.state_only_entropy aspis_prover.state_only_hiding
open aspis_core.state_only_hiding ProverRwRngMaterialControl ProverRwRngMaterialPaths
variable [TypeLeaves] [LocalLeaves]

theorem wrong_mask_keeps_ack (hash : Hash) (binding entropy : Array U8 32#usize) (c : Context)
    (wrong : c.mask_layout_fingerprint ≠ PINNED_POOL_V1_PAIR_FOREST_RELATION_FREE_MASK_FINGERPRINT_V1) :
    material hash binding c entropy = .ok (.Err .Layout,freshAck c) := by
  simp [material,build_pool_v1_pair_forest_mask_material_v1_from_entropy_ref,wrong]

theorem wrong_factor_keeps_ack (hash : Hash) (binding entropy : Array U8 32#usize) (c : Context)
    (mask : c.mask_layout_fingerprint = PINNED_POOL_V1_PAIR_FOREST_RELATION_FREE_MASK_FINGERPRINT_V1)
    (wrong : c.layout_factor_fingerprint ≠ PINNED_POOL_V1_PAIR_FOREST_HIDING_LAYOUT_FACTOR_FINGERPRINT_V1) :
    material hash binding c entropy = .ok (.Err .Layout,freshAck c) := by
  simp [material,build_pool_v1_pair_forest_mask_material_v1_from_entropy_ref,mask,wrong]

theorem cells_error_keeps_ack (hash : Hash) (binding entropy : Array U8 32#usize) (c : Context)
    (error : aspis_statement.pool_v1.pair_tree_hiding.PoolV1PairHidingLayoutErrorV1)
    (mask : c.mask_layout_fingerprint = PINNED_POOL_V1_PAIR_FOREST_RELATION_FREE_MASK_FINGERPRINT_V1)
    (factor : c.layout_factor_fingerprint = PINNED_POOL_V1_PAIR_FOREST_HIDING_LAYOUT_FACTOR_FINGERPRINT_V1)
    (hcells : cellsReply = .ok (.Err error)) :
    material hash binding c entropy = .ok (.Err .Layout,freshAck c) := by
  simp only [cellsReply] at hcells
  simp [material,build_pool_v1_pair_forest_mask_material_v1_from_entropy_ref,mask,factor,hcells,
    core.result.Result.map_err,core.result.Result.Insts.CoreOpsTry.branch]
  rfl

theorem active_error_keeps_ack (hash : Hash) (binding entropy : Array U8 32#usize) (c : Context)
    (cells : Cells) (e : BuildError)
    (mask : c.mask_layout_fingerprint = PINNED_POOL_V1_PAIR_FOREST_RELATION_FREE_MASK_FINGERPRINT_V1)
    (factor : c.layout_factor_fingerprint = PINNED_POOL_V1_PAIR_FOREST_HIDING_LAYOUT_FACTOR_FINGERPRINT_V1)
    (hcells : cellsReply = .ok (.Ok cells)) (hactive : activeReply = .ok (.Err e)) :
    material hash binding c entropy = .ok (.Err e,freshAck c) := by
  simp only [cellsReply] at hcells
  simp only [activeReply] at hactive
  simp [material,build_pool_v1_pair_forest_mask_material_v1_from_entropy_ref,mask,factor,hcells,hactive,
    core.result.Result.map_err,core.result.Result.Insts.CoreOpsTry.branch]
  rfl

theorem used_ack_rejected_before_entropy (hash : Hash) (binding entropy : Array U8 32#usize)
    (c : Context) (cells : Slice aspis_statement.trace_v4.TraceCell) (active : Array Bool 1024#usize) :
    build_mask_material_for_layout AckStore hash binding c entropy (usedAck c) cells active =
      .ok (.Err .ReusedMaskNonce,usedAck c) := by
  have ack := acknowledgment_used c c.statement_digest c.mask_nonce
  change PreReservedNonce.Insts.Aspis_proverState_only_hidingStateOnlyMaskNonceStore.reserve
    (usedAck c) c.statement_digest c.mask_nonce = _ at ack
  simp [build_mask_material_for_layout,ack]

#print axioms wrong_mask_keeps_ack
#print axioms wrong_factor_keeps_ack
#print axioms cells_error_keeps_ack
#print axioms active_error_keeps_ack
#print axioms used_ack_rejected_before_entropy
end R1Z.ProverRwRngMaterialPreflight
