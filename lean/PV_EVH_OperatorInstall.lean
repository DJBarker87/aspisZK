import PV_EVH_OperatorFrames
import PV_EVH_OpMaterialFromEntropy
import PV_EVH_OpApplyMaterial
import PV_EVH_OpPrivateSalts
import PV_EVH_OpPrepareOpening
import PV_EVH_OpPublishCompact
import PV_EVH_OpPrivateSaltStep
set_option autoImplicit false
noncomputable section
namespace PV_EVH_OperatorInstall
open Aeneas Aeneas.Std ProverRwFull
open PV_EVH_Prefix (P FinishedView)
variable [ExternalTypes] [ExternalFuns]
/- Source transport only. Native invocation/drop and actual dictionary selection
remain explicit obligations. No successful execution or trace closure follows. -/

namespace MaterialFromEntropy
structure Leaves where
  op112_OPEN : P (Std.U64)
  op113_OPEN : P (Std.U64)
  op132_OPEN : P ((core.result.Result (alloc.vec.Vec aspis_statement.trace_v4.TraceCell) aspis_statement.pool_v1.pair_tree_hiding.PoolV1PairHidingLayoutErrorV1))
  pool_v1_pair_forest_copy_active_rows_OPEN : P ((core.result.Result (Array Bool 1024#usize)
    aspis_prover.state_only_hiding.StateOnlyMaskBuildError))
  build_mask_material_for_layout_OPEN : ∀ {T0 : Type} (StateOnlyMaskNonceStoreInst :
  aspis_prover.state_only_hiding.StateOnlyMaskNonceStore T0)
  (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize))
  (precommit_binding : Array Std.U8 32#usize)
  (context : aspis_core.state_only_hiding.StateOnlyHidingContext)
  (private_entropy : Array Std.U8 32#usize) (nonce_store : T0)
  (cells : Slice aspis_statement.trace_v4.TraceCell)
  (active : Array Bool 1024#usize), P (((core.result.Result
    aspis_prover.state_only_hiding.StateOnlyMaskMaterial
    aspis_prover.state_only_hiding.StateOnlyMaskBuildError) × T0))

structure Compatible (c : Leaves) : Prop where
  op112_fixed : FinishedView (c.op112_OPEN) (aspis_core.state_only_hiding.PINNED_POOL_V1_PAIR_FOREST_RELATION_FREE_MASK_FINGERPRINT_V1)
  op113_fixed : FinishedView (c.op113_OPEN) (aspis_core.state_only_hiding.PINNED_POOL_V1_PAIR_FOREST_HIDING_LAYOUT_FACTOR_FINGERPRINT_V1)
  op132_fixed : FinishedView (c.op132_OPEN) (aspis_statement.pool_v1.pair_forest_hiding.pool_v1_pair_forest_relation_free_mask_cells_v1)
  pool_v1_pair_forest_copy_active_rows_fixed : FinishedView (c.pool_v1_pair_forest_copy_active_rows_OPEN) (aspis_prover.state_only_hiding.pool_v1_pair_forest_copy_active_rows)
  build_mask_material_for_layout_fixed : ∀ {T0 : Type} (StateOnlyMaskNonceStoreInst :
  aspis_prover.state_only_hiding.StateOnlyMaskNonceStore T0)
  (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize))
  (precommit_binding : Array Std.U8 32#usize)
  (context : aspis_core.state_only_hiding.StateOnlyHidingContext)
  (private_entropy : Array Std.U8 32#usize) (nonce_store : T0)
  (cells : Slice aspis_statement.trace_v4.TraceCell)
  (active : Array Bool 1024#usize), FinishedView (c.build_mask_material_for_layout_OPEN StateOnlyMaskNonceStoreInst hash precommit_binding context private_entropy nonce_store cells active) (aspis_prover.state_only_hiding.build_mask_material_for_layout StateOnlyMaskNonceStoreInst hash precommit_binding context private_entropy nonce_store cells active)

def install (c : Leaves) (frames : PV_EVH_OperatorFrames.Frames) : PV_EVH_OpMaterialFromEntropy.Callees where
  op112_OPEN := c.op112_OPEN
  op113_OPEN := c.op113_OPEN
  op132_OPEN := c.op132_OPEN
  op12_OPEN := PV_EVH_OperatorFrames.mapErr frames
  pool_v1_pair_forest_copy_active_rows_OPEN := c.pool_v1_pair_forest_copy_active_rows_OPEN
  build_mask_material_for_layout_OPEN := c.build_mask_material_for_layout_OPEN

theorem install_fixed (c : Leaves) (hc : Compatible c)
    (frames : PV_EVH_OperatorFrames.Frames) (hf : PV_EVH_OperatorFrames.Compatible frames)
    (selected : PV_EVH_OperatorFrames.Selection (inferInstance : ExternalFuns)) :
    PV_EVH_OpMaterialFromEntropy.Compatible (install c frames) where
  op112_fixed := hc.op112_fixed
  op113_fixed := hc.op113_fixed
  op132_fixed := hc.op132_fixed
  op12_fixed := fun inst r closure => PV_EVH_OperatorFrames.mapErr_fixed _ selected frames hf inst r closure
  pool_v1_pair_forest_copy_active_rows_fixed := hc.pool_v1_pair_forest_copy_active_rows_fixed
  build_mask_material_for_layout_fixed := hc.build_mask_material_for_layout_fixed

#print axioms install_fixed
end MaterialFromEntropy

namespace ApplyMaterial
structure Leaves where
  op132_OPEN : P ((core.result.Result (alloc.vec.Vec aspis_statement.trace_v4.TraceCell) aspis_statement.pool_v1.pair_tree_hiding.PoolV1PairHidingLayoutErrorV1))
  pool_v1_pair_forest_copy_active_rows_OPEN : P ((core.result.Result (Array Bool 1024#usize)
    aspis_prover.state_only_hiding.StateOnlyMaskBuildError))
  apply_mask_material_for_layout_OPEN : ∀ (trace : aspis_statement.state_only_trace.StateOnlyTraceFoundation)
  (material : aspis_prover.state_only_hiding.StateOnlyMaskMaterial)
  (cells : Slice aspis_statement.trace_v4.TraceCell)
  (active : Array Bool 1024#usize), P (((core.result.Result
    aspis_prover.state_only_hiding.AppliedStateOnlyMasks
    aspis_prover.state_only_hiding.StateOnlyMaskBuildError) ×
    aspis_statement.state_only_trace.StateOnlyTraceFoundation))

structure Compatible (c : Leaves) : Prop where
  op132_fixed : FinishedView (c.op132_OPEN) (aspis_statement.pool_v1.pair_forest_hiding.pool_v1_pair_forest_relation_free_mask_cells_v1)
  pool_v1_pair_forest_copy_active_rows_fixed : FinishedView (c.pool_v1_pair_forest_copy_active_rows_OPEN) (aspis_prover.state_only_hiding.pool_v1_pair_forest_copy_active_rows)
  apply_mask_material_for_layout_fixed : ∀ (trace : aspis_statement.state_only_trace.StateOnlyTraceFoundation)
  (material : aspis_prover.state_only_hiding.StateOnlyMaskMaterial)
  (cells : Slice aspis_statement.trace_v4.TraceCell)
  (active : Array Bool 1024#usize), FinishedView (c.apply_mask_material_for_layout_OPEN trace material cells active) (aspis_prover.state_only_hiding.apply_mask_material_for_layout trace material cells active)

def install (c : Leaves) (frames : PV_EVH_OperatorFrames.Frames) : PV_EVH_OpApplyMaterial.Callees where
  op132_OPEN := c.op132_OPEN
  op12_OPEN := PV_EVH_OperatorFrames.mapErr frames
  pool_v1_pair_forest_copy_active_rows_OPEN := c.pool_v1_pair_forest_copy_active_rows_OPEN
  apply_mask_material_for_layout_OPEN := c.apply_mask_material_for_layout_OPEN

theorem install_fixed (c : Leaves) (hc : Compatible c)
    (frames : PV_EVH_OperatorFrames.Frames) (hf : PV_EVH_OperatorFrames.Compatible frames)
    (selected : PV_EVH_OperatorFrames.Selection (inferInstance : ExternalFuns)) :
    PV_EVH_OpApplyMaterial.Compatible (install c frames) where
  op132_fixed := hc.op132_fixed
  op12_fixed := fun inst r closure => PV_EVH_OperatorFrames.mapErr_fixed _ selected frames hf inst r closure
  pool_v1_pair_forest_copy_active_rows_fixed := hc.pool_v1_pair_forest_copy_active_rows_fixed
  apply_mask_material_for_layout_fixed := hc.apply_mask_material_for_layout_fixed

#print axioms install_fixed
end ApplyMaterial

namespace PrivateSalts
structure Leaves where
  FIBRE_COUNT_OPEN : P (Std.Usize)
  op32_OPEN : ∀ {T : Type} (A : Type) (arg0 : (alloc.vec.Vec T)) (arg1 : Std.Usize), P (((core.result.Result Unit alloc.collections.TryReserveError) × (alloc.vec.Vec T)))
  derive_private_salts_loop_OPEN : ∀ (reserved : aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets)
  (context : aspis_core.state_only_hiding.StateOnlyHidingContext)
  (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize))
  (tag : Std.U8) (count : Std.Usize)
  (result : core.result.Result (alloc.vec.Vec (Array Std.U8 32#usize))
  verifier.Error) (index : Std.Usize), P ((core.result.Result (alloc.vec.Vec (Array Std.U8 32#usize))
    verifier.Error))

structure Compatible (c : Leaves) : Prop where
  FIBRE_COUNT_fixed : FinishedView (c.FIBRE_COUNT_OPEN) (aspis_core.r0.FIBRE_COUNT)
  op32_fixed : ∀ {T : Type} (A : Type) (arg0 : (alloc.vec.Vec T)) (arg1 : Std.Usize), FinishedView (c.op32_OPEN A arg0 arg1) (alloc.vec.Vec.try_reserve_exact A arg0 arg1)
  derive_private_salts_loop_fixed : ∀ (reserved : aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets)
  (context : aspis_core.state_only_hiding.StateOnlyHidingContext)
  (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize))
  (tag : Std.U8) (count : Std.Usize)
  (result : core.result.Result (alloc.vec.Vec (Array Std.U8 32#usize))
  verifier.Error) (index : Std.Usize), FinishedView (c.derive_private_salts_loop_OPEN reserved context hash tag count result index) (prover.derive_private_salts_loop reserved context hash tag count result index)

def install (c : Leaves) (frames : PV_EVH_OperatorFrames.Frames) : PV_EVH_OpPrivateSalts.Callees where
  FIBRE_COUNT_OPEN := c.FIBRE_COUNT_OPEN
  op32_OPEN := c.op32_OPEN
  op12_OPEN := PV_EVH_OperatorFrames.mapErr frames
  derive_private_salts_loop_OPEN := c.derive_private_salts_loop_OPEN
  op11_OPEN := PV_EVH_OperatorFrames.map frames

theorem install_fixed (c : Leaves) (hc : Compatible c)
    (frames : PV_EVH_OperatorFrames.Frames) (hf : PV_EVH_OperatorFrames.Compatible frames)
    (selected : PV_EVH_OperatorFrames.Selection (inferInstance : ExternalFuns)) :
    PV_EVH_OpPrivateSalts.Compatible (install c frames) where
  FIBRE_COUNT_fixed := hc.FIBRE_COUNT_fixed
  op32_fixed := hc.op32_fixed
  op12_fixed := fun inst r closure => PV_EVH_OperatorFrames.mapErr_fixed _ selected frames hf inst r closure
  derive_private_salts_loop_fixed := hc.derive_private_salts_loop_fixed
  op11_fixed := fun inst r closure => PV_EVH_OperatorFrames.map_fixed _ selected frames hf inst r closure

#print axioms install_fixed
end PrivateSalts

namespace PrepareOpening
structure Leaves where
  traitNe_OPEN : ∀ {T U : Type} (inst : core.cmp.PartialEq T U) (a : T) (b : U), P (Bool)
  opening_coefficients_OPEN : ∀ (variant : transport.Variant)
  (messages : Slice (Array aspis_core.field.wide_exact.WideExact 1024#usize)), P ((alloc.vec.Vec (Array aspis_core.field.wide_exact.WideExact
    1024#usize)))
  op45_OPEN : ∀ (arg0 : aspis_core.field.QM31), P (aspis_core.field.wide_exact.WideExact)
  opening_claim_bytes_OPEN : ∀ (coefficients : Slice (Array aspis_core.field.wide_exact.WideExact
  1024#usize))
  (z1 : aspis_core.r0.domain.Point aspis_core.field.wide_exact.WideExact), P ((alloc.vec.Vec Std.U8))
  state_OPEN : ∀ {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H)
  (self : host_wire.SemanticTranscript H), P ((Array Std.U8 32#usize))
  new_OPEN : ∀ {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H)
  (hash : H) (semantic_state : Array Std.U8 32#usize)
  (variant : transport.Variant), P ((host_transcript.Transcript H))
  scalar_OPEN : ∀ {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H)
  (self : host_transcript.Transcript H) (row : Std.U8) (payload : Slice Std.U8)
  (nonzero : Bool), P ((aspis_core.field.wide_exact.WideExact × (host_transcript.Transcript
    H)))
  opening_batch_OPEN : ∀ (coefficients : Slice (Array aspis_core.field.wide_exact.WideExact
  1024#usize)) (gamma : aspis_core.field.wide_exact.WideExact), P ((alloc.vec.Vec aspis_core.field.wide_exact.WideExact))
  op252_OPEN : ∀ (arg0 : transport.Variant) (arg1 : (Array aspis_core.field.QM31 10#usize)) (arg2 : (Array aspis_core.circle.SecureCirclePoint 2#usize)), P ((core.result.Result weights.Weights verifier.Error))
  opening_inactive_OPEN : ∀ (q : Slice aspis_core.field.wide_exact.WideExact) (w : weights.Weights), P (aspis_core.field.wide_exact.WideExact)
  op51_OPEN : ∀ (arg0 : aspis_core.field.wide_exact.WideExact), P ((Array Std.U8 32#usize))
  op251_OPEN : ∀ (arg0 : weights.Weights) (arg1 : aspis_core.field.wide_exact.WideExact), P ((core.result.Result (alloc.vec.Vec aspis_core.field.wide_exact.WideExact) verifier.Error))
  round_OPEN : ∀ (q : Slice aspis_core.field.wide_exact.WideExact)
  (w : Slice aspis_core.field.wide_exact.WideExact), P ((Array aspis_core.field.wide_exact.WideExact 7#usize))
  encoded_slice_OPEN : ∀ (values : Slice aspis_core.field.wide_exact.WideExact), P ((alloc.vec.Vec Std.U8))
  fold_OPEN : ∀ (q : Slice aspis_core.field.wide_exact.WideExact)
  (alpha : aspis_core.field.wide_exact.WideExact) (dual : Bool), P ((alloc.vec.Vec aspis_core.field.wide_exact.WideExact))
  evaluate_OPEN : ∀ {T : Type} (aspis_corer0scalarCodeFieldInst : aspis_core.r0.scalar.CodeField
  T) (self : host_commitment.EncodingDomain) (coefficients : Slice T)
  (depth : Std.Usize), P ((core.result.Result (alloc.vec.Vec T) aspis_core.r0.Error))

structure Compatible (c : Leaves) : Prop where
  traitNe_fixed : ∀ {T U : Type} (inst : core.cmp.PartialEq T U) (a : T) (b : U), FinishedView (c.traitNe_OPEN inst a b) (core.cmp.PartialEq.ne.trait_default inst a b)
  opening_coefficients_fixed : ∀ (variant : transport.Variant)
  (messages : Slice (Array aspis_core.field.wide_exact.WideExact 1024#usize)), FinishedView (c.opening_coefficients_OPEN variant messages) (prover.opening_coefficients variant messages)
  op45_fixed : ∀ (arg0 : aspis_core.field.QM31), FinishedView (c.op45_OPEN arg0) (aspis_core.field.wide_exact.WideExact.from_qm31 arg0)
  opening_claim_bytes_fixed : ∀ (coefficients : Slice (Array aspis_core.field.wide_exact.WideExact
  1024#usize))
  (z1 : aspis_core.r0.domain.Point aspis_core.field.wide_exact.WideExact), FinishedView (c.opening_claim_bytes_OPEN coefficients z1) (prover.opening_claim_bytes coefficients z1)
  state_fixed : ∀ {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H)
  (self : host_wire.SemanticTranscript H), FinishedView (c.state_OPEN aspis_coredigestDigest32Inst self) (host_wire.SemanticTranscript.impl.state aspis_coredigestDigest32Inst self)
  new_fixed : ∀ {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H)
  (hash : H) (semantic_state : Array Std.U8 32#usize)
  (variant : transport.Variant), FinishedView (c.new_OPEN aspis_coredigestDigest32Inst hash semantic_state variant) (host_transcript.Transcript.new aspis_coredigestDigest32Inst hash semantic_state variant)
  scalar_fixed : ∀ {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H)
  (self : host_transcript.Transcript H) (row : Std.U8) (payload : Slice Std.U8)
  (nonzero : Bool), FinishedView (c.scalar_OPEN aspis_coredigestDigest32Inst self row payload nonzero) (host_transcript.Transcript.scalar aspis_coredigestDigest32Inst self row payload nonzero)
  opening_batch_fixed : ∀ (coefficients : Slice (Array aspis_core.field.wide_exact.WideExact
  1024#usize)) (gamma : aspis_core.field.wide_exact.WideExact), FinishedView (c.opening_batch_OPEN coefficients gamma) (prover.opening_batch coefficients gamma)
  op252_fixed : ∀ (arg0 : transport.Variant) (arg1 : (Array aspis_core.field.QM31 10#usize)) (arg2 : (Array aspis_core.circle.SecureCirclePoint 2#usize)), FinishedView (c.op252_OPEN arg0 arg1 arg2) (weights.Weights.new arg0 arg1 arg2)
  opening_inactive_fixed : ∀ (q : Slice aspis_core.field.wide_exact.WideExact) (w : weights.Weights), FinishedView (c.opening_inactive_OPEN q w) (prover.opening_inactive q w)
  op51_fixed : ∀ (arg0 : aspis_core.field.wide_exact.WideExact), FinishedView (c.op51_OPEN arg0) (aspis_core.field.wide_exact.WideExact.to_le_bytes arg0)
  op251_fixed : ∀ (arg0 : weights.Weights) (arg1 : aspis_core.field.wide_exact.WideExact), FinishedView (c.op251_OPEN arg0 arg1) (weights.Weights.materialize arg0 arg1)
  round_fixed : ∀ (q : Slice aspis_core.field.wide_exact.WideExact)
  (w : Slice aspis_core.field.wide_exact.WideExact), FinishedView (c.round_OPEN q w) (prover.round q w)
  encoded_slice_fixed : ∀ (values : Slice aspis_core.field.wide_exact.WideExact), FinishedView (c.encoded_slice_OPEN values) (prover.encoded_slice values)
  fold_fixed : ∀ (q : Slice aspis_core.field.wide_exact.WideExact)
  (alpha : aspis_core.field.wide_exact.WideExact) (dual : Bool), FinishedView (c.fold_OPEN q alpha dual) (prover.fold q alpha dual)
  evaluate_fixed : ∀ {T : Type} (aspis_corer0scalarCodeFieldInst : aspis_core.r0.scalar.CodeField
  T) (self : host_commitment.EncodingDomain) (coefficients : Slice T)
  (depth : Std.Usize), FinishedView (c.evaluate_OPEN aspis_corer0scalarCodeFieldInst self coefficients depth) (host_commitment.EncodingDomain.evaluate aspis_corer0scalarCodeFieldInst self coefficients depth)

def install (c : Leaves) (frames : PV_EVH_OperatorFrames.Frames) : PV_EVH_OpPrepareOpening.Callees where
  traitNe_OPEN := c.traitNe_OPEN
  opening_coefficients_OPEN := c.opening_coefficients_OPEN
  op45_OPEN := c.op45_OPEN
  opening_claim_bytes_OPEN := c.opening_claim_bytes_OPEN
  state_OPEN := c.state_OPEN
  new_OPEN := c.new_OPEN
  scalar_OPEN := c.scalar_OPEN
  opening_batch_OPEN := c.opening_batch_OPEN
  op252_OPEN := c.op252_OPEN
  opening_inactive_OPEN := c.opening_inactive_OPEN
  op51_OPEN := c.op51_OPEN
  op251_OPEN := c.op251_OPEN
  round_OPEN := c.round_OPEN
  encoded_slice_OPEN := c.encoded_slice_OPEN
  fold_OPEN := c.fold_OPEN
  evaluate_OPEN := c.evaluate_OPEN
  op12_OPEN := PV_EVH_OperatorFrames.mapErr frames

theorem install_fixed (c : Leaves) (hc : Compatible c)
    (frames : PV_EVH_OperatorFrames.Frames) (hf : PV_EVH_OperatorFrames.Compatible frames)
    (selected : PV_EVH_OperatorFrames.Selection (inferInstance : ExternalFuns)) :
    PV_EVH_OpPrepareOpening.Compatible (install c frames) where
  traitNe_fixed := hc.traitNe_fixed
  opening_coefficients_fixed := hc.opening_coefficients_fixed
  op45_fixed := hc.op45_fixed
  opening_claim_bytes_fixed := hc.opening_claim_bytes_fixed
  state_fixed := hc.state_fixed
  new_fixed := hc.new_fixed
  scalar_fixed := hc.scalar_fixed
  opening_batch_fixed := hc.opening_batch_fixed
  op252_fixed := hc.op252_fixed
  opening_inactive_fixed := hc.opening_inactive_fixed
  op51_fixed := hc.op51_fixed
  op251_fixed := hc.op251_fixed
  round_fixed := hc.round_fixed
  encoded_slice_fixed := hc.encoded_slice_fixed
  fold_fixed := hc.fold_fixed
  evaluate_fixed := hc.evaluate_fixed
  op12_fixed := fun inst r closure => PV_EVH_OperatorFrames.mapErr_fixed _ selected frames hf inst r closure

#print axioms install_fixed
end PrepareOpening

namespace PublishCompact
structure Leaves where
  op242_OPEN : P (Std.Usize)
  op245_OPEN : P ((Array Std.U8 8#usize))
  extendFromSlice_OPEN : ∀ {T : Type} (inst : core.clone.Clone T) (v : alloc.vec.Vec T) (s : Slice T), P (alloc.vec.Vec T)
  op234_OPEN : ∀ (arg0 : transport.Variant), P (Std.U8)
  compact_semantic_OPEN : ∀ (logical : Slice Std.U8) (out : alloc.vec.Vec Std.U8), P (((core.result.Result Unit compact.CodecError) × (alloc.vec.Vec
    Std.U8)))
  compact_values_OPEN : ∀ (logical : Slice Std.U8) (out : alloc.vec.Vec Std.U8), P (((core.result.Result Unit compact.CodecError) × (alloc.vec.Vec
    Std.U8)))
  op51_OPEN : ∀ (arg0 : aspis_core.field.wide_exact.WideExact), P ((Array Std.U8 32#usize))
  op244_OPEN : P (Std.Usize)
  assert_OPEN : ∀ (condition : Prop) [Decidable condition], P (Unit)
  unwrap_OPEN : ∀ {T : Type} (value : Option T), P (T)
  append_query_openings_OPEN : ∀ (out : alloc.vec.Vec Std.U8) (cc1 : host_commitment.Commitment)
  (cc2 : host_commitment.Commitment) (queries : Array Std.U32 22#usize)
  (folded_word : Slice aspis_core.field.wide_exact.WideExact)
  (folded_salts : host_commitment.PrivateSalts), P ((alloc.vec.Vec Std.U8))
  op243_OPEN : P (Std.Usize)
  append_node_slots_OPEN : ∀ (out : alloc.vec.Vec Std.U8) (cc1 : host_commitment.Commitment)
  (cc2 : host_commitment.Commitment) (tree : host_tree.BinaryTree)
  (queries : Array Std.U32 22#usize), P ((core.result.Result (alloc.vec.Vec Std.U8) verifier.Error))
  withCapacity_OPEN : ∀ (T : Type) (capacity : Usize), P (alloc.vec.Vec T)

structure Compatible (c : Leaves) : Prop where
  op242_fixed : FinishedView (c.op242_OPEN) (compact.PROOF_BYTES)
  op245_fixed : FinishedView (c.op245_OPEN) (compact.MAGIC)
  extendFromSlice_fixed : ∀ {T : Type} (inst : core.clone.Clone T) (v : alloc.vec.Vec T) (s : Slice T), FinishedView (c.extendFromSlice_OPEN inst v s) (alloc.vec.Vec.extend_from_slice inst v s)
  op234_fixed : ∀ (arg0 : transport.Variant), FinishedView (c.op234_OPEN arg0) (transport.Variant.tag arg0)
  compact_semantic_fixed : ∀ (logical : Slice Std.U8) (out : alloc.vec.Vec Std.U8), FinishedView (c.compact_semantic_OPEN logical out) (host_compact.compact_semantic logical out)
  compact_values_fixed : ∀ (logical : Slice Std.U8) (out : alloc.vec.Vec Std.U8), FinishedView (c.compact_values_OPEN logical out) (host_compact.compact_values logical out)
  op51_fixed : ∀ (arg0 : aspis_core.field.wide_exact.WideExact), FinishedView (c.op51_OPEN arg0) (aspis_core.field.wide_exact.WideExact.to_le_bytes arg0)
  op244_fixed : FinishedView (c.op244_OPEN) (compact.OFF_OPENINGS)
  assert_fixed : ∀ (condition : Prop) [Decidable condition], FinishedView (c.assert_OPEN condition) (massert condition)
  unwrap_fixed : ∀ {T : Type} (value : Option T), FinishedView (c.unwrap_OPEN value) (core.option.Option.unwrap value)
  append_query_openings_fixed : ∀ (out : alloc.vec.Vec Std.U8) (cc1 : host_commitment.Commitment)
  (cc2 : host_commitment.Commitment) (queries : Array Std.U32 22#usize)
  (folded_word : Slice aspis_core.field.wide_exact.WideExact)
  (folded_salts : host_commitment.PrivateSalts), FinishedView (c.append_query_openings_OPEN out cc1 cc2 queries folded_word folded_salts) (prover.append_query_openings out cc1 cc2 queries folded_word folded_salts)
  op243_fixed : FinishedView (c.op243_OPEN) (compact.OFF_NODES)
  append_node_slots_fixed : ∀ (out : alloc.vec.Vec Std.U8) (cc1 : host_commitment.Commitment)
  (cc2 : host_commitment.Commitment) (tree : host_tree.BinaryTree)
  (queries : Array Std.U32 22#usize), FinishedView (c.append_node_slots_OPEN out cc1 cc2 tree queries) (prover.append_node_slots out cc1 cc2 tree queries)
  withCapacity_fixed : ∀ (T : Type) (capacity : Usize), FinishedView (c.withCapacity_OPEN T capacity) (Result.ok (alloc.vec.Vec.with_capacity T capacity))

def install (c : Leaves) (frames : PV_EVH_OperatorFrames.Frames) : PV_EVH_OpPublishCompact.Callees where
  op242_OPEN := c.op242_OPEN
  op245_OPEN := c.op245_OPEN
  extendFromSlice_OPEN := c.extendFromSlice_OPEN
  op234_OPEN := c.op234_OPEN
  compact_semantic_OPEN := c.compact_semantic_OPEN
  op12_OPEN := PV_EVH_OperatorFrames.mapErr frames
  compact_values_OPEN := c.compact_values_OPEN
  op51_OPEN := c.op51_OPEN
  op244_OPEN := c.op244_OPEN
  assert_OPEN := c.assert_OPEN
  unwrap_OPEN := c.unwrap_OPEN
  append_query_openings_OPEN := c.append_query_openings_OPEN
  op243_OPEN := c.op243_OPEN
  append_node_slots_OPEN := c.append_node_slots_OPEN
  withCapacity_OPEN := c.withCapacity_OPEN

theorem install_fixed (c : Leaves) (hc : Compatible c)
    (frames : PV_EVH_OperatorFrames.Frames) (hf : PV_EVH_OperatorFrames.Compatible frames)
    (selected : PV_EVH_OperatorFrames.Selection (inferInstance : ExternalFuns)) :
    PV_EVH_OpPublishCompact.Compatible (install c frames) where
  op242_fixed := hc.op242_fixed
  op245_fixed := hc.op245_fixed
  extendFromSlice_fixed := hc.extendFromSlice_fixed
  op234_fixed := hc.op234_fixed
  compact_semantic_fixed := hc.compact_semantic_fixed
  op12_fixed := fun inst r closure => PV_EVH_OperatorFrames.mapErr_fixed _ selected frames hf inst r closure
  compact_values_fixed := hc.compact_values_fixed
  op51_fixed := hc.op51_fixed
  op244_fixed := hc.op244_fixed
  assert_fixed := hc.assert_fixed
  unwrap_fixed := hc.unwrap_fixed
  append_query_openings_fixed := hc.append_query_openings_fixed
  op243_fixed := hc.op243_fixed
  append_node_slots_fixed := hc.append_node_slots_fixed
  withCapacity_fixed := hc.withCapacity_fixed

#print axioms install_fixed
end PublishCompact

namespace PrivateSaltStep
structure Leaves where
  derive_pool_v1_leaf_salt_OPEN : ∀ (self : aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets)
  (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize))
  (context : aspis_core.state_only_hiding.StateOnlyHidingContext)
  (tree_tag : Std.U8) (leaf_index : Std.U32), P ((core.result.Result (Array Std.U8 32#usize)
    aspis_prover.state_only_hiding.StateOnlyMaskBuildError))
  push_OPEN : ∀ {T : Type} (v : alloc.vec.Vec T) (value : T), P (alloc.vec.Vec T)

structure Compatible (c : Leaves) : Prop where
  derive_pool_v1_leaf_salt_fixed : ∀ (self : aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets)
  (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize))
  (context : aspis_core.state_only_hiding.StateOnlyHidingContext)
  (tree_tag : Std.U8) (leaf_index : Std.U32), FinishedView (c.derive_pool_v1_leaf_salt_OPEN self hash context tree_tag leaf_index) (aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets.derive_pool_v1_leaf_salt self hash context tree_tag leaf_index)
  push_fixed : ∀ {T : Type} (v : alloc.vec.Vec T) (value : T), FinishedView (c.push_OPEN v value) (alloc.vec.Vec.push v value)

def install (c : Leaves) (frames : PV_EVH_OperatorFrames.Frames) : PV_EVH_OpPrivateSaltStep.Callees where
  derive_pool_v1_leaf_salt_OPEN := c.derive_pool_v1_leaf_salt_OPEN
  op12_OPEN := PV_EVH_OperatorFrames.mapErr frames
  push_OPEN := c.push_OPEN

theorem install_fixed (c : Leaves) (hc : Compatible c)
    (frames : PV_EVH_OperatorFrames.Frames) (hf : PV_EVH_OperatorFrames.Compatible frames)
    (selected : PV_EVH_OperatorFrames.Selection (inferInstance : ExternalFuns)) :
    PV_EVH_OpPrivateSaltStep.Compatible (install c frames) where
  derive_pool_v1_leaf_salt_fixed := hc.derive_pool_v1_leaf_salt_fixed
  op12_fixed := fun inst r closure => PV_EVH_OperatorFrames.mapErr_fixed _ selected frames hf inst r closure
  push_fixed := hc.push_fixed

#print axioms install_fixed
end PrivateSaltStep
end PV_EVH_OperatorInstall
