import Aeneas
import NNH_CorrectConfiguration
import NNH_HostSeed
import NNH_Tx2SourceConfiguration
import PRVEq_AdapterStage2_o1
open Aeneas Aeneas.Std Result ControlFlow Error
open AspisR1
set_option autoImplicit false
noncomputable section
namespace PCVO_S2
open AdapterRw AdapterRw.PCVK_S2

theorem bind_ok_id {α : Type} (x : Result α) : (x >>= fun h => ok h) = x := by cases x <;> rfl

/-- The externals read off the Ops, with the hash library fields instantiated by `hashv` (Hash := Array U8 32, to_bytes := ok). -/
def xOf (ops : AdapterRw.Ops) (hashv : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize)) : Ext := {
    Hash := Array Std.U8 32#usize
    aspis_statement_pool_v1_pair_forest_terminal_encode_pool_v1_pair_forest_terminal_statement_v1 := ops.op22
    aspis_statement_pool_v1_pair_forest_terminal_decode_pool_v1_pair_forest_terminal_request_v1 := ops.op23
    aspis_statement_pool_v1_pair_forest_terminal_POOL_V1_PAIR_FOREST_TERMINAL_STATEMENT_BYTES := AdapterRw.aspis_statement.pool_v1.pair_forest_terminal.POOL_V1_PAIR_FOREST_TERMINAL_STATEMENT_BYTES ops
    aspis_statement_pool_v1_pair_forest_terminal_PoolV1PairForestTerminalPaymentV1_nullifier := ops.op20
    aspis_statement_pool_v1_pair_forest_terminal_POOL_V1_PAIR_FOREST_TERMINAL_REQUEST_MAGIC := ok (AdapterRw.aspis_statement.pool_v1.pair_forest_terminal.POOL_V1_PAIR_FOREST_TERMINAL_REQUEST_MAGIC)
    aspis_statement_pool_v1_pair_forest_terminal_POOL_V1_PAIR_FOREST_TERMINAL_REQUEST_BYTES := AdapterRw.aspis_statement.pool_v1.pair_forest_terminal.POOL_V1_PAIR_FOREST_TERMINAL_REQUEST_BYTES
    core_ops_range_RangeFull_Insts_CoreSliceIndexSliceIndexSliceSlice_get_unchecked_mut := @ops.op5
    core_ops_range_RangeFull_Insts_CoreSliceIndexSliceIndexSliceSlice_get_unchecked := @ops.op6
    aspis_statement_pool_v1_pair_forest_accounts_POOL_V1_PAIR_FOREST_ALL_LANES_MASK := ops.op16
    aspis_statement_pool_v1_pair_forest_accounts_pool_v1_pair_forest_output_lane_v1 := ops.op17
    aspis_statement_pool_v1_pair_terminal_POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES := AdapterRw.aspis_statement.pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES ops
    core_ops_range_RangeFull_Insts_CoreSliceIndexSliceIndexSliceSlice_index_mut := @ops.op3
    core_ops_range_RangeFull_Insts_CoreSliceIndexSliceIndexSliceSlice_get_mut := @ops.op7
    core_ops_range_RangeFull_Insts_CoreSliceIndexSliceIndexSliceSlice_index := @ops.op4
    core_ops_range_RangeFull_Insts_CoreSliceIndexSliceIndexSliceSlice_get := @ops.op8
    r1_pool_adapter_owned_authenticate_invariant_release_registry := AdapterRw.r1_pool_adapter.owned.authenticate_invariant_release_registry ops
    solana_program_error_ProgramError_Insts_CoreCloneClone_clone := ops.op35
    solana_pubkey_Pubkey_Insts_CoreConvertAsRefSliceU8_as_ref := ops.op40
    aspis_r1_cost_probe_verifier_candidate_tx2_authenticated := @ops.op11
    solana_pubkey_Pubkey_Insts_CoreCmpPartialEqPubkey_eq := ops.op36
    core_option_Option_Insts_CoreCmpPartialEqOption_eq := @ops.op2
    r1_pool_adapter_owned_require_verifier_checkpoint := AdapterRw.r1_pool_adapter.owned.require_verifier_checkpoint ops
    r1_pool_adapter_owned_require_distinct_accounts := fun {N} => @AdapterRw.r1_pool_adapter.owned.require_distinct_accounts ops N
    r1_pool_adapter_owned_require_readonly_account := AdapterRw.r1_pool_adapter.owned.require_readonly_account ops
    r1_pool_adapter_decode_lane_from_pool_release := ops.op50
    r1_pool_adapter_owned_require_readonly_buffer := AdapterRw.r1_pool_adapter.owned.require_readonly_buffer
    solana_pubkey_Pubkey_create_program_address := ops.op38
    r1_pool_adapter_reconstruct_asq8_statement := ops.op52
    r1_pool_adapter_decode_checkpoint_box := ops.op49
    solana_pubkey_Pubkey_new_from_array := ops.op37
    r1_pool_adapter_decode_master_box := ops.op48
    r1_pool_adapter_scan_proof_buffer := ops.op51
    r1_pool_adapter_pool_program_id := ops.op45
    solana_pubkey_Pubkey_to_bytes := ops.op39
    r1_pool_adapter_emit_result := ops.op53
    solana_sha256_hasher_hashv := hashv
    solana_hash_Hash_to_bytes := fun h => ok h
    core_slice_Slice_first := @ops.op9
    observer := AdapterRw.observer ops
    error := ops.op44
  }

theorem bound (ops : AdapterRw.Ops) (hashv : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize))
    (h42 : ops.op42 = AdapterRw.PCVK_S2.SolanaDigest.Insts.CoreCloneClone.clone)
    (h43 : ops.op43 = fun _ parts => hashv parts) : Bound ops (xOf ops hashv) := by
  have h43' : ops.op43 = AdapterRw.PCVK_S2.SolanaDigest.Insts.Aspis_coreDigestDigest32.digest (xOf ops hashv) := by
    rw [h43]; funext s parts
    unfold AdapterRw.PCVK_S2.SolanaDigest.Insts.Aspis_coreDigestDigest32.digest xOf
    exact (bind_ok_id (hashv parts)).symm
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ => rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, h42, h43⟩

theorem generic_stage2_owned (ops : AdapterRw.Ops) (hashv : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize))
    (h42 : ops.op42 = AdapterRw.PCVK_S2.SolanaDigest.Insts.CoreCloneClone.clone)
    (h43 : ops.op43 = fun _ parts => hashv parts) :
    AdapterRw.PCVK_S2.r1_pool_adapter.owned.stage2_owned (xOf ops hashv) = AdapterRw.r1_pool_adapter.owned.stage2_owned ops :=
  PRVEq.AdapterStage2_k1.r1_pool_adapter_owned_stage2_owned_eq (bound ops hashv h42 h43)

theorem generic_validate_asq8 (ops : AdapterRw.Ops) (hashv : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize))
    (h42 : ops.op42 = AdapterRw.PCVK_S2.SolanaDigest.Insts.CoreCloneClone.clone)
    (h43 : ops.op43 = fun _ parts => hashv parts) :
    AdapterRw.PCVK_S2.r1_pool_adapter.owned.validate_asq8 (xOf ops hashv) = AdapterRw.r1_pool_adapter.owned.validate_asq8 ops :=
  PRVEq.AdapterStage2_k1.r1_pool_adapter_owned_validate_asq8_eq (bound ops hashv h42 h43)

theorem deployed_stage2_owned (missing : IDa_Deployed.Uninstalled NFN_NEW_GeometryDictionary.CE) (env : RSL.Env)
    (err : NFN_NEW_GeometryDictionary.CE) (r : NP6_StdModel.Reservation) :
    AdapterRw.PCVK_S2.r1_pool_adapter.owned.stage2_owned (xOf (NNH_CorrectConfiguration.sdk missing env err r) (LIB_Env.hashv env)) =
      AdapterRw.r1_pool_adapter.owned.stage2_owned (NNH_CorrectConfiguration.sdk missing env err r) :=
  generic_stage2_owned _ _ rfl rfl

theorem deployed_stage2_owned_m0 (env : RSL.Env) (err : NFN_NEW_GeometryDictionary.CE) (r : NP6_StdModel.Reservation) :
    AdapterRw.PCVK_S2.r1_pool_adapter.owned.stage2_owned (xOf (NNH_CorrectConfiguration.sdk NNH_HostSeed.m0 env err r) (LIB_Env.hashv env)) =
      AdapterRw.r1_pool_adapter.owned.stage2_owned (NNH_CorrectConfiguration.sdk NNH_HostSeed.m0 env err r) :=
  generic_stage2_owned _ _ rfl rfl

#print axioms bound
#print axioms generic_stage2_owned
#print axioms generic_validate_asq8
#print axioms deployed_stage2_owned
#print axioms deployed_stage2_owned_m0
end PCVO_S2
