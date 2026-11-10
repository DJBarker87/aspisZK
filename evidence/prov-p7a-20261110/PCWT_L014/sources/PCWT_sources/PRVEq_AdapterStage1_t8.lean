-- PCWT_ discharge for three keys whose only unbound external is the SDK ProgramError::clone (HM-A):
--   AdapterRw.r1_pool_adapter.owned.OwnedAccount.data (AdapterRwModel), NMT_stage1_owned.r1_pool_adapter.owned.OwnedAccount.data, NMT_first.SolanaDigest.Insts.Aspis_coreDigestDigest32.digest.
-- What was bound: the fresh texts (PCVJ_E004 / NMT emissions, frozen 4bb3b3f) call ProgramError::clone (solana-program-error, SDK) and, for the digest, Hash::hashv / Hash::to_bytes (solana-hash, solana-sha256-hasher: SDK).
-- Those are the ONLY externals of these definitions: for the NMT keys they are explicit parameters (the gate takes them as parameters too); for AdapterRw.data the 15 other Ext fields are
-- not used by `data` and are set to the gate's own definitions exactly as PRVEq.AdapterStage1_k1.bound_exists does, for EVERY ops.  Library items besides the SDK: alloc::vec::Vec::deref (HM-D), core Result (HM-C).
import Aeneas
import AdapterRwModel
import PRVEq_AdapterStage1_k4
import PRVEq_NMT_k1
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 200000
set_option maxRecDepth 2048
noncomputable section

namespace PRVEq.AdapterStage1_t8
open AdapterRw AdapterRw.PCVK_S1

/-- the fresh Ext built from an arbitrary Ops; only the ProgramError::clone field (op35, SDK) matters for `data` -/
def xOf (ops : Ops) : Ext where
  aspis_statement_pool_v1_pair_forest_terminal_PoolV1PairForestTerminalStatementV1_semantic_public := AdapterRw.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.semantic_public
  aspis_statement_pool_v1_pair_forest_terminal_validate_pool_v1_pair_forest_terminal_statement_v1 := ops.op21
  aspis_statement_pool_v1_pair_forest_terminal_PoolV1PairForestTerminalStatementV1_common := AdapterRw.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.common
  aspis_statement_pool_v1_pair_terminal_encode_pool_v1_pair_verified_afterstate_v1 := ops.op24
  aspis_statement_pool_v1_pair_terminal_POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES := AdapterRw.aspis_statement.pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES ops
  solana_program_error_ProgramError_Insts_CoreCloneClone_clone := ops.op35
  r1_pool_adapter_owned_require_verifier_checkpoint := AdapterRw.r1_pool_adapter.owned.require_verifier_checkpoint ops
  r1_pool_adapter_owned_require_distinct_accounts := fun {N} => @AdapterRw.r1_pool_adapter.owned.require_distinct_accounts ops N
  r1_pool_adapter_owned_require_readonly_buffer := AdapterRw.r1_pool_adapter.owned.require_readonly_buffer
  r1_pool_adapter_decode_public_statement_box := ops.op47
  aspis_r1_cost_probe_transport_Variant_tag := AdapterRw.aspis_r1_cost_probe.transport.Variant.tag
  aspis_r1_cost_probe_verifier_PROOF_BYTES := AdapterRw.aspis_r1_cost_probe.verifier.PROOF_BYTES
  Slice_Insts_CoreCmpPartialEqArray_ne := @ops.op0
  Slice_Insts_CoreCmpPartialEqArray_eq := @ops.op1
  r1_pool_adapter_owned_require_zero := AdapterRw.r1_pool_adapter.owned.require_zero
  first_decoded := AdapterRw.first_decoded ops
    

theorem boundOf (ops : Ops) : Bound ops (xOf ops) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ => rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem OwnedAccount_data_frozen (ops : Ops) :
    AdapterRw.PCVK_S1.r1_pool_adapter.owned.OwnedAccount.data (xOf ops) = AdapterRw.r1_pool_adapter.owned.OwnedAccount.data ops :=
  PRVEq.AdapterStage1_k1.data_eq (boundOf ops)

end PRVEq.AdapterStage1_t8

namespace NMT_first
theorem PRVEq_NMT_t8_digest_sdk_params
    (to_bytes : solana_hash.Hash → Result (Array Std.U8 32#usize))
    (hashv : (Slice (Slice Std.U8)) → Result solana_hash.Hash) :
    @NMT_first.PRVFresh_k1.SolanaDigest.Insts.Aspis_coreDigestDigest32.digest to_bytes hashv =
    @NMT_first.SolanaDigest.Insts.Aspis_coreDigestDigest32.digest to_bytes hashv :=
  congrFun (congrFun PRVEq.NMT_first.digest_k1 to_bytes) hashv
end NMT_first

namespace NMT_stage1_owned
theorem PRVEq_NMT_t8_data_sdk_clone
    (clone : solana_program_error.ProgramError → Result solana_program_error.ProgramError) :
    @NMT_stage1_owned.PRVFresh_k1.r1_pool_adapter.owned.OwnedAccount.data clone =
    @NMT_stage1_owned.r1_pool_adapter.owned.OwnedAccount.data clone :=
  congrFun PRVEq.NMT_stage1_owned.data_k1 clone
end NMT_stage1_owned

#print axioms PRVEq.AdapterStage1_t8.OwnedAccount_data_frozen
#print axioms NMT_first.PRVEq_NMT_t8_digest_sdk_params
#print axioms NMT_stage1_owned.PRVEq_NMT_t8_data_sdk_clone
