import Aeneas
import NNH_CorrectConfiguration
import NNH_HostSeed
import NNH_HostCtx
import NNH_Tx2SourceConfiguration
import PRVEq_AdapterStage1_o1
open Aeneas Aeneas.Std Result ControlFlow Error
open AspisR1
set_option autoImplicit false
noncomputable section
namespace PCVO_S1
open AdapterRw AdapterRw.PCVK_S1

/-- The externals read off the Ops: every field is the gate counterpart of the Ops (organisation, see PCVO_HANDOFF.md). -/
def xOf (ops : AdapterRw.Ops) : Ext := {
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
  }

theorem bound (ops : AdapterRw.Ops) : Bound ops (xOf ops) := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ => rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem generic_stage1_owned (ops : AdapterRw.Ops) :
    AdapterRw.PCVK_S1.r1_pool_adapter.owned.stage1_owned (xOf ops) = AdapterRw.r1_pool_adapter.owned.stage1_owned ops :=
  PRVEq.AdapterStage1_k1.r1_pool_adapter_owned_stage1_owned_eq (bound ops)

theorem generic_data (ops : AdapterRw.Ops) :
    AdapterRw.PCVK_S1.r1_pool_adapter.owned.OwnedAccount.data (xOf ops) = AdapterRw.r1_pool_adapter.owned.OwnedAccount.data ops :=
  PRVEq.AdapterStage1_k1.data_eq (bound ops)

/-- The deployed Adapter Ops of the credited host context: NNH_CorrectConfiguration.sdk (every `missing`). -/
theorem deployed_stage1_owned (missing : IDa_Deployed.Uninstalled NFN_NEW_GeometryDictionary.CE) (env : RSL.Env)
    (err : NFN_NEW_GeometryDictionary.CE) (r : NP6_StdModel.Reservation) :
    AdapterRw.PCVK_S1.r1_pool_adapter.owned.stage1_owned (xOf (NNH_CorrectConfiguration.sdk missing env err r)) =
      AdapterRw.r1_pool_adapter.owned.stage1_owned (NNH_CorrectConfiguration.sdk missing env err r) :=
  generic_stage1_owned _

theorem deployed_stage1_owned_m0 (env : RSL.Env) (err : NFN_NEW_GeometryDictionary.CE) (r : NP6_StdModel.Reservation) :
    AdapterRw.PCVK_S1.r1_pool_adapter.owned.stage1_owned (xOf (NNH_CorrectConfiguration.sdk NNH_HostSeed.m0 env err r)) =
      AdapterRw.r1_pool_adapter.owned.stage1_owned (NNH_CorrectConfiguration.sdk NNH_HostSeed.m0 env err r) :=
  generic_stage1_owned _

theorem deployed_stage1_owned_src (missing : IDa_Deployed.Uninstalled NFN_NEW_GeometryDictionary.CE) (env : RSL.Env)
    (err : NFN_NEW_GeometryDictionary.CE) (r : NP6_StdModel.Reservation) :
    AdapterRw.PCVK_S1.r1_pool_adapter.owned.stage1_owned (xOf (NNH_Tx2SourceConfiguration.sdk missing env err r)) =
      AdapterRw.r1_pool_adapter.owned.stage1_owned (NNH_Tx2SourceConfiguration.sdk missing env err r) :=
  generic_stage1_owned _

/-- The Adapter model of the credited host context (NNH_HostCtx.model1): fresh frozen stage1_owned at xOf = model1 c. -/
theorem host_model1 {W Tx : Type} (c : AspisR1.NNH_HostCtx.Ctx W Tx) :
    AdapterRw.PCVK_S1.r1_pool_adapter.owned.stage1_owned (xOf (AspisR1.NNH_HostCtx.sdk c)) = AspisR1.NNH_HostCtx.model1 c :=
  generic_stage1_owned _

#print axioms bound
#print axioms generic_stage1_owned
#print axioms deployed_stage1_owned
#print axioms deployed_stage1_owned_m0
#print axioms deployed_stage1_owned_src
#print axioms host_model1
end PCVO_S1
