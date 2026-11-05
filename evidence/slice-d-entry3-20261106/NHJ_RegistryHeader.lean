import NHJ_DeployedIds
import NGL_ArrayEquality
set_option autoImplicit false
noncomputable section
namespace NHJ_RegistryHeader
open Aeneas Aeneas.Std Result
abbrev Key := AdapterRw.solana_pubkey.Pubkey
abbrev Account := AdapterRw.r1_pool_adapter.owned.OwnedAccount
abbrev Master := AdapterRw.aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1

def bindHeader {E : Type} (missing : AspisR1.IDa_Deployed.Uninstalled E) :=
  {missing with adapter := {missing.adapter with op13 := ok 1#u8,op39 := fun key => ok key}}

def configuration {E : Type} (missing : AspisR1.IDa_Deployed.Uninstalled E)
    (devnet : Bool) (indexError : E) (reservation : AspisR1.NP6_StdModel.Reservation) :=
  NHJ_DeployedIds.configuration (bindHeader missing) devnet indexError reservation

def Bad (devnet : Bool) (pool : Key) (master : Master) : Prop :=
  pool ≠ NHJ_IdPacket.pool devnet ∨
  master.verifier_policy.flags &&& 1#u8 = 0#u8 ∨
  master.verifier_policy.registry_program ≠ NHJ_IdPacket.registry devnet ∨
  master.verifier_policy.registry_authority ≠ Array.repeat 32#usize 0#u8 ∨
  master.verifier_policy.policy_binding ≠ AdapterRw.r1_pool_adapter.AUDIT_POLICY_BINDING

theorem first_error {E : Type} (missing : AspisR1.IDa_Deployed.Uninstalled E)
    (devnet : Bool) (indexError : E) (reservation : AspisR1.NP6_StdModel.Reservation)
    (verifier pool : Key) (account registry entry : Account) (master : Master) (slot : U64)
    (bad : Bad devnet pool master) :
    AdapterRw.r1_pool_adapter.owned.authenticate_invariant_release_registry
      (configuration missing devnet indexError reservation).adapter verifier pool account master registry entry slot =
      ok (.Err AdapterRw.solana_program_error.ProgramError.InvalidAccountData) := by
  classical
  let ops := (configuration missing devnet indexError reservation).adapter
  have key : ops.op39 pool = ok pool := rfl
  have mask : ops.op13 = ok 1#u8 := rfl
  have poolId : ops.op45 = ok (NHJ_IdPacket.pool devnet) := rfl
  have registryId : ops.op46 = ok (NHJ_IdPacket.registry devnet) := rfl
  change AdapterRw.r1_pool_adapter.owned.authenticate_invariant_release_registry ops _ _ _ _ _ _ _ = _
  unfold AdapterRw.r1_pool_adapter.owned.authenticate_invariant_release_registry
  simp only [key,poolId,registryId,mask,NGL_ArrayEquality.ne_value,bind_tc_ok,lift]
  by_cases h0 : pool = NHJ_IdPacket.pool devnet
  · simp [h0,decide_true,Bool.not_true,Bool.false_eq_true,if_false,mask,bind_tc_ok,lift]
    trace_state
    by_cases h1 : master.verifier_policy.flags &&& 1#u8 = 0#u8
    · trace_state
      simp [h1,if_true]
    · trace_state
      simp [h1,if_false,registryId,bind_tc_ok,NGL_ArrayEquality.ne_value]
      by_cases h2 : master.verifier_policy.registry_program = NHJ_IdPacket.registry devnet
      · simp [h2,decide_true,Bool.not_true,Bool.false_eq_true,if_false,NGL_ArrayEquality.ne_value,bind_tc_ok]
        by_cases h3 : master.verifier_policy.registry_authority = Array.repeat 32#usize 0#u8
        · simp [h3,decide_true,Bool.not_true,Bool.false_eq_true,if_false,NGL_ArrayEquality.ne_value,bind_tc_ok]
          have h4 : master.verifier_policy.policy_binding ≠ AdapterRw.r1_pool_adapter.AUDIT_POLICY_BINDING := by
            simpa [Bad,h0,h1,h2,h3] using bad
          simp [h4,decide_false,Bool.not_false,if_true]
        · simp [h3,decide_false,Bool.not_false,if_true]
      · simp [h2,decide_false,Bool.not_false,if_true]
  · simp [h0,decide_false,Bool.not_false,if_true]
#print axioms first_error
end NHJ_RegistryHeader
