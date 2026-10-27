import JHj_MasterPda
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHj_MasterPdaError
open Aeneas Aeneas.Std Result
open _root_.AdapterRw

theorem source  (ops : Ops)
    (verifier_program pool_program : solana_pubkey.Pubkey) (output_lane : U8) (current_slot : U64)
    (master_account checkpoint_account lane_account registry_account entry_account : r1_pool_adapter.owned.OwnedAccount)
    (val1 : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1)
    (p : solana_pubkey.Pubkey) (s2 : Slice (Slice U8))
    (error : solana_pubkey.PubkeyError)
    (rejected : ops.op38 s2 pool_program=ok (.Err error)) :
    JHj_MasterPda.run ops verifier_program pool_program output_lane current_slot master_account checkpoint_account lane_account registry_account entry_account val1 p s2=
    ok (.Err solana_program_error.ProgramError.InvalidAccountData) := by
  unfold JHj_MasterPda.run
  rw [rejected]
  rfl
#print axioms source
end AspisR1.JHj_MasterPdaError
end
