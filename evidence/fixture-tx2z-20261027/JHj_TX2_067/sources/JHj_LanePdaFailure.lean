import JHj_LanePda
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHj_LanePdaFailure
open Aeneas Aeneas.Std Result
open _root_.AdapterRw

theorem source  (ops : Ops)
    (verifier_program pool_program : solana_pubkey.Pubkey) (output_lane : U8) (current_slot : U64)
    (master_account checkpoint_account lane_account registry_account entry_account : r1_pool_adapter.owned.OwnedAccount)
    (val1 : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1)
    (p : solana_pubkey.Pubkey)
    (val4 : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestCheckpointV1) (p2 : solana_pubkey.Pubkey)
    (val7 : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestLaneStateV1) (s10 : Slice (Slice U8))
    (error : Aeneas.Std.Error)
    (rejected : ops.op38 s10 pool_program=.fail error) :
    JHj_LanePda.run ops verifier_program pool_program output_lane current_slot master_account checkpoint_account lane_account registry_account entry_account val1 p val4 p2 val7 s10=
    .fail error := by
  unfold JHj_LanePda.run
  rw [rejected]
  rfl
#print axioms source
end AspisR1.JHj_LanePdaFailure
end
