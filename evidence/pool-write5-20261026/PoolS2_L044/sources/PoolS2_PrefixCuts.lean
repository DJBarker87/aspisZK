import PoolS2_Prefix
set_option autoImplicit false
namespace AspisR1.PoolS2_PrefixCuts
open Aeneas Aeneas.Std Result PoolS2_Prefix PoolS2_PrefixSource

theorem accepted (accounts : Slice Account) (data : Slice U8) (roles : Roles)
    (h : run accounts data = ok (.Ok roles)) :
    PoolS2_InstructionSource.pair_forest.decode_pair_forest_checkpoint_instruction_v1 data = ok (.Ok ()) ∧
    pair_forest.require_exact_account_count accounts 12#usize = ok (.Ok ()) ∧
    unique accounts = ok (.Ok ()) ∧ select accounts = ok roles ∧
    processor.require_payer_and_system_program roles.payer roles.system = ok (.Ok ()) := by
  unfold run at h
  repeat' first
  | (solve | cases h)
  | uncase_result
  | head_reduce h
  | split at h
  all_goals aesop

#print axioms accepted
end AspisR1.PoolS2_PrefixCuts
