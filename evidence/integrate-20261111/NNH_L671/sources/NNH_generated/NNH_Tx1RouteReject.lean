import NNH_Tx1RouteCompare
set_option autoImplicit false
noncomputable section
namespace NNH_Tx1RouteReject
open Aeneas Aeneas.Std AspisR1 AdapterRw

theorem source (ops : Ops) (program : solana_pubkey.Pubkey)
 (xs : Slice r1_pool_adapter.owned.OwnedAccount) (data : Slice U8) (first second : Bool)
 (compare0 : ops.op1 core.cmp.PartialEqU8 data (Array.make 2#usize [3#u8,10#u8])=.ok first)
 (compare1 : ops.op1 core.cmp.PartialEqU8 data (Array.make 2#usize [3#u8,11#u8])=.ok second)
 (bad : (!first && !second || (Slice.len xs != 3#usize))=true) :
 r1_pool_adapter.owned.stage1_owned ops program xs data=.ok (.Err solana_program_error.ProgramError.InvalidInstructionData) := by
 cases first <;> cases second <;>
  cases size : (Slice.len xs != 3#usize) <;>
  simp only [Bool.not_false,Bool.not_true,Bool.false_and,Bool.true_and,
   Bool.false_or,Bool.true_or,size,Bool.false_eq_true] at bad
 all_goals
  unfold r1_pool_adapter.owned.stage1_owned
  simp only [compare0,compare1,bind_tc_ok,Bool.false_eq_true,if_false,if_true,size]
#print axioms source
end NNH_Tx1RouteReject
