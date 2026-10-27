import RPz7_Op5T_Marks
set_option autoImplicit false
namespace AspisR1.Op5T_OuterAccepted
open Aeneas Aeneas.Std Result S2W_Trace _root_.AdapterRw AspisR1.AdapterRw S2W_OuterOccurrences

attribute [local irreducible] _root_.AdapterRw.r1_pool_adapter.owned.require_distinct_accounts
  _root_.AdapterRw.r1_pool_adapter.owned.require_readonly_buffer _root_.AdapterRw.r1_pool_adapter.owned.require_verifier_checkpoint
  _root_.AdapterRw.r1_pool_adapter.owned.OwnedAccount.data _root_.AdapterRw.r1_pool_adapter.owned.require_zero
  _root_.AdapterRw.r1_pool_adapter.owned.validate_asq8

def good (ops : AdapterRw.Ops) (log : Log) : Prop :=
  ∀ event ∈ log, mark event ≠ none → Op5T_Marks.accepted ops event

theorem first_good (ops : Ops) (program : solana_pubkey.Pubkey)
    (accounts : Slice Cuts.Account) (data : Slice U8) (saved : alloc.vec.Vec U8)
    (log : Log)
    (execution : run ops (S2W_Outer.stage1_owned ops S2W_Outer.traceEffects program accounts data)
      [] = ok (.Ok saved,log)) : good ops log := by
  simp only [S2W_Outer.stage1_owned,S2W_TraceFacts.run_bind,run_pure,run_lift,run_liftM,
    S2W_Outer.traceEffects,run_perform,S2W_Outer.mapError,S2W_Outer.first_decoded,then_assoc,then_ok, S2W_Trace.bind] at execution
  repeat' first
  | (solve | cases execution)
  | (fail_if_no_progress simp only [S2W_TraceFacts.run_bind,run_pure,run_lift,run_liftM,run_perform,S2W_Outer.mapError,S2W_Outer.first_decoded,then_assoc,then_ok, S2W_Trace.bind] at execution)
  | uncase_result
  | head_reduce execution
  | split at execution
  all_goals have logs := congrArg Prod.snd (Result.ok.inj execution)
  all_goals dsimp only at logs
  all_goals rw [← logs]
  all_goals
    intro event member marked
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false,false_or] at member
    repeat' (rcases member with member | member)
    all_goals try (rcases member with rfl)
    all_goals simp only [mark] at marked
    all_goals try contradiction
    all_goals simp only [Op5T_Marks.accepted,invoke] at *
    all_goals first
      | exact ⟨_,by assumption⟩
      | assumption

theorem second_good (ops : Ops) (program : solana_pubkey.Pubkey)
    (accounts : Slice Cuts.Account) (data : Slice U8)
    (slot : core.result.Result U64 Cuts.PE) (log : Log)
    (execution : run ops (S2W_Outer.stage2_owned ops S2W_Outer.traceEffects program accounts data slot)
      [] = ok (.Ok (),log)) : good ops log := by
  simp only [S2W_Outer.stage2_owned,S2W_TraceFacts.run_bind,run_pure,run_lift,run_liftM,
    S2W_Outer.traceEffects,run_perform,S2W_Outer.mapError,then_assoc,then_ok, S2W_Trace.bind] at execution
  repeat' first
  | (solve | cases execution)
  | (fail_if_no_progress simp only [S2W_TraceFacts.run_bind,run_pure,run_lift,run_liftM,run_perform,S2W_Outer.mapError,then_assoc,then_ok, S2W_Trace.bind] at execution)
  | uncase_result
  | head_reduce execution
  | split at execution
  all_goals have logs := congrArg Prod.snd (Result.ok.inj execution)
  all_goals dsimp only at logs
  all_goals rw [← logs]
  all_goals
    intro event member marked
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false,false_or] at member
    repeat' (rcases member with member | member)
    all_goals try (rcases member with rfl)
    all_goals simp only [mark] at marked
    all_goals try contradiction
    all_goals simp only [Op5T_Marks.accepted,invoke] at *
    all_goals first
      | exact ⟨_,by assumption⟩
      | assumption

#print axioms first_good
#print axioms second_good
end AspisR1.Op5T_OuterAccepted
