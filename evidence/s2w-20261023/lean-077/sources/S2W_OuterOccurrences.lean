import S2W_ExpandedTrace

/-! Actual outer source occurrence inventory; children remain opaque. -/
set_option autoImplicit false
namespace AspisR1.S2W_OuterOccurrences
open Aeneas Aeneas.Std Result S2W_Trace AdapterRw

def mark : S2W_Trace.Event → Option Bool
  | .returned (.op10 _ _ _ _ _ _ _) _ => some false
  | .returned (.op11 _ _ _ _ _ _) _ => some true
  | _ => none

def tags (log : Log) : List Bool := log.filterMap mark

attribute [local irreducible] r1_pool_adapter.owned.require_distinct_accounts
  r1_pool_adapter.owned.require_readonly_buffer r1_pool_adapter.owned.require_verifier_checkpoint
  r1_pool_adapter.owned.OwnedAccount.data r1_pool_adapter.owned.require_zero
  r1_pool_adapter.owned.validate_asq8

theorem first_occurrence (ops : Ops) (program : solana_pubkey.Pubkey)
    (accounts : Slice Cuts.Account) (data : Slice U8) (saved : alloc.vec.Vec U8)
    (log : Log)
    (execution : run ops (S2W_Outer.stage1_owned ops S2W_Outer.traceEffects program accounts data)
      [] = ok (.Ok saved,log)) : tags log = [false] := by
  unfold S2W_Outer.stage1_owned at execution
  repeat' first
  | (solve | cases execution)
  | Cuts.uncase_result
  | Cuts.head_reduce execution
  | split at execution
  all_goals try { have same := Result.ok.inj execution; cases same }
  all_goals simp [tags,mark]

#print axioms first_occurrence
end AspisR1.S2W_OuterOccurrences
