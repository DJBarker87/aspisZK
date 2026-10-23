import S2W_Observation
import AdapterRwCuts

/-! Actual outer source occurrence inventory; children remain opaque. -/
set_option autoImplicit false
namespace AspisR1.S2W_OuterOccurrences
open Aeneas Aeneas.Std Result S2W_Trace _root_.AdapterRw AspisR1.AdapterRw

def mark : S2W_Trace.Event → Option Bool
  | .returned (.op10 _ _ _ _ _ _ _) _ => some false
  | .returned (.op11 _ _ _ _ _ _) _ => some true
  | _ => none

def tags (log : Log) : List Bool := log.filterMap mark

attribute [local irreducible] _root_.AdapterRw.r1_pool_adapter.owned.require_distinct_accounts
  _root_.AdapterRw.r1_pool_adapter.owned.require_readonly_buffer _root_.AdapterRw.r1_pool_adapter.owned.require_verifier_checkpoint
  _root_.AdapterRw.r1_pool_adapter.owned.OwnedAccount.data _root_.AdapterRw.r1_pool_adapter.owned.require_zero
  _root_.AdapterRw.r1_pool_adapter.owned.validate_asq8

theorem run_pure (ops : Ops) {A : Type} (a : A) (log : Log) :
    run ops (pure a) log = ok (a,log) := rfl

theorem run_lift (ops : Ops) {A : Type} (r : Result A) (log : Log) :
    run ops (monadLift r : Code A) log = thenResult r (fun a => ok (a,log)) := by
  cases r <;> rfl

theorem run_perform (ops : Ops) {A : Type} (call : Call A) (log : Log) :
    run ops (perform call) log = thenResult (invoke ops call) (fun a =>
      ok (a,log ++ [.returned call a])) := rfl

theorem second_occurrence (ops : Ops) (program : solana_pubkey.Pubkey)
    (accounts : Slice Cuts.Account) (data : Slice U8)
    (slot : core.result.Result U64 Cuts.PE) (log : Log)
    (execution : run ops (S2W_Outer.stage2_owned ops S2W_Outer.traceEffects program accounts data slot)
      [] = ok (.Ok (),log)) : tags log = [true] := by
  simp only [S2W_Outer.stage2_owned,S2W_TraceFacts.run_bind,run_pure,run_lift,
    S2W_Outer.traceEffects,run_perform, S2W_Trace.bind] at execution
  repeat' first
  | (solve | cases execution)
  | uncase_result
  | head_reduce execution
  | split at execution
  all_goals try { have same := Result.ok.inj execution; cases same }
  all_goals simp [tags,mark]

#print axioms run_pure
#print axioms run_lift
#print axioms run_perform
#print axioms second_occurrence
end AspisR1.S2W_OuterOccurrences
