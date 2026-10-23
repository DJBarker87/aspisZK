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

theorem run_liftM (ops : Ops) {A : Type} (r : Result A) (log : Log) :
    run ops (liftM r : Code A) log = thenResult r (fun a => ok (a,log)) := by
  cases r <;> rfl

theorem run_perform (ops : Ops) {A : Type} (call : Call A) (log : Log) :
    run ops (perform call) log = thenResult (invoke ops call) (fun a =>
      ok (a,log ++ [.returned call a])) := rfl

universe u v w
theorem then_assoc {A : Type u} {B : Type v} {C : Type w}
    (r : Result A) (f : A → Result B) (g : B → Result C) :
    thenResult (thenResult r f) g = thenResult r (fun a => thenResult (f a) g) := by
  cases r <;> rfl

theorem then_ok {A : Type u} {B : Type v} (a : A) (f : A → Result B) :
    thenResult (ok a) f = f a := rfl

theorem second_occurrence (ops : Ops) (program : solana_pubkey.Pubkey)
    (accounts : Slice Cuts.Account) (data : Slice U8)
    (slot : core.result.Result U64 Cuts.PE) (log : Log)
    (execution : run ops (S2W_Outer.stage2_owned ops S2W_Outer.traceEffects program accounts data slot)
      [] = ok (.Ok (),log)) : tags log = [true] := by
  simp only [S2W_Outer.stage2_owned,S2W_TraceFacts.run_bind,run_pure,run_lift,run_liftM,
    S2W_Outer.traceEffects,run_perform,then_assoc,then_ok, S2W_Trace.bind] at execution
  repeat' first
  | (solve | cases execution)
  | (fail_if_no_progress simp only [S2W_TraceFacts.run_bind,run_pure,run_lift,run_liftM,run_perform,then_assoc,then_ok, S2W_Trace.bind] at execution)
  | uncase_result
  | head_reduce execution
  | split at execution
  all_goals have logs := congrArg Prod.snd (Result.ok.inj execution)
  all_goals rw [← logs]
  all_goals simp [tags,mark]

#print axioms run_pure
#print axioms run_lift
#print axioms run_liftM
#print axioms run_perform
#print axioms then_assoc
#print axioms then_ok
#print axioms second_occurrence
end AspisR1.S2W_OuterOccurrences
