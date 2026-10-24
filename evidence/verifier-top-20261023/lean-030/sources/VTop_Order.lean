import VTop_Run
import VTop_Cuts

set_option autoImplicit false
noncomputable section
namespace AspisR1.VTop_Order
open Aeneas Aeneas.Std Result VTop_Stages VTop_Trace VTop_Run VTop_Flow

def tx1Schedule : List Nat := [16,3,4,13,1,7,12,13,15,14,24,5,13,11,10,6,9,8,13]
def tx2CommonSchedule : List Nat := [18,16,17,13,23,22,2,0,15,14,24,5,13,11,10,6,9,21,20,19]
def tx2Schedule : List Nat := [3,13,18,16,17,13,23,22,2,0,15,14,24,5,13,11,10,6,9,21,20,19]

theorem tx1_order (ops : Ops) {Hash : Type}
    (D : aspis_core.digest.Digest32 Hash) (hash : Hash)
    (semantic : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (pub proof : Slice U8) (split : Usize)
    (obs : Option (verifier.Phase → Result Unit)) (saved : alloc.vec.Vec U8)
    (before after : Log)
    (accepted : run ops (tx1 traceEffects D semantic pub proof split hash obs) before = ok (.Ok saved,after)) :
    ids after = ids before ++ tx1Schedule := by
  unfold tx1 at accepted
  repeat' first
  | (solve | cases accepted)
  | (fail_if_no_progress simp only [VTop_Trace.run,VTop_Trace.bind,VTop_Trace.perform,traceEffects,VTop_Trace.thenResult,VTop_Trace.liftResult] at accepted)
  | uncase_result
  | head_reduce accepted
  | split at accepted
  all_goals
    have same := congrArg Prod.snd (Result.ok.inj accepted)
    dsimp only [Prod.snd] at same
    rw [← same]
    simp only [ids,tx1Schedule,List.map_append,List.map_cons,List.map_nil,operationId,List.append_assoc,List.cons_append,List.nil_append]

theorem tx2_common_order (ops : Ops) {Hash : Type}
    (D : aspis_core.digest.Digest32 Hash) (hash : Hash)
    (pub proof checkpoint : Slice U8)
    (obs : Option (verifier.Phase → Result Unit)) (before after : Log)
    (accepted : run ops (tx2_common traceEffects D pub proof checkpoint hash obs)
      before = ok (.Ok (),after)) :
    ids after = ids before ++ tx2CommonSchedule := by
  unfold tx2_common at accepted
  repeat' first
  | (solve | cases accepted)
  | (fail_if_no_progress simp only [run_bind,run_perform,run_lift,run_pure,traceEffects,VTop_Trace.bind,thenResult_assoc,thenResult_ok] at accepted)
  | uncase_result
  | head_reduce accepted
  | split at accepted
  all_goals
    have same := congrArg Prod.snd (Result.ok.inj accepted)
    dsimp only [Prod.snd] at same
    rw [← same]
    simp only [ids,tx2CommonSchedule,List.map_append,List.map_cons,List.map_nil,operationId,List.append_assoc,List.cons_append,List.nil_append]


attribute [local irreducible] tx2_common

theorem tx2_order (ops : Ops) {Hash : Type}
    (D : aspis_core.digest.Digest32 Hash) (hash : Hash)
    (pub proof checkpoint : Slice U8)
    (obs : Option (verifier.Phase → Result Unit)) (before after : Log)
    (accepted : run ops (tx2_authenticated traceEffects D pub proof checkpoint hash obs)
      before = ok (.Ok (),after)) :
    ids after = ids before ++ tx2Schedule := by
  unfold tx2_authenticated at accepted
  repeat' first
  | (solve | cases accepted)
  | (fail_if_no_progress simp only [run_bind,run_perform,run_lift,run_pure,traceEffects,VTop_Trace.bind,thenResult_assoc,thenResult_ok] at accepted)
  | uncase_result
  | head_reduce accepted
  | split at accepted
  all_goals
    have tail := tx2_common_order ops D hash pub proof checkpoint obs _ after accepted
    simpa only [ids,tx2CommonSchedule,tx2Schedule,List.map_append,List.map_cons,List.map_nil,
      operationId,List.append_assoc,List.cons_append,List.nil_append] using tail

/-- Every accepted extracted TX1 has a typed execution in source order.
The trace records complete arguments and returns, rather than just these IDs. -/
theorem accepted_tx1 (ops : Ops) {Hash : Type}
    (D : aspis_core.digest.Digest32 Hash) (hash : Hash)
    (semantic : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (pub proof : Slice U8) (split : Usize)
    (obs : Option (verifier.Phase → Result Unit)) (saved : alloc.vec.Vec U8)
    (accepted : verifier.candidate.tx1 ops D semantic pub proof split hash obs = ok (.Ok saved)) :
    ∃ after, run ops (tx1 traceEffects D semantic pub proof split hash obs) [] = ok (.Ok saved,after) ∧
      ids after = tx1Schedule := by
  have erased := VTop_Erasure.tx1_erasure ops D hash semantic pub proof split obs
  rw [accepted] at erased
  obtain ⟨after,success⟩ := accepted_execution ops _ [] (core.result.Result.Ok saved : core.result.Result _ verifier.Error) erased
  exact ⟨after,success,tx1_order ops D hash semantic pub proof split obs saved [] after success⟩

theorem accepted_tx2 (ops : Ops) {Hash : Type}
    (D : aspis_core.digest.Digest32 Hash) (hash : Hash)
    (pub proof checkpoint : Slice U8) (obs : Option (verifier.Phase → Result Unit))
    (accepted : verifier.candidate.tx2_authenticated ops D pub proof checkpoint hash obs = ok (.Ok ())) :
    ∃ after, run ops (tx2_authenticated traceEffects D pub proof checkpoint hash obs) [] = ok (.Ok (),after) ∧
      ids after = tx2Schedule := by
  have erased := VTop_Erasure.tx2_authenticated_erasure ops D hash pub proof checkpoint obs
  rw [accepted] at erased
  obtain ⟨after,success⟩ := accepted_execution ops _ [] (core.result.Result.Ok () : core.result.Result Unit verifier.Error) erased
  exact ⟨after,success,tx2_order ops D hash pub proof checkpoint obs [] after success⟩

#print axioms tx1_order
#print axioms tx2_common_order
#print axioms tx2_order
#print axioms accepted_tx1
#print axioms accepted_tx2
end AspisR1.VTop_Order
end
