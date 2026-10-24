import VTop_Run
import VTop_Cuts

set_option autoImplicit false
noncomputable section
namespace AspisR1.VTop_Order
open Aeneas Aeneas.Std Result VTop_Stages VTop_Trace VTop_Run VTop_Flow

def tx1Schedule : List Nat := [16,3,4,13,1,7,12,13,15,14,24,5,13,11,10,6,9,8,13]
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
    rw [← same]
    simp only [ids,tx1Schedule,List.map_append,List.map_cons,List.map_nil,operationId]

#print axioms tx1_order
end AspisR1.VTop_Order
end
