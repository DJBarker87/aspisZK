import VTop_SecondFlow
import VTop_Run
import VTop_Cuts

set_option autoImplicit false
noncomputable section
namespace AspisR1.VTop_SecondOrder
open Aeneas Aeneas.Std Result VTop_Stages VTop_Trace VTop_Run VTop_Flow VTop_SecondFlow

def tailSchedule : List Nat := [9,21,20,19]
def commonSchedule : List Nat := [18,16,17,13,23,22,2,0,15,14,24,5,13,11,10,6,9,21,20,19]

theorem tail_order (ops : Ops) (proof : Slice U8) (p : verifier.Prepared)
    (obs : Option (verifier.Phase → Result Unit))
    (inactive : aspis_core.field.wide_exact.WideExact) (round0 folded round1 : Usize)
    (state : verifier.Accumulator × verifier.BatchedWeights) (before after : Log)
    (accepted : run ops (tail traceEffects proof p obs inactive round0 folded round1 state)
      before = ok (.Ok (),after)) : ids after = ids before ++ tailSchedule := by
  unfold tail at accepted
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
    simp only [ids,tailSchedule,List.map_append,List.map_cons,List.map_nil,operationId,List.append_assoc,List.cons_append,List.nil_append]

attribute [local irreducible] tail

theorem common_order (ops : Ops) {Hash : Type}
    (D : aspis_core.digest.Digest32 Hash) (hash : Hash)
    (pub proof checkpoint : Slice U8)
    (obs : Option (verifier.Phase → Result Unit)) (before after : Log)
    (accepted : run ops (VTop_Flow.tx2_common traceEffects D pub proof checkpoint hash obs)
      before = ok (.Ok (),after)) : ids after = ids before ++ commonSchedule := by
  rw [← common_source D hash pub proof checkpoint obs] at accepted
  unfold common at accepted
  repeat' first
  | (solve | cases accepted)
  | (fail_if_no_progress simp only [VTop_Trace.run,VTop_Trace.bind,VTop_Trace.perform,traceEffects,VTop_Trace.thenResult,VTop_Trace.liftResult] at accepted)
  | uncase_result
  | head_reduce accepted
  | split at accepted
  all_goals
    have rest := tail_order ops proof _ obs _ _ _ _ _ _ after accepted
    simpa only [ids,tailSchedule,commonSchedule,List.map_append,List.map_cons,List.map_nil,
      operationId,List.append_assoc,List.cons_append,List.nil_append] using rest

#print axioms tail_order
#print axioms common_order
end AspisR1.VTop_SecondOrder
end
