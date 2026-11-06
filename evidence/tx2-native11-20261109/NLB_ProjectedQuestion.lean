import NLB_EventObservation
import NLB_QuestionTrace
set_option autoImplicit false
noncomputable section
namespace NLB_ErrorTransport
open Aeneas Aeneas.Std Result VTop_Stages AspisR1 NJU_CommonObserved

theorem projected_question {A : Type}
 (native source : NJU_Log.Run Event (core.result.Result Unit verifier.Error))
 (nativeTail sourceTail : Unit → NJU_Log.Run Event (core.result.Result A verifier.Error))
 (child : ReplyRel native.result source.result)
 (events : native.events.map projectEvent=source.events.map projectEvent)
 (tail : ∀ u,observeCommon (nativeTail u)=observeCommon (sourceTail u)) :
 observeCommon (questionRun native nativeTail)=observeCommon (questionRun source sourceTail) := by
 rcases native with ⟨nativeReply,nativeEvents⟩
 rcases source with ⟨sourceReply,sourceEvents⟩
 change nativeEvents.map projectEvent=sourceEvents.map projectEvent at events
 change ReplyRel nativeReply sourceReply at child
 cases child with
 | rejected error =>
   change ((fail .panic : Result A),(nativeEvents++[]).map projectEvent)=
    ((fail .panic : Result A),sourceEvents.map projectEvent)
   rw [List.append_nil,events]
 | same =>
   cases nativeReply with
   | fail error => exact Prod.ext rfl events
   | div => exact Prod.ext rfl events
   | ok r =>
     cases r with
     | Err error =>
       change ((fail .panic : Result A),(nativeEvents++[]).map projectEvent)=
        ((fail .panic : Result A),(sourceEvents++[]).map projectEvent)
       rw [List.append_nil,List.append_nil,events]
     | Ok u =>
       change (reject (nativeTail u).result,(nativeEvents++(nativeTail u).events).map projectEvent)=
        (reject (sourceTail u).result,(sourceEvents++(sourceTail u).events).map projectEvent)
       rw [List.map_append,List.map_append,events]
       exact congrArg (fun x : Result A × List Event => (x.1,sourceEvents.map projectEvent++x.2)) (tail u)

theorem merkle_question {A : Type} (proof : Slice U8) (p : verifier.Prepared) (root : Array U8 32#usize)
 (native source : R Unit)
 (nativeTail sourceTail : Unit → NJU_Log.Run Event (core.result.Result A verifier.Error))
 (child : ReplyRel native source)
 (tail : ∀ u,observeCommon (nativeTail u)=observeCommon (sourceTail u)) :
 observeCommon (questionRun (NJU_Log.record (.merkle proof p root) native) nativeTail)=
 observeCommon (questionRun (NJU_Log.record (.merkle proof p root) source) sourceTail) := by
 apply projected_question _ _ _ _ child _ tail
 exact congrArg List.singleton (merkle_event proof p root native source child)
#print axioms projected_question
#print axioms merkle_question
end NLB_ErrorTransport
