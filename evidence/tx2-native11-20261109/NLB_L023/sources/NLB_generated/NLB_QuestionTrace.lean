import NLB_ErrorTransport
set_option autoImplicit false
noncomputable section
namespace NLB_ErrorTransport
open Aeneas Aeneas.Std Result VTop_Stages

def questionRun {E A : Type} (m : NJU_Log.Run E (core.result.Result Unit verifier.Error))
 (next : Unit → NJU_Log.Run E (core.result.Result A verifier.Error)) :
 NJU_Log.Run E (core.result.Result A verifier.Error) := do
 let r ← m
 let cf ← core.result.Result.Insts.CoreOpsTry.branch r
 match cf with
 | .Continue value => next value
 | .Break residual =>
   liftM (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
     A (core.convert.FromSame verifier.Error) residual)

def observeRun {E A : Type} (m : NJU_Log.Run E (core.result.Result A verifier.Error)) :
 Result A × List E := (reject m.result,m.events)

/-- The full child packet supplies the SAME ordered effects/query prefix;
only the explicit returned Err/cohort fail boundary differs. No native Err is
changed or dropped from questionRun itself. -/
theorem question_trace {E A : Type}
 (native source : NJU_Log.Run E (core.result.Result Unit verifier.Error))
 (nativeTail sourceTail : Unit → NJU_Log.Run E (core.result.Result A verifier.Error))
 (child : ReplyRel native.result source.result) (events : native.events=source.events)
 (tail : ∀ u,observeRun (nativeTail u)=observeRun (sourceTail u)) :
 observeRun (questionRun native nativeTail)=observeRun (questionRun source sourceTail) := by
 rcases native with ⟨nativeReply,nativeEvents⟩
 rcases source with ⟨sourceReply,sourceEvents⟩
 change nativeEvents=sourceEvents at events
 subst sourceEvents
 change ReplyRel nativeReply sourceReply at child
 cases child with
 | rejected error => rfl
 | same =>
   cases nativeReply with
   | fail error => rfl
   | div => rfl
   | ok r =>
     cases r with
     | Err error => rfl
     | Ok u =>
       change (reject (nativeTail u).result,nativeEvents++(nativeTail u).events)=
        (reject (sourceTail u).result,nativeEvents++(sourceTail u).events)
       have h:=tail u
       exact congrArg (fun x : Result A × List E => (x.1,nativeEvents++x.2)) h

theorem native_error_prefix {E A : Type} (events : List E) (error : verifier.Error)
 (next : Unit → NJU_Log.Run E (core.result.Result A verifier.Error)) :
 questionRun ⟨ok (.Err error),events⟩ next=⟨ok (.Err error),events⟩ := rfl

theorem source_abort_prefix {E A : Type} (events : List E) (error : Error)
 (next : Unit → NJU_Log.Run E (core.result.Result A verifier.Error)) :
 questionRun ⟨fail error,events⟩ next=⟨fail error,events⟩ := rfl

theorem divergence_prefix {E A : Type} (events : List E)
 (next : Unit → NJU_Log.Run E (core.result.Result A verifier.Error)) :
 questionRun ⟨div,events⟩ next=⟨div,events⟩ := rfl
#print axioms question_trace
#print axioms native_error_prefix
#print axioms source_abort_prefix
#print axioms divergence_prefix
end NLB_ErrorTransport
