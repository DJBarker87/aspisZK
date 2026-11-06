import NLB_ErrorTransport
set_option autoImplicit false
noncomputable section
namespace NLB_ErrorTransport
open Aeneas Aeneas.Std Result VTop_Stages AspisR1 NJU_CommonObserved
/-- Only the named Merkle return boundary is projected. Every other occurrence
retains its entire payload and full Result, with order and multiplicity intact. -/
def projectEvent : Event → Event
 | .merkle proof p root (.ok (.Err _)) => .merkle proof p root (.fail .panic)
 | event => event

def observeCommon {A : Type} (m : NJU_Log.Run Event (core.result.Result A verifier.Error)) :
 Result A × List Event := (reject m.result,m.events.map projectEvent)

theorem merkle_event (proof : Slice U8) (p : verifier.Prepared) (root : Array U8 32#usize)
 (native source : R Unit) (child : ReplyRel native source) :
 projectEvent (.merkle proof p root native)=projectEvent (.merkle proof p root source) := by
 cases child <;> rfl

/-- Prefix transport for any identical preceding primitive/child invocation;
its entire log is retained, including on fail/div. -/
theorem observe_bind_congr {A B : Type} (m : NJU_Log.Run Event A)
 (native source : A → NJU_Log.Run Event (core.result.Result B verifier.Error))
 (tail : ∀ a,observeCommon (native a)=observeCommon (source a)) :
 observeCommon (m >>= native)=observeCommon (m >>= source) := by
 rcases m with ⟨reply,events⟩
 cases reply with
 | fail error => rfl
 | div => rfl
 | ok value =>
   change (reject (native value).result,(events++(native value).events).map projectEvent)=
    (reject (source value).result,(events++(source value).events).map projectEvent)
   rw [List.map_append,List.map_append]
   exact congrArg (fun x : Result B × List Event => (x.1,events.map projectEvent++x.2)) (tail value)
#print axioms merkle_event
#print axioms observe_bind_congr
end NLB_ErrorTransport
