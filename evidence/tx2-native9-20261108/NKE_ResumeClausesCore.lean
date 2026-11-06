import NKE_ResumeAssociation
import NKE_EventTactic
set_option autoImplicit false
noncomputable section
namespace NKE_ResumeClauses
open Aeneas Aeneas.Std Result AspisR1 NID_ResumeEmission NJU_ResumeObserved
/-- SAME actual reader arguments and full replies. Digest value, header closure
and allocator/copy evidence remain separately reviewed obligations. -/
def Clause : Event → Prop
 | .raw n reader reply => reply=NJC_ConcreteUnwrap.raw n reader
 | .k reader reply => reply=NIL_FreshOps.readK reader
 | .e reader reply => reply=NIL_FreshOps.readE reader
 | .semantic bytes cursor reply => reply=NIL_FreshOps.semantic bytes cursor
 | .weights bytes cursor before reply => reply=NIL_FreshOps.weights bytes cursor before
 | .validate queries reply => reply=NJC_ValidateEmission.verifier.validate_checkpoint_queries queries
 | _ => True
end NKE_ResumeClauses
open Lean Elab Tactic
elab "nke_resume_record" : tactic => do
 let t ← getMainTarget
 unless t.isAppOf ``NKE_EventAll.Holds do throwError "not writer property"
 unless t.getAppArgs.back!.isAppOf ``NJU_Log.record do throwError "not record"
 evalTactic (← `(tactic| apply NKE_EventAll.record_all))
 evalTactic (← `(tactic| first | rfl | exact True.intro))
