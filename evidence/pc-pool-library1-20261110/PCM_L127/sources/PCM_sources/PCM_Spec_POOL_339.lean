import PCM_AvoidRejection
import PCM_Spec_POOL_336
import PCM_Spec_POOL_338
import PCM_Spec_POOL_342
import PCM_ErrorMap
import PCM_Carriers
set_option autoImplicit false
namespace PCM_POOL_339
open RSL PCM PCM.Computation
abbrev CommonArgs := B32 × B32 × B32 × Master × Checkpoint × LaneState × UInt8 × TerminalResult
abbrev Args := B32 × B32 × B32 × Master × Checkpoint × LaneState × UInt8 × Request × TerminalResult
structure Children where
  validate : Child (Statement × TerminalResult) Unit
/-- Both Box allocations belong to the named children; they happen before
the final validator may return InvalidVerifierReturnData (0x4153202d). -/
def Ref (C : Children) (a : Args) : Computation Unit := do
  let (masterKey,checkpointKey,laneKey,master,checkpoint,lane,output,request,result) := a
  let common ← PCM_POOL_336.Ref (masterKey,checkpointKey,laneKey,master,checkpoint,lane,output,result)
  let statement ← match request.pub with
    | .transfer p => PCM_POOL_338.Ref (common,p)
    | .withdrawal p => PCM_POOL_342.Ref (common,p)
  mapError (fun _ => .custom 0x4153202d) (C.validate.call (statement,result))
def RowSpec (C : Children) (impl : Args → State → Env → Observation Unit) : Prop :=
  PCM.RowSpec (fun _ => True) (Ref C) impl

theorem avoids_wrong_error (C : Children) (a : Args) :
    PCM.Computation.Avoid .invalidArgument (Ref C a) := by
  rcases a with ⟨ma,ca,la,master,checkpoint,lane,output,request,result⟩
  unfold Ref
  apply PCM.Computation.bind_avoid
  · unfold PCM_POOL_336.Ref
    apply PCM.Computation.bind_avoid
    · exact PCM.Computation.alloc_avoid _
    · intro u; exact PCM.Computation.pure_avoid _ _
  · intro common
    apply PCM.Computation.bind_avoid
    · cases request.pub <;> (
        first | unfold PCM_POOL_338.Ref | unfold PCM_POOL_342.Ref)
      all_goals
        apply PCM.Computation.bind_avoid
        · exact PCM.Computation.alloc_avoid _
        · intro u; exact PCM.Computation.pure_avoid _ _
    · intro statement
      exact PCM.Computation.mapError_avoid _ _ (by intro h; cases h) _

theorem rejects_wrong_error (C : Children) (a : Args) :
    ¬ RowSpec C (fun _ s _ => ⟨.ret (.error .invalidArgument,s),[]⟩) :=
  PCM.rejects_avoided_error (fun _ : Args => True) (Ref C) a trivial
    .invalidArgument (avoids_wrong_error C a)
#print axioms avoids_wrong_error
#print axioms rejects_wrong_error
end PCM_POOL_339
