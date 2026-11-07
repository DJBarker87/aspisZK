import PCM_Rejection
import PCM_StepLaws
import PCM_Carriers
set_option autoImplicit false
namespace PCM_POOL_357
open RSL PCM
abbrev Args := Instruction × List AccountInfo × List (List Bytes)
def Ref (sdkInvokeSigned : Child Args Unit) (a : Args) : Computation Unit := sdkInvokeSigned.call a
def RowSpec (sdkInvokeSigned : Child Args Unit) (impl : Args → State → Env → Observation Unit) : Prop :=
  PCM.RowSpec (fun _ => True) (Ref sdkInvokeSigned) impl

/-- At a real rejecting argument, dropping the exact child error is rejected.
`early` is supplied by the named child's canonical graph at these arguments;
this lemma is supporting work and never a parent row root. -/
theorem rejects_wrong_error (sdkInvokeSigned : Child Args Unit) (a : Args)
    (early : sdkInvokeSigned.call a = PCM.Computation.throw (.accountBorrowFailed)) :
    ¬ RowSpec sdkInvokeSigned (fun _ s _ => ⟨.ret (.error .invalidArgument,s),[]⟩) := by
  apply PCM.rejects_error (fun _ => True) (Ref sdkInvokeSigned) a (.accountBorrowFailed) .invalidArgument trivial
  · unfold Ref
    exact early
  · intro h; cases h
#print axioms rejects_wrong_error
end PCM_POOL_357
