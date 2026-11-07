import PCM_Rejection
import PCM_StepLaws
import PCM_Carriers
set_option autoImplicit false
namespace PCM_POOL_356
open RSL PCM
abbrev Args := Instruction × List AccountInfo
/-- Exact SolanaPoolCpiRuntimeV1 wrapper. The program::invoke implementation
is a separate OPEN SDK slot; this is not a CPI-success or readonly premise. -/
def Ref (sdkInvoke : Child Args Unit) (a : Args) : Computation Unit := sdkInvoke.call a
def RowSpec (sdkInvoke : Child Args Unit) (impl : Args → State → Env → Observation Unit) : Prop :=
  PCM.RowSpec (fun _ => True) (Ref sdkInvoke) impl

/-- At a real rejecting argument, dropping the exact child error is rejected.
`early` is supplied by the named child's canonical graph at these arguments;
this lemma is supporting work and never a parent row root. -/
theorem rejects_wrong_error (sdkInvoke : Child Args Unit) (a : Args)
    (early : sdkInvoke.call a = PCM.Computation.throw (.accountBorrowFailed)) :
    ¬ RowSpec sdkInvoke (fun _ s _ => ⟨.ret (.error .invalidArgument,s),[]⟩) := by
  apply PCM.rejects_error (fun _ => True) (Ref sdkInvoke) a (.accountBorrowFailed) .invalidArgument trivial
  · unfold Ref
    exact early
  · intro h; cases h
#print axioms rejects_wrong_error
end PCM_POOL_356
