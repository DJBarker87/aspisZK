import PCM_Witness
import PCM_StepLaws
import PCM_Spec_POOL_347
import PCM_ErrorMap
set_option autoImplicit false
namespace PCM_POOL_349
open RSL PCM PCM.Computation
abbrev Args := PCM_POOL_347.Args
structure Children where
  encode : Child Request Bytes
  plan : Child PCM_POOL_350.Args DispatchPlan
/-- The to_vec allocation happens before plan350's possible identity error. -/
def Ref (C : Children) (a : Args) : Computation DispatchPlan := do
  let bytes ← mapError (fun _ => .invalidInstructionData) (C.encode.call a.request)
  alloc
  C.plan.call ⟨a.pool_program,a.master,a.checkpoint,a.lane,a.policy,a.registry,
    a.verifier_program,a.proof,a.verifier_checkpoint,a.request,a.current_slot,bytes⟩
def RowSpec (C : Children) (impl : Args → State → Env → Observation DispatchPlan) : Prop :=
  PCM.RowSpec (fun _ => True) (Ref C) impl

theorem rejects_wrong_error (C : Children) (a : Args)
    (early : C.encode.call a.request = Computation.throw .invalidInstructionData) :
    ¬ RowSpec C (fun _ s _ => ⟨.ret (.error .invalidArgument,s),[]⟩) := by
  apply PCM.rejects_error (fun _ : Args => True) (Ref C) a .invalidInstructionData .invalidArgument trivial
  · unfold Ref
    rw [early,PCM.Computation.mapError_throw]
    exact PCM.Computation.bind_throw _ _
  · intro h; cases h
#print axioms rejects_wrong_error
end PCM_POOL_349
