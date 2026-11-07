import PCM_Spec_POOL_350
import PCM_Spec_POOL_348
set_option autoImplicit false
namespace PCM_POOL_347
open RSL PCM PCM.Computation
/-- Same arguments as 350 except the internally encoded request Vec. -/
structure Args where
  pool_program : B32
  master : AccountInfo
  checkpoint : AccountInfo
  lane : AccountInfo
  policy : VerifierPolicy
  registry : List AccountInfo
  verifier_program : AccountInfo
  proof : AccountInfo
  verifier_checkpoint : Option AccountInfo
  request : Request
  current_slot : UInt64
structure Children where
  plan : Child Args DispatchPlan
  invoke : Child PCM_POOL_348.Args AuthenticatedResult

def Ref (C : Children) (a : Args) : Computation AuthenticatedResult := do
  let plan ← C.plan.call a
  C.invoke.call ⟨plan,a.proof,a.master,a.checkpoint,a.lane,a.registry,a.verifier_program,a.verifier_checkpoint⟩
def RowSpec (C : Children) (impl : Args → State → Env → Observation AuthenticatedResult) : Prop :=
  PCM.RowSpec (fun _ => True) (Ref C) impl
end PCM_POOL_347
