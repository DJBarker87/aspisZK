import PCM_Rejection
import PCM_StepLaws
import PCM_ErrorMap
import PCM_Carriers
set_option autoImplicit false
namespace PCM_POOL_314
open RSL PCM PCM.Computation
abbrev Args := Bytes
/-- Frozen real callee: decode_pool_v1_pair_forest_terminal_request_v1; map all errors to InvalidInstructionData. Its graph and domain must be installed
at the SAME arguments; this module is supporting work until that installation. -/
abbrev Decoder := Child (Bytes) Request
def Ref (decoder : Decoder) (a : Args) : Computation Request := do
  let value ← mapError (fun _ => .invalidInstructionData) (decoder.call a)
  alloc
  Computation.pure value
def RowSpec (decoder : Decoder)
    (impl : Args → State → Env → Observation Request) : Prop :=
  PCM.RowSpec (fun _ => True) (Ref decoder) impl

/-- At a real rejecting argument, dropping the exact child error is rejected.
`early` is supplied by the named child's canonical graph at these arguments;
this lemma is supporting work and never a parent row root. -/
theorem rejects_wrong_error (decoder : Decoder) (a : Args)
    (early : decoder.call a = PCM.Computation.throw (.invalidInstructionData)) :
    ¬ RowSpec decoder (fun _ s _ => ⟨.ret (.error .invalidArgument,s),[]⟩) := by
  apply PCM.rejects_error (fun _ => True) (Ref decoder) a (.invalidInstructionData) .invalidArgument trivial
  · unfold Ref
    rw [early,PCM.Computation.mapError_throw]
    exact PCM.Computation.bind_throw _ _
  · intro h; cases h
#print axioms rejects_wrong_error
end PCM_POOL_314
