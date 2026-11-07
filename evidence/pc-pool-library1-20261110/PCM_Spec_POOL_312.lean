import PCM_Rejection
import PCM_StepLaws
import PCM_Carriers
set_option autoImplicit false
namespace PCM_POOL_312
open RSL PCM PCM.Computation
abbrev Args := B32 × B32 × UInt8 × AccountInfo
/-- Frozen real callee: decode_lane_account_from_program_invariant_v1 (writable=true). Its graph and domain must be installed
at the SAME arguments; this module is supporting work until that installation. -/
abbrev Decoder := Child ((B32 × B32 × UInt8 × AccountInfo) × Bool) LaneState
def Ref (decoder : Decoder) (a : Args) : Computation LaneState := do
  let value ← decoder.call (a,true)
  alloc
  Computation.pure value
def RowSpec (decoder : Decoder)
    (impl : Args → State → Env → Observation LaneState) : Prop :=
  PCM.RowSpec (fun _ => True) (Ref decoder) impl

/-- At a real rejecting argument, dropping the exact child error is rejected.
`early` is supplied by the named child's canonical graph at these arguments;
this lemma is supporting work and never a parent row root. -/
theorem rejects_wrong_error (decoder : Decoder) (a : Args)
    (early : decoder.call (a,true) = PCM.Computation.throw (.invalidAccountData)) :
    ¬ RowSpec decoder (fun _ s _ => ⟨.ret (.error .invalidArgument,s),[]⟩) := by
  apply PCM.rejects_error (fun _ => True) (Ref decoder) a (.invalidAccountData) .invalidArgument trivial
  · unfold Ref
    rw [early]
    exact PCM.Computation.bind_throw _ _
  · intro h; cases h
#print axioms rejects_wrong_error
end PCM_POOL_312
