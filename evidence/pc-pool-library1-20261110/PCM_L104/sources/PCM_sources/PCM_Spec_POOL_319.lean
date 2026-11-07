import PCM_Rejection
import PCM_StepLaws
import PCM_ErrorMap
import PCM_Carriers
set_option autoImplicit false
namespace PCM_POOL_319
open RSL PCM PCM.Computation
abbrev Args := LaneState × TerminalResult
structure Children where
  nextLane : Child Args LaneState
  encodeLane : Child LaneState Bytes
/-- Deployed source-result-invariant-audit ON: a next-lane Box allocation
precedes the encoder, so even a later encoder Err has a real earlier abort arm. -/
def Ref (C : Children) (a : Args) : Computation Bytes := do
  let lane ← C.nextLane.call a
  alloc
  let image ← C.encodeLane.call lane
  alloc
  Computation.pure image

def RowSpec (C : Children) (impl : Args → State → Env → Observation Bytes) : Prop :=
  PCM.RowSpec (fun _ => True) (Ref C) impl

/-- At a real rejecting argument, dropping the exact child error is rejected.
`early` is supplied by the named child's canonical graph at these arguments;
this lemma is supporting work and never a parent row root. -/
theorem rejects_wrong_error (C : Children) (a : Args)
    (early : C.nextLane.call a = PCM.Computation.throw (.custom 0x41532003)) :
    ¬ RowSpec C (fun _ s _ => ⟨.ret (.error .invalidArgument,s),[]⟩) := by
  apply PCM.rejects_error (fun _ => True) (Ref C) a (.custom 0x41532003) .invalidArgument trivial
  · unfold Ref
    rw [early]
    exact PCM.Computation.bind_throw _ _
  · intro h; cases h
#print axioms rejects_wrong_error
end PCM_POOL_319
