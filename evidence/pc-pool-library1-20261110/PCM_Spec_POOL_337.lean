import PCM_Rejection
import PCM_StepLaws
import PCM_ErrorMap
import PCM_Carriers
set_option autoImplicit false
namespace PCM_POOL_337
open RSL PCM PCM.Computation
abbrev Encoder := Child TerminalResult Bytes
/-- Encoder Err maps to exactly Custom(0x4153202d); its by-value output has no
heap allocation. The Box site is reached only after encoder success. -/
def Ref (encoder : Encoder) (a : TerminalResult) : Computation Bytes := do
  let bytes ← mapError (fun _ => .custom 0x4153202d) (encoder.call a)
  alloc
  Computation.pure bytes
def RowSpec (encoder : Encoder) (impl : TerminalResult → State → Env → Observation Bytes) : Prop :=
  PCM.RowSpec (fun _ => True) (Ref encoder) impl

/-- At a real rejecting argument, dropping the exact child error is rejected.
`early` is supplied by the named child's canonical graph at these arguments;
this lemma is supporting work and never a parent row root. -/
theorem rejects_wrong_error (encoder : Encoder) (a : TerminalResult)
    (early : encoder.call a = PCM.Computation.throw (.custom 0x4153202d)) :
    ¬ RowSpec encoder (fun _ s _ => ⟨.ret (.error .invalidArgument,s),[]⟩) := by
  apply PCM.rejects_error (fun _ => True) (Ref encoder) a (.custom 0x4153202d) .invalidArgument trivial
  · unfold Ref
    rw [early,PCM.Computation.mapError_throw]
    exact PCM.Computation.bind_throw _ _
  · intro h; cases h
#print axioms rejects_wrong_error
end PCM_POOL_337
