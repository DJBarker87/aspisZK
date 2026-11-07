import PCM_Rejection
import PCM_StepLaws
import PCM_Carriers
import PCM_ErrorMap
set_option autoImplicit false
namespace PCM_POOL_294
open RSL PCM PCM.Computation
abbrev Args := B32 × AccountInfo × Marker
structure Children where
  encode : Child Marker Bytes
  canonicalNullifier : Marker → B32
  address : Child (B32 × B32 × B32) (B32 × B32)
  classify : Child (B32 × AccountInfo) Preparation

def Ref (C : Children) (a : Args) : Computation PlannedMarker := do
  let (program,account,marker) := a
  let encoded ← mapError (fun _ => .custom 0x41532025) (C.encode.call marker)
  let (expected,seed) ← C.address.call (program,marker.pool,C.canonicalNullifier marker)
  check (account.key != expected || account.key == marker.pool) (.custom 0x41532024)
  let prep ← C.classify.call (program,account)
  Computation.pure ⟨prep,seed,encoded⟩
def RowSpec (C : Children) (impl : Args → State → Env → Observation PlannedMarker) : Prop :=
  PCM.RowSpec (fun _ => True) (Ref C) impl

/-- At a real rejecting argument, dropping the exact child error is rejected.
`early` is supplied by the named child's canonical graph at these arguments;
this lemma is supporting work and never a parent row root. -/
theorem rejects_wrong_error (C : Children) (a : Args)
    (early : C.encode.call a.2.2 = PCM.Computation.throw (.custom 0x41532025)) :
    ¬ RowSpec C (fun _ s _ => ⟨.ret (.error .invalidArgument,s),[]⟩) := by
  apply PCM.rejects_error (fun _ => True) (Ref C) a (.custom 0x41532025) .invalidArgument trivial
  · rcases a with ⟨program,account,marker⟩
    unfold Ref
    dsimp only at early ⊢
    rw [early,PCM.Computation.mapError_throw]
    exact PCM.Computation.bind_throw _ _
  · intro h; cases h
#print axioms rejects_wrong_error
end PCM_POOL_294
