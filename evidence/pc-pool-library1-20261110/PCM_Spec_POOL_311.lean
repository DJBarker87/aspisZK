import PCM_Rejection
import PCM_StepLaws
import PCM_Carriers
set_option autoImplicit false
namespace PCM_POOL_311
open RSL PCM PCM.Computation
abbrev Args := B32 × B32 × AccountInfo
/-- Frozen real callee: decode_retained_pair_forest_checkpoint_account_v1. Its graph and domain must be installed
at the SAME arguments; this module is supporting work until that installation. -/
abbrev Decoder := Child (B32 × B32 × AccountInfo) Checkpoint
def Ref (decoder : Decoder) (a : Args) : Computation Checkpoint := do
  let value ← decoder.call a
  alloc
  Computation.pure value
def RowSpec (decoder : Decoder)
    (impl : Args → State → Env → Observation Checkpoint) : Prop :=
  PCM.RowSpec (fun _ => True) (Ref decoder) impl

/-- At a real rejecting argument, dropping the exact child error is rejected.
`early` is supplied by the named child's canonical graph at these arguments;
this lemma is supporting work and never a parent row root. -/
theorem rejects_wrong_error (decoder : Decoder) (a : Args)
    (early : decoder.call a = PCM.Computation.throw (.invalidAccountData)) :
    ¬ RowSpec decoder (fun _ s _ => ⟨.ret (.error .invalidArgument,s),[]⟩) := by
  apply PCM.rejects_error (fun _ => True) (Ref decoder) a (.invalidAccountData) .invalidArgument trivial
  · unfold Ref
    rw [early]
    exact PCM.Computation.bind_throw _ _
  · intro h; cases h
#print axioms rejects_wrong_error
end PCM_POOL_311
