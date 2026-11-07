import PCM_AvoidRejection
import PCM_Carriers
set_option autoImplicit false
namespace PCM_POOL_336
open RSL PCM PCM.Computation
abbrev Args := B32 × B32 × B32 × Master × Checkpoint × LaneState × UInt8 × TerminalResult
def value (a : Args) : Common :=
  let (ma,ca,la,m,c,l,output,r) := a
  ⟨ma,ca,la,output,c.checkpoint_sequence,c.global_root,
    ⟨ma,m.identity.deployment_domain,l.tree.next_leaf_index,l.tree.next_leaf_index,l.tree.root,l.tree.frontier⟩,
    r.verified_afterstate⟩
def Ref (a : Args) : Computation Common := do
  alloc
  Computation.pure (value a)
def RowSpec (impl : Args → State → Env → Observation Common) : Prop :=
  PCM.RowSpec (fun _ => True) Ref impl

theorem rejects_wrong_error (a : Args) :
    ¬ RowSpec (fun _ s _ => ⟨.ret (.error .invalidArgument,s),[]⟩) := by
  apply PCM.rejects_avoided_error (fun _ : Args => True) Ref a trivial .invalidArgument
  unfold Ref
  apply PCM.Computation.bind_avoid
  · exact PCM.Computation.alloc_avoid _
  · intro u
    exact PCM.Computation.pure_avoid _ _
#print axioms rejects_wrong_error
end PCM_POOL_336
