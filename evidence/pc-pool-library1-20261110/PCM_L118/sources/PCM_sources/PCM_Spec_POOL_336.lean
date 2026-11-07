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
end PCM_POOL_336
