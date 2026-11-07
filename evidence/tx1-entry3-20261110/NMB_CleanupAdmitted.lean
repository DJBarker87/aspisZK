import NMB_Cleanup
set_option autoImplicit false
noncomputable section
namespace NMB_CleanupAdmitted
open Aeneas Aeneas.Std Result AspisR1 NMB_Stage1Source NMB_Cleanup
/-- Exact semantic drop sequence for the successful child arm. Every input
buffer comes from the SAME snapshots; no new caller extent premise is added. -/
theorem source (x : NMB_Input.Input) (ops : AdapterRw.Ops) (p : Key) (d : Slice U8) (saved : Bytes)
 (accepted : AdapterRw.r1_pool_adapter.owned.stage1_owned ops p
   (NMB_ThreeSnapshots.first x) d=.ok (.Ok saved)) :
 NMB_Cleanup.G {(NMB_Stage1Tail.ready x) with checkpoint:=some saved}=
 [.checkpoint saved,.bytesValue 0 (x.buffers (x.handles 0).1),
  .bytesValue 1 (x.buffers (x.handles 1).1),.bytesValue 2 (x.buffers (x.handles 2).1)] := by
 obtain ⟨proof,pub,cp⟩ := NMB_AcceptedExtents.source x ops p d saved accepted
 simp [NMB_Cleanup.G,NMB_Cleanup.owned,NMB_Cleanup.account,
  NMB_Stage1Tail.ready,NMB_ThreeSnapshots.final,NMB_ThreeSnapshots.first,NMB_Snapshot.ready,
  NMB_Input.Input.snapshot,proof,pub,cp]
#print source
#print axioms source
end NMB_CleanupAdmitted
