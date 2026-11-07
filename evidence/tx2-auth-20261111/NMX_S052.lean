import NMX_ResultSteps
set_option autoImplicit false
noncomputable section
namespace NMX_S052
open Aeneas Aeneas.Std Result AdapterRw NMX_OwnedPackets NMX_Program NMX_SourceModel NMX_ResultSteps
/-- Source occurrence 52: snapshot; SAME typed call operands, all outcome arms.
Intermediate emitted-value/owner erasure support; no native/root credit. -/
theorem step (ops : Ops) (owners : Owners) (snapshotPool : Array U8 32#usize)
 (master : Box Master)
 (lane : Box Lane)
 (next : Box Snapshot → Program Auth) :
 NMX_ValueLink.erase (eval (source ops owners)
  (NMX_Program.bind (NMX_SourceProgram.call (.snapshot ⟨snapshotPool,master.payload.identity.deployment_domain,
  lane.payload.tree.next_leaf_index,lane.payload.tree.next_leaf_index,
  lane.payload.tree.root,lane.payload.tree.frontier⟩)) next) ()) =
 NMX_ValueLink.erase (eval (source ops owners) (next ⟨owners.snapshot,⟨snapshotPool,master.payload.identity.deployment_domain,
  lane.payload.tree.next_leaf_index,lane.payload.tree.next_leaf_index,
  lane.payload.tree.root,lane.payload.tree.frontier⟩⟩) ()) := by
 rw [NMX_StepCore.entered]
 exact NMX_ValueLink.erase_prepend [] _
#print axioms step
end NMX_S052
end
