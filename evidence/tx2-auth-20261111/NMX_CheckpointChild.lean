import NMX_BoxPostProjection
import NMX_CheckpointValue
set_option autoImplicit false
noncomputable section
namespace NMX_CheckpointChild
open Aeneas Aeneas.Std Result AspisR1

theorem source {S : Type} (a : S2W_D189Wrappers.Allocator S) (s : S)
 (before : NKY_BoxFrame.Heap NJQ_Carrier.CC) (r : NP6_StdModel.Reservation) (allocated : Nat)
 (b : Slice U8) (raw : core.result.Result NJQ_Carrier.C NJQ_Carrier.F)
 (box : NKY_BoxAction.Owned NJQ_Carrier.CC) (readsAfter : Nat → NJQ_Carrier.CC)
 (decode : NJQ_CheckpointTotal.Cut b raw)
 (allocate : NKY_BoxTotal.CheckpointWindows a s r allocated (NJQ_Carrier.checkpoint_result raw) box)
 (frame : NKY_BoxPost.Windows NKY_FrameObservation.Checkpoint a s 176 r
  (NJQ_Carrier.checkpoint_result raw) box before readsAfter) :
 NMX_BoxPostProjection.dropHeap
  (NKY_BoxPost.native a s 176 r (NJQ_Carrier.checkpoint_result raw) box before readsAfter) =
 NKY_BoxAction.run a s 176 r allocated (.ok (NMX_CheckpointValue.decoded b)) := by
 rw [NKY_BoxSource.checkpoint a s before r allocated b raw box readsAfter decode allocate frame]
 rw [NMX_BoxPostProjection.attach,NMX_CheckpointValue.source]
#print axioms source
end NMX_CheckpointChild
end
