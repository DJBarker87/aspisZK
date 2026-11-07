import NMX_R2_BoxActionObservation
import NMX_CheckpointChild
set_option autoImplicit false
noncomputable section
namespace NMX_R2_CheckpointObservation
open Aeneas Aeneas.Std AspisR1
/-- Apply the CLOSED216 root at the SAME bytes and actual native cuts, then
transport its full owner/payload and stopped prefix. Obtaining these cuts at
233's reached call is still a separate parent obligation. -/
theorem packet {S : Type} (a : S2W_D189Wrappers.Allocator S) (s : S)
 (before : NKY_BoxFrame.Heap NJQ_Carrier.CC) (r : NP6_StdModel.Reservation) (allocated : Nat)
 (b : Slice U8) (raw : core.result.Result NJQ_Carrier.C NJQ_Carrier.F)
 (box : NKY_BoxAction.Owned NJQ_Carrier.CC) (readsAfter : Nat → NJQ_Carrier.CC)
 (decode : NJQ_CheckpointTotal.Cut b raw)
 (allocate : NKY_BoxTotal.CheckpointWindows a s r allocated (NJQ_Carrier.checkpoint_result raw) box)
 (frame : NKY_BoxPost.Windows NKY_FrameObservation.Checkpoint a s 176 r
  (NJQ_Carrier.checkpoint_result raw) box before readsAfter)
 (env : RSL.Env)
 (allocation : (∃ post, a.allocate s 176 = .ok post) ∨ (∃ failure, a.allocate s 176 = .fail failure)) :
 NMX_R2_Semantics.boxed allocated (NMX_CheckpointValue.decoded b) env
  (NMX_R2_BoxActionObservation.view (NMX_BoxPostProjection.dropHeap
   (NKY_BoxPost.native a s 176 r (NJQ_Carrier.checkpoint_result raw) box before readsAfter))) := by
 rw [NMX_CheckpointChild.source a s before r allocated b raw box readsAfter decode allocate frame]
 exact NMX_R2_BoxActionObservation.member a s 176 r allocated (NMX_CheckpointValue.decoded b) env allocation
#print axioms packet
end NMX_R2_CheckpointObservation
end
