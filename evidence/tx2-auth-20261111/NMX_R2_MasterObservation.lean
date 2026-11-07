import NMX_R2_BoxActionObservation
import NMX_MasterChild
set_option autoImplicit false
noncomputable section
namespace NMX_R2_MasterObservation
open Aeneas Aeneas.Std AspisR1
/-- Apply the CLOSED218 root at the SAME bytes and actual native cuts, then
transport its full owner/payload and stopped prefix. Obtaining these cuts at
233's reached call is still a separate parent obligation. -/
theorem packet {S : Type} (a : S2W_D189Wrappers.Allocator S) (s : S)
 (before : NKY_BoxFrame.Heap NJQ_Carrier.CM) (r : NP6_StdModel.Reservation) (allocated : Nat)
 (b : Slice U8) (raw : core.result.Result NJQ_Carrier.M NJQ_Carrier.F)
 (box : NKY_BoxAction.Owned NJQ_Carrier.CM) (readsAfter : Nat → NJQ_Carrier.CM)
 (decode : NJQ_MasterTotal.Cut b raw)
 (allocate : NKY_BoxTotal.MasterWindows a s r allocated (NJQ_Carrier.master_result raw) box)
 (frame : NKY_BoxPost.Windows NKY_FrameObservation.Master a s 304 r
  (NJQ_Carrier.master_result raw) box before readsAfter)
 (env : RSL.Env)
 (allocation : (∃ post, a.allocate s 304 = .ok post) ∨ (∃ failure, a.allocate s 304 = .fail failure)) :
 NMX_R2_Semantics.boxed allocated (NMX_MasterValue.decoded b) env
  (NMX_R2_BoxActionObservation.view (NMX_BoxPostProjection.dropHeap
   (NKY_BoxPost.native a s 304 r (NJQ_Carrier.master_result raw) box before readsAfter))) := by
 rw [NMX_MasterChild.source a s before r allocated b raw box readsAfter decode allocate frame]
 exact NMX_R2_BoxActionObservation.member a s 304 r allocated (NMX_MasterValue.decoded b) env allocation
#print axioms packet
end NMX_R2_MasterObservation
end
