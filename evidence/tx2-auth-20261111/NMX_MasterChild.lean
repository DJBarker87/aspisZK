import NMX_BoxPostProjection
import NMX_MasterValue
set_option autoImplicit false
noncomputable section
namespace NMX_MasterChild
open Aeneas Aeneas.Std Result AspisR1
/-- CLOSED218 installed at the SAME bytes/allocator/owner/post-read cuts.
These are the licensed native child cut fields, not a child result premise.
A parent must obtain them at its actual occurrence; this is not a233 root. -/
theorem source {S : Type} (a : S2W_D189Wrappers.Allocator S) (s : S)
 (before : NKY_BoxFrame.Heap NJQ_Carrier.CM) (r : NP6_StdModel.Reservation) (allocated : Nat)
 (b : Slice U8) (raw : core.result.Result NJQ_Carrier.M NJQ_Carrier.F)
 (box : NKY_BoxAction.Owned NJQ_Carrier.CM) (readsAfter : Nat → NJQ_Carrier.CM)
 (decode : NJQ_MasterTotal.Cut b raw)
 (allocate : NKY_BoxTotal.MasterWindows a s r allocated (NJQ_Carrier.master_result raw) box)
 (frame : NKY_BoxPost.Windows NKY_FrameObservation.Master a s 304 r
  (NJQ_Carrier.master_result raw) box before readsAfter) :
 NMX_BoxPostProjection.dropHeap
  (NKY_BoxPost.native a s 304 r (NJQ_Carrier.master_result raw) box before readsAfter) =
 NKY_BoxAction.run a s 304 r allocated (.ok (NMX_MasterValue.decoded b)) := by
 rw [NKY_BoxSource.master a s before r allocated b raw box readsAfter decode allocate frame]
 rw [NMX_BoxPostProjection.attach,NMX_MasterValue.source]
#print axioms source
end NMX_MasterChild
end
