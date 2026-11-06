import NKY_BoxPostWindows
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKY_BoxSource
open Aeneas Aeneas.Std Result
open NKY_BoxAction
open NKY_BoxFrame (Heap)
/-- Exact actual carrier, allocator post and observed caller-visible post-heap
in the SAME wrapper Result. The only native hypotheses are field/pointer
windows and per-cell frame windows; neither a successful allocation nor a
whole poststate equality is an input. -/
theorem checkpoint {S : Type} (a : S2W_D189Wrappers.Allocator S) (s : S)
 (before : Heap NJQ_Carrier.CC) (r : NP6_StdModel.Reservation) (allocated : Nat)
 (bytes : Slice U8) (raw : core.result.Result NJQ_Carrier.C NJQ_Carrier.F)
 (box : Owned NJQ_Carrier.CC) (readsAfter : Nat → NJQ_Carrier.CC)
 (decoder : NJQ_CheckpointTotal.Cut bytes raw)
 (returned : NKY_BoxTotal.CheckpointWindows a s r allocated (NJQ_Carrier.checkpoint_result raw) box)
 (frame : NKY_BoxPost.Windows NKY_FrameObservation.Checkpoint a s 176 r
  (NJQ_Carrier.checkpoint_result raw) box before readsAfter) :
 NKY_BoxPost.native a s 176 r (NJQ_Carrier.checkpoint_result raw) box before readsAfter=
 NKY_BoxPost.attach before (run a s 176 r allocated (NKF_CheckpointBox.reference bytes)) := by
 have result := (NKY_BoxTotal.checkpoint a s before r allocated bytes raw box decoder returned).1
 exact (NKY_BoxPost.association a s 176 r _ box before readsAfter
  (NKY_BoxPostWindows.checkpoint a s r _ box before readsAfter frame)).trans
  (congrArg (NKY_BoxPost.attach before) result)

theorem master {S : Type} (a : S2W_D189Wrappers.Allocator S) (s : S)
 (before : Heap NJQ_Carrier.CM) (r : NP6_StdModel.Reservation) (allocated : Nat)
 (bytes : Slice U8) (raw : core.result.Result NJQ_Carrier.M NJQ_Carrier.F)
 (box : Owned NJQ_Carrier.CM) (readsAfter : Nat → NJQ_Carrier.CM)
 (decoder : NJQ_MasterTotal.Cut bytes raw)
 (returned : NKY_BoxTotal.MasterWindows a s r allocated (NJQ_Carrier.master_result raw) box)
 (frame : NKY_BoxPost.Windows NKY_FrameObservation.Master a s 304 r
  (NJQ_Carrier.master_result raw) box before readsAfter) :
 NKY_BoxPost.native a s 304 r (NJQ_Carrier.master_result raw) box before readsAfter=
 NKY_BoxPost.attach before (run a s 304 r allocated (NKF_MasterBox.reference bytes)) := by
 have result := (NKY_BoxTotal.master a s before r allocated bytes raw box decoder returned).1
 exact (NKY_BoxPost.association a s 304 r _ box before readsAfter
  (NKY_BoxPostWindows.master a s r _ box before readsAfter frame)).trans
  (congrArg (NKY_BoxPost.attach before) result)
#print checkpoint
#print axioms checkpoint
#print master
#print axioms master
end AspisR1.NKY_BoxSource
end
