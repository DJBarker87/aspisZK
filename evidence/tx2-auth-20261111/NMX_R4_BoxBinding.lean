import NMX_R4_BoxAction
import LIBB_PoolAccounts
set_option autoImplicit false
noncomputable section
namespace NMX_R4_BoxBinding
open Aeneas Aeneas.Std Result AspisR1

theorem master_congr (first second : Slice U8 → Result
 (core.result.Result NMX_OwnedPackets.Master NJQ_Carrier.CF))
 (b : Slice U8) (same : first b = second b) :
 NMX_R4_BoxEmitted.master first b = NMX_R4_BoxEmitted.master second b := by
 unfold NMX_R4_BoxEmitted.master
 rw [same]

theorem checkpoint_congr (first second : Slice U8 → Result
 (core.result.Result NMX_OwnedPackets.Checkpoint NJQ_Carrier.CF))
 (b : Slice U8) (same : first b = second b) :
 NMX_R4_BoxEmitted.checkpoint first b = NMX_R4_BoxEmitted.checkpoint second b := by
 unfold NMX_R4_BoxEmitted.checkpoint
 rw [same]

/-- The CLOSED raw native root is installed at the SAME byte argument before
interpreting the freshly emitted wrapper and its named std allocation site.
Unlike the former native Box-window path, no parent Box-field/window premise
is needed: this wrapper now emits, with Box::new under the pinned std item. -/
theorem master (b : Slice U8) (raw : core.result.Result NJQ_Carrier.M NJQ_Carrier.F)
 (cut : NJQ_MasterTotal.Cut b raw) (aborts : Bool) (owner : Nat) :
 NKY_BoxAction.run (NMX_R4_BoxAction.allocator aborts) () 304 (.Ok ()) owner
  (NMX_R4_BoxEmitted.master (fun _ => .ok (NJQ_Carrier.master_result raw)) b) =
 NMX_R4_BoxAction.master aborts owner b := by
 unfold NMX_R4_BoxAction.master
 rw [master_congr _ NJQ_Canonical.master b (NJQ_Canonical.master_result b raw cut)]

theorem checkpoint (b : Slice U8) (raw : core.result.Result NJQ_Carrier.C NJQ_Carrier.F)
 (cut : NJQ_CheckpointTotal.Cut b raw) (aborts : Bool) (owner : Nat) :
 NKY_BoxAction.run (NMX_R4_BoxAction.allocator aborts) () 176 (.Ok ()) owner
  (NMX_R4_BoxEmitted.checkpoint (fun _ => .ok (NJQ_Carrier.checkpoint_result raw)) b) =
 NMX_R4_BoxAction.checkpoint aborts owner b := by
 unfold NMX_R4_BoxAction.checkpoint
 rw [checkpoint_congr _ NJQ_Canonical.checkpoint b (NJQ_Canonical.checkpoint_result b raw cut)]

#print axioms master_congr
#print axioms checkpoint_congr
#print axioms master
#print axioms checkpoint
end NMX_R4_BoxBinding
end
