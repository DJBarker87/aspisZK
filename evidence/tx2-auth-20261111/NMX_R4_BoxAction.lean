import NMX_R4_BoxValue
import NMX_R2_BoxActionObservation
import NMX_R2_NativeExecution
set_option autoImplicit false
noncomputable section
namespace NMX_R4_BoxAction
open Aeneas Aeneas.Std Result AspisR1 NMX_OwnedPackets

/-- A reached std allocator decision. Returning allocations return their
poststate; failure has no invented poststate. This is the retained std item. -/
def allocator (aborts : Bool) : S2W_D189Wrappers.Allocator Unit :=
 ⟨(fun _ _ => if aborts then .fail .panic else .ok ()),(fun _ => .ok ())⟩

theorem view {A : Type} (aborts : Bool) (owner size : Nat)
 (decoded : core.result.Result A NKY_BoxAction.PE) :
 NMX_R2_BoxActionObservation.view
   (NKY_BoxAction.run (allocator aborts) () size (.Ok ()) owner (.ok decoded)) =
 NMX_R2_NativeExecution.box aborts owner decoded := by
 cases decoded with
 | Err e => rfl
 | Ok a => cases aborts <;> rfl

def master (aborts : Bool) (owner : Nat) (b : Slice U8) :=
 NKY_BoxAction.run (allocator aborts) () 304 (.Ok ()) owner
  (NMX_R4_BoxEmitted.master NJQ_Canonical.master b)

def checkpoint (aborts : Bool) (owner : Nat) (b : Slice U8) :=
 NKY_BoxAction.run (allocator aborts) () 176 (.Ok ()) owner
  (NMX_R4_BoxEmitted.checkpoint NJQ_Canonical.checkpoint b)

theorem master_source (aborts : Bool) (owner : Nat) (b : Slice U8) :
 NMX_R2_BoxActionObservation.view (master aborts owner b) =
 NMX_R2_NativeExecution.box aborts owner (NMX_MasterValue.decoded b) := by
 unfold master
 rw [NMX_R4_BoxValue.master,NMX_MasterValue.source]
 exact view aborts owner 304 (NMX_MasterValue.decoded b)

theorem checkpoint_source (aborts : Bool) (owner : Nat) (b : Slice U8) :
 NMX_R2_BoxActionObservation.view (checkpoint aborts owner b) =
 NMX_R2_NativeExecution.box aborts owner (NMX_CheckpointValue.decoded b) := by
 unfold checkpoint
 rw [NMX_R4_BoxValue.checkpoint,NMX_CheckpointValue.source]
 exact view aborts owner 176 (NMX_CheckpointValue.decoded b)

/-- CLOSED allocation/frame packet at the original emitted child input. -/
theorem master_packet (aborts : Bool) (owner : Nat) (b : Slice U8)
 (heap : NKY_BoxFrame.Heap Master) :
 NKY_BoxPacket.Law (allocator aborts) () 304 8 (.Ok ()) owner heap
   (NMX_R4_BoxEmitted.master NJQ_Canonical.master b) :=
 NKY_BoxPacket.complete _ _ _ _ _ _ _ _

theorem checkpoint_packet (aborts : Bool) (owner : Nat) (b : Slice U8)
 (heap : NKY_BoxFrame.Heap Checkpoint) :
 NKY_BoxPacket.Law (allocator aborts) () 176 8 (.Ok ()) owner heap
   (NMX_R4_BoxEmitted.checkpoint NJQ_Canonical.checkpoint b) :=
 NKY_BoxPacket.complete _ _ _ _ _ _ _ _
#print axioms view
#print axioms master_source
#print axioms checkpoint_source
#print axioms master_packet
#print axioms checkpoint_packet
end NMX_R4_BoxAction
end
